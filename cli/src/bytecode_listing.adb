--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Listings of compiled chunks for the pyro program.

pragma SPARK_Mode (Off);

with Ada.Characters.Handling;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with GNAT.OS_Lib;
with Interfaces;
with Interfaces.C;
with Pyro.Integer_Arithmetic;

package body Bytecode_Listing is

   use Pyro.Bytecode;
   use type Pyro.Symbols.Symbol_Index;

   Output : Unbounded_String;

   procedure Put (Text : String) is
   begin
      Append (Output, Text);
      if Length (Output) > 65_536 then
         declare
            Text_Out : constant String := To_String (Output);
            Written  : Integer;
            pragma Unreferenced (Written);
         begin
            Written := GNAT.OS_Lib.Write (GNAT.OS_Lib.Standout, Text_Out'Address, Text_Out'Length);
            Output := Null_Unbounded_String;
         end;
      end if;
   end Put;

   procedure Flush is
      Text_Out : constant String := To_String (Output);
      Written  : Integer;
      pragma Unreferenced (Written);
   begin
      if Text_Out'Length > 0 then
         Written := GNAT.OS_Lib.Write (GNAT.OS_Lib.Standout, Text_Out'Address, Text_Out'Length);
      end if;
      Output := Null_Unbounded_String;
   end Flush;

   function Image (Value : Long_Long_Integer) return String is
      Text : constant String := Long_Long_Integer'Image (Value);
   begin
      return (if Text (Text'First) = ' ' then Text (Text'First + 1 .. Text'Last) else Text);
   end Image;

   function Image (Value : Integer) return String is (Image (Long_Long_Integer (Value)));

   --  [puc lopcodes.c:luaP_opnames].
   type Name_Access is access constant String;
   Names : constant array (Opcode) of Name_Access :=
     [new String'("MOVE"), new String'("LOADI"), new String'("LOADF"), new String'("LOADK"),
      new String'("LOADKX"), new String'("LOADFALSE"), new String'("LFALSESKIP"),
      new String'("LOADTRUE"), new String'("LOADNIL"), new String'("GETUPVAL"),
      new String'("SETUPVAL"), new String'("GETTABUP"), new String'("GETTABLE"),
      new String'("GETI"), new String'("GETFIELD"), new String'("SETTABUP"),
      new String'("SETTABLE"), new String'("SETI"), new String'("SETFIELD"),
      new String'("NEWTABLE"), new String'("SELF"), new String'("ADDI"), new String'("ADDK"),
      new String'("SUBK"), new String'("MULK"), new String'("MODK"), new String'("POWK"),
      new String'("DIVK"), new String'("IDIVK"), new String'("BANDK"), new String'("BORK"),
      new String'("BXORK"), new String'("SHRI"), new String'("SHLI"), new String'("ADD"),
      new String'("SUB"), new String'("MUL"), new String'("MOD"), new String'("POW"),
      new String'("DIV"), new String'("IDIV"), new String'("BAND"), new String'("BOR"),
      new String'("BXOR"), new String'("SHL"), new String'("SHR"), new String'("MMBIN"),
      new String'("MMBINI"), new String'("MMBINK"), new String'("UNM"), new String'("BNOT"),
      new String'("NOT"), new String'("LEN"), new String'("CONCAT"), new String'("CLOSE"),
      new String'("TBC"), new String'("JMP"), new String'("EQ"), new String'("LT"),
      new String'("LE"), new String'("EQK"), new String'("EQI"), new String'("LTI"),
      new String'("LEI"), new String'("GTI"), new String'("GEI"), new String'("TEST"),
      new String'("TESTSET"), new String'("CALL"), new String'("TAILCALL"),
      new String'("RETURN"), new String'("RETURN0"), new String'("RETURN1"),
      new String'("FORLOOP"), new String'("FORPREP"), new String'("TFORPREP"),
      new String'("TFORCALL"), new String'("TFORLOOP"), new String'("SETLIST"),
      new String'("CLOSURE"), new String'("VARARG"), new String'("VARARGPREP"),
      new String'("EXTRAARG")];

   --  [puc ltm.c:luaT_eventname].
   Events : constant array (0 .. 24) of Name_Access :=
     [new String'("__index"), new String'("__newindex"), new String'("__gc"),
      new String'("__mode"), new String'("__len"), new String'("__eq"), new String'("__add"),
      new String'("__sub"), new String'("__mul"), new String'("__mod"), new String'("__pow"),
      new String'("__div"), new String'("__idiv"), new String'("__band"), new String'("__bor"),
      new String'("__bxor"), new String'("__shl"), new String'("__shr"), new String'("__unm"),
      new String'("__bnot"), new String'("__lt"), new String'("__le"), new String'("__concat"),
      new String'("__call"), new String'("__close")];

   function Hexadecimal (Value : Natural) return String is
      Digits_Text : constant String := "0123456789abcdef";
      Result      : String (1 .. 12) := [others => '0'];
      Remaining   : Natural := Value;
   begin
      for Position in reverse Result'Range loop
         Result (Position) := Digits_Text (Remaining mod 16 + 1);
         Remaining := Remaining / 16;
      end loop;
      return "0x" & Result;
   end Hexadecimal;

   procedure Print
     (Item      : Pyro.Bytecode.Chunk;
      Symbols   : Pyro.Symbols.Symbol_Table;
      Source    : Pyro.Sources.Source;
      Lua_Style : Boolean)
   is
      --  The made-up address or number of prototype P.
      --  [differs] luac prints the prototype's memory address.
      function Name_Of (P : Prototype_Index) return String
      is (if Lua_Style then Hexadecimal (16#1000# + Natural (P) * 16#100#)
          else "#" & Image (Natural (P)));

      function Symbol_Text (Symbol : Pyro.Symbols.Symbol_Index) return String
      is (if Symbol = Pyro.Symbols.No_Symbol then "" else Pyro.Symbols.Text (Symbols, Symbol));

      --  [puc luac.c:PrintString].
      procedure Put_String (Text : String) is
      begin
         Put ("""");
         for Byte of Text loop
            case Byte is
               when '"' => Put ("\""");
               when '\' => Put ("\\");
               when ASCII.BEL => Put ("\a");
               when ASCII.BS => Put ("\b");
               when ASCII.FF => Put ("\f");
               when ASCII.LF => Put ("\n");
               when ASCII.CR => Put ("\r");
               when ASCII.HT => Put ("\t");
               when ASCII.VT => Put ("\v");
               when others =>
                  if Byte in ' ' .. '~' then
                     Put ([1 => Byte]);
                  else
                     declare
                        Code : constant String := Image (Integer (Character'Pos (Byte)));
                     begin
                        Put ("\" & [1 .. 3 - Code'Length => '0'] & Code);
                     end;
                  end if;
            end case;
         end loop;
         Put ("""");
      end Put_String;

      function Float_Image (Bits : Interfaces.Unsigned_64) return String is
         function Format
           (Bits : Interfaces.Unsigned_64; Buffer : out Interfaces.C.char_array;
            Size : Interfaces.C.int) return Interfaces.C.int
         with Import, Convention => C, External_Name => "pyro_format_float";
         Buffer : Interfaces.C.char_array (0 .. 99);
         Length : constant Natural := Natural (Format (Bits, Buffer, 100));
         Text   : String (1 .. Length);
      begin
         for Index in Text'Range loop
            Text (Index) := Character (Buffer (Interfaces.C.size_t (Index - 1)));
         end loop;
         return Text;
      end Float_Image;

      --  [puc luac.c:PrintConstant].
      procedure Put_Constant (P : Prototype_Index; Number : Natural) is
      begin
         if Number >= Constant_Count (Item, P) then
            Put ("?");
            return;
         end if;
         declare
            Value : constant Constant_Value := Constant_At (Item, P, Number);
         begin
            case Value.Kind is
               when Nil_Constant => Put ("nil");
               when False_Constant => Put ("false");
               when True_Constant => Put ("true");
               when Float_Constant =>
                  declare
                     Text : constant String := Float_Image (Value.Bits);
                  begin
                     Put (Text);
                     if (for all Byte of Text => Byte in '-' | '0' .. '9') then
                        Put (".0");
                     end if;
                  end;
               when Integer_Constant =>
                  Put (Image (Long_Long_Integer
                         (Pyro.Integer_Arithmetic.To_Signed (Value.Bits))));
               when Short_String_Constant | Long_String_Constant =>
                  Put_String (Symbol_Text (Value.Symbol));
            end case;
         end;
      end Put_Constant;

      function Type_Of (Kind : Constant_Kind) return String
      is (case Kind is
            when Nil_Constant => "N",
            when False_Constant | True_Constant => "B",
            when Float_Constant => "F",
            when Integer_Constant => "I",
            when Short_String_Constant | Long_String_Constant => "S");

      function Plural (Count : Natural) return String is (if Count = 1 then "" else "s");

      procedure Put_Function (P : Prototype_Index) is
         Facts : constant Prototype_Header := Header (Item, P);
         Count : constant Natural := Code_Length (Item, P);

         function Upvalue_Name (Number : Natural) return String
         is (if Number < Upvalue_Count (Item, P)
                and then Upvalue_At (Item, P, Number).Name /= Pyro.Symbols.No_Symbol
             then Symbol_Text (Upvalue_At (Item, P, Number).Name) else "-");

         function Extra_Argument (PC : Natural) return Natural
         is (if PC + 1 < Count then Natural (Instruction_At (Item, P, PC + 1).Wide) else 0);

         Chunk_Name : constant String := Source.Name;
         Shown_Name : constant String :=
           (if Chunk_Name'Length > 0
              and then Chunk_Name (Chunk_Name'First) in '@' | '='
            then Chunk_Name (Chunk_Name'First + 1 .. Chunk_Name'Last)
            elsif Chunk_Name'Length > 0 and then Chunk_Name (Chunk_Name'First) = ASCII.ESC
            then "(bstring)" else "(string)");
      begin
         --  [puc luac.c:PrintHeader]
         Put ([1 => ASCII.LF]
              & (if Facts.Line_Defined = 0 then "main" else "function") & " <" & Shown_Name
              & ":" & Image (Facts.Line_Defined) & "," & Image (Facts.Last_Line_Defined)
              & "> (" & Image (Count) & " instruction" & Plural (Count) & " at "
              & Name_Of (P) & ")" & ASCII.LF);
         Put (Image (Natural (Facts.Parameter_Count)) & (if Facts.Is_Vararg then "+" else "")
              & " param" & Plural (Natural (Facts.Parameter_Count)) & ", "
              & Image (Natural (Facts.Stack_Size)) & " slot"
              & Plural (Natural (Facts.Stack_Size)) & ", "
              & Image (Upvalue_Count (Item, P)) & " upvalue" & Plural (Upvalue_Count (Item, P))
              & ", " & Image (Local_Count (Item, P)) & " local" & Plural (Local_Count (Item, P))
              & ", " & Image (Constant_Count (Item, P)) & " constant"
              & Plural (Constant_Count (Item, P)) & ", " & Image (Child_Count (Item, P))
              & " function" & Plural (Child_Count (Item, P)) & ASCII.LF);
         --  [puc luac.c:PrintCode]
         for PC in 0 .. Count - 1 loop
            declare
               I   : constant Instruction := Instruction_At (Item, P, PC);
               A   : constant Integer := Integer (I.A);
               B   : constant Integer := Integer (I.B);
               C   : constant Integer := Integer (I.C);
               Bx  : constant Integer := Integer (I.Wide);
               SB  : constant Integer := B - Offset_sC;
               SC  : constant Integer := C - Offset_sC;
               SBx : constant Integer := Bx - Offset_sBx;
               SJ  : constant Integer := Bx - Offset_sJ;
               K   : constant String := (if I.K then "k" else "");
               KN  : constant Integer := Boolean'Pos (I.K);
               Name : constant String :=
                 (if Lua_Style then Names (I.Operation).all
                  else Ada.Characters.Handling.To_Lower (Opcode'Image (I.Operation)));
               Comment : constant String := ASCII.HT & "; ";
               procedure Operands (Text : String) is
               begin
                  Put (Text);
               end Operands;
               function Event (Value : Integer) return String
               is (if Value in Events'Range then Events (Value).all else "?");
            begin
               Put (ASCII.HT & Image (PC + 1) & ASCII.HT & "["
                    & Image (Natural (Line_At (Item, P, PC))) & "]" & ASCII.HT);
               Put (Name & (if Name'Length < 9 then [1 .. 9 - Name'Length => ' '] else "")
                    & ASCII.HT);
               case I.Operation is
                  when Move | Negate | Bitwise_Not | Logical_Not | Length | Concatenate =>
                     Operands (Image (A) & " " & Image (B));
                  when Load_Integer | Load_Float =>
                     Operands (Image (A) & " " & Image (SBx));
                  when Load_Constant =>
                     Operands (Image (A) & " " & Image (Bx));
                     Put (Comment);
                     Put_Constant (P, Bx);
                  when Load_Constant_Extra =>
                     Operands (Image (A));
                     Put (Comment);
                     Put_Constant (P, Extra_Argument (PC));
                  when Load_False | Load_False_Skip | Load_True | Close | To_Be_Closed
                     | Return_One | Vararg_Prepare =>
                     Operands (Image (A));
                  when Load_Nil =>
                     Operands (Image (A) & " " & Image (B));
                     Put (Comment & Image (B + 1) & " out");
                  when Get_Upvalue | Set_Upvalue =>
                     Operands (Image (A) & " " & Image (B));
                     Put (Comment & Upvalue_Name (B));
                  when Get_Table_Upvalue =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C));
                     Put (Comment & Upvalue_Name (B) & " ");
                     Put_Constant (P, C);
                  when Get_Table | Get_Integer | Add .. Shift_Right =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C));
                  when Get_Field | Add_Constant .. Bitwise_Exclusive_Or_Constant =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C));
                     Put (Comment);
                     Put_Constant (P, C);
                  when Set_Table_Upvalue =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C) & K);
                     Put (Comment & Upvalue_Name (A) & " ");
                     Put_Constant (P, B);
                     if I.K then
                        Put (" ");
                        Put_Constant (P, C);
                     end if;
                  when Set_Table | Set_Integer | Self =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C) & K);
                     if I.K then
                        Put (Comment);
                        Put_Constant (P, C);
                     end if;
                  when Set_Field =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C) & K);
                     Put (Comment);
                     Put_Constant (P, B);
                     if I.K then
                        Put (" ");
                        Put_Constant (P, C);
                     end if;
                  when New_Table =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C));
                     Put (Comment & Image (C + Extra_Argument (PC) * (Maximum_C + 1)));
                  when Add_Integer | Shift_Right_Integer | Shift_Left_Integer =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (SC));
                  when Metamethod_Binary =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C));
                     Put (Comment & Event (C));
                  when Metamethod_Binary_Integer =>
                     Operands (Image (A) & " " & Image (SB) & " " & Image (C) & " " & Image (KN));
                     Put (Comment & Event (C));
                     if I.K then
                        Put (" flip");
                     end if;
                  when Metamethod_Binary_Constant =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C) & " " & Image (KN));
                     Put (Comment & Event (C) & " ");
                     Put_Constant (P, B);
                     if I.K then
                        Put (" flip");
                     end if;
                  when Jump =>
                     Operands (Image (SJ));
                     Put (Comment & "to " & Image (SJ + PC + 2));
                  when Equal | Less_Than | Less_Equal =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (KN));
                  when Equal_Constant =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (KN));
                     Put (Comment);
                     Put_Constant (P, B);
                  when Equal_Integer .. Greater_Equal_Integer =>
                     Operands (Image (A) & " " & Image (SB) & " " & Image (KN));
                  when Test =>
                     Operands (Image (A) & " " & Image (KN));
                  when Test_Set =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (KN));
                  when Call =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C));
                     Put (Comment & (if B = 0 then "all in " else Image (B - 1) & " in ")
                          & (if C = 0 then "all out" else Image (C - 1) & " out"));
                  when Tail_Call =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C) & K);
                     Put (Comment & Image (B - 1) & " in");
                  when Return_Values =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C) & K);
                     Put (Comment & (if B = 0 then "all out" else Image (B - 1) & " out"));
                  when Return_None =>
                     null;
                  when For_Loop | Generic_For_Loop =>
                     Operands (Image (A) & " " & Image (Bx));
                     Put (Comment & "to " & Image (PC - Bx + 2));
                  when For_Prepare =>
                     Operands (Image (A) & " " & Image (Bx));
                     Put (Comment & "exit to " & Image (PC + Bx + 3));
                  when Generic_For_Prepare =>
                     Operands (Image (A) & " " & Image (Bx));
                     Put (Comment & "to " & Image (PC + Bx + 2));
                  when Generic_For_Call =>
                     Operands (Image (A) & " " & Image (C));
                  when Set_List =>
                     Operands (Image (A) & " " & Image (B) & " " & Image (C));
                     if I.K then
                        Put (Comment & Image (C + Extra_Argument (PC) * (Maximum_C + 1)));
                     end if;
                  when Closure =>
                     Operands (Image (A) & " " & Image (Bx));
                     Put (Comment & (if Bx < Child_Count (Item, P)
                                     then Name_Of (Child_At (Item, P, Bx)) else "?"));
                  when Vararg =>
                     Operands (Image (A) & " " & Image (C));
                     Put (Comment & (if C = 0 then "all out" else Image (C - 1) & " out"));
                  when Extra_Argument =>
                     Operands (Image (Bx));
               end case;
               Put ([1 => ASCII.LF]);
            end;
         end loop;
         --  [puc luac.c:PrintDebug]
         Put ("constants (" & Image (Constant_Count (Item, P)) & ") for " & Name_Of (P) & ":"
              & ASCII.LF);
         for Number in 0 .. Constant_Count (Item, P) - 1 loop
            Put (ASCII.HT & Image (Number) & ASCII.HT
                 & Type_Of (Constant_At (Item, P, Number).Kind) & ASCII.HT);
            Put_Constant (P, Number);
            Put ([1 => ASCII.LF]);
         end loop;
         Put ("locals (" & Image (Local_Count (Item, P)) & ") for " & Name_Of (P) & ":"
              & ASCII.LF);
         for Number in 0 .. Local_Count (Item, P) - 1 loop
            declare
               Variable : constant Local_Variable := Local_At (Item, P, Number);
            begin
               Put (ASCII.HT & Image (Number) & ASCII.HT & Symbol_Text (Variable.Name) & ASCII.HT
                    & Image (Variable.Start_PC + 1) & ASCII.HT & Image (Variable.End_PC + 1)
                    & ASCII.LF);
            end;
         end loop;
         Put ("upvalues (" & Image (Upvalue_Count (Item, P)) & ") for " & Name_Of (P) & ":"
              & ASCII.LF);
         for Number in 0 .. Upvalue_Count (Item, P) - 1 loop
            Put (ASCII.HT & Image (Number) & ASCII.HT & Upvalue_Name (Number) & ASCII.HT
                 & Image (Integer (Boolean'Pos (Upvalue_At (Item, P, Number).In_Stack)))
                 & ASCII.HT
                 & Image (Natural (Upvalue_At (Item, P, Number).Index)) & ASCII.LF);
         end loop;
         for Number in 0 .. Child_Count (Item, P) - 1 loop
            Put_Function (Child_At (Item, P, Number));
         end loop;
      end Put_Function;
   begin
      if Prototype_Count (Item) > 0 then
         Put_Function (Prototype_Count (Item));
      end if;
      Flush;
   end Print;

end Bytecode_Listing;
