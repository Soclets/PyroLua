--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The pyro command-line program: reads a Lua file and inspects or checks it.

--  [trusted] File and console I/O and argument handling, outside the proven library.
pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Streams.Stream_IO;
with Ada.Unchecked_Conversion;
with Ada.Unchecked_Deallocation;
with GNAT.OS_Lib;
with Interfaces;
with Pyro;
with Pyro.Character_Arrays;
with Pyro.Diagnostics;
with Pyro.Diagnostics.Rendering;
with Pyro.Diagnostic_Lists;
with Pyro.Lexer;
with Pyro.Memory_Budgets;
with Pyro.Parser;
with Pyro.Resolver;
with Pyro.Sources;
with Pyro.Symbols;
with Pyro.Syntax_Trees;
with Pyro.Tokens;

procedure Pyro_Program is
   use Ada.Command_Line;
   use Pyro.Tokens;
   use type Pyro.Symbols.Symbol_Index;

   type Source_Access is access Pyro.Sources.Source;
   procedure Free is new Ada.Unchecked_Deallocation (Pyro.Sources.Source, Source_Access);

   function To_Integer is new Ada.Unchecked_Conversion
     (Interfaces.Unsigned_64, Interfaces.Integer_64);

   type Mode is (Tokens_Mode, Tree_Mode, Check_Mode);

   --  Report errors as luac does (one line), rather than the rich report.
   Lua_Style : Boolean := False;

   procedure Write (File : GNAT.OS_Lib.File_Descriptor; Text : String) is
      Written : Integer;
      pragma Unreferenced (Written);
   begin
      if Text'Length > 0 then
         Written := GNAT.OS_Lib.Write (File, Text'Address, Text'Length);
      end if;
   end Write;

   procedure Put (Text : String) is
   begin
      Write (GNAT.OS_Lib.Standout, Text);
   end Put;

   procedure Put_Error (Text : String) is
   begin
      Write (GNAT.OS_Lib.Standerr, Text);
   end Put_Error;

   function Image (Value : Long_Long_Integer) return String is
      Text : constant String := Long_Long_Integer'Image (Value);
   begin
      return (if Text (Text'First) = ' ' then Text (Text'First + 1 .. Text'Last) else Text);
   end Image;

   function Hexadecimal (Value : Interfaces.Unsigned_64) return String is
      Digits_Text : constant String := "0123456789ABCDEF";
      Result      : String (1 .. 18) := "0x" & [1 .. 16 => '0'];
      Remaining   : Interfaces.Unsigned_64 := Value;
      use type Interfaces.Unsigned_64;
   begin
      for Position in reverse 3 .. 18 loop
         Result (Position) := Digits_Text (Natural (Remaining mod 16) + 1);
         Remaining := Remaining / 16;
      end loop;
      return Result;
   end Hexadecimal;

   --  Bytes shown as a Lua string literal: printable ASCII as is, others as \ddd.
   function Quoted (Text : String) return String is
      Result : String (1 .. 4 * Text'Length + 2);
      Last   : Natural := 1;
   begin
      Result (1) := '"';
      for Byte of Text loop
         if Byte = '"' or else Byte = '\' then
            Result (Last + 1 .. Last + 2) := '\' & Byte;
            Last := Last + 2;
         elsif Byte in ' ' .. '~' then
            Last := Last + 1;
            Result (Last) := Byte;
         else
            declare
               Code : constant String := Image (Long_Long_Integer (Character'Pos (Byte)));
            begin
               Result (Last + 1 .. Last + 1 + Code'Length) := '\' & Code;
               Last := Last + 1 + Code'Length;
            end;
         end if;
      end loop;
      Last := Last + 1;
      Result (Last) := '"';
      return Result (1 .. Last);
   end Quoted;

   function Lower (Text : String) return String is
      Result : String := Text;
   begin
      for Byte of Result loop
         if Byte in 'A' .. 'Z' then
            Byte := Character'Val (Character'Pos (Byte) + 32);
         end if;
      end loop;
      return Result;
   end Lower;

   --  Reads the file and builds the chunk as luaL_loadfilex would.
   function Load (Path : String; Binary : out Boolean) return Source_Access is
      use Ada.Streams;
      File    : Stream_IO.File_Type;
      Size    : constant Natural := Natural (Ada.Directories.Size (Path));
      Content : String (1 .. Size);
      Data    : Stream_Element_Array (1 .. Stream_Element_Offset (Size));
      Last    : Stream_Element_Offset;
   begin
      Stream_IO.Open (File, Stream_IO.In_File, Path);
      Stream_IO.Read (File, Data, Last);
      Stream_IO.Close (File);
      for Index in 1 .. Natural (Last) loop
         Content (Index) := Character'Val (Data (Stream_Element_Offset (Index)));
      end loop;
      declare
         Start : constant Pyro.Sources.File_Start :=
           Pyro.Sources.Read_File_Start (Content (1 .. Natural (Last)));
         Text  : constant String :=
           (if Start.Comment_Skipped then [1 => ASCII.LF] else "")
           & (if Start.Has_First_Byte then [1 => Start.First_Byte] else "")
           & Content (Start.Rest .. Natural (Last));
         Name  : constant String := "@" & Path;
      begin
         Binary := Start.Binary;
         return new Pyro.Sources.Source'
           (Name_Size => Name'Length, Length => Text'Length, Name => Name, Text => Text);
      end;
   end Load;

   procedure Run (Selected : Mode; Path : String) is
      Source  : Source_Access;
      Binary  : Boolean;
      Budget  : Pyro.Memory_Budgets.Memory_Budget :=
        Pyro.Memory_Budgets.Create (Pyro.Memory_Budgets.Default_Limit);
      Symbols : Pyro.Symbols.Symbol_Table;
      Lexer   : Pyro.Lexer.Lexer_State;
      Item    : Token;
      Output  : Pyro.Character_Arrays.Growable_Array;

      procedure Flush_Output (Error : Boolean) is
         Text : String (1 .. Natural (Pyro.Character_Arrays.Length (Output)));
      begin
         for Index in Text'Range loop
            Text (Index) := Pyro.Character_Arrays.Element
              (Output, Pyro.Byte_Position (Index));
         end loop;
         if Error then
            Put_Error (Text);
         else
            Put (Text);
         end if;
         Pyro.Character_Arrays.Truncate (Output, 0);
      end Flush_Output;

      procedure Report (Item : Pyro.Diagnostics.Diagnostic) is
      begin
         if Lua_Style then
            Pyro.Diagnostics.Append (Output, Budget, "pyro: ");
            Pyro.Diagnostics.Append_Lua_Message (Output, Budget, Item, Symbols, Source.all);
            Pyro.Diagnostics.Append (Output, Budget, [1 => ASCII.LF]);
         else
            Pyro.Diagnostics.Rendering.Append_Rich_Message
              (Output, Budget, Item, Symbols, Source.all, Path);
         end if;
         Flush_Output (Error => True);
         Set_Exit_Status (Failure);
      end Report;
   begin
      if Natural (Ada.Directories.Size (Path)) > Pyro.Maximum_Source_Length then
         --  [differs] Chunks larger than Pyro.Maximum_Source_Length are refused.
         Source := new Pyro.Sources.Source'
           (Name_Size => Path'Length + 1, Length => 0, Name => "@" & Path, Text => "");
         Report ((What => Pyro.Diagnostics.Not_Enough_Memory, others => <>));
         Free (Source);
         return;
      end if;
      Source := Load (Path, Binary);
      if Binary then
         Report ((What => Pyro.Diagnostics.Binary_Chunk, others => <>));
         Free (Source);
         return;
      end if;
      Pyro.Lexer.Start (Lexer, Source.all, Budget);
      case Selected is
         when Tokens_Mode =>
            loop
               Pyro.Lexer.Next_Token (Lexer, Source.all, Symbols, Budget, Item);
               exit when Pyro.Lexer.Failed (Lexer);
               Put (Image (Long_Long_Integer (Item.Line)) & " ");
               case Item.Kind is
                  when Name =>
                     Put ("name " & Pyro.Symbols.Text (Symbols, Item.Symbol));
                  when String_Literal =>
                     Put ("string "
                          & Quoted (if Item.Symbol = Pyro.Symbols.No_Symbol then ""
                                    else Pyro.Symbols.Text (Symbols, Item.Symbol)));
                  when Integer_Numeral =>
                     Put ("integer " & Image (Long_Long_Integer (Item.Integer_Value)));
                  when Float_Numeral =>
                     Put ("float "
                          & Source.Text (Positive (Item.First) .. Natural (Item.Last))
                          & " " & Hexadecimal (Item.Float_Bits));
                  when Other_Byte =>
                     Put ("byte " & Image (Long_Long_Integer (Character'Pos (Item.Byte))));
                  when Keyword =>
                     Put ("keyword " & Spelling (Item.Kind));
                  when others =>
                     Put (Lower (Spelling (Item.Kind)));
               end case;
               Put ([1 => ASCII.LF]);
               exit when Item.Kind = End_Of_Stream;
            end loop;
            if Pyro.Lexer.Failed (Lexer) then
               Report (Pyro.Lexer.Error (Lexer));
            end if;
         when Tree_Mode | Check_Mode =>
            declare
               use Pyro.Syntax_Trees;
               Tree     : Syntax_Tree;
               Problems : Pyro.Diagnostic_Lists.Growable_Array;
               Root     : Node_Index;
               Count    : Natural;
               Bindings : Pyro.Resolver.Binding_Table;

               procedure Print (Index : Node_Index; Depth : Natural) is
                  Item : Node;
               begin
                  if Index = No_Node then
                     return;
                  end if;
                  Item := Get (Tree, Index);
                  Put ([1 .. 2 * Depth => ' '] & Image (Long_Long_Integer (Item.Line)) & " "
                       & Lower (Node_Kind'Image (Item.Kind)));
                  if Item.Symbol /= Pyro.Symbols.No_Symbol then
                     Put (" " & Quoted (Pyro.Symbols.Text (Symbols, Item.Symbol)));
                  end if;
                  case Item.Kind is
                     when Integer_Literal =>
                        Put (" " & Image (Long_Long_Integer (To_Integer (Item.Value))));
                     when Float_Literal => Put (" " & Hexadecimal (Item.Value));
                     when Binary_Operation | Unary_Operation =>
                        Put (" " & Lower (Operator_Kind'Image (Item.Operator)));
                     when Local_Name =>
                        if Item.Attribute /= Regular then
                           Put (" " & Lower (Attribute_Kind'Image (Item.Attribute)));
                        end if;
                     when others => null;
                  end case;
                  if Item.Kind = Name_Expression then
                     declare
                        use Pyro.Resolver;
                        Found : constant Binding := Binding_Of (Bindings, Index);
                     begin
                        case Found.Kind is
                           when Local_Variable =>
                              Put (" local@" & Image (Long_Long_Integer (Found.Declaration)));
                           when Upvalue =>
                              Put (" upvalue@" & Image (Long_Long_Integer (Found.Declaration)));
                           when Global => Put (" global");
                           when Unbound => null;
                        end case;
                     end;
                  end if;
                  if Item.Is_Vararg then
                     Put (" vararg");
                  end if;
                  if Item.Is_Method then
                     Put (" method");
                  end if;
                  if Item.Is_Name_Key then
                     Put (" name-key");
                  end if;
                  if Item.Is_Last_Label then
                     Put (" last");
                  end if;
                  if Item.Is_Incomplete then
                     Put (" incomplete");
                  end if;
                  Put ([1 => ASCII.LF]);
                  for Slot in Child_Slot loop
                     Print (Child (Tree, Index, Slot), Depth + 1);
                  end loop;
                  for Position in 1 .. Item.List_Length loop
                     Print (List_Item (Tree, Index, Position), Depth + 1);
                  end loop;
               end Print;
            begin
               Pyro.Parser.Parse (Source.all, Symbols, Budget, Tree, Problems, Root);
               Pyro.Resolver.Resolve (Tree, Root, Symbols, Budget, Problems, Bindings);
               Count := Natural (Pyro.Diagnostic_Lists.Length (Problems));
               if Selected = Tree_Mode then
                  Print (Root, 0);
               end if;
               if Count > 0 and then Lua_Style then
                  --  The error PUC Lua would raise first.
                  declare
                     First : Pyro.Diagnostics.Diagnostic :=
                       Pyro.Diagnostic_Lists.Element (Problems, 1);
                  begin
                     for Index in 2 .. Count loop
                        declare
                           Item : constant Pyro.Diagnostics.Diagnostic :=
                             Pyro.Diagnostic_Lists.Element
                               (Problems, Pyro.Diagnostics.Diagnostic_Position (Index));
                        begin
                           if Pyro.Diagnostics.Before (Item.Detection, First.Detection) then
                              First := Item;
                           end if;
                        end;
                     end loop;
                     Report (First);
                  end;
               elsif Count > 0 then
                  --  Every error, in source order.
                  declare
                     type Order_Array is array (1 .. Count) of Positive;
                     Order : Order_Array;
                     function Place_Of (Index : Positive) return Natural is
                        Item : constant Pyro.Diagnostics.Diagnostic :=
                          Pyro.Diagnostic_Lists.Element
                            (Problems, Pyro.Diagnostics.Diagnostic_Position (Index));
                     begin
                        return (if Item.Has_Place then Natural (Item.Place.First) else 0);
                     end Place_Of;
                  begin
                     for Index in Order'Range loop
                        Order (Index) := Index;
                     end loop;
                     for Index in 2 .. Count loop
                        declare
                           Moving : constant Positive := Order (Index);
                           Slot   : Natural := Index - 1;
                        begin
                           while Slot >= 1 and then Place_Of (Order (Slot)) > Place_Of (Moving) loop
                              Order (Slot + 1) := Order (Slot);
                              Slot := Slot - 1;
                           end loop;
                           Order (Slot + 1) := Moving;
                        end;
                     end loop;
                     for Index in Order'Range loop
                        if Index > 1 then
                           Put_Error ([1 => ASCII.LF]);
                        end if;
                        Report (Pyro.Diagnostic_Lists.Element
                                  (Problems, Pyro.Diagnostics.Diagnostic_Position (Order (Index))));
                     end loop;
                  end;
               end if;
               Clear (Tree, Budget);
               Pyro.Diagnostic_Lists.Clear (Problems, Budget);
               Pyro.Resolver.Clear (Bindings, Budget);
            end;
      end case;
      Pyro.Lexer.Clear (Lexer, Budget);
      Pyro.Symbols.Clear (Symbols, Budget);
      Pyro.Character_Arrays.Clear (Output, Budget);
      Free (Source);
   end Run;

   procedure Usage is
   begin
      Put_Error ("usage: pyro (--tokens | --ast | --check [--lua-style]) file.lua" & ASCII.LF);
      Set_Exit_Status (2);
   end Usage;
begin
   if Argument_Count = 3 and then Argument (1) = "--check" and then Argument (2) = "--lua-style"
   then
      Lua_Style := True;
      Run (Check_Mode, Argument (3));
   elsif Argument_Count /= 2 then
      Usage;
   elsif Argument (1) = "--tokens" then
      Run (Tokens_Mode, Argument (2));
   elsif Argument (1) = "--ast" then
      Run (Tree_Mode, Argument (2));
   elsif Argument (1) = "--check" then
      Run (Check_Mode, Argument (2));
   else
      Usage;
   end if;
end Pyro_Program;
