--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The pyro command-line program: reads a Lua file and inspects or checks it.

--  [trusted] File and console I/O and argument handling, outside the proven library.
pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Containers.Generic_Array_Sort;
with Ada.Containers.Vectors;
with Ada.Exceptions;
with Ada.Unchecked_Conversion;
with Ada.Unchecked_Deallocation;
with GNAT.OS_Lib;
with Interfaces;
with Bytecode_Listing;
with Pyro;
with Pyro.Bytecode;
with Pyro.Character_Arrays;
with Pyro.Compiler;
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

   type Mode is (Tokens_Mode, Tree_Mode, Check_Mode, Bytecode_Mode);

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

   --  Writes bytes as a Lua string literal: printable ASCII as is, others as \ddd. The text
   --  can be as long as a chunk, so it is written in pieces rather than built on the stack.
   procedure Put_Quoted (Text : String) is
      Buffer : String (1 .. 4096);
      Last   : Natural := 0;

      procedure Add (Part : String) is
      begin
         if Last + Part'Length > Buffer'Last then
            Put (Buffer (1 .. Last));
            Last := 0;
         end if;
         Buffer (Last + 1 .. Last + Part'Length) := Part;
         Last := Last + Part'Length;
      end Add;
   begin
      Add ("""");
      for Byte of Text loop
         if Byte = '"' or else Byte = '\' then
            Add ('\' & Byte);
         elsif Byte in ' ' .. '~' then
            Add ([1 => Byte]);
         else
            Add ('\' & Image (Long_Long_Integer (Character'Pos (Byte))));
         end if;
      end loop;
      Add ("""");
      Put (Buffer (1 .. Last));
   end Put_Quoted;

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

   --  Why a file could not be loaded.
   type Load_Result is (Loaded, Too_Large, Cannot_Open, Cannot_Read);

   --  Reads the file at Path into a chunk on the heap, as luaL_loadfilex would, with no copy of
   --  its bytes on the stack. Error is the system's message when the file cannot be opened or
   --  read.
   procedure Load
     (Path   : String;
      Source : out Source_Access;
      Binary : out Boolean;
      Result : out Load_Result;
      Error  : out Natural)
   is
      use GNAT.OS_Lib;
      File : File_Descriptor;
      Size : Long_Integer;
      Done : Natural := 0;
      Name : constant String := "@" & Path;
   begin
      Source := null;
      Binary := False;
      Error := 0;
      File := Open_Read (Path, GNAT.OS_Lib.Binary);
      if File = Invalid_FD then
         Error := Errno;
         Result := Cannot_Open;
         return;
      end if;
      Size := File_Length (File);
      if Size > Long_Integer (Pyro.Maximum_Source_Length) then
         --  [differs] Chunks larger than Pyro.Maximum_Source_Length are refused.
         Close (File);
         Result := Too_Large;
         return;
      end if;
      Source := new Pyro.Sources.Source (Name_Size => Name'Length, Length => Natural (Size));
      Source.Name := Name;
      --  Read can return fewer bytes than asked for; it returns 0 at the end of the file.
      while Done < Source.Length loop
         declare
            Count : constant Integer :=
              Read (File, Source.Text (Done + 1)'Address, Source.Length - Done);
         begin
            if Count < 0 then
               Error := Errno;
               Close (File);
               Free (Source);
               Result := Cannot_Read;
               return;
            end if;
            exit when Count = 0;
            Done := Done + Count;
         end;
      end loop;
      --  A file length that is no byte count (a directory) shows up when it is read.
      if Done = Source.Length and then Source.Length = 0 then
         declare
            Probe : String (1 .. 1);
         begin
            if Read (File, Probe'Address, 1) < 0 then
               Error := Errno;
               Close (File);
               Free (Source);
               Result := Cannot_Read;
               return;
            end if;
         end;
      end if;
      Close (File);
      declare
         Start  : constant Pyro.Sources.File_Start :=
           Pyro.Sources.Read_File_Start (Source.Text (1 .. Done));
         Prefix : constant Natural :=
           Boolean'Pos (Start.Comment_Skipped) + Boolean'Pos (Start.Has_First_Byte);
         Length : constant Natural := Prefix + (Done - Start.Rest + 1);
         Chunk  : Source_Access;
      begin
         Binary := Start.Binary;
         if Done = Source.Length
           and then not Start.Comment_Skipped
           and then Start.Rest - Boolean'Pos (Start.Has_First_Byte) = 1
         then
            --  The chunk is the file as read.
            Result := Loaded;
            return;
         end if;
         --  The chunk differs from the file: move it into a chunk of its own length.
         Chunk := new Pyro.Sources.Source (Name_Size => Name'Length, Length => Length);
         Chunk.Name := Name;
         if Start.Comment_Skipped then
            Chunk.Text (1) := ASCII.LF;
         end if;
         if Start.Has_First_Byte then
            Chunk.Text (Prefix) := Start.First_Byte;
         end if;
         Chunk.Text (Prefix + 1 .. Length) := Source.Text (Start.Rest .. Done);
         Free (Source);
         Source := Chunk;
         Result := Loaded;
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
         Text  : String (1 .. 4096);
         Last  : Natural := 0;
         Total : constant Natural := Natural (Pyro.Character_Arrays.Length (Output));
      begin
         for Index in 1 .. Total loop
            Last := Last + 1;
            Text (Last) := Pyro.Character_Arrays.Element (Output, Pyro.Byte_Position (Index));
            if Last = Text'Last or else Index = Total then
               if Error then
                  Put_Error (Text (1 .. Last));
               else
                  Put (Text (1 .. Last));
               end if;
               Last := 0;
            end if;
         end loop;
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
      Loading : Load_Result;
      Error   : Natural;
   begin
      Load (Path, Source, Binary, Loading, Error);
      case Loading is
         when Loaded => null;
         when Cannot_Open | Cannot_Read =>
            --  [puc lauxlib.c:errfile]
            Put_Error ("pyro: cannot " & (if Loading = Cannot_Open then "open" else "read") & " "
                       & Path & ": " & GNAT.OS_Lib.Errno_Message (Err => Error) & ASCII.LF);
            Set_Exit_Status (Failure);
            return;
         when Too_Large =>
            Source := new Pyro.Sources.Source'
              (Name_Size => Path'Length + 1, Length => 0, Name => "@" & Path, Text => "");
            Report ((What => Pyro.Diagnostics.Not_Enough_Memory, others => <>));
            Free (Source);
            Pyro.Character_Arrays.Clear (Output, Budget);
            return;
      end case;
      if Binary then
         Report ((What => Pyro.Diagnostics.Binary_Chunk, others => <>));
         Free (Source);
         Pyro.Character_Arrays.Clear (Output, Budget);
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
                     Put ("string ");
                     Put_Quoted (if Item.Symbol = Pyro.Symbols.No_Symbol then ""
                                 else Pyro.Symbols.Text (Symbols, Item.Symbol));
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
         when Tree_Mode | Check_Mode | Bytecode_Mode =>
            declare
               use Pyro.Syntax_Trees;
               Tree     : Syntax_Tree;
               Problems : Pyro.Diagnostic_Lists.Growable_Array;
               Root     : Node_Index;
               Count    : Natural;
               Bindings : Pyro.Resolver.Binding_Table;
               Compiled : Pyro.Bytecode.Chunk;

               --  Prints one node's line. Trees can be far deeper than the parser's nesting limit
               --  (a long chain of "a + a + ..."), so nothing here depends on the depth.
               procedure Print_Node (Index : Node_Index; Depth : Natural) is
                  Item   : constant Node := Get (Tree, Index);
                  Spaces : constant String (1 .. 256) := [others => ' '];
                  Indent : Natural := 2 * Depth;
               begin
                  while Indent > 0 loop
                     Put (Spaces (1 .. Natural'Min (Indent, Spaces'Last)));
                     Indent := Indent - Natural'Min (Indent, Spaces'Last);
                  end loop;
                  Put (Image (Long_Long_Integer (Item.Line)) & " "
                       & Lower (Node_Kind'Image (Item.Kind)));
                  if Item.Symbol /= Pyro.Symbols.No_Symbol then
                     Put (" ");
                     Put_Quoted (Pyro.Symbols.Text (Symbols, Item.Symbol));
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
               end Print_Node;

               --  Prints the tree from Top in preorder, with a stack on the heap.
               procedure Print (Top : Node_Index) is
                  type Pending_Node is record
                     Index : Node_Index;
                     Depth : Natural;
                  end record;
                  package Pending_Vectors is new Ada.Containers.Vectors (Positive, Pending_Node);
                  Pending : Pending_Vectors.Vector;
                  Current : Pending_Node;
                  Item    : Node;
               begin
                  if Top /= No_Node then
                     Pending.Append (Pending_Node'(Top, 0));
                  end if;
                  while not Pending.Is_Empty loop
                     Current := Pending.Last_Element;
                     Pending.Delete_Last;
                     Print_Node (Current.Index, Current.Depth);
                     Item := Get (Tree, Current.Index);
                     --  Pushed in reverse, so they come off in order.
                     for Position in reverse 1 .. Item.List_Length loop
                        Pending.Append
                          (Pending_Node'
                             (List_Item (Tree, Current.Index, Position), Current.Depth + 1));
                     end loop;
                     for Slot in reverse Child_Slot loop
                        if Child (Tree, Current.Index, Slot) /= No_Node then
                           Pending.Append
                             (Pending_Node'(Child (Tree, Current.Index, Slot), Current.Depth + 1));
                        end if;
                     end loop;
                  end loop;
               end Print;
            begin
               Pyro.Parser.Parse (Source.all, Symbols, Budget, Tree, Problems, Root);
               Pyro.Resolver.Resolve (Tree, Root, Symbols, Budget, Problems, Bindings);
               Count := Natural (Pyro.Diagnostic_Lists.Length (Problems));
               if Selected /= Tree_Mode then
                  --  Also in a chunk with errors, for the limit errors PUC Lua finds first.
                  Pyro.Compiler.Compile
                    (Source.all, Tree, Root, Symbols, Budget, Problems, Compiled);
                  Count := Natural (Pyro.Diagnostic_Lists.Length (Problems));
               end if;
               if Selected = Tree_Mode then
                  Print (Root);
               elsif Selected = Bytecode_Mode and then Count = 0 then
                  Bytecode_Listing.Print (Compiled, Symbols, Source.all, Lua_Style);
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
                     --  Errors sort by place, then by the order they were found in.
                     type Ordered is record
                        Place : Natural;
                        Index : Positive;
                     end record;
                     type Ordered_Array is array (Positive range <>) of Ordered;
                     type Ordered_Access is access Ordered_Array;
                     procedure Free is new Ada.Unchecked_Deallocation
                       (Ordered_Array, Ordered_Access);
                     function "<" (Left, Right : Ordered) return Boolean
                     is (Left.Place < Right.Place
                         or else (Left.Place = Right.Place and then Left.Index < Right.Index));
                     procedure Sort is new Ada.Containers.Generic_Array_Sort
                       (Positive, Ordered, Ordered_Array);
                     Order : Ordered_Access := new Ordered_Array (1 .. Count);
                  begin
                     for Index in Order'Range loop
                        declare
                           Item : constant Pyro.Diagnostics.Diagnostic :=
                             Pyro.Diagnostic_Lists.Element
                               (Problems, Pyro.Diagnostics.Diagnostic_Position (Index));
                        begin
                           Order (Index) :=
                             ((if Item.Has_Place then Natural (Item.Place.First) else 0), Index);
                        end;
                     end loop;
                     Sort (Order.all);
                     for Index in Order'Range loop
                        if Index > 1 then
                           Put_Error ([1 => ASCII.LF]);
                        end if;
                        Report (Pyro.Diagnostic_Lists.Element
                                  (Problems,
                                   Pyro.Diagnostics.Diagnostic_Position (Order (Index).Index)));
                     end loop;
                     Free (Order);
                  end;
               end if;
               Pyro.Bytecode.Clear (Compiled, Budget);
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
      Put_Error ("usage: pyro (--tokens | --ast | --check [--lua-style]"
                 & " | --bytecode [--lua-style]) file.lua" & ASCII.LF);
      Set_Exit_Status (2);
   end Usage;
   procedure Main is
   begin
      if Argument_Count = 3 and then Argument (1) in "--check" | "--bytecode"
        and then Argument (2) = "--lua-style"
      then
         Lua_Style := True;
         Run ((if Argument (1) = "--check" then Check_Mode else Bytecode_Mode), Argument (3));
      elsif Argument_Count /= 2 then
         Usage;
      elsif Argument (1) = "--tokens" then
         Run (Tokens_Mode, Argument (2));
      elsif Argument (1) = "--ast" then
         Run (Tree_Mode, Argument (2));
      elsif Argument (1) = "--check" then
         Run (Check_Mode, Argument (2));
      elsif Argument (1) = "--bytecode" then
         Run (Bytecode_Mode, Argument (2));
      else
         Usage;
      end if;
   end Main;

   --  The work runs in a task with a stack of known size, whatever the system gives the main
   --  thread: what Pyro needs (Pyro.Minimum_Stack_Size) plus this program's own frames.
   task Worker with Storage_Size => Pyro.Minimum_Stack_Size + 2 ** 20;

   task body Worker is
   begin
      Main;
   exception
      when Error : others =>
         --  An exception would otherwise end the task silently.
         Put_Error ("pyro: internal error: "
                    & Ada.Exceptions.Exception_Information (Error) & ASCII.LF);
         Set_Exit_Status (Failure);
   end Worker;
begin
   null;
end Pyro_Program;
