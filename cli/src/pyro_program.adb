--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The pyro command-line program: reads a Lua file and inspects or checks it.

--  [trusted] File and console I/O and argument handling, outside the proven library.
pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Streams.Stream_IO;
with Ada.Unchecked_Deallocation;
with GNAT.OS_Lib;
with Interfaces;
with Pyro.Character_Arrays;
with Pyro.Diagnostics;
with Pyro.Lexer;
with Pyro.Memory_Budgets;
with Pyro.Sources;
with Pyro.Symbols;
with Pyro.Tokens;

procedure Pyro_Program is
   use Ada.Command_Line;
   use Pyro.Tokens;
   use type Pyro.Symbols.Symbol_Index;

   type Source_Access is access Pyro.Sources.Source;
   procedure Free is new Ada.Unchecked_Deallocation (Pyro.Sources.Source, Source_Access);

   type Mode is (Tokens_Mode, Check_Mode);

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
         Pyro.Diagnostics.Append (Output, Budget, "pyro: ");
         Pyro.Diagnostics.Append_Lua_Message (Output, Budget, Item, Symbols, Source.all);
         Pyro.Diagnostics.Append (Output, Budget, [1 => ASCII.LF]);
         Flush_Output (Error => True);
         Set_Exit_Status (Failure);
      end Report;
   begin
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
         when Check_Mode =>
            loop
               Pyro.Lexer.Next_Token (Lexer, Source.all, Symbols, Budget, Item);
               exit when Pyro.Lexer.Failed (Lexer) or else Item.Kind = End_Of_Stream;
            end loop;
            if Pyro.Lexer.Failed (Lexer) then
               Report (Pyro.Lexer.Error (Lexer));
            end if;
      end case;
      Pyro.Lexer.Clear (Lexer, Budget);
      Pyro.Symbols.Clear (Symbols, Budget);
      Pyro.Character_Arrays.Clear (Output, Budget);
      Free (Source);
   end Run;

   procedure Usage is
   begin
      Put_Error ("usage: pyro (--tokens | --check) file.lua" & ASCII.LF);
      Set_Exit_Status (2);
   end Usage;
begin
   if Argument_Count /= 2 then
      Usage;
   elsif Argument (1) = "--tokens" then
      Run (Tokens_Mode, Argument (2));
   elsif Argument (1) = "--check" then
      Run (Check_Mode, Argument (2));
   else
      Usage;
   end if;
end Pyro_Program;
