--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Source chunks: the bytes of a chunk, its name, positions and line numbers.

package body Pyro.Sources with SPARK_Mode => On is

   --  Text, indexed from 1.
   function From_One (Text : String) return String
   with Post => From_One'Result'First = 1 and then From_One'Result'Length = Text'Length
   is
      Result : constant String (1 .. Text'Length) := Text;
   begin
      return Result;
   end From_One;

   function Chunk_Id (Source : Sources.Source) return String is
      Ellipsis : constant String := "...";
   begin
      if Source.Name_Size >= 1 and then Source.Name (1) = '=' then
         --  Literal name: kept as is, cut to the buffer size.
         return From_One (Source.Name (2 .. Natural'Min (Source.Name_Size, Chunk_Id_Size + 1)));
      elsif Source.Name_Size >= 1 and then Source.Name (1) = '@' then
         if Source.Name_Size <= Chunk_Id_Size + 1 then
            return From_One (Source.Name (2 .. Source.Name_Size));
         else
            --  The '...' and the end of the name fill the buffer.
            return Ellipsis
              & Source.Name (Source.Name_Size - (Chunk_Id_Size - Ellipsis'Length) + 1
                             .. Source.Name_Size);
         end if;
      else
         --  String chunk: its first line, cut to fit between the prefix and the suffix.
         declare
            Room      : constant := 45;
            Line_Last : Natural := Source.Name_Size;
            One_Line  : Boolean := True;
         begin
            for Position in 1 .. Source.Name_Size loop
               if Source.Name (Position) = ASCII.LF then
                  Line_Last := Position - 1;
                  One_Line := False;
                  exit;
               end if;
               pragma Loop_Invariant (Line_Last = Source.Name_Size and then One_Line);
            end loop;
            if One_Line and then Source.Name_Size < Room then
               return "[string """ & Source.Name & """]";
            else
               return "[string """ & Source.Name (1 .. Natural'Min (Line_Last, Room)) & Ellipsis
                 & """]";
            end if;
         end;
      end if;
   end Chunk_Id;

   function Read_File_Start (Content : String) return File_Start is
      Byte_Order_Mark : constant String :=
        Character'Val (16#EF#) & Character'Val (16#BB#) & Character'Val (16#BF#);
      Escape          : constant Character := Character'Val (16#1B#);
      Result          : File_Start :=
        (Comment_Skipped => False, Has_First_Byte => False, First_Byte => ASCII.NUL,
         Rest            => 1, Binary => False);
      Next            : Positive := 1;
   begin
      --  [puc lauxlib.c:skipBOM] Each byte of the mark is consumed as it is compared.
      if Content'Length >= 1 and then Content (1) = Byte_Order_Mark (1) then
         if Content'Length >= 2 and then Content (2) = Byte_Order_Mark (2) then
            if Content'Length >= 3 and then Content (3) = Byte_Order_Mark (3) then
               Next := 4;
            else
               Result.Has_First_Byte := True;
               Result.First_Byte := Content (1);
               Next := Natural'Min (4, Content'Last + 1);
            end if;
         else
            Result.Has_First_Byte := True;
            Result.First_Byte := Content (1);
            Next := Natural'Min (3, Content'Last + 1);
         end if;
      end if;

      if not Result.Has_First_Byte and then Next <= Content'Last then
         Result.Has_First_Byte := True;
         Result.First_Byte := Content (Next);
         Next := Next + 1;
      end if;

      --  [puc lauxlib.c:skipcomment] A first line starting with '#' is skipped.
      if Result.Has_First_Byte and then Result.First_Byte = '#' then
         Result.Comment_Skipped := True;
         Result.Has_First_Byte := False;
         loop
            pragma Loop_Invariant (Next <= Content'Last + 1);
            pragma Loop_Variant (Increases => Next);
            exit when Next > Content'Last;
            Next := Next + 1;
            exit when Content (Next - 1) = ASCII.LF;
         end loop;
         if Next <= Content'Last then
            Result.Has_First_Byte := True;
            Result.First_Byte := Content (Next);
            Next := Next + 1;
         end if;
      end if;

      Result.Binary := Result.Has_First_Byte and then Result.First_Byte = Escape;
      Result.Rest := Next;
      return Result;
   end Read_File_Start;

end Pyro.Sources;
