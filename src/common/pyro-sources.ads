--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Source chunks: the bytes of a chunk, its name, positions and line numbers.

package Pyro.Sources with SPARK_Mode => On, Pure, Always_Terminates is

   --  The number of bytes in a chunk.
   subtype Source_Length is Natural range 0 .. Maximum_Source_Length;

   --  A position in a chunk: 1 .. Length for a byte, Length + 1 for the end of the chunk.
   type Source_Position is range 1 .. Maximum_Source_Length + 1;

   --  A line number. Every line break is at least one byte, so a chunk has at most
   --  Maximum_Source_Length + 1 lines.
   type Line_Number is range 1 .. Maximum_Source_Length + 1;

   --  The longest chunk name kept.
   Maximum_Name_Length : constant := 4096;

   --  The length of a chunk name.
   subtype Name_Length is Natural range 0 .. Maximum_Name_Length;

   --  A chunk: its name, in Lua's convention ("@file.lua" for a file, "=stdin" for a literal
   --  name, anything else for a string chunk), and its bytes.
   type Source (Name_Size : Name_Length; Length : Source_Length) is record
      Name : String (1 .. Name_Size);
      Text : String (1 .. Length);
   end record;

   --  The byte at Position, which must be a byte of the chunk.
   function Byte (Source : Sources.Source; Position : Source_Position) return Character
   is (Source.Text (Positive (Position)))
   with Global => null, Pre => Natural (Position) <= Source.Length;

   --  [puc lobject.c:luaO_chunkid] The longest chunk id.
   Chunk_Id_Size : constant := 59;

   --  The chunk name as Lua prints it in messages (luaO_chunkid with LUA_IDSIZE = 60): a file
   --  name without its '@', shortened to "..." and its last characters when too long.
   function Chunk_Id (Source : Sources.Source) return String
   with
     Global => null,
     Post   => Chunk_Id'Result'First = 1 and then Chunk_Id'Result'Length <= Chunk_Id_Size + 15;

   --  How luaL_loadfilex starts reading a file, before handing the rest to the lexer.
   type File_Start is record
      --  The first line started with '#' and was skipped; a line break stands in for it.
      Comment_Skipped : Boolean;
      --  First_Byte is the first byte of the chunk, taken from the file before Rest.
      Has_First_Byte : Boolean;
      First_Byte     : Character;
      --  Position in the file of the first byte after First_Byte.
      Rest : Positive;
      --  The chunk is precompiled (it starts with the escape byte of Lua's binary signature).
      Binary : Boolean;
   end record;

   --  [puc lauxlib.c:luaL_loadfilex] Reads the start of a file as luaL_loadfilex does: a UTF-8
   --  byte order mark is skipped (and, as in PUC Lua, the bytes of an incomplete one are lost),
   --  then a first line starting with '#' is replaced by a line break. The chunk is the line
   --  break if any, then First_Byte if any, then Content (Rest .. Content'Last).
   function Read_File_Start (Content : String) return File_Start
   with
     Global => null,
     Pre    => Content'First = 1 and then Content'Last in 0 .. Positive'Last - 1,
     Post   => Read_File_Start'Result.Rest <= Content'Last + 1;

end Pyro.Sources;
