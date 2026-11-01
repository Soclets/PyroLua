--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Tokenizer for Lua 5.4 source text.

with Interfaces;
with Pyro.Numbers;

package body Pyro.Lexer with SPARK_Mode => On is

   function Is_Valid (Lexer : Lexer_State; Source : Sources.Source) return Boolean
   is (Natural (Lexer.Position) <= Source.Length + 1
       and then Natural (Lexer.Line) <= Natural (Lexer.Position));

   use type Interfaces.Unsigned_32;

   --  [puc lctype.h] Lua's own character classes, in the C locale.

   function Is_Alphabetic (Byte : Character) return Boolean
   is (Byte in 'a' .. 'z' | 'A' .. 'Z' | '_');

   function Is_Digit (Byte : Character) return Boolean is (Byte in '0' .. '9');

   function Is_Alphanumeric (Byte : Character) return Boolean
   is (Is_Alphabetic (Byte) or else Is_Digit (Byte));

   function Is_Hexadecimal_Digit (Byte : Character) return Boolean
   is (Byte in '0' .. '9' | 'a' .. 'f' | 'A' .. 'F');

   function Is_Space (Byte : Character) return Boolean
   is (Byte in ' ' | ASCII.HT | ASCII.LF | ASCII.VT | ASCII.FF | ASCII.CR);

   function Hexadecimal_Value (Byte : Character) return Interfaces.Unsigned_32
   is (case Byte is
         when '0' .. '9' => Character'Pos (Byte) - Character'Pos ('0'),
         when 'a' .. 'f' => Character'Pos (Byte) - Character'Pos ('a') + 10,
         when others     => Character'Pos (Byte) - Character'Pos ('A') + 10)
   with Pre => Is_Hexadecimal_Digit (Byte), Post => Hexadecimal_Value'Result < 16;

   --  Reading bytes.

   function At_End (Lexer : Lexer_State; Source : Sources.Source) return Boolean
   is (Natural (Lexer.Position) > Source.Length);

   function Current (Lexer : Lexer_State; Source : Sources.Source) return Character
   is (Source.Text (Positive (Lexer.Position)))
   with Pre => Is_Valid (Lexer, Source) and then not At_End (Lexer, Source);

   function Current_Is
     (Lexer : Lexer_State; Source : Sources.Source; Byte : Character) return Boolean
   is (not At_End (Lexer, Source) and then Current (Lexer, Source) = Byte)
   with Pre => Is_Valid (Lexer, Source);

   --  [puc llex.c:currIsNewline]
   function At_Newline (Lexer : Lexer_State; Source : Sources.Source) return Boolean
   is (Current_Is (Lexer, Source, ASCII.LF) or else Current_Is (Lexer, Source, ASCII.CR))
   with Pre => Is_Valid (Lexer, Source);

   --  The contract every step below keeps: the state stays valid, the lexer only moves
   --  forward, symbols are only added, and the budget keeps its limit.
   function Kept
     (Lexer       : Lexer_State;
      Source      : Sources.Source;
      Symbols     : Symbol_Table;
      Old_Position : Source_Position;
      Old_Count   : Symbol_Index) return Boolean
   is (Is_Valid (Lexer, Source)
       and then Is_Valid (Symbols)
       and then Lexer.Position >= Old_Position
       and then Count (Symbols) >= Old_Count);

   --  [puc llex.c:next]
   procedure Advance (Lexer : in out Lexer_State; Source : Sources.Source)
   with
     Pre  => Is_Valid (Lexer, Source) and then not At_End (Lexer, Source),
     Post =>
       Is_Valid (Lexer, Source)
       and then Lexer.Position = Lexer.Position'Old + 1
       and then Lexer.Line = Lexer.Line'Old
       and then Lexer.Stopped = Lexer.Stopped'Old
   is
   begin
      Lexer.Position := Lexer.Position + 1;
   end Advance;

   --  Stops the lexer with a lexical error. The "near" text, when PUC Lua prints one, is the
   --  token's text so far (Near_Text) or the end of the chunk.
   procedure Fail
     (Lexer      : in out Lexer_State;
      Symbols    : in out Symbol_Table;
      Budget     : in out Memory_Budget;
      What       : Problem;
      Near       : Near_Kind;
      Place      : Span;
      Other_Line : Line_Number := 1)
   with
     Pre  => Is_Valid (Symbols),
     Post =>
       Lexer.Stopped
       and then Lexer.Position = Lexer.Position'Old
       and then Lexer.Line = Lexer.Line'Old
       and then Is_Valid (Symbols)
       and then Count (Symbols) >= Count (Symbols)'Old
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Problem_Record : Diagnostic;
   begin
      Problem_Record.What := What;
      Problem_Record.Has_Place := True;
      Problem_Record.Place := Place;
      Problem_Record.Has_Lua_Line := True;
      Problem_Record.Lua_Line := Lexer.Line;
      Problem_Record.Near := Near;
      Problem_Record.Near_Token := End_Of_Stream;
      Problem_Record.Other_Line := Other_Line;
      Problem_Record.Detection :=
        (Ordinal => (if Lexer.Ordinal < Token_Ordinal'Last then Lexer.Ordinal + 1
                     else Lexer.Ordinal),
         During  => Lexing);
      if Near = Near_Text then
         Token_Text (Lexer, Symbols, Budget, Problem_Record.Near_Text);
      end if;
      Lexer.Problem := Problem_Record;
      Lexer.Stopped := True;
   end Fail;

   --  Stops the lexer because the memory budget ran out.
   procedure Fail_Memory (Lexer : in out Lexer_State)
   with
     Post =>
       Lexer.Stopped
       and then Lexer.Position = Lexer.Position'Old
       and then Lexer.Line = Lexer.Line'Old
   is
      Problem_Record : Diagnostic;
   begin
      Problem_Record.What := Not_Enough_Memory;
      Lexer.Problem := Problem_Record;
      Lexer.Stopped := True;
   end Fail_Memory;

   --  [puc llex.c:save]
   procedure Save (Lexer : in out Lexer_State; Budget : in out Memory_Budget; Byte : Character)
   with
     Post =>
       Lexer.Position = Lexer.Position'Old
       and then Lexer.Line = Lexer.Line'Old
       and then (if Lexer.Stopped'Old then Lexer.Stopped)
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Success : Boolean;
   begin
      Character_Arrays.Append (Lexer.Buffer, Byte, Budget, Success);
      if not Success then
         Fail_Memory (Lexer);
      end if;
   end Save;

   --  [puc llex.c:save_and_next]
   procedure Save_And_Advance
     (Lexer : in out Lexer_State; Source : Sources.Source; Budget : in out Memory_Budget)
   with
     Pre  => Is_Valid (Lexer, Source) and then not At_End (Lexer, Source),
     Post =>
       Is_Valid (Lexer, Source)
       and then Lexer.Position = Lexer.Position'Old + 1
       and then Lexer.Line = Lexer.Line'Old
       and then (if Lexer.Stopped'Old then Lexer.Stopped)
       and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      Save (Lexer, Budget, Current (Lexer, Source));
      Advance (Lexer, Source);
   end Save_And_Advance;

   --  [puc lzio.h:luaZ_buffremove] Drops the last Count bytes of the buffer.
   procedure Remove (Lexer : in out Lexer_State; Count : Natural)
   with
     Post =>
       Lexer.Position = Lexer.Position'Old
       and then Lexer.Line = Lexer.Line'Old
       and then Lexer.Stopped = Lexer.Stopped'Old
   is
      Length : constant Character_Arrays.Extended_Index :=
        Character_Arrays.Length (Lexer.Buffer);
   begin
      Character_Arrays.Truncate
        (Lexer.Buffer,
         (if Natural (Length) >= Count then Length - Character_Arrays.Extended_Index (Count)
          else 0));
   end Remove;

   --  [puc llex.c:inclinenumber] Skips '\n', '\r', "\n\r" or "\r\n" and counts one line.
   procedure Next_Line (Lexer : in out Lexer_State; Source : Sources.Source)
   with
     Pre  => Is_Valid (Lexer, Source) and then At_Newline (Lexer, Source),
     Post =>
       Is_Valid (Lexer, Source)
       and then Lexer.Position > Lexer.Position'Old
       and then Lexer.Stopped = Lexer.Stopped'Old
   is
      Old : constant Character := Current (Lexer, Source);
   begin
      Advance (Lexer, Source);
      if At_Newline (Lexer, Source) and then Current (Lexer, Source) /= Old then
         Advance (Lexer, Source);
      end if;
      Lexer.Line := Lexer.Line + 1;
   end Next_Line;

   --  [puc llex.c:check_next1]
   procedure Check_Next
     (Lexer : in out Lexer_State; Source : Sources.Source; Byte : Character; Found : out Boolean)
   with
     Pre  => Is_Valid (Lexer, Source),
     Post =>
       Is_Valid (Lexer, Source)
       and then Lexer.Position >= Lexer.Position'Old
       and then Lexer.Line = Lexer.Line'Old
       and then Lexer.Stopped = Lexer.Stopped'Old
   is
   begin
      Found := Current_Is (Lexer, Source, Byte);
      if Found then
         Advance (Lexer, Source);
      end if;
   end Check_Next;

   --  [puc llex.c:check_next2] Saves and skips the current byte if it is First or Second.
   procedure Check_Next_Two
     (Lexer         : in out Lexer_State;
      Source        : Sources.Source;
      Budget        : in out Memory_Budget;
      First, Second : Character;
      Found         : out Boolean)
   with
     Pre  => Is_Valid (Lexer, Source),
     Post =>
       Is_Valid (Lexer, Source)
       and then Lexer.Position >= Lexer.Position'Old
       and then (Found = (Lexer.Position > Lexer.Position'Old))
       and then Lexer.Line = Lexer.Line'Old
       and then (if Lexer.Stopped'Old then Lexer.Stopped)
       and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      Found := Current_Is (Lexer, Source, First) or else Current_Is (Lexer, Source, Second);
      if Found then
         Save_And_Advance (Lexer, Source, Budget);
      end if;
   end Check_Next_Two;

   --  [puc llex.c:skip_sep] Reads '[' or ']' followed by '='s. Returns the number of '='s
   --  plus 2 when the same bracket follows, 1 for a lone bracket, and 0 otherwise.
   procedure Skip_Separator
     (Lexer     : in out Lexer_State;
      Source    : Sources.Source;
      Budget    : in out Memory_Budget;
      Separator : out Natural)
   with
     Pre  =>
       Is_Valid (Lexer, Source)
       and then (Current_Is (Lexer, Source, '[') or else Current_Is (Lexer, Source, ']')),
     Post =>
       Is_Valid (Lexer, Source)
       and then Lexer.Position > Lexer.Position'Old
       and then Separator <= Natural (Lexer.Position - Lexer.Position'Old) + 1
       and then (if Separator >= 2
                 then Current_Is (Lexer, Source, Source.Text (Positive (Lexer.Position'Old))))
       and then Lexer.Line = Lexer.Line'Old
       and then (if Lexer.Stopped'Old then Lexer.Stopped)
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Bracket : constant Character := Current (Lexer, Source);
      Equals  : Natural := 0;
      Start   : constant Source_Position := Lexer.Position;
   begin
      Save_And_Advance (Lexer, Source, Budget);
      while Current_Is (Lexer, Source, '=') loop
         pragma Loop_Invariant (Is_Valid (Lexer, Source));
         pragma Loop_Invariant (Natural (Lexer.Position - Start) = Equals + 1);
         pragma Loop_Invariant (Lexer.Line = Lexer.Line'Loop_Entry);
         pragma Loop_Invariant (if Lexer.Stopped'Loop_Entry then Lexer.Stopped);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Variant (Increases => Lexer.Position);
         Save_And_Advance (Lexer, Source, Budget);
         Equals := Equals + 1;
      end loop;
      Separator :=
        (if Current_Is (Lexer, Source, Bracket) then Equals + 2
         elsif Equals = 0 then 1
         else 0);
   end Skip_Separator;

   --  [puc llex.c:read_long_string] Reads a long string (Is_Comment False) or long comment
   --  from its second '['. Start is where the token starts.
   procedure Read_Long_String
     (Lexer      : in out Lexer_State;
      Source     : Sources.Source;
      Symbols    : in out Symbol_Table;
      Budget     : in out Memory_Budget;
      Separator  : Natural;
      Is_Comment : Boolean;
      Start      : Source_Position;
      Result     : in out Token)
   with
     Pre  =>
       Is_Valid (Lexer, Source)
       and then Is_Valid (Symbols)
       and then not Lexer.Stopped
       and then Current_Is (Lexer, Source, '[')
       and then Start <= Lexer.Position,
     Post =>
       Kept (Lexer, Source, Symbols, Lexer.Position'Old, Count (Symbols)'Old)
       and then Lexer.Position > Lexer.Position'Old
       and then Result.Symbol <= Count (Symbols)
       and then Limit (Budget) = Limit (Budget)'Old
   is
      First_Line : constant Line_Number := Lexer.Line;
      Found      : Natural;
      Length     : Character_Arrays.Extended_Index;
   begin
      Result.Symbol := No_Symbol;
      Save_And_Advance (Lexer, Source, Budget);
      if At_Newline (Lexer, Source) then
         Next_Line (Lexer, Source);
      end if;
      loop
         pragma Loop_Invariant (Is_Valid (Lexer, Source));
         pragma Loop_Invariant (Lexer.Position > Lexer.Position'Loop_Entry - 1);
         pragma Loop_Invariant (Lexer.Position > Start);
         pragma Loop_Invariant (Is_Valid (Symbols));
         pragma Loop_Invariant (Count (Symbols) >= Count (Symbols)'Loop_Entry);
         pragma Loop_Invariant (Result.Symbol <= Count (Symbols));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Variant (Increases => Lexer.Position);
         exit when Lexer.Stopped;
         if At_End (Lexer, Source) then
            Fail
              (Lexer, Symbols, Budget,
               (if Is_Comment then Unfinished_Long_Comment else Unfinished_Long_String),
               Near_Token,
               (First => Start,
                Last  => Source_Position'Base'Min
                  (Start + Source_Position'Base (Natural'Min (Separator, Maximum_Source_Length))
                   + (if Is_Comment then 1 else -1),
                   Lexer.Position - 1)),
               Other_Line => First_Line);
            return;
         elsif Current_Is (Lexer, Source, ']') then
            Skip_Separator (Lexer, Source, Budget, Found);
            if Found = Separator then
               if not At_End (Lexer, Source) then
                  Save_And_Advance (Lexer, Source, Budget);
               end if;
               exit;
            end if;
         elsif At_Newline (Lexer, Source) then
            Save (Lexer, Budget, ASCII.LF);
            Next_Line (Lexer, Source);
            if Is_Comment then
               Character_Arrays.Truncate (Lexer.Buffer, 0);
            end if;
         elsif Is_Comment then
            Advance (Lexer, Source);
         else
            Save_And_Advance (Lexer, Source, Budget);
         end if;
      end loop;
      if Lexer.Stopped or else Is_Comment then
         return;
      end if;
      Length := Character_Arrays.Length (Lexer.Buffer);
      if Natural (Length) >= 2 * Separator then
         Intern
           (Symbols, Budget, Lexer.Buffer,
            Byte_Position (Separator + 1),
            Length - Character_Arrays.Extended_Index (Separator),
            Result.Symbol);
         if Result.Symbol = No_Symbol then
            Fail_Memory (Lexer);
         end if;
      end if;
   end Read_Long_String;

   --  [puc llex.c:esccheck] Fails with an escape error unless Condition holds, first saving
   --  the current byte (if any) for the message. Escape is where the escape sequence starts.
   procedure Check_Escape
     (Lexer     : in out Lexer_State;
      Source    : Sources.Source;
      Symbols   : in out Symbol_Table;
      Budget    : in out Memory_Budget;
      Condition : Boolean;
      What      : Problem;
      Escape    : Source_Position)
   with
     Pre  =>
       Is_Valid (Lexer, Source)
       and then Is_Valid (Symbols)
       and then not Lexer.Stopped
       and then Escape <= Lexer.Position,
     Post =>
       Kept (Lexer, Source, Symbols, Lexer.Position'Old, Count (Symbols)'Old)
       and then (Lexer.Stopped = not Condition)
       and then (if Condition then Lexer.Position = Lexer.Position'Old
                   and then Count (Symbols) = Count (Symbols)'Old)
       and then Lexer.Line = Lexer.Line'Old
       and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      if not Condition then
         if not At_End (Lexer, Source) then
            Save_And_Advance (Lexer, Source, Budget);
         end if;
         Fail (Lexer, Symbols, Budget, What, Near_Text,
               (First => Escape, Last => Lexer.Position - 1));
      end if;
   end Check_Escape;

   --  [puc lobject.c:luaO_utf8esc] Saves Value as extended UTF-8 (up to 6 bytes).
   procedure Save_UTF_8
     (Lexer : in out Lexer_State; Budget : in out Memory_Budget; Value : Interfaces.Unsigned_32)
   with
     Pre  => Value <= 16#7FFF_FFFF#,
     Post =>
       Lexer.Position = Lexer.Position'Old
       and then Lexer.Line = Lexer.Line'Old
       and then (if Lexer.Stopped'Old then Lexer.Stopped)
       and then Limit (Budget) = Limit (Budget)'Old
   is
      type Byte_Count is range 1 .. 6;
      Bytes      : array (Byte_Count) of Interfaces.Unsigned_32 := [others => 0];
      Count      : Byte_Count := 1;
      Remaining  : Interfaces.Unsigned_32 := Value;
      Most_First : Interfaces.Unsigned_32 := 16#3F#;
   begin
      if Value < 16#80# then
         Save (Lexer, Budget, Character'Val (Value));
         return;
      end if;
      --  Continuation bytes, last first, until the rest fits the first byte.
      loop
         pragma Loop_Variant (Increases => Count);
         pragma Loop_Invariant (Count <= 5);
         pragma Loop_Invariant (Most_First = Interfaces.Shift_Right (16#3F#, Natural (Count) - 1));
         pragma Loop_Invariant
           (Remaining <= Interfaces.Shift_Right (16#7FFF_FFFF#, 6 * (Natural (Count) - 1)));
         pragma Loop_Invariant (Lexer.Position = Lexer.Position'Loop_Entry);
         pragma Loop_Invariant (Lexer.Line = Lexer.Line'Loop_Entry);
         Bytes (Count) := 16#80# or (Remaining and 16#3F#);
         Remaining := Interfaces.Shift_Right (Remaining, 6);
         Most_First := Interfaces.Shift_Right (Most_First, 1);
         exit when Remaining <= Most_First or else Count = 5;
         Count := Count + 1;
      end loop;
      Save (Lexer, Budget,
            Character'Val ((Interfaces.Shift_Left (not Most_First, 1) or Remaining) and 16#FF#));
      for Index in reverse 1 .. Count loop
         pragma Loop_Invariant (Lexer.Position = Lexer.Position'Loop_Entry);
         pragma Loop_Invariant (Lexer.Line = Lexer.Line'Loop_Entry);
         pragma Loop_Invariant (if Lexer.Stopped'Loop_Entry then Lexer.Stopped);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Save (Lexer, Budget, Character'Val (Bytes (Index) and 16#FF#));
      end loop;
   end Save_UTF_8;

   --  Reads one escape sequence of a short string, from its '\'.
   procedure Read_Escape
     (Lexer   : in out Lexer_State;
      Source  : Sources.Source;
      Symbols : in out Symbol_Table;
      Budget  : in out Memory_Budget)
   with
     Pre  =>
       Is_Valid (Lexer, Source)
       and then Is_Valid (Symbols)
       and then not Lexer.Stopped
       and then Current_Is (Lexer, Source, '\'),
     Post =>
       Kept (Lexer, Source, Symbols, Lexer.Position'Old, Count (Symbols)'Old)
       and then Lexer.Position > Lexer.Position'Old
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Escape : constant Source_Position := Lexer.Position;
      Byte   : Character;
      Value  : Interfaces.Unsigned_32;
   begin
      Save_And_Advance (Lexer, Source, Budget);
      if Lexer.Stopped or else At_End (Lexer, Source) then
         --  At the end, the next step of the string reports it unfinished.
         return;
      end if;
      Byte := Current (Lexer, Source);
      case Byte is
         when 'a' | 'b' | 'f' | 'n' | 'r' | 't' | 'v' | '\' | '"' | ''' =>
            Advance (Lexer, Source);
            Remove (Lexer, 1);
            Save (Lexer, Budget,
                  (case Byte is
                     when 'a' => ASCII.BEL,
                     when 'b' => ASCII.BS,
                     when 'f' => ASCII.FF,
                     when 'n' => ASCII.LF,
                     when 'r' => ASCII.CR,
                     when 't' => ASCII.HT,
                     when 'v' => ASCII.VT,
                     when others => Byte));
         when 'x' =>
            --  [puc llex.c:readhexaesc]
            Save_And_Advance (Lexer, Source, Budget);
            if Lexer.Stopped then
               return;
            end if;
            Check_Escape
              (Lexer, Source, Symbols, Budget,
               not At_End (Lexer, Source) and then Is_Hexadecimal_Digit (Current (Lexer, Source)),
               Hexadecimal_Digit_Expected, Escape);
            if Lexer.Stopped then
               return;
            end if;
            Value := Hexadecimal_Value (Current (Lexer, Source));
            Save_And_Advance (Lexer, Source, Budget);
            if Lexer.Stopped then
               return;
            end if;
            Check_Escape
              (Lexer, Source, Symbols, Budget,
               not At_End (Lexer, Source) and then Is_Hexadecimal_Digit (Current (Lexer, Source)),
               Hexadecimal_Digit_Expected, Escape);
            if Lexer.Stopped then
               return;
            end if;
            Value := Value * 16 + Hexadecimal_Value (Current (Lexer, Source));
            Remove (Lexer, 2);
            Advance (Lexer, Source);
            Remove (Lexer, 1);
            Save (Lexer, Budget, Character'Val (Value));
         when 'u' =>
            --  [puc llex.c:readutf8esc] The '\', 'u', '{' and every digit are removed after.
            declare
               Saved : Natural := 4;
            begin
               Save_And_Advance (Lexer, Source, Budget);
               if Lexer.Stopped then
                  return;
               end if;
               Check_Escape
                 (Lexer, Source, Symbols, Budget, Current_Is (Lexer, Source, '{'),
                  Missing_Opening_Brace, Escape);
               if Lexer.Stopped then
                  return;
               end if;
               Save_And_Advance (Lexer, Source, Budget);
               if Lexer.Stopped then
                  return;
               end if;
               Check_Escape
                 (Lexer, Source, Symbols, Budget,
                  not At_End (Lexer, Source)
                  and then Is_Hexadecimal_Digit (Current (Lexer, Source)),
                  Hexadecimal_Digit_Expected, Escape);
               if Lexer.Stopped then
                  return;
               end if;
               Value := Hexadecimal_Value (Current (Lexer, Source));
               loop
                  pragma Loop_Invariant (Is_Valid (Lexer, Source));
                  pragma Loop_Invariant (Lexer.Position > Escape);
                  pragma Loop_Invariant (not Lexer.Stopped);
                  pragma Loop_Invariant (Value <= 16#7FFF_FFFF#);
                  pragma Loop_Invariant (Saved <= Natural (Lexer.Position - Escape) + 1);
                  pragma Loop_Invariant (not At_End (Lexer, Source));
                  pragma Loop_Invariant (Is_Valid (Symbols));
                  pragma Loop_Invariant (Count (Symbols) >= Count (Symbols)'Loop_Entry);
                  pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
                  pragma Loop_Variant (Increases => Lexer.Position);
                  Save_And_Advance (Lexer, Source, Budget);
                  exit when Lexer.Stopped
                    or else At_End (Lexer, Source)
                    or else not Is_Hexadecimal_Digit (Current (Lexer, Source));
                  Saved := Saved + 1;
                  Check_Escape
                    (Lexer, Source, Symbols, Budget, Value <= 16#7FF_FFFF#,
                     UTF_8_Value_Too_Large, Escape);
                  if Lexer.Stopped then
                     return;
                  end if;
                  Value := Value * 16 + Hexadecimal_Value (Current (Lexer, Source));
               end loop;
               if Lexer.Stopped then
                  return;
               end if;
               Check_Escape
                 (Lexer, Source, Symbols, Budget, Current_Is (Lexer, Source, '}'),
                  Missing_Closing_Brace, Escape);
               if Lexer.Stopped then
                  return;
               end if;
               Advance (Lexer, Source);
               Remove (Lexer, Saved);
               Save_UTF_8 (Lexer, Budget, Value);
            end;
         when ASCII.LF | ASCII.CR =>
            Next_Line (Lexer, Source);
            Remove (Lexer, 1);
            Save (Lexer, Budget, ASCII.LF);
         when 'z' =>
            Remove (Lexer, 1);
            Advance (Lexer, Source);
            while not At_End (Lexer, Source) and then Is_Space (Current (Lexer, Source)) loop
               pragma Loop_Invariant (Is_Valid (Lexer, Source));
               pragma Loop_Invariant (Lexer.Position > Escape);
               pragma Loop_Invariant (Lexer.Stopped = Lexer.Stopped'Loop_Entry);
               pragma Loop_Variant (Increases => Lexer.Position);
               if At_Newline (Lexer, Source) then
                  Next_Line (Lexer, Source);
               else
                  Advance (Lexer, Source);
               end if;
            end loop;
         when others =>
            --  [puc llex.c:readdecesc]
            Check_Escape
              (Lexer, Source, Symbols, Budget, Is_Digit (Byte), Invalid_Escape_Sequence, Escape);
            if Lexer.Stopped then
               return;
            end if;
            Value := 0;
            declare
               Read : Natural := 0;
            begin
               while Read < 3
                 and then not At_End (Lexer, Source)
                 and then Is_Digit (Current (Lexer, Source))
               loop
                  pragma Loop_Invariant (Is_Valid (Lexer, Source));
                  pragma Loop_Invariant (Lexer.Position > Escape);
                  pragma Loop_Invariant
                    ((Read = 0 and then Value = 0)
                     or else (Read = 1 and then Value <= 9)
                     or else (Read = 2 and then Value <= 99));
                  pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
                  pragma Loop_Variant (Increases => Lexer.Position);
                  Value := Value * 10
                    + Interfaces.Unsigned_32
                        (Character'Pos (Current (Lexer, Source)) - Character'Pos ('0'));
                  Save_And_Advance (Lexer, Source, Budget);
                  Read := Read + 1;
               end loop;
               if Lexer.Stopped then
                  return;
               end if;
               Check_Escape
                 (Lexer, Source, Symbols, Budget, Value <= 255, Decimal_Escape_Too_Large, Escape);
               if Lexer.Stopped then
                  return;
               end if;
               Remove (Lexer, Read);
               Remove (Lexer, 1);
               Save (Lexer, Budget, Character'Val (Value));
            end;
      end case;
   end Read_Escape;

   --  [puc llex.c:read_string] Reads a short string from its opening delimiter.
   procedure Read_String
     (Lexer     : in out Lexer_State;
      Source    : Sources.Source;
      Symbols   : in out Symbol_Table;
      Budget    : in out Memory_Budget;
      Delimiter : Character;
      Result    : in out Token)
   with
     Pre  =>
       Is_Valid (Lexer, Source)
       and then Is_Valid (Symbols)
       and then not Lexer.Stopped
       and then Current_Is (Lexer, Source, Delimiter),
     Post =>
       Kept (Lexer, Source, Symbols, Lexer.Position'Old, Count (Symbols)'Old)
       and then Lexer.Position > Lexer.Position'Old
       and then Result.Symbol <= Count (Symbols)
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Start  : constant Source_Position := Lexer.Position;
      Length : Character_Arrays.Extended_Index;
   begin
      Result.Symbol := No_Symbol;
      Save_And_Advance (Lexer, Source, Budget);
      loop
         pragma Loop_Invariant (Is_Valid (Lexer, Source));
         pragma Loop_Invariant (Lexer.Position > Start);
         pragma Loop_Invariant (Is_Valid (Symbols));
         pragma Loop_Invariant (Count (Symbols) >= Count (Symbols)'Loop_Entry);
         pragma Loop_Invariant (Result.Symbol <= Count (Symbols));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Variant (Increases => Lexer.Position);
         exit when Lexer.Stopped or else Current_Is (Lexer, Source, Delimiter);
         if At_End (Lexer, Source) then
            Fail (Lexer, Symbols, Budget, Unfinished_String, Near_Token,
                  (First => Start, Last => Lexer.Position - 1));
            return;
         elsif At_Newline (Lexer, Source) then
            Fail (Lexer, Symbols, Budget, Unfinished_String, Near_Text,
                  (First => Start, Last => Lexer.Position - 1));
            return;
         elsif Current (Lexer, Source) = '\' then
            Read_Escape (Lexer, Source, Symbols, Budget);
         else
            Save_And_Advance (Lexer, Source, Budget);
         end if;
      end loop;
      if Lexer.Stopped then
         return;
      end if;
      Save_And_Advance (Lexer, Source, Budget);
      Length := Character_Arrays.Length (Lexer.Buffer);
      if Length >= 2 then
         Intern (Symbols, Budget, Lexer.Buffer, 2, Length - 1, Result.Symbol);
         if Result.Symbol = No_Symbol then
            Fail_Memory (Lexer);
         end if;
      end if;
   end Read_String;

   --  The buffer as a string.
   function Buffer_Text (Lexer : Lexer_State) return String
   with
     Post =>
       Buffer_Text'Result'First = 1
       and then Buffer_Text'Result'Length = Natural (Character_Arrays.Length (Lexer.Buffer))
   is
      Size   : constant Natural := Natural (Character_Arrays.Length (Lexer.Buffer));
      Result : String (1 .. Size);
   begin
      for Position in 1 .. Size loop
         pragma Loop_Invariant (Size = Natural (Character_Arrays.Length (Lexer.Buffer)));
         Result (Position) := Character_Arrays.Element (Lexer.Buffer, Byte_Position (Position));
      end loop;
      return Result;
   end Buffer_Text;

   --  [puc llex.c:read_numeral] Reads a numeral greedily, then converts it.
   procedure Read_Numeral
     (Lexer   : in out Lexer_State;
      Source  : Sources.Source;
      Symbols : in out Symbol_Table;
      Budget  : in out Memory_Budget;
      Start   : Source_Position;
      Result  : in out Token)
   with
     Pre  =>
       Is_Valid (Lexer, Source)
       and then Is_Valid (Symbols)
       and then not Lexer.Stopped
       and then not At_End (Lexer, Source)
       and then Is_Digit (Current (Lexer, Source))
       and then Start <= Lexer.Position,
     Post =>
       Kept (Lexer, Source, Symbols, Lexer.Position'Old, Count (Symbols)'Old)
       and then Lexer.Position > Lexer.Position'Old
       and then Result.Symbol = Result.Symbol'Old
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Exponent_Lower : Character := 'e';
      Exponent_Upper : Character := 'E';
      First          : constant Character := Current (Lexer, Source);
      Found          : Boolean;
      Value          : Numbers.Numeral_Value;
      Valid          : Boolean;
   begin
      Save_And_Advance (Lexer, Source, Budget);
      if First = '0' then
         Check_Next_Two (Lexer, Source, Budget, 'x', 'X', Found);
         if Found then
            Exponent_Lower := 'p';
            Exponent_Upper := 'P';
         end if;
      end if;
      loop
         pragma Loop_Invariant (Is_Valid (Lexer, Source));
         pragma Loop_Invariant (Lexer.Position > Lexer.Position'Loop_Entry - 1);
         pragma Loop_Invariant (Lexer.Position > Start);
         pragma Loop_Invariant (Lexer.Line = Lexer.Line'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Variant (Increases => Lexer.Position);
         Check_Next_Two (Lexer, Source, Budget, Exponent_Lower, Exponent_Upper, Found);
         if Found then
            --  An optional sign after the exponent mark.
            if Current_Is (Lexer, Source, '-') or else Current_Is (Lexer, Source, '+') then
               Save_And_Advance (Lexer, Source, Budget);
            end if;
         elsif not At_End (Lexer, Source)
           and then (Is_Hexadecimal_Digit (Current (Lexer, Source))
                     or else Current (Lexer, Source) = '.')
         then
            Save_And_Advance (Lexer, Source, Budget);
         else
            exit;
         end if;
      end loop;
      if not At_End (Lexer, Source) and then Is_Alphabetic (Current (Lexer, Source)) then
         Save_And_Advance (Lexer, Source, Budget);
      end if;
      if Lexer.Stopped then
         return;
      end if;
      declare
         Text : constant String := Buffer_Text (Lexer);
      begin
         if Text'Length = 0 or else Text'Length > 2 ** 30 then
            Valid := False;
            Value := (Is_Integer => True, Integer_Value => 0, Float_Bits => 0);
         else
            Numbers.Convert (Text, Value, Valid);
         end if;
      end;
      if not Valid then
         Fail (Lexer, Symbols, Budget, Malformed_Number, Near_Text,
               (First => Start, Last => Lexer.Position - 1));
         return;
      end if;
      if Value.Is_Integer then
         Result.Kind := Integer_Numeral;
         Result.Integer_Value := Value.Integer_Value;
      else
         Result.Kind := Float_Numeral;
         Result.Float_Bits := Value.Float_Bits;
      end if;
   end Read_Numeral;

   --  The keyword spelled by the buffer, or Name.
   function Keyword_Or_Name (Lexer : Lexer_State) return Token_Kind is
      Length : constant Natural := Natural (Character_Arrays.Length (Lexer.Buffer));
   begin
      if Length > 8 then
         return Name;
      end if;
      for Kind in Keyword loop
         declare
            Spelled : constant String := Spelling (Kind);
            Same    : Boolean := Spelled'Length = Length;
         begin
            if Same then
               for Offset in 0 .. Length - 1 loop
                  if Character_Arrays.Element (Lexer.Buffer, Byte_Position (Offset + 1))
                    /= Spelled (Spelled'First + Offset)
                  then
                     Same := False;
                     exit;
                  end if;
               end loop;
               if Same then
                  return Kind;
               end if;
            end if;
         end;
      end loop;
      return Name;
   end Keyword_Or_Name;

   procedure Start
     (Lexer : in out Lexer_State; Source : Sources.Source; Budget : in out Memory_Budget)
   is
      pragma Unreferenced (Source);
   begin
      Character_Arrays.Clear (Lexer.Buffer, Budget);
      Lexer.Position := 1;
      Lexer.Line := 1;
      Lexer.Ordinal := 0;
      Lexer.Stopped := False;
   end Start;

   procedure Next_Token
     (Lexer   : in out Lexer_State;
      Source  : Sources.Source;
      Symbols : in out Symbol_Table;
      Budget  : in out Memory_Budget;
      Result  : out Token)
   is
      Found     : Boolean;
      Separator : Natural;
      Start     : Source_Position;
      First_Line : Line_Number;
   begin
      Result := (others => <>);
      if Lexer.Ordinal < Token_Ordinal'Last then
         Lexer.Ordinal := Lexer.Ordinal + 1;
      end if;
      Result.Ordinal := Lexer.Ordinal;
      Character_Arrays.Truncate (Lexer.Buffer, 0);
      loop
         pragma Loop_Invariant (Is_Valid (Lexer, Source));
         pragma Loop_Invariant (Is_Valid (Symbols));
         pragma Loop_Invariant (Count (Symbols) >= Count (Symbols)'Loop_Entry);
         pragma Loop_Invariant (Result.Symbol <= Count (Symbols));
         pragma Loop_Invariant (not Lexer.Stopped);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Variant (Increases => Lexer.Position);
         Start := Lexer.Position;
         First_Line := Lexer.Line;
         Result.First := Start;
         Result.First_Line := First_Line;
         if At_End (Lexer, Source) then
            Result.Kind := End_Of_Stream;
            exit;
         end if;
         case Current (Lexer, Source) is
            when ASCII.LF | ASCII.CR =>
               Next_Line (Lexer, Source);
            when ' ' | ASCII.FF | ASCII.HT | ASCII.VT =>
               Advance (Lexer, Source);
            when '-' =>
               Advance (Lexer, Source);
               if not Current_Is (Lexer, Source, '-') then
                  Result.Kind := Minus_Sign;
                  exit;
               end if;
               Advance (Lexer, Source);
               Separator := 0;
               if Current_Is (Lexer, Source, '[') then
                  Skip_Separator (Lexer, Source, Budget, Separator);
                  Character_Arrays.Truncate (Lexer.Buffer, 0);
                  if Lexer.Stopped then
                     exit;
                  end if;
                  if Separator >= 2 then
                     Read_Long_String
                       (Lexer, Source, Symbols, Budget, Separator, True, Start, Result);
                     Character_Arrays.Truncate (Lexer.Buffer, 0);
                     exit when Lexer.Stopped;
                  end if;
               end if;
               if Separator < 2 then
                  while not At_End (Lexer, Source) and then not At_Newline (Lexer, Source) loop
                     pragma Loop_Invariant (Is_Valid (Lexer, Source));
                     pragma Loop_Invariant (Lexer.Position > Start);
                     pragma Loop_Invariant (not Lexer.Stopped);
                     pragma Loop_Variant (Increases => Lexer.Position);
                     Advance (Lexer, Source);
                  end loop;
               end if;
            when '[' =>
               Skip_Separator (Lexer, Source, Budget, Separator);
               if Lexer.Stopped then
                  exit;
               elsif Separator >= 2 then
                  Read_Long_String
                    (Lexer, Source, Symbols, Budget, Separator, False, Start, Result);
                  Result.Kind := String_Literal;
               elsif Separator = 0 then
                  Fail (Lexer, Symbols, Budget, Invalid_Long_String_Delimiter, Near_Text,
                        (First => Start, Last => Lexer.Position - 1));
               else
                  Result.Kind := Left_Bracket;
               end if;
               exit;
            when '=' =>
               Advance (Lexer, Source);
               Check_Next (Lexer, Source, '=', Found);
               Result.Kind := (if Found then Equal_Equal else Equals_Sign);
               exit;
            when '<' =>
               Advance (Lexer, Source);
               Check_Next (Lexer, Source, '=', Found);
               if Found then
                  Result.Kind := Less_Equal;
               else
                  Check_Next (Lexer, Source, '<', Found);
                  Result.Kind := (if Found then Shift_Left else Less_Than);
               end if;
               exit;
            when '>' =>
               Advance (Lexer, Source);
               Check_Next (Lexer, Source, '=', Found);
               if Found then
                  Result.Kind := Greater_Equal;
               else
                  Check_Next (Lexer, Source, '>', Found);
                  Result.Kind := (if Found then Shift_Right else Greater_Than);
               end if;
               exit;
            when '/' =>
               Advance (Lexer, Source);
               Check_Next (Lexer, Source, '/', Found);
               Result.Kind := (if Found then Double_Slash else Slash);
               exit;
            when '~' =>
               Advance (Lexer, Source);
               Check_Next (Lexer, Source, '=', Found);
               Result.Kind := (if Found then Not_Equal else Tilde);
               exit;
            when ':' =>
               Advance (Lexer, Source);
               Check_Next (Lexer, Source, ':', Found);
               Result.Kind := (if Found then Double_Colon else Colon);
               exit;
            when '"' | ''' =>
               Read_String (Lexer, Source, Symbols, Budget, Current (Lexer, Source), Result);
               Result.Kind := String_Literal;
               exit;
            when '.' =>
               Save_And_Advance (Lexer, Source, Budget);
               Check_Next (Lexer, Source, '.', Found);
               if Found then
                  Check_Next (Lexer, Source, '.', Found);
                  Result.Kind := (if Found then Triple_Dot else Double_Dot);
               elsif At_End (Lexer, Source) or else not Is_Digit (Current (Lexer, Source)) then
                  Result.Kind := Dot;
               elsif not Lexer.Stopped then
                  Read_Numeral (Lexer, Source, Symbols, Budget, Start, Result);
               end if;
               exit;
            when '0' .. '9' =>
               Read_Numeral (Lexer, Source, Symbols, Budget, Start, Result);
               exit;
            when others =>
               if Is_Alphabetic (Current (Lexer, Source)) then
                  loop
                     pragma Loop_Invariant (Is_Valid (Lexer, Source));
                     pragma Loop_Invariant (Lexer.Position >= Start);
                     pragma Loop_Invariant (not At_End (Lexer, Source));
                     pragma Loop_Invariant (Lexer.Line = First_Line);
                     pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
                     pragma Loop_Variant (Increases => Lexer.Position);
                     Save_And_Advance (Lexer, Source, Budget);
                     exit when At_End (Lexer, Source)
                       or else not Is_Alphanumeric (Current (Lexer, Source));
                  end loop;
                  if not Lexer.Stopped then
                     Result.Kind := Keyword_Or_Name (Lexer);
                     if Result.Kind = Name then
                        Intern
                          (Symbols, Budget, Lexer.Buffer, 1,
                           Character_Arrays.Length (Lexer.Buffer), Result.Symbol);
                        if Result.Symbol = No_Symbol then
                           Fail_Memory (Lexer);
                        end if;
                     end if;
                  end if;
               else
                  Result.Kind := Kind_Of_Byte (Current (Lexer, Source));
                  Result.Byte := Current (Lexer, Source);
                  Advance (Lexer, Source);
               end if;
               exit;
         end case;
      end loop;
      if Lexer.Stopped then
         Result.Kind := End_Of_Stream;
      end if;
      Result.Last := Lexer.Position - 1;
      Result.Line := Lexer.Line;
      Result.Ordinal := Lexer.Ordinal;
   end Next_Token;

   procedure Token_Text
     (Lexer   : Lexer_State;
      Symbols : in out Symbol_Table;
      Budget  : in out Memory_Budget;
      Symbol  : out Symbol_Index)
   is
      Length : constant Character_Arrays.Extended_Index :=
        Character_Arrays.Length (Lexer.Buffer);
      Last   : Character_Arrays.Extended_Index := Length;
   begin
      --  PUC Lua formats the text with "%s", which stops at the first NUL byte.
      for Position in 1 .. Length loop
         if Character_Arrays.Element (Lexer.Buffer, Position) = ASCII.NUL then
            Last := Position - 1;
            exit;
         end if;
         pragma Loop_Invariant (Last = Length);
      end loop;
      Intern (Symbols, Budget, Lexer.Buffer, 1, Last, Symbol);
   end Token_Text;

   procedure Clear (Lexer : in out Lexer_State; Budget : in out Memory_Budget) is
   begin
      Character_Arrays.Clear (Lexer.Buffer, Budget);
   end Clear;

end Pyro.Lexer;
