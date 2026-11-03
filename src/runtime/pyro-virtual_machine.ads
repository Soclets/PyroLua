--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The virtual machine: runs a compiled chunk on one thread, calling host functions through
--  the host-function protocol.

with Interfaces;          use Interfaces;
with Pyro.Bytecode;
with Pyro.Garbage_Collector;
with Pyro.Heap;
with Pyro.Kind_Sequences;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Strings;
with Pyro.Symbols;
with Pyro.Tables;
with Pyro.Values;         use Pyro.Values;

package Pyro.Virtual_Machine with SPARK_Mode => On, Always_Terminates is

   use type Pyro.Bytecode.Prototype_Index;
   use type Pyro.Bytecode.Instruction;
   use type Pyro.Kind_Sequences.Sequence;

   --  A Lua state with one thread: the heap, the loaded chunk, the stack and the frames. It
   --  owns heap memory: release it with Clear.
   type Machine is limited private
   with
     Default_Initial_Condition => Is_Released (Machine) and then not Is_Loaded (Machine),
     Annotate => (GNATprove, Ownership, "Needs_Reclamation");

   --  [proof] The machine is consistent: its heap is valid, every value it keeps refers to an
   --  object the heap holds, the chunk is valid, and its frames lie inside its stack without
   --  overlapping (the frame invariant, PROOFS.md).
   function Is_Valid (M : Machine) return Boolean
   with Ghost, Global => null;

   --  True when the machine holds no memory.
   function Is_Released (M : Machine) return Boolean
   with Global => null, Annotate => (GNATprove, Ownership, "Is_Reclaimed");

   --  A chunk has been loaded, so the machine can run it.
   function Is_Loaded (M : Machine) return Boolean
   with Global => null;

   --  A compiled chunk and the symbols its constants and debug information name, handed over
   --  to the machine (Load takes them, leaving null).
   type Chunk_Access is access Pyro.Bytecode.Chunk;
   type Symbols_Access is access Pyro.Symbols.Symbol_Table;

   --  [limit LUAI_MAXSTACK] The most stack places a thread may use.
   Maximum_Stack : constant := 1_000_000;

   --  The numbers hosts give their functions.
   type Host_Id is range 1 .. 2 ** 16;

   --  Settings of a run.
   type Settings is record
      --  Instructions Run executes before it stops with Step_Limit_Reached (0 for no limit).
      Step_Limit : Unsigned_64 := 0;
      --  Collect at every safe point, for tests: a handle the machine keeps without rooting it
      --  is then freed at once.
      Stress     : Boolean := False;
   end record;

   --  The longest chunk name kept for messages.
   Maximum_Chunk_Name : constant := 80;

   --  Takes the valid chunk Program and the symbols Names (leaving both null), makes its
   --  constants heap values, and prepares a call of its main function with no arguments, its
   --  _ENV a new table of globals. Chunk_Name starts error positions ("file.lua:3:"). Success is
   --  False when Budget cannot pay; the machine then holds what it took, for Clear.
   procedure Load
     (M          : in out Machine;
      Budget     : in out Memory_Budget;
      Program    : in out Chunk_Access;
      Names      : in out Symbols_Access;
      Chunk_Name : String;
      Seed       : Pyro.Strings.Seed;
      Options    : Settings;
      Success    : out Boolean)
   with
     Global => null,
     Pre    =>
       Is_Released (M)
       and then not Is_Loaded (M)
       and then Program /= null
       and then Names /= null
       and then Pyro.Bytecode.Is_Well_Formed (Program.all)
       and then Pyro.Bytecode.Is_Valid (Program.all)
       and then Pyro.Bytecode.Prototype_Count (Program.all) > 0
       and then Pyro.Symbols.Is_Valid (Names.all)
       and then Chunk_Name'Length <= Maximum_Chunk_Name,
     Post   =>
       Program = null
       and then Names = null
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Success then Is_Valid (M) and then Is_Loaded (M));

   --  Makes the global Name hold a new host function with number Id. Success is False when
   --  Budget cannot pay.
   procedure Register
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Name    : String;
      Id      : Host_Id;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M) and then Name'Length in 1 .. 64,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  Why Run stopped.
   type Run_Status is
     (Finished,            --  the main function returned
      Errored,             --  an error was not caught: Error_Text says what
      Host_Call,           --  a host function was called: answer it, then Run again
      Paused,              --  Slice instructions ran: Run again to go on
      Step_Limit_Reached); --  Settings.Step_Limit instructions ran

   --  The most instructions one Run executes, so that every call returns (a Lua program need
   --  not end).
   Slice : constant := 2 ** 20;

   --  Runs until the main function returns, an error is not caught, a host function is called
   --  (or still waits for its answer), Slice instructions ran or the step limit is reached.
   procedure Run (M : in out Machine; Budget : in out Memory_Budget; Status : out Run_Status)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M),
     Post   =>
       Is_Valid (M)
       and then Is_Loaded (M)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Is_Waiting (M) = (Status = Host_Call)
       and then (if Status in Finished | Errored then Is_Done (M));

   --  A host function is waiting for its answer.
   function Is_Waiting (M : Machine) return Boolean
   with Global => null;

   --  The main function returned or an error was not caught: Run has nothing more to do.
   function Is_Done (M : Machine) return Boolean
   with Global => null;

   --  The message of the error that was not caught, as lua.c prints it: the error if it is a
   --  string or a number, "(error object is a <type> value)" otherwise.
   function Error_Text (M : Machine) return String
   with Global => null, Pre => Is_Valid (M) and then Is_Loaded (M);

   ----------------------------------------------------------------------------------------
   --  The host-function protocol (DESIGN.md, Host functions)
   ----------------------------------------------------------------------------------------

   --  The host function waiting for its answer, and the continuation it asked for: 0 when it
   --  was just called, else the number it gave Call.
   function Host_Function (M : Machine) return Host_Id
   with Global => null, Pre => Is_Valid (M) and then Is_Waiting (M);

   function Continuation (M : Machine) return Natural
   with Global => null, Pre => Is_Valid (M) and then Is_Waiting (M);

   --  The arguments of the waiting host function (Nil past the last).
   function Argument_Count (M : Machine) return Natural
   with Global => null, Pre => Is_Valid (M) and then Is_Waiting (M);

   function Argument (M : Machine; Position : Positive) return Value
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Waiting (M),
     Post   => Is_Canonical (Argument'Result) and then Is_Live (M, Argument'Result);

   --  After a call the host asked for: whether it succeeded (it always did unless protected),
   --  and its results, or the error as its only result.
   function Call_Succeeded (M : Machine) return Boolean
   with Global => null, Pre => Is_Valid (M) and then Is_Waiting (M);

   function Result_Count (M : Machine) return Natural
   with Global => null, Pre => Is_Valid (M) and then Is_Waiting (M);

   function Result (M : Machine; Position : Positive) return Value
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Waiting (M),
     Post   => Is_Canonical (Result'Result) and then Is_Live (M, Result'Result);

   --  [proof] Item refers to no object, or to one the machine's heap holds.
   function Is_Live (M : Machine; Item : Value) return Boolean
   with Ghost, Global => null, Post => (if Item.Kind /= Object_Value then Is_Live'Result);

   --  The values a host function returns or passes on.
   type Value_List is array (Positive range <>) of Value;

   --  [proof] Every value of Items is canonical and live.
   function All_Live (M : Machine; Items : Value_List) return Boolean
   is (for all Position in Items'Range =>
         Is_Canonical (Items (Position)) and then Is_Live (M, Items (Position)))
   with Ghost;

   --  The most values a host function returns or passes in one answer.
   Maximum_Values : constant := 255;

   --  Answers: the host function returns Values.
   procedure Return_Values
     (M : in out Machine; Budget : in out Memory_Budget; Values : Value_List)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Is_Waiting (M)
       and then Values'Length <= Maximum_Values
       and then All_Live (M, Values),
     Post   =>
       Is_Valid (M)
       and then Is_Loaded (M)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Answers: the host function raises Error.
   procedure Raise_Error (M : in out Machine; Budget : in out Memory_Budget; Error : Value)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Is_Waiting (M)
       and then Is_Canonical (Error)
       and then Is_Live (M, Error),
     Post   =>
       Is_Valid (M)
       and then Is_Loaded (M)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Answers: the host function raises the string Message, after the position of the
   --  function Level levels up ("file.lua:3: "), as luaL_error and error do (Level 0: none; 1:
   --  the function that called the host function).
   procedure Raise_Message
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Message : String;
      Level   : Natural)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Waiting (M) and then Message'Length <= 2 ** 20,
     Post   =>
       Is_Valid (M)
       and then Is_Loaded (M)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Answers: call Callee with Arguments, then continue the host function with Continuation
   --  (at least 1) and the call's results. With Protect, an error in the call is caught and
   --  continues the host function with the error instead (Call_Succeeded False).
   procedure Call
     (M            : in out Machine;
      Budget       : in out Memory_Budget;
      Callee       : Value;
      Arguments    : Value_List;
      Continuation : Positive;
      Protect      : Boolean)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Is_Waiting (M)
       and then Is_Canonical (Callee)
       and then Is_Live (M, Callee)
       and then Arguments'Length <= Maximum_Values
       and then All_Live (M, Arguments),
     Post   =>
       Is_Valid (M)
       and then Is_Loaded (M)
       and then Limit (Budget) = Limit (Budget)'Old;

   ----------------------------------------------------------------------------------------
   --  What host functions need from the machine
   ----------------------------------------------------------------------------------------

   --  [lua §6.1:type] The type name of Item.
   function Type_Name (M : Machine; Item : Value) return String
   with
     Global => null,
     Post   => Type_Name'Result'First = 1 and then Type_Name'Result'Length <= 8;

   --  Item is a string.
   function Is_String (M : Machine; Item : Value) return Boolean
   with Global => null;

   --  The bytes of string Item.
   function String_Text (M : Machine; Item : Value) return String
   with Global => null, Pre => Is_Valid (M) and then Is_String (M, Item);

   --  A string holding Text. Success is False when Budget cannot pay.
   procedure New_String
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Text    : String;
      Result  : out Value;
      Success : out Boolean)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Waiting (M) and then Text'Length <= 2 ** 20,
     Post   =>
       Is_Valid (M)
       and then Is_Waiting (M)
       and then Is_Canonical (Result)
       and then Is_Live (M, Result)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  Releases everything the machine holds; it is then unloaded.
   procedure Clear (M : in out Machine; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Is_Released (M) and then not Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc lobject.c:tostringbuff] Item as tostring writes a nil, a boolean or a number
   --  ("nil", "true", "10", "1.5"); Item must be one of those.
   function Basic_Image (Item : Value) return String
   with
     Global => null,
     Pre    => Is_Canonical (Item) and then Item.Kind /= Object_Value,
     Post   => Basic_Image'Result'First = 1 and then Basic_Image'Result'Length <= 32;

private
   --  Clients see the machine through the operations above, which keeps its representation
   --  (the heap, the chunk, the stack and frames) out of their proofs.
   pragma Annotate (GNATprove, Hide_Info, "Private_Part");

   subtype Root_Array is Pyro.Garbage_Collector.Root_Array;
   type Root_Array_Access is access Root_Array;

   --  Where each prototype's constants start in the machine's array of constants.
   type Base_Array is array (Pyro.Bytecode.Prototype_Index range <>) of Natural;
   type Base_Array_Access is access Base_Array;

   --  What a frame is: a Lua function's, or a host function's.
   type Frame_Kind is (Lua_Frame, Host_Frame);

   --  [puc lstate.h:CallInfo] A call in progress. The function is at Func in the stack; a Lua
   --  function's registers follow it up to Top (excluded), a host function's arguments up to
   --  its Top. Results is how many results the caller wants (-1: all of them), which go to
   --  Origin, where the function was called. A vararg function's Func moves above its
   --  arguments, Extra of which it keeps below Func. A host function that asked for a call
   --  waits with Context (its continuation) and Protect.
   type Frame is record
      Kind      : Frame_Kind := Lua_Frame;
      Origin    : Positive := 1;
      Func      : Positive := 1;
      Top       : Positive := 1;
      Prototype : Pyro.Bytecode.Prototype_Index := 0;
      PC        : Pyro.Bytecode.Entry_Count := 0;
      Results   : Integer range -1 .. 255 := -1;
      Extra     : Natural := 0;
      Host      : Host_Id := 1;
      Context   : Natural := 0;
      Protect   : Boolean := False;
   end record;

   --  [limit LUAI_MAXCCALLS] The deepest nesting of calls, Lua and host.
   Maximum_Frames : constant := 200_000;

   type Frame_Array is array (Positive range <>) of Frame;
   type Frame_Array_Access is access Frame_Array;

   --  What the machine is doing.
   type Machine_State is
     (Unloaded,   --  nothing to run
      Ready,      --  Run executes the top frame
      Waiting,    --  a host function waits for its answer
      Done);      --  the main function returned, or an error was not caught

   type Machine is limited record
      Heap        : Pyro.Heap.Heap;
      Program     : Chunk_Access := null;
      Names       : Symbols_Access := null;
      --  Every prototype's constants as values, and where each prototype's start.
      Constants   : Root_Array_Access := null;
      Bases       : Base_Array_Access := null;
      --  The values the machine keeps besides the stack: the globals table, then the host
      --  functions, then the error being raised.
      Registry    : Root_Array_Access := null;
      Stack       : Root_Array_Access := null;
      --  One past the last value in use above the top frame's registers (open results).
      Top         : Positive := 1;
      Frames      : Frame_Array_Access := null;
      Depth       : Natural := 0;
      --  The open upvalues (upvalue objects whose variable is still in the stack).
      Open        : Root_Array_Access := null;
      Open_Count  : Natural := 0;
      State       : Machine_State := Unloaded;
      Failed      : Boolean := False;
      --  After a call a host function asked for: where its results are and how many.
      Results_At  : Positive := 1;
      Result_Size : Natural := 0;
      Succeeded   : Boolean := True;
      Name        : String (1 .. Maximum_Chunk_Name) := [others => ' '];
      Name_Length : Natural range 0 .. Maximum_Chunk_Name := 0;
      Options     : Settings;
      Steps       : Unsigned_64 := 0;
      --  Collect when the memory used passes it.
      Threshold   : Byte_Count := 0;
   end record;

   ----------------------------------------------------------------------------------------
   --  The core: what the instruction handlers (private children) do to a machine. Contracts
   --  are stated with functions completed in the body, so handlers prove against them alone.
   ----------------------------------------------------------------------------------------

   --  [proof] The machine is ready to execute an instruction of its top frame, a Lua frame.
   function Running (M : Machine) return Boolean
   with Ghost, Global => null, Post => (if Running'Result then Is_Loaded (M));

   --  The facts of the running frame an instruction is checked against: its prototype, the
   --  program counter of the instruction it executes, how many registers, constants and
   --  upvalues it has, and how long its code is.
   type Frame_View is record
      Prototype : Pyro.Bytecode.Prototype_Index := 0;
      PC        : Pyro.Bytecode.Entry_Number := 0;
      Registers : Natural := 0;
      Constants : Natural := 0;
      Upvalues  : Natural := 0;
      Code      : Natural := 0;
      Vararg    : Boolean := False;
      Fixed     : Natural := 0;
      Children  : Natural := 0;
   end record;

   function View (M : Machine) return Frame_View
   with Global => null, Pre => Is_Valid (M) and then Running (M);

   --  [proof] The running frame's instruction is in its code, and its registers hold its
   --  parameters.
   procedure Lemma_View (M : Machine)
   with
     Ghost,
     Global => null,
     Pre    => Is_Valid (M) and then Running (M),
     Post   =>
       View (M).PC < View (M).Code
       and then View (M).Registers in 2 .. 255
       and then View (M).Fixed <= View (M).Registers;

   --  The instruction the running frame executes.
   function Current (M : Machine) return Pyro.Bytecode.Instruction
   with Global => null, Pre => Is_Valid (M) and then Running (M);

   --  [proof] What Pyro.Bytecode.Instruction_Valid says of instruction I of the running frame
   --  (View V): its registers, constants and upvalues exist, and it is not the last
   --  instruction unless it returns or jumps.
   function Is_Register (V : Frame_View; Number : Integer) return Boolean
   is (Number in 0 .. V.Registers - 1);

   function Fits (V : Frame_View; I : Pyro.Bytecode.Instruction) return Boolean
   is ((if I.Operation
            not in Pyro.Bytecode.Return_Values | Pyro.Bytecode.Return_None
                 | Pyro.Bytecode.Return_One | Pyro.Bytecode.Jump
        then V.PC + 1 < V.Code)
       and then
         (case I.Operation is
            when Pyro.Bytecode.Move =>
              Is_Register (V, Integer (I.A)) and then Is_Register (V, Integer (I.B)),
            when Pyro.Bytecode.Load_Integer | Pyro.Bytecode.Load_Float
               | Pyro.Bytecode.Load_False | Pyro.Bytecode.Load_True =>
              Is_Register (V, Integer (I.A)),
            when Pyro.Bytecode.Load_Constant =>
              Is_Register (V, Integer (I.A)) and then Natural (I.Wide) < V.Constants,
            when Pyro.Bytecode.Load_Constant_Extra | Pyro.Bytecode.Load_False_Skip =>
              Is_Register (V, Integer (I.A)) and then V.PC + 2 < V.Code,
            when Pyro.Bytecode.Load_Nil =>
              Is_Register (V, Integer (I.A) + Integer (I.B)),
            when Pyro.Bytecode.Get_Upvalue | Pyro.Bytecode.Set_Upvalue =>
              Is_Register (V, Integer (I.A)) and then Natural (I.B) < V.Upvalues,
            when Pyro.Bytecode.Get_Table_Upvalue =>
              Is_Register (V, Integer (I.A))
              and then Natural (I.B) < V.Upvalues
              and then Natural (I.C) < V.Constants,
            when Pyro.Bytecode.Set_Table_Upvalue =>
              Natural (I.A) < V.Upvalues
              and then Natural (I.B) < V.Constants
              and then (if I.K then Natural (I.C) < V.Constants
                        else Is_Register (V, Integer (I.C))),
            when Pyro.Bytecode.Jump =>
              V.PC + 1 + Integer (I.Wide) - Pyro.Bytecode.Offset_sJ in 0 .. V.Code - 1,
            when Pyro.Bytecode.Closure =>
              Is_Register (V, Integer (I.A)) and then Natural (I.Wide) < V.Children,
            when Pyro.Bytecode.Call | Pyro.Bytecode.Tail_Call =>
              Is_Register (V, Integer (I.A)),
            when Pyro.Bytecode.Return_Values =>
              Natural (I.A) <= V.Registers,
            when Pyro.Bytecode.Return_One =>
              Is_Register (V, Integer (I.A)),
            when Pyro.Bytecode.Vararg_Prepare =>
              V.Vararg and then Natural (I.A) = V.Fixed,
            when Pyro.Bytecode.Vararg =>
              V.Vararg and then Is_Register (V, Integer (I.A)),
            when others => True))
   with Ghost;

   --  [proof] The instruction the running frame executes fits it.
   procedure Lemma_Fits (M : Machine)
   with
     Ghost,
     Global => null,
     Pre    => Is_Valid (M) and then Running (M),
     Post   => Fits (View (M), Current (M));

   --  [proof] The kind of every object of the machine's heap.
   function Objects (M : Machine) return Pyro.Kind_Sequences.Sequence
   with Ghost, Global => null;

   --  [proof] Values the machine knew to be live before Objects grew are still live.
   procedure Lemma_Still_Live (Before : Pyro.Kind_Sequences.Sequence; M : Machine; Item : Value)
   with
     Ghost,
     Global => null,
     Pre    =>
       Pyro.Heap.Live_In (Before, Item)
       and then Pyro.Heap.Keeps_Objects (Before, Objects (M)),
     Post   => Is_Live (M, Item);

   --  [proof] A live value is live in Objects.
   procedure Lemma_Live_In (M : Machine; Item : Value)
   with
     Ghost,
     Global => null,
     Pre    => Is_Live (M, Item),
     Post   => Pyro.Heap.Live_In (Objects (M), Item);

   --  Register Number of the running frame.
   function Register (M : Machine; Number : Natural) return Value
   with
     Global => null,
     Pre    => Is_Valid (M) and then Running (M) and then Number < View (M).Registers,
     Post   => Is_Canonical (Register'Result) and then Is_Live (M, Register'Result);

   --  Makes register Number of the running frame Item.
   procedure Set_Register (M : in out Machine; Number : Natural; Item : Value)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Number < View (M).Registers
       and then Is_Canonical (Item)
       and then Is_Live (M, Item),
     Post   =>
       Is_Valid (M)
       and then Running (M)
       and then View (M) = View (M)'Old
       and then Current (M) = Current (M)'Old
       and then Objects (M) = Objects (M)'Old;

   --  Constant Number of the running frame's prototype.
   function Constant_At (M : Machine; Number : Natural) return Value
   with
     Global => null,
     Pre    => Is_Valid (M) and then Running (M) and then Number < View (M).Constants,
     Post   => Is_Canonical (Constant_At'Result) and then Is_Live (M, Constant_At'Result);

   --  The value of upvalue Number of the running function.
   function Upvalue (M : Machine; Number : Natural) return Value
   with
     Global => null,
     Pre    => Is_Valid (M) and then Running (M) and then Number < View (M).Upvalues,
     Post   => Is_Canonical (Upvalue'Result) and then Is_Live (M, Upvalue'Result);

   --  Makes upvalue Number of the running function hold Item.
   procedure Set_Upvalue (M : in out Machine; Number : Natural; Item : Value)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Number < View (M).Upvalues
       and then Is_Canonical (Item)
       and then Is_Live (M, Item),
     Post   =>
       Is_Valid (M)
       and then Running (M)
       and then View (M) = View (M)'Old
       and then Current (M) = Current (M)'Old
       and then Objects (M) = Objects (M)'Old;

   --  Moves the running frame on by 1 + Offset instructions (the next one when Offset is 0).
   procedure Next (M : in out Machine; Offset : Integer := 0)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Offset in -1 - View (M).PC .. View (M).Code - 2 - View (M).PC,
     Post   => Is_Valid (M) and then Is_Loaded (M);

   --  Table T's value for Key, without metamethods (Nil when T is not a table).
   function Raw_Get (M : Machine; T : Value; Key : Value) return Value
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M) and then Is_Canonical (Key),
     Post   => Is_Canonical (Raw_Get'Result) and then Is_Live (M, Raw_Get'Result);

   --  Binds Key to Item in table T, without metamethods. Status is Done when T is not a table
   --  (nothing is stored).
   procedure Raw_Set
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      T      : Value;
      Key    : Value;
      Item   : Value;
      Status : out Pyro.Tables.Set_Status)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Is_Canonical (Key)
       and then Is_Live (M, Key)
       and then Is_Canonical (Item)
       and then Is_Live (M, Item),
     Post   =>
       Is_Valid (M)
       and then Running (M)
       and then View (M) = View (M)'Old
       and then Current (M) = Current (M)'Old
       and then Objects (M) = Objects (M)'Old
       and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc ldebug.c:luaG_runerror] Raises the message Text after the running frame's position
   --  ("name:line: "). The frames unwind to a protected call, or the machine is done.
   procedure Raise_Runtime_Error
     (M : in out Machine; Budget : in out Memory_Budget; Text : String)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M) and then Text'Length <= 2 ** 16,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  Raises "not enough memory".
   procedure Raise_Memory_Error (M : in out Machine)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M),
     Post   => Is_Valid (M) and then Is_Loaded (M);

   --  [lua §3.4.11] A new closure of nested prototype Number of the running frame's, in
   --  register Target, with its upvalues: the running frame's registers or upvalues, as the
   --  prototype describes them.
   procedure Make_Closure
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Number : Natural;
      Target : Natural)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Number < View (M).Children
       and then Target < View (M).Registers
       and then View (M).PC + 1 < View (M).Code,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc ldo.c:luaD_precall] Calls the function in register Func of the running frame, with
   --  Arguments arguments after it (-1: up to the top of the stack), wanting Results results
   --  (-1: all). The running frame moves on to its next instruction first.
   procedure Call_Register
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Func      : Natural;
      Arguments : Integer;
      Results   : Integer)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Func < View (M).Registers
       and then Arguments in -1 .. 254
       and then Results in -1 .. 254
       and then View (M).PC + 1 < View (M).Code,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc lvm.c:OP_TAILCALL] The running frame calls the function in register Func with
   --  Arguments arguments (-1: up to the top) in its own place, its caller getting the
   --  results.
   procedure Tail_Call_Register
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Func      : Natural;
      Arguments : Integer)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Func < View (M).Registers
       and then Arguments in -1 .. 254,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc lvm.c:OP_RETURN] The running frame returns Count values from register First
   --  (-1: up to the top), closing its upvalues when Close.
   procedure Return_Registers
     (M      : in out Machine;
      First  : Natural;
      Count  : Integer;
      Close  : Boolean)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then First <= View (M).Registers
       and then Count in -1 .. 254,
     Post   => Is_Valid (M) and then Is_Loaded (M);

   --  [puc ltm.c:luaT_adjustvarargs] Moves the running vararg function above its extra
   --  arguments, Fixed parameters with it.
   procedure Prepare_Varargs
     (M : in out Machine; Budget : in out Memory_Budget; Fixed : Natural)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Fixed = View (M).Fixed
       and then View (M).PC + 1 < View (M).Code,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   --  [puc ltm.c:luaT_getvarargs] Copies Wanted extra arguments (-1: all of them, setting the
   --  top) of the running function to its registers from Target.
   procedure Copy_Varargs
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Target : Natural;
      Wanted : Integer)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Target < View (M).Registers
       and then Wanted in -1 .. 254
       and then View (M).PC + 1 < View (M).Code,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old;

   function Is_Released (M : Machine) return Boolean
   is (Pyro.Heap.Is_Released (M.Heap)
       and then M.Program = null
       and then M.Names = null
       and then M.Constants = null
       and then M.Bases = null
       and then M.Registry = null
       and then M.Stack = null
       and then M.Frames = null
       and then M.Open = null);

   function Is_Loaded (M : Machine) return Boolean
   is (M.State /= Unloaded);

   function Is_Waiting (M : Machine) return Boolean
   is (M.State = Waiting);

   function Is_Done (M : Machine) return Boolean
   is (M.State = Done);

end Pyro.Virtual_Machine;
