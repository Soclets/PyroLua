--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The virtual machine: runs a compiled chunk on one thread, calling host functions through
--  the host-function protocol.

with Ada.Unchecked_Deallocation;
with Pyro.Color_Sequences;
with Pyro.Floats;
with Pyro.Heap.String_Reads;
with Pyro.Heap.Table_Reads;
with Pyro.Integer_Arithmetic;
with Pyro.Numbers;
with Pyro.Virtual_Machine.Execution;

package body Pyro.Virtual_Machine with SPARK_Mode => On is

   use Pyro.Bytecode;
   use type Pyro.Tables.Set_Status;

   procedure Free_Values is new Ada.Unchecked_Deallocation (Root_Array, Root_Array_Access);
   procedure Free_Bases is new Ada.Unchecked_Deallocation (Base_Array, Base_Array_Access);
   procedure Free_Frames is new Ada.Unchecked_Deallocation (Frame_Array, Frame_Array_Access);
   procedure Free_Places is new Ada.Unchecked_Deallocation (Place_Array, Place_Array_Access);
   procedure Free_Chunk is new Ada.Unchecked_Deallocation (Pyro.Bytecode.Chunk, Chunk_Access);
   procedure Free_Symbols is new Ada.Unchecked_Deallocation
     (Pyro.Symbols.Symbol_Table, Symbols_Access);

   --  Bytes charged for each place of the stack and of the machine's other value arrays, for
   --  each frame, and for each prototype's base.
   Value_Bytes : constant Byte_Count := 16;
   Frame_Bytes : constant Byte_Count := 48;
   Base_Bytes  : constant Byte_Count := 8;

   --  [puc lstate.h:EXTRA_STACK] Places past the last a frame may use, for metamethod calls.
   Extra_Stack : constant := 5;

   --  The most places of the stack.
   Stack_Limit : constant := Maximum_Stack + Extra_Stack;

   --  The places of the registry: the globals, the error being raised, the message for
   --  running out of memory, the host functions by number (so that each has one value, as a
   --  C function has one address), and the name of each event (ltm.c's luaT_init interns
   --  them).
   Globals_Place   : constant := 1;
   Error_Place     : constant := 2;
   Memory_Place    : constant := 3;
   Functions_Place : constant := 4;
   Event_Base      : constant := 5;
   Registry_Size : constant := Event_Base + Event'Pos (Event'Last);

   function Event_Place (Item : Event) return Positive
   is (Event_Base + Event'Pos (Item))
   with Post => Event_Place'Result <= Registry_Size;

   --  [puc lvm.c:MAXTAGLOOP] The longest chain of __index or __newindex tables.
   Maximum_Tag_Loop : constant := 2_000;

   --  The sizes of the stack, the frames and the open upvalues a machine starts with.
   Initial_Stack  : constant := 64;
   Initial_Frames : constant := 16;
   Initial_Open   : constant := 16;

   ----------------------------------------------------------------------------------------
   --  Validity
   ----------------------------------------------------------------------------------------

   --  The last place of a stack.
   subtype Stack_Size is Natural range 0 .. Stack_Limit;

   --  The most places of the array of open upvalues.
   Maximum_Open : constant := 2 * Stack_Limit;

   --  The most constants of a chunk, all prototypes together.
   Maximum_Constants : constant := 2 ** 24;

   --  [proof] Every value of A is canonical and refers to an object K shows.
   function Values_Live (K : Pyro.Kind_Sequences.Sequence; A : Root_Array) return Boolean
   is (for all Index in A'Range =>
         Is_Canonical (A (Index)) and then Pyro.Heap.Live_In (K, A (Index)))
   with Ghost;
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Values_Live);

   --  [proof] Frame F lies in a stack whose last place is Stack_Last: its function and
   --  registers (a host function's arguments) are in it, the results its caller wants fit
   --  from its origin, and a Lua frame has its prototype's registers, an instruction to run,
   --  and its extra arguments below its function.
   function Frame_Valid (F : Frame; Stack_Last : Stack_Size; Program : Chunk) return Boolean
   is (F.Origin <= F.Func
       and then F.Func < F.Top
       and then F.Top <= Stack_Last + 1
       and then (F.Results < 0 or else F.Results <= Stack_Last + 1 - F.Origin)
       and then (case F.Kind is
                   when Lua_Frame =>
                     F.Prototype in 1 .. Prototype_Count (Program)
                     and then F.Top
                              = F.Func + 1 + Natural (Header (Program, F.Prototype).Stack_Size)
                     and then F.PC < Code_Length (Program, F.Prototype)
                     and then F.Extra < F.Func
                     and then (if F.Action in Store_Result | Concat_Result
                               then F.Target < F.Top - F.Func - 1)
                     and then (if F.Action = Concat_Result then F.PC >= 1)
                     and then (if F.Action = Test_Result
                               then F.PC + 1 < Code_Length (Program, F.Prototype)),
                   when Host_Frame => True))
   with Ghost, Pre => Is_Well_Formed (Program);

   --  [proof] The frame invariant (PROOFS.md, VM stack and frames): every frame lies in the
   --  stack, and each starts after the function of the one below it.
   function Frames_Valid
     (Frames : Frame_Array; Depth : Natural; Stack_Last : Stack_Size; Program : Chunk)
      return Boolean
   is (Frames'First = 1
       and then Depth <= Frames'Last
       and then (for all F in 1 .. Depth =>
                   Frame_Valid (Frames (F), Stack_Last, Program)
                   and then (F = 1 or else Frames (F - 1).Func < Frames (F).Origin)))
   with Ghost, Pre => Is_Well_Formed (Program);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Frames_Valid);

   --  [proof] Every prototype's constants are inside the array of constants, of Total values.
   function Bases_Valid (Bases : Base_Array; Total : Natural; Program : Chunk) return Boolean
   is (for all P in Bases'Range =>
         P in 1 .. Prototype_Count (Program)
         and then Bases (P) <= Total
         and then Constant_Count (Program, P) <= Total - Bases (P))
   with Ghost, Pre => Is_Well_Formed (Program);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Bases_Valid);

   --  [proof] The machine's arrays are allocated, of the shapes the machine relies on.
   function Shape_Valid (M : Machine) return Boolean
   is (M.Program /= null
       and then Is_Well_Formed (M.Program.all)
       and then Pyro.Bytecode.Is_Valid (M.Program.all)
       and then Prototype_Count (M.Program.all) > 0
       and then M.Names /= null
       and then Pyro.Symbols.Is_Valid (M.Names.all)
       and then M.Constants /= null
       and then M.Constants'First = 1
       and then M.Bases /= null
       and then M.Bases'First = 1
       and then M.Bases'Last = Prototype_Count (M.Program.all)
       and then Bases_Valid (M.Bases.all, M.Constants'Length, M.Program.all)
       and then M.Registry /= null
       and then M.Registry'First = 1
       and then M.Registry'Last = Registry_Size
       and then M.Stack /= null
       and then M.Stack'First = 1
       and then M.Stack'Last in Initial_Stack .. Stack_Limit
       and then M.Top <= M.Stack'Last + 1
       and then M.Frames /= null
       and then M.Frames'First = 1
       and then M.Frames'Last <= Maximum_Frames
       and then M.Depth <= M.Frames'Last
       and then M.Open /= null
       and then M.Open'First = 1
       and then M.Open'Last in Initial_Open .. Maximum_Open
       and then M.Open_Count <= M.Open'Last
       and then M.Closing /= null
       and then M.Closing'First = 1
       and then M.Closing'Last in Initial_Open .. Maximum_Open
       and then M.Closing_Count <= M.Closing'Last
       and then M.Results_At <= M.Stack'Last
       and then M.Result_Size <= M.Stack'Last + 1 - M.Results_At)
   with Ghost;

   function Objects (M : Machine) return Pyro.Kind_Sequences.Sequence
   is (Pyro.Heap.Kinds (M.Heap));

   --  [proof] Every value the machine keeps refers to an object K shows.
   function Roots_Live_In (K : Pyro.Kind_Sequences.Sequence; M : Machine) return Boolean
   is (Values_Live (K, M.Constants.all)
       and then Values_Live (K, M.Registry.all)
       and then Values_Live (K, M.Stack.all)
       and then Values_Live (K, M.Open.all))
   with
     Ghost,
     Pre => M.Constants /= null and then M.Registry /= null and then M.Stack /= null
            and then M.Open /= null;

   --  [proof] Every value the machine keeps refers to an object of its heap.
   function Roots_Live (M : Machine) return Boolean
   is (Roots_Live_In (Objects (M), M))
   with
     Ghost,
     Pre => M.Constants /= null and then M.Registry /= null and then M.Stack /= null
            and then M.Open /= null;

   --  [proof] What the state says of the frames: a Lua frame with nothing pending runs when
   --  Ready, a host frame waits when Waiting.
   function State_Valid (M : Machine) return Boolean
   is (case M.State is
         when Ready   =>
           M.Depth >= 1
           and then M.Frames (M.Depth).Kind = Lua_Frame
           and then M.Frames (M.Depth).Action = No_Action,
         when Waiting => M.Depth >= 1 and then M.Frames (M.Depth).Kind = Host_Frame,
         when others  => True)
   with
     Ghost,
     Pre => M.Frames /= null and then M.Frames'First = 1 and then M.Depth <= M.Frames'Last;

   --  [proof] The machine is consistent but for what its state says of its frames: within an
   --  operation, between popping or pushing a frame and settling the state.
   function Core_Valid (M : Machine) return Boolean
   is (Pyro.Heap.Is_Valid (M.Heap)
       and then Shape_Valid (M)
       and then Frames_Valid (M.Frames.all, M.Depth, M.Stack'Last, M.Program.all)
       and then Roots_Live (M))
   with Ghost;

   function Is_Valid (M : Machine) return Boolean
   is (M.State = Unloaded or else (Core_Valid (M) and then State_Valid (M)));

   function Running (M : Machine) return Boolean
   is (M.State = Ready);

   function Is_Live (M : Machine; Item : Value) return Boolean
   is (Pyro.Heap.Is_Live (M.Heap, Item));

   --  The facts of prototype P, running the instruction at PC.
   function View_Of_Prototype
     (Program : Chunk; P : Prototype_Index; PC : Entry_Count) return Frame_View
   is ((Prototype => P,
        PC        => Natural'Min (PC, Maximum_Entries - 1),
        Registers => Natural (Header (Program, P).Stack_Size),
        Constants => Constant_Count (Program, P),
        Upvalues  => Upvalue_Count (Program, P),
        Code      => Code_Length (Program, P),
        Vararg    => Header (Program, P).Is_Vararg,
        Fixed     => Natural (Header (Program, P).Parameter_Count),
        Children  => Child_Count (Program, P)))
   with Pre => Is_Well_Formed (Program) and then P in 1 .. Prototype_Count (Program);

   --  The facts of the frame F: those of its prototype, or of the first one when it has none.
   function View_Of (Program : Chunk; F : Frame) return Frame_View
   is (View_Of_Prototype
         (Program,
          (if F.Prototype in 1 .. Prototype_Count (Program) then F.Prototype else 1),
          F.PC))
   with Pre => Is_Well_Formed (Program) and then Prototype_Count (Program) > 0;

   function View (M : Machine) return Frame_View
   is (View_Of (M.Program.all, M.Frames (M.Depth)));

   --  The instruction frame F executes, or a MOVE when it has none.
   function Instruction_Of (Program : Chunk; F : Frame) return Pyro.Bytecode.Instruction
   is (if F.Prototype in 1 .. Prototype_Count (Program)
          and then F.PC < Code_Length (Program, F.Prototype)
       then Instruction_At (Program, F.Prototype, F.PC)
       else (others => <>))
   with Pre => Is_Well_Formed (Program);

   function Current (M : Machine) return Pyro.Bytecode.Instruction
   is (Instruction_Of (M.Program.all, M.Frames (M.Depth)));

   ----------------------------------------------------------------------------------------
   --  Proof helpers
   ----------------------------------------------------------------------------------------

   --  [proof] Unfolds the frame invariant for frame F.
   procedure Lemma_Frame_In
     (Frames : Frame_Array; Depth : Natural; Last : Stack_Size; Program : Chunk; F : Positive)
   with
     Ghost,
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then Frames_Valid (Frames, Depth, Last, Program)
       and then F <= Depth,
     Post   =>
       Frames'First = 1
       and then Depth <= Frames'Last
       and then Frame_Valid (Frames (F), Last, Program)
       and then (F = 1 or else Frames (F - 1).Func < Frames (F).Origin)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Frames_Valid);
   begin
      null;
   end Lemma_Frame_In;

   --  [proof] Unfolds the frame invariant for frame F of M.
   procedure Lemma_Frame (M : Machine; F : Positive)
   with
     Ghost,
     Global => null,
     Pre    => Core_Valid (M) and then F <= M.Depth,
     Post   =>
       Frame_Valid (M.Frames (F), M.Stack'Last, M.Program.all)
       and then (F = 1 or else M.Frames (F - 1).Func < M.Frames (F).Origin)
   is
   begin
      Lemma_Frame_In (M.Frames.all, M.Depth, M.Stack'Last, M.Program.all, F);
   end Lemma_Frame;

   --  [proof] No frames are valid.
   procedure Lemma_Frames_Empty (Frames : Frame_Array; Last : Stack_Size; Program : Chunk)
   with
     Ghost,
     Global => null,
     Pre    => Is_Well_Formed (Program) and then Frames'First = 1 and then Frames'Last >= 0,
     Post   => Frames_Valid (Frames, 0, Last, Program)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Frames_Valid);
   begin
      null;
   end Lemma_Frames_Empty;

   --  [proof] The frame invariant holds in a larger stack.
   procedure Lemma_Frames_Larger
     (Frames : Frame_Array; Depth : Natural; Before, After : Stack_Size; Program : Chunk)
   with
     Ghost,
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then Frames_Valid (Frames, Depth, Before, Program)
       and then Before <= After,
     Post   => Frames_Valid (Frames, Depth, After, Program)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Frames_Valid);
   begin
      null;
   end Lemma_Frames_Larger;

   --  [proof] The frame invariant holds for the frames below the top one.
   procedure Lemma_Frames_Pop
     (Frames : Frame_Array; Depth : Positive; Last : Stack_Size; Program : Chunk)
   with
     Ghost,
     Global => null,
     Pre    => Is_Well_Formed (Program) and then Frames_Valid (Frames, Depth, Last, Program),
     Post   => Frames_Valid (Frames, Depth - 1, Last, Program)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Frames_Valid);
   begin
      null;
   end Lemma_Frames_Pop;

   --  [proof] The frame invariant holds in After, which starts with the frames of Before.
   procedure Lemma_Frames_Copy
     (Before, After : Frame_Array; Depth : Natural; Last : Stack_Size; Program : Chunk)
   with
     Ghost,
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then Frames_Valid (Before, Depth, Last, Program)
       and then After'First = 1
       and then Depth <= After'Last
       and then (for all F in 1 .. Depth => After (F) = Before (F)),
     Post   => Frames_Valid (After, Depth, Last, Program)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Frames_Valid);
   begin
      null;
   end Lemma_Frames_Copy;

   --  [proof] The frame invariant holds for After, which keeps the frames of Before below
   --  Depth and has at Depth a frame in the stack above them.
   procedure Lemma_Frames_Set
     (Before, After : Frame_Array; Depth : Positive; Last : Stack_Size; Program : Chunk)
   with
     Ghost,
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then Frames_Valid (Before, Depth - 1, Last, Program)
       and then After'First = 1
       and then Depth <= After'Last
       and then (for all F in 1 .. Depth - 1 => After (F) = Before (F))
       and then Frame_Valid (After (Depth), Last, Program)
       and then (Depth = 1 or else After (Depth - 1).Func < After (Depth).Origin),
     Post   => Frames_Valid (After, Depth, Last, Program)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Frames_Valid);
   begin
      null;
   end Lemma_Frames_Set;

   --  [proof] Prototype P's constants are inside the array of constants.
   procedure Lemma_Base (M : Machine; P : Prototype_Index)
   with
     Ghost,
     Global => null,
     Pre    => Core_Valid (M) and then P in 1 .. Prototype_Count (M.Program.all),
     Post   =>
       M.Bases (P) <= M.Constants'Length
       and then Constant_Count (M.Program.all, P) <= M.Constants'Length - M.Bases (P)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Bases_Valid);
   begin
      null;
   end Lemma_Base;

   --  [proof] Bases that hold each prototype's constants inside Total values are valid.
   procedure Lemma_Bases (Bases : Base_Array; Total : Natural; Program : Chunk)
   with
     Ghost,
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then (for all P in Bases'Range =>
                   P in 1 .. Prototype_Count (Program)
                   and then Bases (P) <= Total
                   and then Constant_Count (Program, P) <= Total - Bases (P)),
     Post   => Bases_Valid (Bases, Total, Program)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Bases_Valid);
   begin
      null;
   end Lemma_Bases;

   --  [proof] Live values stay live when the heap keeps its objects.
   procedure Lemma_Grow (Before, After : Pyro.Kind_Sequences.Sequence; A : Root_Array)
   with
     Ghost,
     Global => null,
     Pre    => Values_Live (Before, A) and then Pyro.Heap.Keeps_Objects (Before, After),
     Post   => Values_Live (After, A)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Grow;

   --  [proof] The machine's values stay live when its heap keeps its objects.
   procedure Lemma_Roots_Grow (Before : Pyro.Kind_Sequences.Sequence; M : Machine)
   with
     Ghost,
     Global => null,
     Pre    =>
       M.Constants /= null and then M.Registry /= null and then M.Stack /= null
       and then M.Open /= null
       and then Roots_Live_In (Before, M)
       and then Pyro.Heap.Keeps_Objects (Before, Objects (M)),
     Post   => Roots_Live (M)
   is
   begin
      Lemma_Grow (Before, Objects (M), M.Constants.all);
      Lemma_Grow (Before, Objects (M), M.Registry.all);
      Lemma_Grow (Before, Objects (M), M.Stack.all);
      Lemma_Grow (Before, Objects (M), M.Open.all);
   end Lemma_Roots_Grow;

   --  [proof] The machine's values stay live when its heap keeps its objects, its open
   --  upvalues being live in the heap as it is now.
   procedure Lemma_Roots_Open_Grow (Before : Pyro.Kind_Sequences.Sequence; M : Machine)
   with
     Ghost,
     Global => null,
     Pre    =>
       M.Constants /= null and then M.Registry /= null and then M.Stack /= null
       and then M.Open /= null
       and then Values_Live (Before, M.Constants.all)
       and then Values_Live (Before, M.Registry.all)
       and then Values_Live (Before, M.Stack.all)
       and then Values_Live (Objects (M), M.Open.all)
       and then Pyro.Heap.Keeps_Objects (Before, Objects (M)),
     Post   => Roots_Live (M)
   is
   begin
      Lemma_Grow (Before, Objects (M), M.Constants.all);
      Lemma_Grow (Before, Objects (M), M.Registry.all);
      Lemma_Grow (Before, Objects (M), M.Stack.all);
   end Lemma_Roots_Open_Grow;

   --  [proof] An array of nil values is live.
   procedure Lemma_Nil (K : Pyro.Kind_Sequences.Sequence; A : Root_Array)
   with
     Ghost,
     Global => null,
     Pre    => (for all Index in A'Range => A (Index) = Nil),
     Post   => Values_Live (K, A)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Nil;

   --  [proof] An array that starts with the values of a live one and goes on with nil is live.
   procedure Lemma_Extend (K : Pyro.Kind_Sequences.Sequence; Before, After : Root_Array)
   with
     Ghost,
     Global => null,
     Pre    =>
       Values_Live (K, Before)
       and then Before'First = 1
       and then After'First = 1
       and then Before'Last <= After'Last
       and then (for all Index in After'Range =>
                   (if Index <= Before'Last then After (Index) = Before (Index)
                    else After (Index) = Nil)),
     Post   => Values_Live (K, After)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Extend;

   --  [proof] A value of A is canonical and live.
   procedure Lemma_Value (K : Pyro.Kind_Sequences.Sequence; A : Root_Array; Index : Positive)
   with
     Ghost,
     Global => null,
     Pre    => Values_Live (K, A) and then Index in A'Range,
     Post   => Is_Canonical (A (Index)) and then Pyro.Heap.Live_In (K, A (Index))
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Value;

   --  [proof] Writing a canonical, live value into A keeps it live.
   procedure Lemma_Store
     (K : Pyro.Kind_Sequences.Sequence; Before, After : Root_Array; Index : Positive)
   with
     Ghost,
     Global => null,
     Pre    =>
       Values_Live (K, Before)
       and then After'First = Before'First
       and then After'Last = Before'Last
       and then Index in After'Range
       and then Is_Canonical (After (Index))
       and then Pyro.Heap.Live_In (K, After (Index))
       and then (for all Other in After'Range =>
                   (if Other /= Index then After (Other) = Before (Other))),
     Post   => Values_Live (K, After)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Store;

   --  [proof] A value the heap holds is live in its kinds, and back.
   procedure Lemma_Heap_Live (H : Pyro.Heap.Heap; Item : Value)
   with
     Ghost,
     Global => null,
     Pre    => Pyro.Heap.Is_Live (H, Item),
     Post   => Pyro.Heap.Live_In (Pyro.Heap.Kinds (H), Item)
   is
   begin
      null;
   end Lemma_Heap_Live;

   procedure Lemma_Live_Heap (H : Pyro.Heap.Heap; Item : Value)
   with
     Ghost,
     Global => null,
     Pre    => Pyro.Heap.Live_In (Pyro.Heap.Kinds (H), Item),
     Post   => Pyro.Heap.Is_Live (H, Item)
   is
   begin
      null;
   end Lemma_Live_Heap;

   procedure Lemma_Still_Live (Before : Pyro.Kind_Sequences.Sequence; M : Machine; Item : Value)
   is
      pragma Unreferenced (Before);
   begin
      Lemma_Live_Heap (M.Heap, Item);
   end Lemma_Still_Live;

   procedure Lemma_Live_In (M : Machine; Item : Value) is
   begin
      Lemma_Heap_Live (M.Heap, Item);
   end Lemma_Live_In;

   procedure Lemma_View (M : Machine) is
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Valid_Prototype (M.Program.all, M.Frames (M.Depth).Prototype);
   end Lemma_View;

   ----------------------------------------------------------------------------------------
   --  Value arrays
   ----------------------------------------------------------------------------------------

   --  Makes place Place of Items hold Item.
   procedure Store_Value
     (Items : in out Root_Array; Heap : Pyro.Heap.Heap; Place : Positive; Item : Value)
   with
     Global => null,
     Pre    =>
       Place in Items'Range
       and then Is_Canonical (Item)
       and then Pyro.Heap.Live_In (Pyro.Heap.Kinds (Heap), Item)
       and then Values_Live (Pyro.Heap.Kinds (Heap), Items),
     Post   =>
       Values_Live (Pyro.Heap.Kinds (Heap), Items)
       and then Items (Place) = Item
       and then (for all Other in Items'Range =>
                   (if Other /= Place then Items (Other) = Items'Old (Other)))
   is
      Before : constant Root_Array := Items with Ghost;
   begin
      Items (Place) := Item;
      Lemma_Store (Pyro.Heap.Kinds (Heap), Before, Items, Place);
   end Store_Value;

   --  Makes the places of Items from From hold the values of List.
   procedure Store_Values
     (Items : in out Root_Array; Heap : Pyro.Heap.Heap; From : Positive; List : Value_List)
   with
     Global => null,
     Pre    =>
       Items'First = 1
       and then List'Length <= Items'Last
       and then From - 1 <= Items'Last - List'Length
       and then (for all Position in List'Range =>
                   Is_Canonical (List (Position))
                   and then Pyro.Heap.Is_Live (Heap, List (Position)))
       and then Values_Live (Pyro.Heap.Kinds (Heap), Items),
     Post   => Values_Live (Pyro.Heap.Kinds (Heap), Items)
   is
   begin
      for Index in List'Range loop
         Lemma_Heap_Live (Heap, List (Index));
         Store_Value (Items, Heap, From + (Index - List'First), List (Index));
         pragma Loop_Invariant (Values_Live (Pyro.Heap.Kinds (Heap), Items));
      end loop;
   end Store_Values;

   --  Copies Count values of Items from From to To, as memmove does.
   procedure Copy
     (Items : in out Root_Array; Heap : Pyro.Heap.Heap; From, To : Positive; Count : Natural)
   with
     Global => null,
     Pre    =>
       Items'First = 1
       and then Count <= Items'Last
       and then From - 1 <= Items'Last - Count
       and then To - 1 <= Items'Last - Count
       and then Values_Live (Pyro.Heap.Kinds (Heap), Items),
     Post   => Values_Live (Pyro.Heap.Kinds (Heap), Items)
   is
   begin
      if To <= From then
         for Index in 0 .. Count - 1 loop
            pragma Loop_Invariant (Values_Live (Pyro.Heap.Kinds (Heap), Items));
            declare
               Item : constant Value := Items (From + Index);
            begin
               Lemma_Value (Pyro.Heap.Kinds (Heap), Items, From + Index);
               Store_Value (Items, Heap, To + Index, Item);
            end;
         end loop;
      else
         for Index in reverse 0 .. Count - 1 loop
            pragma Loop_Invariant (Values_Live (Pyro.Heap.Kinds (Heap), Items));
            declare
               Item : constant Value := Items (From + Index);
            begin
               Lemma_Value (Pyro.Heap.Kinds (Heap), Items, From + Index);
               Store_Value (Items, Heap, To + Index, Item);
            end;
         end loop;
      end if;
   end Copy;

   --  Makes Count places of Items from From nil.
   procedure Fill_Nil
     (Items : in out Root_Array; Heap : Pyro.Heap.Heap; From : Positive; Count : Natural)
   with
     Global => null,
     Pre    =>
       Items'First = 1
       and then Count <= Items'Last
       and then From - 1 <= Items'Last - Count
       and then Values_Live (Pyro.Heap.Kinds (Heap), Items),
     Post   =>
       Values_Live (Pyro.Heap.Kinds (Heap), Items)
       and then (for all Index in From .. From - 1 + Count => Items (Index) = Nil)
   is
   begin
      for Index in 0 .. Count - 1 loop
         Store_Value (Items, Heap, From + Index, Nil);
         pragma Loop_Invariant (Values_Live (Pyro.Heap.Kinds (Heap), Items));
         pragma Loop_Invariant (for all Earlier in From .. From + Index => Items (Earlier) = Nil);
      end loop;
   end Fill_Nil;

   ----------------------------------------------------------------------------------------
   --  Values
   ----------------------------------------------------------------------------------------

   function Basic_Image (Item : Value) return String is
   begin
      case Item.Kind is
         when Boolean_Value =>
            return (if Item.Bits = 1 then "true" else "false");
         when Integer_Value =>
            return Pyro.Integer_Arithmetic.Image (Pyro.Integer_Arithmetic.To_Signed (Item.Bits));
         when Float_Value =>
            return Pyro.Floats.Image (Item.Bits);
         when others =>
            return "nil";
      end case;
   end Basic_Image;

   function Is_String (M : Machine; Item : Value) return Boolean
   is (Item.Kind = Object_Value
       and then Pyro.Heap.Kind_Of (M.Heap, Item.Object) = String_Object);

   --  (An unloaded machine holds no string.)
   function String_Text (M : Machine; Item : Value) return String
   is (if M.State = Unloaded then ""
       else Pyro.Heap.String_Reads.String_Text (M.Heap, Item.Object));

   procedure To_Number (M : Machine; Item : Value; Result : out Value; Valid : out Boolean) is
      Number : Pyro.Numbers.Numeral_Value;
   begin
      Result := Nil;
      Valid := Item.Kind in Integer_Value | Float_Value;
      if Valid then
         Result := Item;
      elsif Is_String (M, Item) then
         Pyro.Numbers.String_To_Number (String_Text (M, Item), Number, Valid);
         if Valid then
            Result :=
              (if Number.Is_Integer then Integer_Value_Of (Number.Integer_Value)
               else Float_Value_Of (Number.Float_Bits));
         end if;
      end if;
   end To_Number;

   function Type_Name (M : Machine; Item : Value) return String is
   begin
      case Item.Kind is
         when Nil_Value => return "nil";
         when Boolean_Value => return "boolean";
         when Integer_Value | Float_Value => return "number";
         when Object_Value =>
            case Pyro.Heap.Kind_Of (M.Heap, Item.Object) is
               when String_Object => return "string";
               when Table_Object => return "table";
               when Closure_Object | Host_Function_Object => return "function";
               when Free_Object | Upvalue_Object => return "userdata";
            end case;
      end case;
   end Type_Name;

   function Is_Table (M : Machine; Item : Value) return Boolean
   is (Item.Kind = Object_Value
       and then Pyro.Heap.Kind_Of (M.Heap, Item.Object) = Table_Object);

   function Is_Function (M : Machine; Item : Value) return Boolean
   is (Item.Kind = Object_Value
       and then Pyro.Heap.Kind_Of (M.Heap, Item.Object)
                in Closure_Object | Host_Function_Object);

   function Raw_Equal (Left, Right : Value) return Boolean is
      Converted : Integer_64;
      Exact     : Boolean;
   begin
      if Left.Kind = Float_Value and then Right.Kind = Float_Value then
         return Pyro.Floats.Compare (Pyro.Floats.Equal, Left.Bits, Right.Bits);
      elsif Left.Kind = Float_Value and then Right.Kind = Integer_Value then
         Pyro.Floats.To_Integer (Left.Bits, Converted, Exact);
         return Exact and then Converted = Integer_Of (Right);
      elsif Left.Kind = Integer_Value and then Right.Kind = Float_Value then
         Pyro.Floats.To_Integer (Right.Bits, Converted, Exact);
         return Exact and then Converted = Integer_Of (Left);
      end if;
      return Left = Right;
   end Raw_Equal;

   --  The bytes of Text, for the heap.
   function To_Bytes (Text : String) return Pyro.Strings.Byte_Array
   with
     Pre  => Text'Length <= Pyro.Heap.Maximum_String_Length,
     Post => To_Bytes'Result'First = 1 and then To_Bytes'Result'Length = Text'Length
   is
      Result : Pyro.Strings.Byte_Array (1 .. Text'Length);
   begin
      for Index in Result'Range loop
         Result (Index) := Text (Text'First - 1 + Natural (Index));
      end loop;
      return Result;
   end To_Bytes;

   ----------------------------------------------------------------------------------------
   --  The core
   ----------------------------------------------------------------------------------------

   procedure Lemma_Fits (M : Machine) is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Instruction_Valid);
      P : constant Prototype_Index := M.Frames (M.Depth).Prototype;
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Valid_Prototype (M.Program.all, P);
      pragma Assert
        (Instruction_Valid (M.Program.all, P, M.Frames (M.Depth).PC, Current (M)));
   end Lemma_Fits;

   function Previous_Target (M : Machine) return Natural is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Instruction_Valid);
      P : constant Prototype_Index := M.Frames (M.Depth).Prototype;
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Valid_Prototype (M.Program.all, P);
      pragma Assert
        (Instruction_Valid (M.Program.all, P, M.Frames (M.Depth).PC, Current (M)));
      pragma Assert (M.Frames (M.Depth).PC > 0);
      return Natural (Instruction_At (M.Program.all, P, M.Frames (M.Depth).PC - 1).A);
   end Previous_Target;

   function String_Order (M : Machine; Left, Right : Value) return Integer is
      Left_Length  : constant Natural :=
        Natural'Min (Pyro.Heap.String_Length (M.Heap, Left.Object),
                     Pyro.Heap.Maximum_String_Length);
      Right_Length : constant Natural :=
        Natural'Min (Pyro.Heap.String_Length (M.Heap, Right.Object),
                     Pyro.Heap.Maximum_String_Length);
      X, Y         : Character;
   begin
      for Position in 1 .. Natural'Min (Left_Length, Right_Length) loop
         X := Pyro.Heap.String_Byte (M.Heap, Left.Object, Byte_Position (Position));
         Y := Pyro.Heap.String_Byte (M.Heap, Right.Object, Byte_Position (Position));
         if X /= Y then
            return (if X < Y then -1 else 1);
         end if;
      end loop;
      return (if Left_Length < Right_Length then -1
              elsif Left_Length > Right_Length then 1
              else 0);
   end String_Order;

   --  The place in the stack of register Number of the running frame.
   function Register_Place (M : Machine; Number : Natural) return Positive
   with
     Global => null,
     Pre    => Is_Valid (M) and then Running (M) and then Number < View (M).Registers,
     Post   =>
       Register_Place'Result in M.Stack'Range
       and then Register_Place'Result = M.Frames (M.Depth).Func + 1 + Number
   is
   begin
      Lemma_Frame (M, M.Depth);
      return M.Frames (M.Depth).Func + 1 + Number;
   end Register_Place;

   function Register (M : Machine; Number : Natural) return Value is
      Place : constant Positive := Register_Place (M, Number);
   begin
      Lemma_Value (Objects (M), M.Stack.all, Place);
      Lemma_Live_Heap (M.Heap, M.Stack (Place));
      return M.Stack (Place);
   end Register;

   procedure Set_Register (M : in out Machine; Number : Natural; Item : Value) is
      Place : constant Positive := Register_Place (M, Number);
   begin
      Lemma_Heap_Live (M.Heap, Item);
      Store_Value (M.Stack.all, M.Heap, Place, Item);
   end Set_Register;

   function Constant_At (M : Machine; Number : Natural) return Value is
      P : constant Prototype_Index := M.Frames (M.Depth).Prototype;
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Base (M, P);
      Lemma_Value (Objects (M), M.Constants.all, M.Bases (P) + Number + 1);
      Lemma_Live_Heap (M.Heap, M.Constants (M.Bases (P) + Number + 1));
      return M.Constants (M.Bases (P) + Number + 1);
   end Constant_At;

   --  The upvalue object of upvalue Number of the closure in stack place Func, or No_Object
   --  when it is not one.
   function Upvalue_Cell (M : Machine; Func : Positive; Number : Natural) return Object_Handle
   with
     Global => null,
     Pre    => Core_Valid (M) and then Func in M.Stack'Range,
     Post   =>
       (if Upvalue_Cell'Result /= No_Object
        then Pyro.Heap.Kind_Of (M.Heap, Upvalue_Cell'Result) = Upvalue_Object
             and then Pyro.Heap.Reference_Count (M.Heap, Upvalue_Cell'Result) >= 1)
   is
      Closure : constant Value := M.Stack (Func);
      Cell    : Value;
   begin
      if Closure.Kind /= Object_Value
        or else Pyro.Heap.Kind_Of (M.Heap, Closure.Object) /= Closure_Object
        or else Number >= Pyro.Heap.Reference_Count (M.Heap, Closure.Object)
      then
         return No_Object;
      end if;
      Cell := Pyro.Heap.Reference_At (M.Heap, Closure.Object, Number + 1);
      if Cell.Kind /= Object_Value
        or else Pyro.Heap.Kind_Of (M.Heap, Cell.Object) /= Upvalue_Object
        or else Pyro.Heap.Reference_Count (M.Heap, Cell.Object) < 1
      then
         return No_Object;
      end if;
      return Cell.Object;
   end Upvalue_Cell;

   function Upvalue (M : Machine; Number : Natural) return Value is
      Cell  : Object_Handle;
      Place : Natural;
   begin
      Lemma_Frame (M, M.Depth);
      Cell := Upvalue_Cell (M, M.Frames (M.Depth).Func, Number);
      if Cell = No_Object then
         return Nil;
      end if;
      Place := Pyro.Heap.Tag_Of (M.Heap, Cell);
      if Place in M.Stack'Range then
         Lemma_Value (Objects (M), M.Stack.all, Place);
         Lemma_Live_Heap (M.Heap, M.Stack (Place));
         return M.Stack (Place);
      end if;
      Pyro.Heap.Lemma_Reference_Live (M.Heap, Cell, 1);
      return Pyro.Heap.Reference_At (M.Heap, Cell, 1);
   end Upvalue;

   procedure Set_Upvalue (M : in out Machine; Number : Natural; Item : Value) is
      Cell  : Object_Handle;
      Place : Natural;
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Heap_Live (M.Heap, Item);
      Cell := Upvalue_Cell (M, M.Frames (M.Depth).Func, Number);
      if Cell = No_Object then
         return;
      end if;
      Place := Pyro.Heap.Tag_Of (M.Heap, Cell);
      if Place in M.Stack'Range then
         Store_Value (M.Stack.all, M.Heap, Place, Item);
      else
         Pyro.Heap.Set_Reference (M.Heap, Cell, 1, Item);
      end if;
   end Set_Upvalue;

   --  Makes Item the top frame of Frames, at Depth.
   procedure Set_Top_Frame
     (Frames  : in out Frame_Array;
      Depth   : Positive;
      Item    : Frame;
      Last    : Stack_Size;
      Program : Chunk)
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then Frames'First = 1
       and then Depth <= Frames'Last
       and then Frames_Valid (Frames, Depth, Last, Program)
       and then Frame_Valid (Item, Last, Program)
       and then (Depth = 1 or else Frames (Depth - 1).Func < Item.Origin),
     Post   => Frames_Valid (Frames, Depth, Last, Program) and then Frames (Depth) = Item
   is
      Before : constant Frame_Array := Frames with Ghost;
   begin
      Lemma_Frames_Pop (Frames, Depth, Last, Program);
      Frames (Depth) := Item;
      Lemma_Frames_Set (Before, Frames, Depth, Last, Program);
   end Set_Top_Frame;

   --  Moves the running frame on by 1 + Offset instructions.
   procedure Advance (M : in out Machine; Offset : Integer)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then Offset in -1 - View (M).PC .. View (M).Code - 2 - View (M).PC,
     Post   =>
       Is_Valid (M)
       and then Running (M)
       and then M.Depth = M.Depth'Old
       and then M.Frames (M.Depth)
                = (M.Frames (M.Depth)'Old with delta PC => M.Frames (M.Depth)'Old.PC + 1 + Offset)
       and then View (M).Registers = View (M).Registers'Old
   is
      F : constant Frame := M.Frames (M.Depth);
   begin
      Lemma_Frame (M, M.Depth);
      Set_Top_Frame
        (M.Frames.all, M.Depth, (F with delta PC => F.PC + 1 + Offset), M.Stack'Last,
         M.Program.all);
   end Advance;

   procedure Next (M : in out Machine; Offset : Integer := 0) is
   begin
      Advance (M, Offset);
   end Next;

   function Raw_Get (M : Machine; T : Value; Key : Value) return Value is
   begin
      if T.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, T.Object) = Table_Object
      then
         return Pyro.Heap.Table_Get (M.Heap, T.Object, Key);
      end if;
      return Nil;
   end Raw_Get;

   procedure Raw_Set
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      T      : Value;
      Key    : Value;
      Item   : Value;
      Status : out Pyro.Tables.Set_Status)
   is
   begin
      Status := Pyro.Tables.Done;
      if T.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, T.Object) = Table_Object
      then
         Pyro.Heap.Table_Set (M.Heap, Budget, T.Object, Key, Item, Status);
      end if;
   end Raw_Set;

   --  The metatable of Item, in a machine that may be between two states.
   function Metatable_Of (M : Machine; Item : Value) return Value
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   =>
       Is_Canonical (Metatable_Of'Result)
       and then Pyro.Heap.Live_In (Objects (M), Metatable_Of'Result)
   is
      Result : Value;
   begin
      if not Is_Table (M, Item)
        or else Pyro.Heap.Reference_Count (M.Heap, Item.Object) < 1
      then
         return Nil;
      end if;
      Pyro.Heap.Lemma_Reference_Live (M.Heap, Item.Object, 1);
      Result := Pyro.Heap.Reference_At (M.Heap, Item.Object, 1);
      Lemma_Heap_Live (M.Heap, Result);
      return (if Is_Table (M, Result) then Result else Nil);
   end Metatable_Of;

   --  Field Field of Item's metatable, in a machine that may be between two states.
   function Field_Of (M : Machine; Item : Value; Field : Event) return Value
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   =>
       Is_Canonical (Field_Of'Result) and then Pyro.Heap.Live_In (Objects (M), Field_Of'Result)
   is
      Table  : constant Value := Metatable_Of (M, Item);
      Result : Value;
   begin
      if not Is_Table (M, Table) then
         return Nil;
      end if;
      Lemma_Value (Objects (M), M.Registry.all, Event_Place (Field));
      Result := Pyro.Heap.Table_Get (M.Heap, Table.Object, M.Registry (Event_Place (Field)));
      Lemma_Heap_Live (M.Heap, Result);
      return Result;
   end Field_Of;

   function Metatable (M : Machine; Item : Value) return Value is
      Result : constant Value := Metatable_Of (M, Item);
   begin
      Lemma_Live_Heap (M.Heap, Result);
      return Result;
   end Metatable;

   function Metafield (M : Machine; Item : Value; Field : Event) return Value is
      Result : constant Value := Field_Of (M, Item, Field);
   begin
      Lemma_Live_Heap (M.Heap, Result);
      return Result;
   end Metafield;

   procedure Set_Metatable (M : in out Machine; T : Value; Table : Value) is
   begin
      if Pyro.Heap.Reference_Count (M.Heap, T.Object) >= 1 then
         Pyro.Heap.Set_Reference (M.Heap, T.Object, 1, Table);
      end if;
   end Set_Metatable;

   function Raw_Index (M : Machine; T : Value; Key : Value) return Value is
   begin
      if Is_Table (M, T) then
         return Pyro.Heap.Table_Get (M.Heap, T.Object, Key);
      end if;
      return Nil;
   end Raw_Index;

   procedure Raw_Store
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      T      : Value;
      Key    : Value;
      Item   : Value;
      Status : out Pyro.Tables.Set_Status) is
   begin
      Pyro.Heap.Table_Set (M.Heap, Budget, T.Object, Key, Item, Status);
   end Raw_Store;

   procedure Next_Pair
     (M         : Machine;
      T         : Value;
      Key       : Value;
      Next_Key  : out Value;
      Next_Item : out Value;
      Status    : out Pyro.Tables.Next_Status) is
   begin
      Pyro.Heap.Table_Reads.Table_Next (M.Heap, T.Object, Key, Next_Key, Next_Item, Status);
   end Next_Pair;

   function Raw_Length (M : Machine; Item : Value) return Integer_64 is
      Length : Integer_64 := 0;
   begin
      if Is_String (M, Item) then
         Length := Integer_64 (Pyro.Heap.String_Length (M.Heap, Item.Object));
      elsif Is_Table (M, Item) then
         Pyro.Heap.Table_Reads.Table_Length (M.Heap, Item.Object, Length);
      end if;
      return Length;
   end Raw_Length;

   ----------------------------------------------------------------------------------------
   --  Stack and frames
   ----------------------------------------------------------------------------------------

   --  Makes the stack have at least Needed places. Success is False when that would pass
   --  Stack_Limit (a stack overflow) or Budget cannot pay; the stack is then unchanged.
   procedure Reserve
     (Stack   : in out Root_Array_Access;
      Heap    : Pyro.Heap.Heap;
      Budget  : in out Memory_Budget;
      Needed  : Positive;
      Success : out Boolean)
   with
     Global => null,
     Pre    =>
       Stack /= null
       and then Stack'First = 1
       and then Stack'Last in Initial_Stack .. Stack_Limit
       and then Values_Live (Pyro.Heap.Kinds (Heap), Stack.all),
     Post   =>
       Stack /= null
       and then Stack'First = 1
       and then Stack'Last in Stack'Last'Old .. Stack_Limit
       and then Values_Live (Pyro.Heap.Kinds (Heap), Stack.all)
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Success then Needed <= Stack'Last)
   is
      Size    : Positive;
      Larger  : Root_Array_Access;
      Charged : Boolean;
   begin
      Success := True;
      if Needed <= Stack'Last then
         return;
      end if;
      if Needed > Stack_Limit then
         Success := False;
         return;
      end if;
      Size := Positive'Min (Stack_Limit, Positive'Max (Needed, 2 * Stack'Length));
      Charge (Budget, Value_Bytes * Byte_Count (Size - Stack'Length), Charged);
      if not Charged then
         Success := False;
         return;
      end if;
      declare
         Before : constant Root_Array := Stack.all with Ghost;
      begin
         Larger := new Root_Array'(1 .. Size => Nil);
         Larger (1 .. Stack'Length) := Stack.all;
         Lemma_Extend (Pyro.Heap.Kinds (Heap), Before, Larger.all);
      end;
      Free_Values (Stack);
      Stack := Larger;
   end Reserve;

   --  Pushes Item as the new top frame. Success is False when the frames would pass
   --  Maximum_Frames or Budget cannot pay.
   procedure Push_Frame
     (Frames  : in out Frame_Array_Access;
      Depth   : in out Natural;
      Budget  : in out Memory_Budget;
      Item    : Frame;
      Last    : Stack_Size;
      Program : Chunk;
      Success : out Boolean)
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then Frames /= null
       and then Frames'First = 1
       and then Frames'Last <= Maximum_Frames
       and then Depth <= Frames'Last
       and then Frames_Valid (Frames.all, Depth, Last, Program)
       and then Frame_Valid (Item, Last, Program)
       and then (Depth = 0 or else Frames (Depth).Func < Item.Origin),
     Post   =>
       Frames /= null
       and then Frames'First = 1
       and then Frames'Last <= Maximum_Frames
       and then Depth <= Frames'Last
       and then Frames_Valid (Frames.all, Depth, Last, Program)
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Success then Depth = Depth'Old + 1 and then Frames (Depth) = Item
                 else Depth = Depth'Old)
   is
      Size    : Positive;
      Larger  : Frame_Array_Access;
      Charged : Boolean;
   begin
      Success := False;
      if Depth = Frames'Last then
         if Depth >= Maximum_Frames then
            return;
         end if;
         Size := Positive'Min (Maximum_Frames, Positive'Max (Initial_Frames, 2 * Frames'Length));
         Charge (Budget, Frame_Bytes * Byte_Count (Size - Frames'Length), Charged);
         if not Charged then
            return;
         end if;
         Larger := new Frame_Array'(1 .. Size => (others => <>));
         Larger (1 .. Frames'Length) := Frames.all;
         Lemma_Frames_Copy (Frames.all, Larger.all, Depth, Last, Program);
         Free_Frames (Frames);
         Frames := Larger;
      end if;
      declare
         Before : constant Frame_Array := Frames.all with Ghost;
      begin
         Depth := Depth + 1;
         Frames (Depth) := Item;
         Lemma_Frames_Set (Before, Frames.all, Depth, Last, Program);
      end;
      Success := True;
   end Push_Frame;

   --  The source line of the instruction frame Level (counted from the top) is running, 0
   --  when it is not a Lua frame. A frame below the top, or the top one when At_Call (it moved
   --  on past the call it makes), is at the instruction before its program counter, as
   --  ldebug.c's currentpc finds it.
   function Current_Line
     (M : Machine; Level : Positive; At_Call : Boolean := False) return Natural
   with Global => null, Pre => Core_Valid (M)
   is
      F : Frame;
   begin
      if Level > M.Depth then
         return 0;
      end if;
      Lemma_Frame (M, M.Depth + 1 - Level);
      F := M.Frames (M.Depth + 1 - Level);
      if F.Kind /= Lua_Frame then
         return 0;
      end if;
      return Natural
        (Line_At
           (M.Program.all, F.Prototype,
            (if (Level > 1 or else At_Call) and then F.PC > 0 and then F.Action /= Rerun
             then F.PC - 1 else F.PC)));
   end Current_Line;

   --  "name:line: " for frame Level, or "" when it is not a Lua frame.
   function Position_Of
     (M : Machine; Level : Positive; At_Call : Boolean := False) return String
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   => Position_Of'Result'First = 1 and then Position_Of'Result'Length <= 128
   is
      Line : constant Natural := Current_Line (M, Level, At_Call);
   begin
      if Line = 0 then
         return "";
      end if;
      return M.Name (1 .. M.Name_Length) & ":"
        & Pyro.Integer_Arithmetic.Image (Integer_64 (Line)) & ": ";
   end Position_Of;

   ----------------------------------------------------------------------------------------
   --  Upvalues
   ----------------------------------------------------------------------------------------

   --  Closes the open upvalues of places Level and above: each keeps its variable's value.
   procedure Close_Upvalues
     (Heap  : in out Pyro.Heap.Heap;
      Open  : in out Root_Array;
      Count : in out Natural;
      Stack : Root_Array;
      Level : Positive)
   with
     Global => null,
     Pre    =>
       Pyro.Heap.Is_Valid (Heap)
       and then Open'First = 1
       and then Open'Last <= Maximum_Open
       and then Count <= Open'Last
       and then Values_Live (Pyro.Heap.Kinds (Heap), Open)
       and then Values_Live (Pyro.Heap.Kinds (Heap), Stack),
     Post   =>
       Pyro.Heap.Is_Valid (Heap)
       and then Pyro.Heap.Kinds (Heap) = Pyro.Heap.Kinds (Heap)'Old
       and then Count <= Open'Last
       and then Values_Live (Pyro.Heap.Kinds (Heap), Open)
   is
      Kept  : Natural := 0;
      Cell  : Value;
      Place : Natural;
   begin
      for Index in 1 .. Count loop
         Lemma_Value (Pyro.Heap.Kinds (Heap), Open, Index);
         Cell := Open (Index);
         if Cell.Kind = Object_Value
           and then Pyro.Heap.Kind_Of (Heap, Cell.Object) = Upvalue_Object
         then
            Place := Pyro.Heap.Tag_Of (Heap, Cell.Object);
            if Place >= Level and then Place in Stack'Range
              and then Pyro.Heap.Reference_Count (Heap, Cell.Object) >= 1
            then
               Lemma_Value (Pyro.Heap.Kinds (Heap), Stack, Place);
               Lemma_Live_Heap (Heap, Stack (Place));
               Pyro.Heap.Set_Reference (Heap, Cell.Object, 1, Stack (Place));
               Pyro.Heap.Set_Tag (Heap, Cell.Object, 0);
            else
               Kept := Kept + 1;
               Store_Value (Open, Heap, Kept, Cell);
            end if;
         end if;
         pragma Loop_Invariant (Pyro.Heap.Is_Valid (Heap));
         pragma Loop_Invariant (Pyro.Heap.Kinds (Heap) = Pyro.Heap.Kinds (Heap)'Loop_Entry);
         pragma Loop_Invariant (Kept <= Index);
         pragma Loop_Invariant (Values_Live (Pyro.Heap.Kinds (Heap), Open));
      end loop;
      Fill_Nil (Open, Heap, Kept + 1, Count - Kept);
      Count := Kept;
   end Close_Upvalues;

   --  The open upvalue of stack place Place: the one that exists, or a new one. Result is Nil
   --  when Budget cannot pay.
   procedure Find_Upvalue
     (Heap   : in out Pyro.Heap.Heap;
      Open   : in out Root_Array_Access;
      Count  : in out Natural;
      Budget : in out Memory_Budget;
      Place  : Positive;
      Result : out Value)
   with
     Global => null,
     Pre    =>
       Pyro.Heap.Is_Valid (Heap)
       and then Open /= null
       and then Open'First = 1
       and then Open'Last in Initial_Open .. Maximum_Open
       and then Count <= Open'Last
       and then Values_Live (Pyro.Heap.Kinds (Heap), Open.all),
     Post   =>
       Pyro.Heap.Is_Valid (Heap)
       and then Pyro.Heap.Keeps_Objects (Pyro.Heap.Kinds (Heap)'Old, Pyro.Heap.Kinds (Heap))
       and then Limit (Budget) = Limit (Budget)'Old
       and then Open /= null
       and then Open'First = 1
       and then Open'Last in Initial_Open .. Maximum_Open
       and then Count <= Open'Last
       and then Values_Live (Pyro.Heap.Kinds (Heap), Open.all)
       and then Is_Canonical (Result)
       and then Pyro.Heap.Live_In (Pyro.Heap.Kinds (Heap), Result)
   is
      Handle  : Object_Handle;
      Larger  : Root_Array_Access;
      Charged : Boolean;
      Before  : constant Pyro.Kind_Sequences.Sequence := Pyro.Heap.Kinds (Heap) with Ghost;
   begin
      for Index in 1 .. Count loop
         if Open (Index).Kind = Object_Value
           and then Pyro.Heap.Kind_Of (Heap, Open (Index).Object) = Upvalue_Object
           and then Pyro.Heap.Tag_Of (Heap, Open (Index).Object) = Place
         then
            Lemma_Value (Pyro.Heap.Kinds (Heap), Open.all, Index);
            Result := Open (Index);
            return;
         end if;
      end loop;
      Result := Nil;
      if Count = Open'Last then
         if Open'Length > Stack_Limit then
            return;
         end if;
         Charge (Budget, Value_Bytes * Byte_Count (Open'Length), Charged);
         if not Charged then
            return;
         end if;
         declare
            Old : constant Root_Array := Open.all with Ghost;
         begin
            Larger := new Root_Array'(1 .. 2 * Open'Length => Nil);
            Larger (1 .. Open'Length) := Open.all;
            Lemma_Extend (Pyro.Heap.Kinds (Heap), Old, Larger.all);
         end;
         Free_Values (Open);
         Open := Larger;
      end if;
      Pyro.Heap.New_Object (Heap, Budget, Upvalue_Object, Place, 1, Handle);
      Lemma_Grow (Before, Pyro.Heap.Kinds (Heap), Open.all);
      if Handle = No_Object then
         return;
      end if;
      Result := Object_Value_Of (Handle);
      Lemma_Heap_Live (Heap, Result);
      Count := Count + 1;
      Store_Value (Open.all, Heap, Count, Result);
   end Find_Upvalue;

   ----------------------------------------------------------------------------------------
   --  Names in error messages
   ----------------------------------------------------------------------------------------

   --  The longest name a message gives, so that messages stay bounded.
   Maximum_Name : constant := 2 ** 12;

   --  [puc ldebug.c:getobjname] What a name names.
   type Name_Kind is
     (No_Name, Local_Name, Upvalue_Name, Constant_Name, Global_Name, Field_Name, Method_Name,
      Iterator_Name, Metamethod_Name);

   function Kind_Word (Kind : Name_Kind) return String
   is (case Kind is
         when No_Name         => "",
         when Local_Name      => "local",
         when Upvalue_Name    => "upvalue",
         when Constant_Name   => "constant",
         when Global_Name     => "global",
         when Field_Name      => "field",
         when Method_Name     => "method",
         when Iterator_Name   => "for iterator",
         when Metamethod_Name => "metamethod");

   --  A name found for a value: its kind and its text.
   type Found_Name is record
      Kind   : Name_Kind := No_Name;
      Text   : String (1 .. Maximum_Name) := [others => ' '];
      Length : Natural range 0 .. Maximum_Name := 0;
   end record;

   No_Found_Name : constant Found_Name := (Kind => No_Name, Text => [others => ' '], Length => 0);

   function Named (Kind : Name_Kind; Text : String) return Found_Name
   with Pre => Text'Length <= Maximum_Name
   is
      Result : Found_Name := No_Found_Name;
   begin
      Result.Kind := Kind;
      Result.Length := Text'Length;
      for Index in 1 .. Text'Length loop
         Result.Text (Index) := Text (Text'First - 1 + Index);
      end loop;
      return Result;
   end Named;

   --  [puc ldebug.c:formatvarinfo] " (kind 'name')", or "" for no name.
   function Formatted (Name : Found_Name) return String
   is (if Name.Kind = No_Name then ""
       else " (" & Kind_Word (Name.Kind) & " '" & Name.Text (1 .. Name.Length) & "')")
   with Post => Formatted'Result'Length <= Maximum_Name + 20;

   --  The text of symbol Symbol, at most Maximum_Name bytes; "?" when there is none.
   function Symbol_Name (Names : Pyro.Symbols.Symbol_Table; Symbol : Pyro.Symbols.Symbol_Index)
     return String
   with
     Global => null,
     Pre    => Pyro.Symbols.Is_Valid (Names),
     Post   => Symbol_Name'Result'Length <= Maximum_Name
   is
   begin
      if Symbol not in 1 .. Pyro.Symbols.Count (Names) then
         return "?";
      end if;
      declare
         Text : constant String := Pyro.Symbols.Text (Names, Symbol);
      begin
         return Text (Text'First .. Text'First - 1 + Natural'Min (Text'Length, Maximum_Name));
      end;
   end Symbol_Name;

   --  [puc ldebug.c:upvalname] The name of upvalue Number of prototype P.
   function Upvalue_Text
     (Program : Chunk; Names : Pyro.Symbols.Symbol_Table; P : Prototype_Index; Number : Natural)
     return String
   is (if Number < Upvalue_Count (Program, P)
       then Symbol_Name (Names, Upvalue_At (Program, P, Number).Name)
       else "?")
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names),
     Post   => Upvalue_Text'Result'Length <= Maximum_Name;

   --  [puc ldebug.c:kname] Constant Number of prototype P as a name: a string's text, else
   --  no name ("?").
   function Constant_Text
     (Program : Chunk; Names : Pyro.Symbols.Symbol_Table; P : Prototype_Index; Number : Natural)
     return Found_Name
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names)
   is
   begin
      if Number < Constant_Count (Program, P)
        and then Constant_At (Program, P, Number).Kind
                 in Short_String_Constant | Long_String_Constant
      then
         return Named (Constant_Name, Symbol_Name (Names, Constant_At (Program, P, Number).Symbol));
      end if;
      return Named (No_Name, "?");
   end Constant_Text;

   --  [puc lfunc.c:luaF_getlocalname] The name of the Number-th local variable active at PC
   --  in prototype P, or no name.
   function Local_Text
     (Program : Chunk;
      Names   : Pyro.Symbols.Symbol_Table;
      P       : Prototype_Index;
      Number  : Positive;
      PC      : Natural) return Found_Name
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names)
   is
      Left : Natural := Number;
   begin
      for Index in 0 .. Local_Count (Program, P) - 1 loop
         exit when Local_At (Program, P, Index).Start_PC > PC;
         if PC < Local_At (Program, P, Index).End_PC then
            if Left = 1 then
               return Named (Local_Name, Symbol_Name (Names, Local_At (Program, P, Index).Name));
            end if;
            Left := Left - 1;
         end if;
         pragma Loop_Invariant (Left >= 1);
      end loop;
      return No_Found_Name;
   end Local_Text;

   --  [puc lopcodes.c:luaP_opmodes] Instruction Code sets its register A (testAMode).
   function Sets_A (Code : Opcode) return Boolean
   is (Code in Move .. Get_Upvalue | Get_Table_Upvalue .. Get_Field | New_Table .. Shift_Right
             | Negate .. Concatenate | Test_Set | Call | Tail_Call | For_Loop | For_Prepare
             | Generic_For_Loop | Closure | Vararg | Vararg_Prepare);

   --  [puc ldebug.c:findsetreg] The instruction before Last in prototype P that last set
   --  register Register, or -1 when there is none or it ran only on some paths.
   function Find_Set_Register
     (Program : Chunk; P : Prototype_Index; Last : Natural; Register : Natural) return Integer
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Last < Code_Length (Program, P),
     Post   => Find_Set_Register'Result in -1 .. Last - 1
   is
      Stop   : Natural := Last;
      Set    : Integer := -1;
      Target : Natural := 0;
      Item   : Instruction;
      A      : Natural;
      Change : Boolean;
      Goal   : Integer;
   begin
      if Opcode_At (Program, P, Last)
         in Metamethod_Binary .. Metamethod_Binary_Constant
        and then Stop > 0
      then
         --  The arithmetic instruction before it did not run to its end.
         Stop := Stop - 1;
      end if;
      for PC in 0 .. Stop - 1 loop
         pragma Loop_Invariant (Set in -1 .. PC - 1);
         Item := Instruction_At (Program, P, PC);
         A := Natural (Item.A);
         case Item.Operation is
            when Load_Nil =>
               Change := A <= Register and then Register <= A + Natural (Item.B);
            when Generic_For_Call =>
               Change := Register >= A + 2;
            when Call | Tail_Call =>
               Change := Register >= A;
            when Jump =>
               --  Code before the farthest jump target up to Last runs only on some paths.
               Goal := PC + 1 + Integer (Item.Wide) - Offset_sJ;
               if Goal <= Stop and then Goal > Target then
                  Target := Goal;
               end if;
               Change := False;
            when others =>
               Change := Sets_A (Item.Operation) and then Register = A;
         end case;
         if Change then
            Set := (if PC < Target then -1 else PC);
         end if;
      end loop;
      return Set;
   end Find_Set_Register;

   --  [puc ldebug.c:basicgetobjname] A name for register Register at instruction PC of
   --  prototype P: a local's, an upvalue's or a constant's, through moves. PC becomes the
   --  instruction that set the register, or -1.
   procedure Basic_Name
     (Program  : Chunk;
      Names    : Pyro.Symbols.Symbol_Table;
      P        : Prototype_Index;
      PC       : in out Integer;
      Register : Natural;
      Result   : out Found_Name)
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names)
       and then PC in 0 .. Code_Length (Program, P) - 1
       and then Register <= 255,
     Post   => PC in -1 .. Code_Length (Program, P) - 1
   is
      Current : Natural := Register;
      Item    : Instruction;
   begin
      loop
         pragma Loop_Invariant (PC in 0 .. Code_Length (Program, P) - 1);
         pragma Loop_Invariant (Current <= 255);
         pragma Loop_Variant (Decreases => PC);
         Result := Local_Text (Program, Names, P, Current + 1, PC);
         exit when Result.Kind /= No_Name;
         PC := Find_Set_Register (Program, P, PC, Current);
         exit when PC < 0;
         Item := Instruction_At (Program, P, PC);
         case Item.Operation is
            when Move =>
               exit when Natural (Item.B) >= Natural (Item.A);
               Current := Natural (Item.B);
            when Get_Upvalue =>
               Result :=
                 Named (Upvalue_Name, Upvalue_Text (Program, Names, P, Natural (Item.B)));
               exit;
            when Load_Constant =>
               Result := Constant_Text (Program, Names, P, Natural (Item.Wide));
               if Result.Kind = No_Name then
                  Result := No_Found_Name;
               end if;
               exit;
            when Load_Constant_Extra =>
               if PC + 1 < Code_Length (Program, P) then
                  Result :=
                    Constant_Text
                      (Program, Names, P, Natural (Instruction_At (Program, P, PC + 1).Wide));
                  if Result.Kind = No_Name then
                     Result := No_Found_Name;
                  end if;
               end if;
               exit;
            when others =>
               exit;
         end case;
      end loop;
   end Basic_Name;

   --  The name Basic_Name finds, without the instruction it found it at.
   function Basic_Name_At
     (Program  : Chunk;
      Names    : Pyro.Symbols.Symbol_Table;
      P        : Prototype_Index;
      PC       : Natural;
      Register : Natural) return Found_Name
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names)
       and then PC < Code_Length (Program, P)
       and then Register <= 255
   is
      At_PC  : Integer := PC;
      Result : Found_Name;
   begin
      Basic_Name (Program, Names, P, At_PC, Register, Result);
      pragma Unreferenced (At_PC);
      return Result;
   end Basic_Name_At;

   --  [puc ldebug.c:isEnv] Global when table register or upvalue Table, of instruction PC,
   --  is _ENV; field otherwise.
   function Table_Kind
     (Program  : Chunk;
      Names    : Pyro.Symbols.Symbol_Table;
      P        : Prototype_Index;
      PC       : Natural;
      Table    : Natural;
      Upvalue  : Boolean) return Name_Kind
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names)
       and then PC < Code_Length (Program, P)
       and then Table <= 255
   is
   begin
      if Upvalue then
         return (if Upvalue_Text (Program, Names, P, Table) = "_ENV" then Global_Name
                 else Field_Name);
      end if;
      declare
         Name : constant Found_Name := Basic_Name_At (Program, Names, P, PC, Table);
      begin
         return (if Name.Kind /= No_Name and then Name.Text (1 .. Name.Length) = "_ENV"
                 then Global_Name else Field_Name);
      end;
   end Table_Kind;

   --  [puc ldebug.c:rname] Register Register as a key's name: a constant's text, else "?".
   function Key_Name
     (Program  : Chunk;
      Names    : Pyro.Symbols.Symbol_Table;
      P        : Prototype_Index;
      PC       : Natural;
      Register : Natural) return Found_Name
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names)
       and then PC < Code_Length (Program, P)
       and then Register <= 255
   is
      Name : constant Found_Name := Basic_Name_At (Program, Names, P, PC, Register);
   begin
      return (if Name.Kind = Constant_Name then Name else Named (No_Name, "?"));
   end Key_Name;

   --  [puc ldebug.c:getobjname] A name for register Register at instruction Last of
   --  prototype P, through table accesses too.
   function Object_Name
     (Program  : Chunk;
      Names    : Pyro.Symbols.Symbol_Table;
      P        : Prototype_Index;
      Last     : Natural;
      Register : Natural) return Found_Name
   with
     Global => null,
     Pre    =>
       Is_Well_Formed (Program)
       and then P in 1 .. Prototype_Count (Program)
       and then Pyro.Symbols.Is_Valid (Names)
       and then Last < Code_Length (Program, P)
       and then Register <= 255
   is
      PC     : Integer := Last;
      Result : Found_Name;
      Item   : Instruction;
      Key    : Found_Name;
   begin
      Basic_Name (Program, Names, P, PC, Register, Result);
      if Result.Kind /= No_Name or else PC < 0 then
         return Result;
      end if;
      Item := Instruction_At (Program, P, PC);
      case Item.Operation is
         when Get_Table_Upvalue =>
            Key := Constant_Text (Program, Names, P, Natural (Item.C));
            Key.Kind := Table_Kind (Program, Names, P, PC, Natural (Item.B), Upvalue => True);
            return Key;
         when Get_Table =>
            Key := Key_Name (Program, Names, P, PC, Natural (Item.C));
            Key.Kind := Table_Kind (Program, Names, P, PC, Natural (Item.B), Upvalue => False);
            return Key;
         when Get_Integer =>
            return Named (Field_Name, "integer index");
         when Get_Field =>
            Key := Constant_Text (Program, Names, P, Natural (Item.C));
            Key.Kind := Table_Kind (Program, Names, P, PC, Natural (Item.B), Upvalue => False);
            return Key;
         when Self =>
            Key :=
              (if Item.K then Constant_Text (Program, Names, P, Natural (Item.C))
               else Key_Name (Program, Names, P, PC, Natural (Item.C)));
            Key.Kind := Method_Name;
            return Key;
         when others =>
            return No_Found_Name;
      end case;
   end Object_Name;

   --  The running frame's prototype and instruction, when the top frame is a Lua frame.
   function Lua_Top (M : Machine) return Boolean
   is (M.Depth >= 1 and then M.Frames (M.Depth).Kind = Lua_Frame)
   with Pre => Core_Valid (M);

   function Variable_Info (M : Machine; Source : Operand) return String is
      F : Frame;
   begin
      if not Lua_Top (M) or else Source.Kind = Other_Operand then
         return "";
      end if;
      Lemma_Frame (M, M.Depth);
      F := M.Frames (M.Depth);
      if Source.Kind = Upvalue_Operand then
         return Formatted
                  (Named (Upvalue_Name,
                          Upvalue_Text (M.Program.all, M.Names.all, F.Prototype, Source.Number)));
      elsif Source.Number > 255 then
         return "";
      end if;
      return Formatted
               (Object_Name (M.Program.all, M.Names.all, F.Prototype, F.PC, Source.Number));
   end Variable_Info;

   --  [puc ldebug.c:funcnamefromcode] A name for the function frame Index calls: through the
   --  CALL, TAILCALL or TFORCALL that calls it, or a metamethod's event. The frame is past
   --  that instruction when At_Call.
   function Call_Name (M : Machine; Index : Positive; At_Call : Boolean) return Found_Name
   with Global => null, Pre => Core_Valid (M) and then Index <= M.Depth
   is
      F    : Frame;
      PC   : Natural;
      Item : Instruction;
   begin
      Lemma_Frame (M, Index);
      F := M.Frames (Index);
      if F.Kind /= Lua_Frame then
         return No_Found_Name;
      end if;
      --  A frame that runs its instruction again after a call (Rerun) is still at it.
      if At_Call and then F.Action /= Rerun then
         if F.PC = 0 then
            return No_Found_Name;
         end if;
         PC := F.PC - 1;
      else
         PC := F.PC;
      end if;
      Item := Instruction_At (M.Program.all, F.Prototype, PC);
      case Item.Operation is
         when Call | Tail_Call =>
            return Object_Name (M.Program.all, M.Names.all, F.Prototype, PC, Natural (Item.A));
         when Generic_For_Call =>
            return Named (Iterator_Name, "for iterator");
         when Self | Get_Table_Upvalue .. Get_Field =>
            return Named (Metamethod_Name, "index");
         when Set_Table_Upvalue .. Set_Field =>
            return Named (Metamethod_Name, "newindex");
         when Metamethod_Binary .. Metamethod_Binary_Constant =>
            if Natural (Item.C) in Natural (First_Binary_Event) .. Natural (Last_Binary_Event)
            then
               declare
                  Name : constant String :=
                    Event_Name
                      (Event'Val (Event'Pos (Add_Event) + Natural (Item.C)
                                  - Natural (First_Binary_Event)));
               begin
                  return Named (Metamethod_Name, Name (Name'First + 2 .. Name'Last));
               end;
            end if;
            return No_Found_Name;
         when Negate =>
            return Named (Metamethod_Name, "unm");
         when Bitwise_Not =>
            return Named (Metamethod_Name, "bnot");
         when Length =>
            return Named (Metamethod_Name, "len");
         when Concatenate =>
            return Named (Metamethod_Name, "concat");
         when Equal =>
            return Named (Metamethod_Name, "eq");
         when Less_Than | Less_Than_Integer | Greater_Than_Integer =>
            return Named (Metamethod_Name, "lt");
         when Less_Equal | Less_Equal_Integer | Greater_Equal_Integer =>
            return Named (Metamethod_Name, "le");
         when Close | Return_Values =>
            return Named (Metamethod_Name, "close");
         when others =>
            return No_Found_Name;
      end case;
   end Call_Name;

   --  The name of the function the running frame calls, as error messages give it.
   function Call_Info (M : Machine; At_Call : Boolean) return String
   is (if Lua_Top (M) then Formatted (Call_Name (M, M.Depth, At_Call)) else "")
   with Global => null, Pre => Core_Valid (M), Post => Call_Info'Result'Length <= 2 ** 14;

   ----------------------------------------------------------------------------------------
   --  Errors
   ----------------------------------------------------------------------------------------

   --  A string value holding Text, or the "not enough memory" message when Budget cannot pay.
   procedure Make_String
     (Heap     : in out Pyro.Heap.Heap;
      Registry : Root_Array;
      Budget   : in out Memory_Budget;
      Text     : String;
      Result   : out Value)
   with
     Global => null,
     Pre    =>
       Pyro.Heap.Is_Valid (Heap)
       and then Registry'First = 1
       and then Registry'Last = Registry_Size
       and then Values_Live (Pyro.Heap.Kinds (Heap), Registry),
     Post   =>
       Pyro.Heap.Is_Valid (Heap)
       and then Pyro.Heap.Keeps_Objects (Pyro.Heap.Kinds (Heap)'Old, Pyro.Heap.Kinds (Heap))
       and then Limit (Budget) = Limit (Budget)'Old
       and then Is_Canonical (Result)
       and then Pyro.Heap.Live_In (Pyro.Heap.Kinds (Heap), Result)
   is
      Handle : Object_Handle;
   begin
      Lemma_Value (Pyro.Heap.Kinds (Heap), Registry, Memory_Place);
      Result := Registry (Memory_Place);
      if Text'Length > Pyro.Heap.Maximum_String_Length then
         return;
      end if;
      Pyro.Heap.New_String (Heap, Budget, To_Bytes (Text), Handle);
      if Handle /= No_Object then
         Result := Object_Value_Of (Handle);
         Lemma_Heap_Live (Heap, Result);
      end if;
   end Make_String;

   --  How setting up a call went.
   type Call_Outcome is (Called, Stack_Overflow, Bad_Closure, Not_Callable);

   --  [puc ldo.c:luaD_precall] Sets up a call of the function at stack place Func with
   --  Arguments arguments after it, its caller wanting Results results (-1: all): a Lua
   --  function's frame runs next, a host function waits. Outcome says why it could not; the
   --  machine then still has its frames.
   procedure Prepare_Call
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Func      : Positive;
      Arguments : Natural;
      Results   : Integer;
      Outcome   : out Call_Outcome)
   with
     Global => null,
     Pre    =>
       Core_Valid (M)
       and then M.State = Ready
       and then Func <= M.Stack'Last
       and then Arguments <= Stack_Limit
       and then Results in -1 .. 255
       and then (M.Depth = 0 or else M.Frames (M.Depth).Func < Func),
     Post   =>
       Core_Valid (M)
       and then Limit (Budget) = Limit (Budget)'Old
       and then M.Closing_Count = M.Closing_Count'Old
       and then (if Outcome = Called then Is_Valid (M) and then Is_Loaded (M)
                 else M.State = Ready and then M.Depth = M.Depth'Old);

   --  [puc lfunc.c:luaF_newtbcupval] Adds stack place Place to the to-be-closed variables.
   --  Success is False when Budget cannot pay for a longer list.
   procedure Push_Closing
     (Closing : in out Place_Array_Access;
      Count   : in out Natural;
      Budget  : in out Memory_Budget;
      Place   : Natural;
      Success : out Boolean)
   with
     Global => null,
     Pre    =>
       Closing /= null
       and then Closing'First = 1
       and then Closing'Last in Initial_Open .. Maximum_Open
       and then Count <= Closing'Last,
     Post   =>
       Closing /= null
       and then Closing'First = 1
       and then Closing'Last in Initial_Open .. Maximum_Open
       and then Count <= Closing'Last
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Larger  : Place_Array_Access;
      Charged : Boolean;
   begin
      Success := False;
      if Count = Closing'Last then
         if Closing'Length > Stack_Limit then
            return;
         end if;
         Charge (Budget, Base_Bytes * Byte_Count (Closing'Length), Charged);
         if not Charged then
            return;
         end if;
         Larger := new Place_Array'(1 .. 2 * Closing'Length => 0);
         Larger (1 .. Closing'Length) := Closing.all;
         Free_Places (Closing);
         Closing := Larger;
      end if;
      Count := Count + 1;
      Closing (Count) := Place;
      Success := True;
   end Push_Closing;

   --  [puc ldo.c:luaD_throw, luaD_closeprotected] Unwinds the frames after an error, the
   --  error value in the registry, down to a host function that asked for a protected call
   --  (or to the bottom). The to-be-closed variables above that point are closed first, each
   --  __close called with the error; it runs as a call of that host function, still
   --  protected, so that an error in it replaces the error, and the unwinding goes on when it
   --  returns. Then the host function waits with the error; with none, the machine is done
   --  and failed.
   procedure Unwind (M : in out Machine; Budget : in out Memory_Budget)
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
      Level   : Positive;
      Place   : Natural;
      Item    : Value;
      Handler : Value;
      F       : Frame;
      Last    : Stack_Size;
      Success : Boolean;
      Outcome : Call_Outcome := Stack_Overflow;
      Error   : Value;
      Before  : Pyro.Kind_Sequences.Sequence with Ghost;
   begin
      M.State := Ready;
      while M.Depth > 0
        and then not (M.Frames (M.Depth).Kind = Host_Frame and then M.Frames (M.Depth).Protect)
      loop
         pragma Loop_Invariant (Core_Valid (M) and then M.State = Ready);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Variant (Decreases => M.Depth);
         Lemma_Frames_Pop (M.Frames.all, M.Depth, M.Stack'Last, M.Program.all);
         M.Depth := M.Depth - 1;
      end loop;
      if M.Depth > 0 then
         Lemma_Frame (M, M.Depth);
         Level := M.Frames (M.Depth).Top;
      else
         Level := 1;
      end if;
      Close_Upvalues (M.Heap, M.Open.all, M.Open_Count, M.Stack.all, Level);
      while M.Closing_Count > 0 and then M.Closing (M.Closing_Count) >= Level loop
         pragma Loop_Invariant (Core_Valid (M) and then M.State = Ready);
         pragma Loop_Invariant (M.Depth = M.Depth'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Variant (Decreases => M.Closing_Count);
         Place := M.Closing (M.Closing_Count);
         M.Closing_Count := M.Closing_Count - 1;
         if Place in M.Stack'Range then
            Lemma_Value (Objects (M), M.Stack.all, Place);
            Item := M.Stack (Place);
            if Item.Kind /= Nil_Value and then Item /= Boolean_Value_Of (False) then
               --  [puc lfunc.c:prepcallclosemth] __close (Item, error), called above Place: the
               --  variables left to close are below it, and keep their values.
               Handler := Field_Of (M, Item, Close_Event);
               Lemma_Value (Objects (M), M.Registry.all, Error_Place);
               Error := M.Registry (Error_Place);
               Last := M.Stack'Last;
               Reserve (M.Stack, M.Heap, Budget, Place + 3 + Extra_Stack, Success);
               Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
               if Success then
                  Store_Value (M.Stack.all, M.Heap, Place + 1, Handler);
                  Store_Value (M.Stack.all, M.Heap, Place + 2, Item);
                  Store_Value (M.Stack.all, M.Heap, Place + 3, Error);
                  if M.Depth > 0 then
                     F := M.Frames (M.Depth);
                     Lemma_Frame (M, M.Depth);
                     Set_Top_Frame
                       (M.Frames.all, M.Depth, (F with delta Closing => True), M.Stack'Last,
                        M.Program.all);
                  else
                     M.Unwinding := True;
                  end if;
                  if M.Depth = 0 or else M.Frames (M.Depth).Func < Place + 1 then
                     Prepare_Call (M, Budget, Place + 1, 2, 0, Outcome);
                     if Outcome = Called then
                        return;
                     end if;
                  end if;
               end if;
               --  The call could not start: its error replaces the error.
               Before := Objects (M);
               Make_String
                 (M.Heap, M.Registry.all, Budget,
                  (if not Success or else Outcome = Stack_Overflow then "stack overflow"
                   elsif Outcome = Bad_Closure then "internal error: bad closure"
                   else "attempt to call a " & Type_Name (M, Handler) & " value"),
                  Error);
               Lemma_Roots_Grow (Before, M);
               Store_Value (M.Registry.all, M.Heap, Error_Place, Error);
            end if;
         end if;
      end loop;
      M.Unwinding := False;
      if M.Depth > 0 and then M.Frames (M.Depth).Kind = Host_Frame then
         F := M.Frames (M.Depth);
         Lemma_Frame (M, M.Depth);
         if Level in M.Stack'Range then
            Lemma_Value (Objects (M), M.Registry.all, Error_Place);
            Store_Value (M.Stack.all, M.Heap, Level, M.Registry (Error_Place));
            M.Results_At := Level;
            M.Result_Size := 1;
         else
            M.Results_At := 1;
            M.Result_Size := 0;
         end if;
         M.Succeeded := False;
         Set_Top_Frame
           (M.Frames.all, M.Depth, (F with delta Protect => False, Closing => False),
            M.Stack'Last, M.Program.all);
         M.State := Waiting;
         return;
      end if;
      M.Failed := True;
      M.State := Done;
   end Unwind;

   --  Raises Error.
   procedure Throw (M : in out Machine; Budget : in out Memory_Budget; Error : Value)
   with
     Global => null,
     Pre    =>
       Core_Valid (M)
       and then Is_Canonical (Error)
       and then Pyro.Heap.Live_In (Objects (M), Error),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
   begin
      Store_Value (M.Registry.all, M.Heap, Error_Place, Error);
      Unwind (M, Budget);
   end Throw;

   --  Raises the string Text.
   procedure Throw_Message (M : in out Machine; Budget : in out Memory_Budget; Text : String)
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
      Error  : Value;
      Before : constant Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Make_String (M.Heap, M.Registry.all, Budget, Text, Error);
      Lemma_Roots_Grow (Before, M);
      Throw (M, Budget, Error);
   end Throw_Message;

   procedure Raise_Runtime_Error
     (M : in out Machine; Budget : in out Memory_Budget; Text : String) is
   begin
      Throw_Message (M, Budget, Position_Of (M, 1) & Text);
   end Raise_Runtime_Error;

   procedure Raise_Memory_Error (M : in out Machine; Budget : in out Memory_Budget) is
      Error : constant Value := M.Registry (Memory_Place);
   begin
      if M.State = Ready and then not M.Retried then
         --  The running instruction, which has not moved on, runs again after a collection.
         M.Retry := True;
         return;
      end if;
      M.Pressure := True;
      Lemma_Value (Objects (M), M.Registry.all, Memory_Place);
      Throw (M, Budget, Error);
   end Raise_Memory_Error;

   function Error_Text (M : Machine) return String is
      Error : constant Value := M.Registry (Error_Place);
   begin
      Lemma_Value (Objects (M), M.Registry.all, Error_Place);
      if Is_String (M, Error) then
         return String_Text (M, Error);
      elsif Error.Kind in Integer_Value | Float_Value then
         return Basic_Image (Error);
      end if;
      return "(error object is a " & Type_Name (M, Error) & " value)";
   end Error_Text;

   ----------------------------------------------------------------------------------------
   --  Calls and returns
   ----------------------------------------------------------------------------------------

   --  [puc lfunc.c:luaF_close] Calls __close (value, nil) for the latest to-be-closed
   --  variable at stack place Level or above that is not nil or false, the running frame then
   --  running its instruction again (Rerun): one variable per pass. Called is False when
   --  there is none left; the running frame is then as it was. Calls start at Base or above.
   procedure Close_Pending
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Level  : Positive;
      Base   : Natural;
      Called : out Boolean)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Running (M),
     Post   =>
       Is_Valid (M)
       and then Is_Loaded (M)
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if not Called
                 then Running (M)
                      and then View (M) = View (M)'Old
                      and then M.Depth = M.Depth'Old
                      and then M.Frames (M.Depth) = M.Frames (M.Depth)'Old
                      and then M.Stack'Last = M.Stack'Last'Old)
   is
      Place   : Natural;
      Item    : Value;
      Handler : Value;
      Last    : constant Stack_Size := M.Stack'Last;
   begin
      Called := False;
      while M.Closing_Count > 0 and then M.Closing (M.Closing_Count) >= Level loop
         pragma Loop_Invariant (Is_Valid (M) and then Running (M));
         pragma Loop_Invariant (M.Depth = M.Depth'Loop_Entry);
         pragma Loop_Invariant (M.Frames (M.Depth) = M.Frames (M.Depth)'Loop_Entry);
         pragma Loop_Invariant (M.Stack'Last = Last);
         pragma Loop_Variant (Decreases => M.Closing_Count);
         Place := M.Closing (M.Closing_Count);
         M.Closing_Count := M.Closing_Count - 1;
         if Place in M.Stack'Range then
            Lemma_Value (Objects (M), M.Stack.all, Place);
            Item := M.Stack (Place);
            if Item.Kind /= Nil_Value and then Item /= Boolean_Value_Of (False) then
               Handler := Field_Of (M, Item, Close_Event);
               Lemma_Live_Heap (M.Heap, Handler);
               Lemma_Live_Heap (M.Heap, Item);
               Call_Metamethod
                 (M, Budget, Handler, [Item, Nil], Rerun, 0, False, Base => Base);
               Called := True;
               return;
            end if;
         end if;
      end loop;
   end Close_Pending;

   --  [puc ldo.c:luaD_poscall] The top frame returns Count results, which start at First:
   --  they go to its origin, as many as its caller wanted (nil for the missing ones).
   procedure Finish_Return
     (M : in out Machine; Budget : in out Memory_Budget; First : Positive; Count : Natural)
   with
     Global => null,
     Pre    =>
       Core_Valid (M)
       and then M.Depth >= 1
       and then First >= M.Frames (M.Depth).Origin
       and then Count <= M.Stack'Last + 1 - First,
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
      F      : constant Frame := M.Frames (M.Depth);
      Target : constant Positive := F.Origin;
      Wanted : Natural;
      Moved  : Natural;
      Caller : Frame;
      Result : Value;
   begin
      Lemma_Frame (M, M.Depth);
      Wanted := (if F.Results < 0 then Count else F.Results);
      Moved := Natural'Min (Count, Wanted);
      Copy (M.Stack.all, M.Heap, First, Target, Moved);
      Fill_Nil (M.Stack.all, M.Heap, Target + Moved, Wanted - Moved);
      M.Top := Target + Wanted;
      Lemma_Frames_Pop (M.Frames.all, M.Depth, M.Stack'Last, M.Program.all);
      M.Depth := M.Depth - 1;
      if M.Depth = 0 and then M.Unwinding then
         --  A __close an uncaught error called returned: the unwinding goes on.
         Unwind (M, Budget);
      elsif M.Depth = 0 then
         M.State := Done;
      elsif M.Frames (M.Depth).Kind = Host_Frame and then M.Frames (M.Depth).Closing then
         --  A __close the host function's protected call called returned: likewise.
         Unwind (M, Budget);
      elsif M.Frames (M.Depth).Kind = Host_Frame then
         --  The call the host function asked for returned: it is no longer protected.
         Caller := M.Frames (M.Depth);
         Lemma_Frame (M, M.Depth);
         Set_Top_Frame
           (M.Frames.all, M.Depth, (Caller with delta Protect => False), M.Stack'Last,
            M.Program.all);
         M.Results_At := Target;
         M.Result_Size := Wanted;
         M.Succeeded := True;
         M.State := Waiting;
      else
         M.State := Ready;
         Caller := M.Frames (M.Depth);
         if Caller.Action /= No_Action then
            --  [puc lvm.c:luaV_finishOp] The metamethod the caller called returned.
            Lemma_Frame (M, M.Depth);
            Result := Nil;
            if Wanted >= 1 then
               Lemma_Value (Objects (M), M.Stack.all, Target);
               Result := M.Stack (Target);
            end if;
            if Caller.Action = Store_Result then
               Store_Value (M.Stack.all, M.Heap, Caller.Func + 1 + Caller.Target, Result);
               Set_Top_Frame
                 (M.Frames.all, M.Depth, (Caller with delta Action => No_Action), M.Stack'Last,
                  M.Program.all);
            elsif Caller.Action = Rerun then
               --  A __close returned: the frame's CLOSE or RETURN goes on.
               Set_Top_Frame
                 (M.Frames.all, M.Depth, (Caller with delta Action => No_Action), M.Stack'Last,
                  M.Program.all);
            elsif Caller.Action = Concat_Result then
               --  [puc lvm.c:luaV_finishOp] The CONCAT goes on with the values left.
               Store_Value (M.Stack.all, M.Heap, Caller.Func + 1 + Caller.Target, Result);
               Set_Top_Frame
                 (M.Frames.all, M.Depth,
                  (Caller with delta Action => No_Action, PC => Caller.PC - 1), M.Stack'Last,
                  M.Program.all);
            else
               Set_Top_Frame
                 (M.Frames.all, M.Depth,
                  (Caller with delta
                     Action => No_Action,
                     PC     =>
                       (if (Result.Kind = Nil_Value or else Result = Boolean_Value_Of (False))
                           = Caller.Expected
                        then Caller.PC + 1 else Caller.PC)),
                  M.Stack'Last, M.Program.all);
            end if;
         end if;
      end if;
   end Finish_Return;

   --  Callee is a Lua function (a closure).
   function Is_Lua_Function (M : Machine; Callee : Value) return Boolean
   is (Callee.Kind = Object_Value
       and then Pyro.Heap.Kind_Of (M.Heap, Callee.Object) = Closure_Object);

   procedure Prepare_Call
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Func      : Positive;
      Arguments : Natural;
      Results   : Integer;
      Outcome   : out Call_Outcome)
   is
      Callee     : Value := M.Stack (Func);
      Count      : Natural := Arguments;
      Last       : Stack_Size := M.Stack'Last;
      Handler    : Value;
      P          : Prototype_Index;
      Parameters : Natural;
      Size       : Natural;
      Success    : Boolean;
   begin
      Outcome := Called;
      Lemma_Value (Objects (M), M.Stack.all, Func);
      if not Is_Function (M, Callee) then
         --  [puc ldo.c:luaD_tryfuncTM] Its __call metamethod, with Callee as first argument.
         Handler := Field_Of (M, Callee, Call_Event);
         if Is_Function (M, Handler) then
            Reserve (M.Stack, M.Heap, Budget, Func + Arguments + 1 + Extra_Stack, Success);
            Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
            if not Success then
               Outcome := Stack_Overflow;
               return;
            end if;
            Last := M.Stack'Last;
            Copy (M.Stack.all, M.Heap, Func, Func + 1, Arguments + 1);
            Store_Value (M.Stack.all, M.Heap, Func, Handler);
            Callee := Handler;
            Count := Arguments + 1;
         end if;
      end if;
      if Callee.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, Callee.Object) = Closure_Object
      then
         P := Prototype_Index (Natural'Min (Pyro.Heap.Tag_Of (M.Heap, Callee.Object),
                                            Natural (Prototype_Index'Last)));
         if P not in 1 .. Prototype_Count (M.Program.all) then
            Outcome := Bad_Closure;
            return;
         end if;
         Lemma_Valid_Prototype (M.Program.all, P);
         Parameters := Natural (Header (M.Program.all, P).Parameter_Count);
         Size := Natural (Header (M.Program.all, P).Stack_Size);
         Reserve
           (M.Stack, M.Heap, Budget,
            Func + Natural'Max (Size, Natural'Max (Count, Results)) + Extra_Stack, Success);
         Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
         if not Success then
            Outcome := Stack_Overflow;
            return;
         end if;
         if Count < Parameters then
            Fill_Nil (M.Stack.all, M.Heap, Func + 1 + Count, Parameters - Count);
         end if;
         M.Top := Func + 1 + Natural'Max (Count, Parameters);
         Push_Frame
           (M.Frames, M.Depth, Budget,
            (Kind      => Lua_Frame,
             Origin    => Func,
             Func      => Func,
             Top       => Func + 1 + Size,
             Prototype => P,
             PC        => 0,
             Results   => Results,
             Extra     => 0,
             Host      => 1,
             Context   => 0,
             Protect   => False,
             Action    => No_Action,
             Target    => 0,
             Expected  => False,
             Resume    => 0,
             Closing   => False,
             Saved     => -1),
            M.Stack'Last, M.Program.all, Success);
         if not Success then
            Outcome := Stack_Overflow;
         end if;
      elsif Callee.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, Callee.Object) = Host_Function_Object
      then
         Reserve
           (M.Stack, M.Heap, Budget,
            Func + Natural'Max (Count, Results) + Extra_Stack, Success);
         Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
         if not Success then
            Outcome := Stack_Overflow;
            return;
         end if;
         Push_Frame
           (M.Frames, M.Depth, Budget,
            (Kind      => Host_Frame,
             Origin    => Func,
             Func      => Func,
             Top       => Func + 1 + Count,
             Prototype => 0,
             PC        => 0,
             Results   => Results,
             Extra     => 0,
             Host      => Host_Id (Natural'Max (1, Natural'Min
                                    (Pyro.Heap.Tag_Of (M.Heap, Callee.Object),
                                     Natural (Host_Id'Last)))),
             Context   => 0,
             Protect   => False,
             Action    => No_Action,
             Target    => 0,
             Expected  => False,
             Resume    => 0,
             Closing   => False,
             Saved     => -1),
            M.Stack'Last, M.Program.all, Success);
         if not Success then
            Outcome := Stack_Overflow;
            return;
         end if;
         M.State := Waiting;
      else
         Outcome := Not_Callable;
      end if;
   end Prepare_Call;

   --  [puc ldo.c:luaD_precall] Calls the function at stack place Func with Arguments
   --  arguments after it, its caller wanting Results results (-1: all).
   procedure Call_At
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Func      : Positive;
      Arguments : Natural;
      Results   : Integer)
   with
     Global => null,
     Pre    =>
       Core_Valid (M)
       and then M.State = Ready
       and then Func <= M.Stack'Last
       and then Arguments <= Stack_Limit
       and then Results in -1 .. 255
       and then (M.Depth = 0 or else M.Frames (M.Depth).Func < Func),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
      Callee  : constant Value := M.Stack (Func);
      Outcome : Call_Outcome;
   begin
      Lemma_Value (Objects (M), M.Stack.all, Func);
      Prepare_Call (M, Budget, Func, Arguments, Results, Outcome);
      case Outcome is
         when Called =>
            null;
         when Stack_Overflow =>
            Throw_Message (M, Budget, Position_Of (M, 1, At_Call => True) & "stack overflow");
         when Bad_Closure =>
            Throw_Message
              (M, Budget, Position_Of (M, 1, At_Call => True) & "internal error: bad closure");
         when Not_Callable =>
            Throw_Message
              (M, Budget,
               Position_Of (M, 1, At_Call => True) & "attempt to call a " & Type_Name (M, Callee)
               & " value" & Call_Info (M, At_Call => True));
      end case;
   end Call_At;

   --  The number of arguments of a call of the function at stack place Place: Arguments, or
   --  those up to the top when it is -1.
   function Argument_Number (M : Machine; Place : Positive; Arguments : Integer) return Natural
   is (if Arguments >= 0 then Arguments elsif M.Top > Place then M.Top - Place - 1 else 0)
   with Pre => Arguments >= -1;

   procedure Call_Register
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Func      : Natural;
      Arguments : Integer;
      Results   : Integer)
   is
      Place : Positive;
   begin
      Advance (M, 0);
      Place := Register_Place (M, Func);
      Call_At (M, Budget, Place, Argument_Number (M, Place, Arguments), Results);
   end Call_Register;

   procedure Tail_Call_Register
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Func      : Natural;
      Arguments : Integer)
   is
      F       : constant Frame := M.Frames (M.Depth);
      Place   : constant Positive := Register_Place (M, Func);
      Count   : Natural := Argument_Number (M, Place, Arguments);
      Last    : Stack_Size := M.Stack'Last;
      Callee  : Value := M.Stack (Place);
      Handler : Value;
      Success : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Value (Objects (M), M.Stack.all, Place);
      if not Is_Function (M, Callee) then
         --  [puc ldo.c:luaD_pretailcall] Its __call metamethod, with Callee as first argument.
         Handler := Field_Of (M, Callee, Call_Event);
         if Is_Lua_Function (M, Handler) then
            Reserve (M.Stack, M.Heap, Budget, Place + Count + 1 + Extra_Stack, Success);
            Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
            if not Success then
               Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
               return;
            end if;
            Last := M.Stack'Last;
            Copy (M.Stack.all, M.Heap, Place, Place + 1, Count + 1);
            Store_Value (M.Stack.all, M.Heap, Place, Handler);
            Callee := Handler;
            Count := Count + 1;
         end if;
      end if;
      if not Is_Lua_Function (M, Callee) then
         --  [puc ldo.c:luaD_pretailcall] A host function, called directly or through __call,
         --  runs above the frame, as an ordinary call; the RETURN that follows every TAILCALL
         --  then returns its results. Anything else fails as that call.
         Call_Register (M, Budget, Func, Arguments, -1);
         return;
      end if;
      Reserve (M.Stack, M.Heap, Budget, Place + Count + Extra_Stack, Success);
      Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
      if not Success then
         Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
         return;
      end if;
      Close_Upvalues (M.Heap, M.Open.all, M.Open_Count, M.Stack.all, F.Func + 1);
      Copy (M.Stack.all, M.Heap, Place, F.Origin, Count + 1);
      Lemma_Frames_Pop (M.Frames.all, M.Depth, M.Stack'Last, M.Program.all);
      M.Depth := M.Depth - 1;
      Call_At (M, Budget, F.Origin, Count, F.Results);
   end Tail_Call_Register;

   procedure Return_Registers
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      First  : Natural;
      Count  : Integer;
      Close  : Boolean)
   is
      F      : constant Frame := M.Frames (M.Depth);
      Place  : Positive;
      Size   : Natural;
      Called : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Place := F.Func + 1 + First;
      Size :=
        (if F.Saved >= 0 then Natural'Min (F.Saved, M.Stack'Last + 1 - Place)
         elsif Count >= 0 then Natural'Min (Count, M.Stack'Last + 1 - Place)
         elsif M.Top > Place then M.Top - Place
         else 0);
      if Close then
         Close_Upvalues (M.Heap, M.Open.all, M.Open_Count, M.Stack.all, F.Func + 1);
         if M.Closing_Count > 0 and then M.Closing (M.Closing_Count) >= F.Func + 1 then
            --  [puc lvm.c:OP_RETURN] The results stay where they are while the to-be-closed
            --  variables close, above them; the frame keeps their number.
            Set_Top_Frame
              (M.Frames.all, M.Depth, (F with delta Saved => Size), M.Stack'Last,
               M.Program.all);
            Close_Pending (M, Budget, F.Func + 1, Place + Size, Called);
            if Called then
               return;
            end if;
         end if;
      end if;
      Finish_Return (M, Budget, Place, Size);
   end Return_Registers;

   procedure Prepare_Varargs
     (M : in out Machine; Budget : in out Memory_Budget; Fixed : Natural)
   is
      F        : constant Frame := M.Frames (M.Depth);
      Last     : constant Stack_Size := M.Stack'Last;
      Size     : Natural;
      Moved    : Natural;
      Actual   : Natural;
      Extra    : Natural;
      New_Func : Positive;
      Success  : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Size := F.Top - F.Func - 1;
      Moved := Natural'Min (Fixed, Size);
      Actual := (if M.Top > F.Func then M.Top - F.Func - 1 else 0);
      Extra := (if Actual > Moved then Actual - Moved else 0);
      New_Func := F.Func + Actual + 1;
      Reserve (M.Stack, M.Heap, Budget, New_Func + 1 + Size + Extra_Stack, Success);
      Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
      if not Success then
         Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
         return;
      end if;
      Copy (M.Stack.all, M.Heap, F.Func, New_Func, Moved + 1);
      Fill_Nil (M.Stack.all, M.Heap, F.Func + 1, Moved);
      Set_Top_Frame
        (M.Frames.all, M.Depth,
         (F with delta Func => New_Func, Top => New_Func + 1 + Size, Extra => Extra,
                       PC => F.PC + 1),
         M.Stack'Last, M.Program.all);
      M.Top := New_Func + 1 + Moved;
   end Prepare_Varargs;

   procedure Copy_Varargs
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Target : Natural;
      Wanted : Integer)
   is
      F       : constant Frame := M.Frames (M.Depth);
      Last    : constant Stack_Size := M.Stack'Last;
      Place   : constant Positive := Register_Place (M, Target);
      Count   : constant Natural := (if Wanted >= 0 then Wanted else F.Extra);
      Moved   : constant Natural := Natural'Min (Count, F.Extra);
      Success : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Reserve (M.Stack, M.Heap, Budget, Place + Count + Extra_Stack, Success);
      Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
      if not Success then
         Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
         return;
      end if;
      Copy (M.Stack.all, M.Heap, F.Func - F.Extra, Place, Moved);
      Fill_Nil (M.Stack.all, M.Heap, Place + Moved, Count - Moved);
      if Wanted < 0 then
         M.Top := Place + Count;
      end if;
      Set_Top_Frame
        (M.Frames.all, M.Depth, (F with delta PC => F.PC + 1), M.Stack'Last, M.Program.all);
   end Copy_Varargs;

   procedure Make_Closure
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Number : Natural;
      Target : Natural)
   is
      F      : constant Frame := M.Frames (M.Depth);
      Place  : constant Positive := Register_Place (M, Target);
      Child  : Prototype_Index;
      Count  : Natural;
      Parent : constant Value := M.Stack (F.Func);
      Handle : Object_Handle;
      Cell   : Value;
      Item   : Upvalue_Description;
      Before : Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Value (Objects (M), M.Stack.all, F.Func);
      Child := Child_At (M.Program.all, F.Prototype, Number);
      if Child = 0 then
         Raise_Runtime_Error (M, Budget, "internal error: bad prototype");
         return;
      end if;
      Count := Natural'Min (Upvalue_Count (M.Program.all, Child), Pyro.Heap.Maximum_References);
      Pyro.Heap.New_Object (M.Heap, Budget, Closure_Object, Natural (Child), Count, Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         Raise_Memory_Error (M, Budget);
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      Store_Value (M.Stack.all, M.Heap, Place, Object_Value_Of (Handle));
      for Index in 0 .. Count - 1 loop
         pragma Loop_Invariant (Is_Valid (M) and then Running (M));
         pragma Loop_Invariant (M.Depth = M.Depth'Loop_Entry and then M.Frames (M.Depth) = F);
         pragma Loop_Invariant (Pyro.Heap.Kind_Of (M.Heap, Handle) = Closure_Object);
         pragma Loop_Invariant (Pyro.Heap.Live_In (Objects (M), Parent));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Item := Upvalue_At (M.Program.all, Child, Index);
         if Item.In_Stack then
            Before := Objects (M);
            Find_Upvalue
              (M.Heap, M.Open, M.Open_Count, Budget, F.Func + 1 + Natural (Item.Index), Cell);
            Lemma_Roots_Open_Grow (Before, M);
            if Cell = Nil then
               Raise_Memory_Error (M, Budget);
               return;
            end if;
         elsif Parent.Kind = Object_Value
           and then Pyro.Heap.Kind_Of (M.Heap, Parent.Object) = Closure_Object
           and then Natural (Item.Index) < Pyro.Heap.Reference_Count (M.Heap, Parent.Object)
         then
            Pyro.Heap.Lemma_Reference_Live (M.Heap, Parent.Object, Natural (Item.Index) + 1);
            Cell := Pyro.Heap.Reference_At (M.Heap, Parent.Object, Natural (Item.Index) + 1);
            Lemma_Heap_Live (M.Heap, Cell);
         else
            Cell := Nil;
         end if;
         if Index < Pyro.Heap.Reference_Count (M.Heap, Handle) then
            Lemma_Live_Heap (M.Heap, Cell);
            Pyro.Heap.Set_Reference (M.Heap, Handle, Index + 1, Cell);
         end if;
      end loop;
      Advance (M, 0);
   end Make_Closure;

   --  Item can be joined by concatenation: a string or a number.
   function Joinable (M : Machine; Item : Value) return Boolean
   is (Is_String (M, Item) or else Item.Kind in Integer_Value | Float_Value);

   --  The text concatenation joins for Item: its bytes, or a number as tostring writes it.
   function Piece (M : Machine; Item : Value) return String
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Canonical (Item) and then Joinable (M, Item),
     Post   =>
       Piece'Result'First = 1 and then Piece'Result'Length <= Pyro.Strings.Maximum_String_Length
   is
   begin
      if Is_String (M, Item) then
         return String_Text (M, Item);
      end if;
      return Basic_Image (Item);
   end Piece;

   --  The length of Piece (M, Item), without reading a string's bytes.
   function Piece_Length (M : Machine; Item : Value) return Natural
   is (if Is_String (M, Item)
       then Natural'Min (Pyro.Heap.String_Length (M.Heap, Item.Object),
                         Pyro.Strings.Maximum_String_Length)
       else Natural'Min (Basic_Image (Item)'Length, Pyro.Strings.Maximum_String_Length))
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Canonical (Item) and then Joinable (M, Item),
     Post   => Piece_Length'Result <= Pyro.Strings.Maximum_String_Length;

   --  A new string joining registers From .. To of the running frame, Length bytes in all.
   --  Handle is No_Object when Budget cannot pay.
   procedure Join
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      From   : Natural;
      To     : Natural;
      Length : Natural;
      Handle : out Object_Handle)
   with
     Global => null,
     Pre    =>
       Is_Valid (M)
       and then Running (M)
       and then From <= To
       and then To < View (M).Registers
       and then Length <= Pyro.Strings.Maximum_String_Length
       and then (for all Place in From .. To => Joinable (M, Register (M, Place))),
     Post   =>
       Is_Valid (M)
       and then Running (M)
       and then View (M) = View (M)'Old
       and then Limit (Budget) = Limit (Budget)'Old
       and then (if Handle /= No_Object then Is_Live (M, Object_Value_Of (Handle)))
   is
      Bytes  : Pyro.Strings.Byte_Array (1 .. Byte_Position'Base (Length)) :=
        [others => ASCII.NUL];
      Filled : Natural := 0;
      Before : constant Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      for Place in From .. To loop
         pragma Loop_Invariant (Filled <= Length);
         declare
            Text : constant String := Piece (M, Register (M, Place));
         begin
            for Index in Text'Range loop
               pragma Loop_Invariant (Filled + Index - 1 <= Length);
               exit when Filled + Index > Length;
               Bytes (Byte_Position (Filled + Index)) := Text (Index);
            end loop;
            Filled := Natural'Min (Length, Filled + Text'Length);
         end;
      end loop;
      Pyro.Heap.New_String (M.Heap, Budget, Bytes, Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle /= No_Object then
         Lemma_Live_Heap (M.Heap, Object_Value_Of (Handle));
      end if;
   end Join;

   procedure Concatenate
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      First  : Natural;
      Count  : Positive)
   is
      F       : constant Frame := M.Frames (M.Depth);
      Total   : Positive := Count;
      Top     : Natural;
      Left    : Value;
      Right   : Value;
      Handler : Value;
      Joined  : Natural;
      Length  : Natural;
      Handle  : Object_Handle;
   begin
      Lemma_Frame (M, M.Depth);
      if F.Resume /= 0 then
         --  The frame runs its CONCAT again after a __concat metamethod: fewer values left.
         if F.Resume <= Count then
            Total := F.Resume;
         end if;
         Set_Top_Frame
           (M.Frames.all, M.Depth, (F with delta Resume => 0), M.Stack'Last, M.Program.all);
      end if;
      while Total > 1 loop
         pragma Loop_Invariant (Is_Valid (M) and then Running (M));
         pragma Loop_Invariant (View (M) = View (M)'Loop_Entry);
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Invariant (Total in 2 .. Count);
         pragma Loop_Variant (Decreases => Total);
         Top := First + Total;
         Left := Register (M, Top - 2);
         Right := Register (M, Top - 1);
         if not (Joinable (M, Left) and then Joinable (M, Right)) then
            --  [puc ltm.c:luaT_tryconcatTM] The first operand's __concat, else the second's.
            Handler := Metafield (M, Left, Concatenate_Event);
            if Handler = Nil then
               Handler := Metafield (M, Right, Concatenate_Event);
            end if;
            if Handler /= Nil then
               Call_Metamethod
                 (M, Budget, Handler, [Left, Right], Concat_Result, Top - 2, False, Total - 1);
            else
               --  [puc ldebug.c:luaG_concaterror]
               Raise_Runtime_Error
                 (M, Budget,
                  "attempt to concatenate a "
                  & Type_Name (M, (if Joinable (M, Left) then Right else Left)) & " value"
                  & Variable_Info
                      (M, Register_Of (if Joinable (M, Left) then Top - 1 else Top - 2)));
            end if;
            return;
         end if;
         --  As many strings and numbers as there are below the top, joined at once.
         Joined := 2;
         Length := Piece_Length (M, Left);
         if Piece_Length (M, Right) > Pyro.Strings.Maximum_String_Length - Length then
            Raise_Runtime_Error (M, Budget, "string length overflow");
            return;
         end if;
         Length := Length + Piece_Length (M, Right);
         while Joined < Total and then Joinable (M, Register (M, Top - Joined - 1)) loop
            pragma Loop_Invariant (Joined in 2 .. Total - 1);
            pragma Loop_Invariant (Length <= Pyro.Strings.Maximum_String_Length);
            pragma Loop_Invariant
              (for all Place in Top - Joined .. Top - 1 => Joinable (M, Register (M, Place)));
            pragma Loop_Variant (Increases => Joined);
            if Piece_Length (M, Register (M, Top - Joined - 1))
              > Pyro.Strings.Maximum_String_Length - Length
            then
               Raise_Runtime_Error (M, Budget, "string length overflow");
               return;
            end if;
            Length := Length + Piece_Length (M, Register (M, Top - Joined - 1));
            Joined := Joined + 1;
         end loop;
         Join (M, Budget, Top - Joined, Top - 1, Length, Handle);
         if Handle = No_Object then
            --  After a collection, the instruction goes on with the values left.
            declare
               Current : constant Frame := M.Frames (M.Depth);
            begin
               Lemma_Frame (M, M.Depth);
               Set_Top_Frame
                 (M.Frames.all, M.Depth, (Current with delta Resume => Total), M.Stack'Last,
                  M.Program.all);
            end;
            Raise_Memory_Error (M, Budget);
            return;
         end if;
         Set_Register (M, Top - Joined, Object_Value_Of (Handle));
         Total := Total - (Joined - 1);
      end loop;
      Next (M);
   end Concatenate;

   procedure Close_From (M : in out Machine; Budget : in out Memory_Budget; First : Natural) is
      F      : constant Frame := M.Frames (M.Depth);
      Called : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Close_Upvalues (M.Heap, M.Open.all, M.Open_Count, M.Stack.all, F.Func + 1 + First);
      Close_Pending (M, Budget, F.Func + 1 + First, 0, Called);
      if not Called then
         Advance (M, 0);
      end if;
   end Close_From;

   procedure Mark_To_Close
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Number : Natural;
      Offset : Integer)
   is
      F       : constant Frame := M.Frames (M.Depth);
      Place   : constant Positive := Register_Place (M, Number);
      Item    : constant Value := Register (M, Number);
      Name    : Found_Name;
      Success : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      if Item.Kind = Nil_Value or else Item = Boolean_Value_Of (False) then
         Next (M, Offset);
         return;
      end if;
      Lemma_Live_In (M, Item);
      if Field_Of (M, Item, Close_Event) = Nil then
         --  [puc lfunc.c:checkclosemth]
         Name := Local_Text (M.Program.all, M.Names.all, F.Prototype, Number + 1, F.PC);
         Raise_Runtime_Error
           (M, Budget,
            "variable '" & (if Name.Kind = No_Name then "?" else Name.Text (1 .. Name.Length))
            & "' got a non-closable value");
         return;
      end if;
      Push_Closing (M.Closing, M.Closing_Count, Budget, Place, Success);
      if not Success then
         Raise_Memory_Error (M, Budget);
         return;
      end if;
      Next (M, Offset);
   end Mark_To_Close;

   ----------------------------------------------------------------------------------------
   --  Tables and metamethods
   ----------------------------------------------------------------------------------------

   function Extra_Argument (M : Machine) return Natural is
      F : constant Frame := M.Frames (M.Depth);
   begin
      Lemma_Frame (M, M.Depth);
      return Natural (Instruction_At (M.Program.all, F.Prototype, F.PC + 1).Wide);
   end Extra_Argument;

   procedure Call_Metamethod
     (M         : in out Machine;
      Budget    : in out Memory_Budget;
      Handler   : Value;
      Arguments : Value_List;
      Action    : Pending_Action;
      Target    : Natural;
      Expected  : Boolean;
      Resume    : Natural := 0;
      Base      : Natural := 0)
   is
      F       : constant Frame := M.Frames (M.Depth);
      Last    : constant Stack_Size := M.Stack'Last;
      Start   : Positive;
      Success : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Start := Positive'Max (F.Top, Natural'Min (Base, Stack_Limit));
      Reserve (M.Stack, M.Heap, Budget, Start + Arguments'Length + Extra_Stack, Success);
      Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
      if not Success then
         Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Handler);
      Store_Value (M.Stack.all, M.Heap, Start, Handler);
      Store_Values (M.Stack.all, M.Heap, Start + 1, Arguments);
      Set_Top_Frame
        (M.Frames.all, M.Depth,
         (F with delta PC => (if Action = Rerun then F.PC else F.PC + 1), Action => Action,
                       Target => Target, Expected => Expected, Resume => Resume),
         M.Stack'Last, M.Program.all);
      Call_At
        (M, Budget, Start, Arguments'Length, (if Action in No_Action | Rerun then 0 else 1));
   end Call_Metamethod;

   procedure Get_Index
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Object : Value;
      Key    : Value;
      Target : Natural;
      Source : Operand)
   is
      T       : Value := Object;
      Result  : Value;
      Handler : Value;
   begin
      for Count in 1 .. Maximum_Tag_Loop loop
         pragma Loop_Invariant (Is_Canonical (T) and then Is_Live (M, T));
         if Is_Table (M, T) then
            Result := Raw_Get (M, T, Key);
            if Result /= Nil then
               Set_Register (M, Target, Result);
               Next (M);
               return;
            end if;
            Handler := Metafield (M, T, Index_Event);
            if Handler = Nil then
               Set_Register (M, Target, Nil);
               Next (M);
               return;
            end if;
         else
            Handler := Metafield (M, T, Index_Event);
            if Handler = Nil then
               Raise_Runtime_Error
                 (M, Budget,
                  "attempt to index a " & Type_Name (M, T) & " value"
                  & (if Count = 1 then Variable_Info (M, Source) else ""));
               return;
            end if;
         end if;
         if Is_Function (M, Handler) then
            Call_Metamethod (M, Budget, Handler, [T, Key], Store_Result, Target, False);
            return;
         end if;
         T := Handler;
      end loop;
      Raise_Runtime_Error (M, Budget, "'__index' chain too long; possible loop");
   end Get_Index;

   procedure Set_Index
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Object : Value;
      Key    : Value;
      Item   : Value;
      Source : Operand)
   is
      T       : Value := Object;
      Handler : Value;
      Status  : Pyro.Tables.Set_Status;
   begin
      for Count in 1 .. Maximum_Tag_Loop loop
         pragma Loop_Invariant (Is_Canonical (T) and then Is_Live (M, T));
         if Is_Table (M, T) then
            Handler :=
              (if Raw_Get (M, T, Key) /= Nil then Nil else Metafield (M, T, New_Index_Event));
            if Handler = Nil then
               Raw_Set (M, Budget, T, Key, Item, Status);
               case Status is
                  when Pyro.Tables.Done =>
                     Next (M);
                  when Pyro.Tables.Invalid_Key =>
                     --  [puc ltable.c:luaH_newkey]
                     Raise_Runtime_Error
                       (M, Budget, (if Key.Kind = Nil_Value then "table index is nil"
                                    else "table index is NaN"));
                  when Pyro.Tables.Out_Of_Memory =>
                     Raise_Memory_Error (M, Budget);
               end case;
               return;
            end if;
         else
            Handler := Metafield (M, T, New_Index_Event);
            if Handler = Nil then
               Raise_Runtime_Error
                 (M, Budget,
                  "attempt to index a " & Type_Name (M, T) & " value"
                  & (if Count = 1 then Variable_Info (M, Source) else ""));
               return;
            end if;
         end if;
         if Is_Function (M, Handler) then
            Call_Metamethod (M, Budget, Handler, [T, Key, Item], No_Action, 0, False);
            return;
         end if;
         T := Handler;
      end loop;
      Raise_Runtime_Error (M, Budget, "'__newindex' chain too long; possible loop");
   end Set_Index;

   procedure Make_Table
     (M          : in out Machine;
      Budget     : in out Memory_Budget;
      Target     : Natural;
      Array_Size : Natural;
      Hash_Size  : Natural)
   is
      Handle  : Object_Handle;
      Success : Boolean;
      Before  : constant Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Pyro.Heap.New_Table (M.Heap, Budget, Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         Raise_Memory_Error (M, Budget);
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      --  Sizes past what a table can hold leave it to grow as keys arrive: no constructor
      --  fills them.
      if (Array_Size /= 0 or else Hash_Size /= 0)
        and then Array_Size <= Pyro.Tables.Maximum_Array_Size
        and then Hash_Size <= Pyro.Tables.Maximum_Capacity / 2
      then
         Pyro.Heap.Table_Resize (M.Heap, Budget, Handle, Array_Size, Hash_Size, Success);
         if not Success then
            Raise_Memory_Error (M, Budget);
            return;
         end if;
         Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      end if;
      Set_Register (M, Target, Object_Value_Of (Handle));
      Next (M, 1);
   end Make_Table;

   procedure Store_List
     (M      : in out Machine;
      Budget : in out Memory_Budget;
      Table  : Natural;
      Count  : Integer;
      First  : Integer_64;
      Skip   : Natural)
   is
      Place      : constant Positive := Register_Place (M, Table);
      T          : constant Value := Register (M, Table);
      Size       : Natural;
      Item       : Value;
      Status     : Pyro.Tables.Set_Status;
      Array_Size : Natural;
      Hash_Room  : Natural;
      Success    : Boolean;
   begin
      Size :=
        (if Count >= 0 then Count elsif M.Top > Place then M.Top - Place - 1 else 0);
      Size := Natural'Min (Size, M.Stack'Last - Place);
      if not Is_Table (M, T) then
         Next (M, Skip);
         return;
      end if;
      --  [puc lvm.c:OP_SETLIST] The array part grows at once to hold the last key.
      Pyro.Heap.Table_Reads.Table_Sizes (M.Heap, T.Object, Array_Size, Hash_Room);
      if First + Integer_64 (Size) > Integer_64 (Array_Size)
        and then First + Integer_64 (Size) <= Pyro.Tables.Maximum_Array_Size
      then
         Pyro.Heap.Table_Resize
           (M.Heap, Budget, T.Object, Natural (First + Integer_64 (Size)), Hash_Room, Success);
         if not Success then
            Raise_Memory_Error (M, Budget);
            return;
         end if;
      end if;
      for Index in 1 .. Size loop
         pragma Loop_Invariant (Is_Valid (M) and then Running (M));
         pragma Loop_Invariant (Is_Table (M, T));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Invariant (View (M) = View (M)'Loop_Entry);
         exit when Place + Index > M.Stack'Last;
         Lemma_Value (Objects (M), M.Stack.all, Place + Index);
         Item := M.Stack (Place + Index);
         Lemma_Live_Heap (M.Heap, Item);
         Raw_Set (M, Budget, T, Integer_Value_Of (First + Integer_64 (Index)), Item, Status);
         if Status = Pyro.Tables.Out_Of_Memory then
            Raise_Memory_Error (M, Budget);
            return;
         end if;
      end loop;
      Next (M, Skip);
   end Store_List;

   ----------------------------------------------------------------------------------------
   --  Garbage collection
   ----------------------------------------------------------------------------------------

   --  [proof] Every object value of A is an object C does not show white.
   function Marked (C : Pyro.Color_Sequences.Sequence; A : Root_Array) return Boolean
   is (for all R in A'Range =>
         A (R).Kind /= Object_Value
         or else (A (R).Object in 1 .. Pyro.Color_Sequences.Last (C)
                  and then Pyro.Color_Sequences.Get (C, A (R).Object) /= White))
   with Ghost;

   --  [proof] The values of A, live in the heap's kinds, are live as Mark_Roots needs them.
   procedure Lemma_Roots_Heap_Live (H : Pyro.Heap.Heap; A : Root_Array)
   with
     Ghost,
     Global => null,
     Pre    => Values_Live (Pyro.Heap.Kinds (H), A),
     Post   => (for all R in A'Range => Pyro.Heap.Is_Live (H, A (R)))
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Roots_Heap_Live;

   --  [proof] The values of A Mark_Roots left non-white are marked.
   procedure Lemma_Marked (H : Pyro.Heap.Heap; A : Root_Array)
   with
     Ghost,
     Global => null,
     Pre    =>
       Values_Live (Pyro.Heap.Kinds (H), A)
       and then (for all R in A'Range =>
                   A (R).Kind /= Object_Value
                   or else Pyro.Heap.Color_Of (H, A (R).Object) /= White),
     Post   => Marked (Pyro.Heap.Colors (H), A)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Marked;

   --  [proof] A stack whose places up to Extent Mark_Roots left non-white, and nil above, is
   --  marked.
   procedure Lemma_Marked_Prefix (H : Pyro.Heap.Heap; A : Root_Array; Extent : Natural)
   with
     Ghost,
     Global => null,
     Pre    =>
       Values_Live (Pyro.Heap.Kinds (H), A)
       and then A'First = 1
       and then Extent <= A'Last
       and then (for all R in 1 .. Extent =>
                   A (R).Kind /= Object_Value
                   or else Pyro.Heap.Color_Of (H, A (R).Object) /= White)
       and then (for all R in A'Range => (if R > Extent then A (R) = Nil)),
     Post   => Marked (Pyro.Heap.Colors (H), A)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Marked_Prefix;

   --  The stack places a collection keeps: up to the top of the running frame, or the top of
   --  the stack when it is higher (lgc.c's traversethread keeps up to L->top). A caller's
   --  registers above the function it called are dead: a call overwrites them.
   function Stack_Extent (M : Machine) return Natural
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   => Stack_Extent'Result <= M.Stack'Last and then Stack_Extent'Result <= Stack_Limit
   is
      Extent : Natural := Natural'Min (M.Top - 1, M.Stack'Last);
   begin
      if M.Depth > 0 then
         Extent := Natural'Max (Extent, Natural'Min (M.Frames (M.Depth).Top - 1, M.Stack'Last));
      end if;
      if M.State = Waiting then
         --  The results of the call a waiting host function asked for.
         Extent :=
           Natural'Max (Extent, Natural'Min (M.Results_At - 1 + M.Result_Size, M.Stack'Last));
      end if;
      return Extent;
   end Stack_Extent;

   --  [proof] Marked values stay marked while colours only grow.
   procedure Lemma_Still_Marked (C1, C2 : Pyro.Color_Sequences.Sequence; A : Root_Array)
   with
     Ghost,
     Global => null,
     Pre    => Marked (C1, A) and then Pyro.Garbage_Collector.Grown (C1, C2),
     Post   => Marked (C2, A)
   is
   begin
      null;
   end Lemma_Still_Marked;

   --  [proof] Marked values, live before Finish, are live after it: Finish keeps every
   --  object that was not white.
   procedure Lemma_Survived
     (K1 : Pyro.Kind_Sequences.Sequence;
      C1 : Pyro.Color_Sequences.Sequence;
      H  : Pyro.Heap.Heap;
      A  : Root_Array)
   with
     Ghost,
     Global => null,
     Pre    =>
       Values_Live (K1, A)
       and then Marked (C1, A)
       and then Pyro.Color_Sequences.Last (C1) = Pyro.Kind_Sequences.Last (K1)
       and then Pyro.Heap.Slot_Count (H) = Pyro.Kind_Sequences.Last (K1)
       and then (for all Handle in 1 .. Pyro.Heap.Slot_Count (H) =>
                   (if Pyro.Color_Sequences.Get (C1, Handle) /= White
                    then Pyro.Heap.Kind_Of (H, Handle) = Pyro.Kind_Sequences.Get (K1, Handle))),
     Post   => Values_Live (Pyro.Heap.Kinds (H), A)
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Values_Live);
   begin
      null;
   end Lemma_Survived;

   --  [puc lgc.c:fullgc] Collects garbage: every value the machine keeps (its constants,
   --  registry, whole stack and open upvalues) is a root, so they all stay live.
   procedure Collect_Garbage (M : in out Machine; Budget : in out Memory_Budget)
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   =>
       Core_Valid (M)
       and then Limit (Budget) = Limit (Budget)'Old
       and then M.State = M.State'Old
       and then (if Is_Valid (M)'Old then Is_Valid (M))
   is
      Extent   : constant Natural := Stack_Extent (M);
      K0       : Pyro.Kind_Sequences.Sequence with Ghost;
      C0       : Pyro.Color_Sequences.Sequence with Ghost;
      Complete : Boolean;
   begin
      --  [puc lgc.c:traversethread] The places above the frames hold nothing to keep.
      Fill_Nil (M.Stack.all, M.Heap, Extent + 1, M.Stack'Last - Extent);
      Pyro.Garbage_Collector.Start (M.Heap);
      Lemma_Roots_Heap_Live (M.Heap, M.Constants.all);
      Pyro.Garbage_Collector.Mark_Roots (M.Heap, M.Constants.all);
      Lemma_Marked (M.Heap, M.Constants.all);
      C0 := Pyro.Heap.Colors (M.Heap);
      Lemma_Roots_Heap_Live (M.Heap, M.Registry.all);
      Pyro.Garbage_Collector.Mark_Roots (M.Heap, M.Registry.all);
      Lemma_Marked (M.Heap, M.Registry.all);
      Lemma_Still_Marked (C0, Pyro.Heap.Colors (M.Heap), M.Constants.all);
      C0 := Pyro.Heap.Colors (M.Heap);
      Lemma_Roots_Heap_Live (M.Heap, M.Stack.all);
      Pyro.Garbage_Collector.Mark_Roots (M.Heap, M.Stack (1 .. Extent));
      Lemma_Marked_Prefix (M.Heap, M.Stack.all, Extent);
      Lemma_Still_Marked (C0, Pyro.Heap.Colors (M.Heap), M.Constants.all);
      Lemma_Still_Marked (C0, Pyro.Heap.Colors (M.Heap), M.Registry.all);
      C0 := Pyro.Heap.Colors (M.Heap);
      Lemma_Roots_Heap_Live (M.Heap, M.Open.all);
      Pyro.Garbage_Collector.Mark_Roots (M.Heap, M.Open.all);
      Lemma_Marked (M.Heap, M.Open.all);
      Lemma_Still_Marked (C0, Pyro.Heap.Colors (M.Heap), M.Constants.all);
      Lemma_Still_Marked (C0, Pyro.Heap.Colors (M.Heap), M.Registry.all);
      Lemma_Still_Marked (C0, Pyro.Heap.Colors (M.Heap), M.Stack.all);
      K0 := Pyro.Heap.Kinds (M.Heap);
      C0 := Pyro.Heap.Colors (M.Heap);
      Pyro.Garbage_Collector.Finish (M.Heap, Budget, Complete);
      pragma Unreferenced (Complete);
      Lemma_Survived (K0, C0, M.Heap, M.Constants.all);
      Lemma_Survived (K0, C0, M.Heap, M.Registry.all);
      Lemma_Survived (K0, C0, M.Heap, M.Stack.all);
      Lemma_Survived (K0, C0, M.Heap, M.Open.all);
   end Collect_Garbage;

   --  The memory used doubled.
   function Doubled (Budget : Memory_Budget) return Byte_Count
   is (2 * Used (Budget));

   ----------------------------------------------------------------------------------------
   --  Loading and running
   ----------------------------------------------------------------------------------------

   procedure Load
     (M          : in out Machine;
      Budget     : in out Memory_Budget;
      Program    : in out Chunk_Access;
      Names      : in out Symbols_Access;
      Chunk_Name : String;
      Seed       : Pyro.Strings.Seed;
      Options    : Settings;
      Success    : out Boolean)
   is
      Count   : Prototype_Index;
      Total   : Natural := 0;
      Handle  : Object_Handle;
      Main    : Prototype_Index;
      Cell    : Object_Handle;
      Item    : Pyro.Bytecode.Constant_Value;
      Text    : Value;
      Before  : Pyro.Kind_Sequences.Sequence with Ghost;
   begin
      Success := False;
      Pyro.Heap.Clear (M.Heap, Budget);
      M.Program := Program;
      Program := null;
      M.Names := Names;
      Names := null;
      M.Options := Options;
      M.Name_Length := Chunk_Name'Length;
      M.Name (1 .. Chunk_Name'Length) := Chunk_Name;
      Pyro.Heap.Set_Seed (M.Heap, Seed);
      Count := Prototype_Count (M.Program.all);
      for P in 1 .. Count loop
         if Constant_Count (M.Program.all, P) > Maximum_Constants - Total then
            return;
         end if;
         Total := Total + Constant_Count (M.Program.all, P);
         pragma Loop_Invariant (Total <= Maximum_Constants);
      end loop;
      Charge (Budget, Value_Bytes * Byte_Count (Total + Registry_Size + Initial_Stack
                                                 + Initial_Open)
                      + Frame_Bytes * Initial_Frames + Base_Bytes * Byte_Count (Count)
                      + Base_Bytes * Initial_Open, Success);
      if not Success then
         return;
      end if;
      Success := False;
      M.Constants := new Root_Array'(1 .. Total => Nil);
      M.Bases := new Base_Array'(1 .. Count => 0);
      M.Registry := new Root_Array'(1 .. Registry_Size => Nil);
      M.Stack := new Root_Array'(1 .. Initial_Stack => Nil);
      M.Frames := new Frame_Array'(1 .. Initial_Frames => (others => <>));
      M.Open := new Root_Array'(1 .. Initial_Open => Nil);
      M.Closing := new Place_Array'(1 .. Initial_Open => 0);
      M.Closing_Count := 0;
      M.Unwinding := False;
      M.State := Done;
      M.Failed := True;
      M.Depth := 0;
      M.Top := 1;
      M.Open_Count := 0;
      M.Results_At := 1;
      M.Result_Size := 0;
      Lemma_Nil (Objects (M), M.Constants.all);
      Lemma_Nil (Objects (M), M.Registry.all);
      Lemma_Nil (Objects (M), M.Stack.all);
      Lemma_Nil (Objects (M), M.Open.all);

      --  The constants, strings interned in the heap.
      Total := 0;
      for P in 1 .. Count loop
         pragma Loop_Invariant (Pyro.Heap.Is_Valid (M.Heap));
         pragma Loop_Invariant (Roots_Live (M));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Invariant (Total <= M.Constants'Length);
         pragma Loop_Invariant
           (for all Q in 1 .. P - 1 =>
              M.Bases (Q) <= M.Constants'Length
              and then Constant_Count (M.Program.all, Q) <= M.Constants'Length - M.Bases (Q));
         if Constant_Count (M.Program.all, P) > M.Constants'Length - Total then
            return;
         end if;
         M.Bases (P) := Total;
         for Number in 0 .. Constant_Count (M.Program.all, P) - 1 loop
            pragma Loop_Invariant (Pyro.Heap.Is_Valid (M.Heap));
            pragma Loop_Invariant (Roots_Live (M));
            pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
            pragma Loop_Invariant (Total = M.Bases (P) + Number);
            Item := Constant_At (M.Program.all, P, Number);
            case Item.Kind is
               when Nil_Constant => Text := Nil;
               when False_Constant => Text := Boolean_Value_Of (False);
               when True_Constant => Text := Boolean_Value_Of (True);
               when Integer_Constant =>
                  Text := Integer_Value_Of (Pyro.Integer_Arithmetic.To_Signed (Item.Bits));
               when Float_Constant => Text := Float_Value_Of (Item.Bits);
               when Short_String_Constant | Long_String_Constant =>
                  if Item.Symbol not in 1 .. Pyro.Symbols.Count (M.Names.all) then
                     return;
                  end if;
                  declare
                     Bytes : constant String := Pyro.Symbols.Text (M.Names.all, Item.Symbol);
                  begin
                     if Bytes'Length > Pyro.Heap.Maximum_String_Length then
                        return;
                     end if;
                     Before := Objects (M);
                     Pyro.Heap.New_String (M.Heap, Budget, To_Bytes (Bytes), Handle);
                     Lemma_Roots_Grow (Before, M);
                     if Handle = No_Object then
                        return;
                     end if;
                     Text := Object_Value_Of (Handle);
                     Lemma_Heap_Live (M.Heap, Text);
                  end;
            end case;
            Total := Total + 1;
            Store_Value (M.Constants.all, M.Heap, Total, Text);
         end loop;
      end loop;
      Lemma_Bases (M.Bases.all, M.Constants'Length, M.Program.all);

      --  The registry.
      Before := Objects (M);
      Pyro.Heap.New_Table (M.Heap, Budget, Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      Store_Value (M.Registry.all, M.Heap, Globals_Place, Object_Value_Of (Handle));
      Before := Objects (M);
      Pyro.Heap.New_Table (M.Heap, Budget, Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      Store_Value (M.Registry.all, M.Heap, Functions_Place, Object_Value_Of (Handle));
      Before := Objects (M);
      Pyro.Heap.New_String (M.Heap, Budget, To_Bytes ("not enough memory"), Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      Store_Value (M.Registry.all, M.Heap, Memory_Place, Object_Value_Of (Handle));
      for Item in Event loop
         pragma Loop_Invariant (Pyro.Heap.Is_Valid (M.Heap));
         pragma Loop_Invariant (Roots_Live (M));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         Before := Objects (M);
         Pyro.Heap.New_String (M.Heap, Budget, To_Bytes (Event_Name (Item)), Handle);
         Lemma_Roots_Grow (Before, M);
         if Handle = No_Object then
            return;
         end if;
         Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
         Store_Value (M.Registry.all, M.Heap, Event_Place (Item), Object_Value_Of (Handle));
      end loop;

      --  The main function, its first upvalue _ENV the globals.
      Main := Count;
      Before := Objects (M);
      Pyro.Heap.New_Object
        (M.Heap, Budget, Closure_Object, Natural (Main),
         Natural'Min (Upvalue_Count (M.Program.all, Main), Pyro.Heap.Maximum_References),
         Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      Store_Value (M.Stack.all, M.Heap, 1, Object_Value_Of (Handle));
      for Number in 1 .. Pyro.Heap.Reference_Count (M.Heap, Handle) loop
         pragma Loop_Invariant (Pyro.Heap.Is_Valid (M.Heap));
         pragma Loop_Invariant (Roots_Live (M));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         pragma Loop_Invariant (M.Stack (1) = Object_Value_Of (Handle));
         Before := Objects (M);
         Pyro.Heap.New_Object (M.Heap, Budget, Upvalue_Object, 0, 1, Cell);
         Lemma_Roots_Grow (Before, M);
         if Cell = No_Object then
            return;
         end if;
         if Number = 1 then
            Lemma_Value (Objects (M), M.Registry.all, Globals_Place);
            Lemma_Live_Heap (M.Heap, M.Registry (Globals_Place));
            Pyro.Heap.Set_Reference (M.Heap, Cell, 1, M.Registry (Globals_Place));
         end if;
         Lemma_Value (Objects (M), M.Stack.all, 1);
         if Number <= Pyro.Heap.Reference_Count (M.Heap, Handle) then
            Pyro.Heap.Set_Reference (M.Heap, Handle, Number, Object_Value_Of (Cell));
         end if;
      end loop;
      Lemma_Frames_Empty (M.Frames.all, M.Stack'Last, M.Program.all);
      M.Depth := 0;
      M.Top := 2;
      M.State := Ready;
      M.Failed := False;
      pragma Assert (M.Program /= null and then Is_Well_Formed (M.Program.all));
      pragma Assert (Pyro.Bytecode.Is_Valid (M.Program.all));
      pragma Assert (Prototype_Count (M.Program.all) > 0);
      pragma Assert (M.Names /= null and then Pyro.Symbols.Is_Valid (M.Names.all));
      pragma Assert (M.Bases'Last = Prototype_Count (M.Program.all));
      pragma Assert (Bases_Valid (M.Bases.all, M.Constants'Length, M.Program.all));
      pragma Assert (M.Stack'Last in Initial_Stack .. Stack_Limit);
      pragma Assert (M.Frames'First = 1 and then M.Frames'Last <= Maximum_Frames);
      pragma Assert (M.Open'First = 1 and then M.Open'Last in Initial_Open .. Maximum_Open);
      M.Threshold := Doubled (Budget);
      M.Retry := False;
      M.Retried := False;
      M.Pressure := False;
      Call_At (M, Budget, 1, 0, -1);
      Success := M.State = Ready;
   end Load;

   --  The host function with number Id: the one the registry keeps, or a new one, kept.
   --  Success is False when Budget cannot pay.
   procedure Function_Value
     (Heap     : in out Pyro.Heap.Heap;
      Registry : Root_Array;
      Budget   : in out Memory_Budget;
      Id       : Host_Id;
      Result   : out Value;
      Success  : out Boolean)
   with
     Global => null,
     Pre    =>
       Pyro.Heap.Is_Valid (Heap)
       and then Registry'First = 1
       and then Registry'Last = Registry_Size
       and then Values_Live (Pyro.Heap.Kinds (Heap), Registry),
     Post   =>
       Pyro.Heap.Is_Valid (Heap)
       and then Pyro.Heap.Keeps_Objects (Pyro.Heap.Kinds (Heap)'Old, Pyro.Heap.Kinds (Heap))
       and then Limit (Budget) = Limit (Budget)'Old
       and then Is_Canonical (Result)
       and then Pyro.Heap.Live_In (Pyro.Heap.Kinds (Heap), Result)
       and then (if Success
                 then Result.Kind = Object_Value
                      and then Pyro.Heap.Kind_Of (Heap, Result.Object) = Host_Function_Object)
   is
      Functions : constant Value := Registry (Functions_Place);
      Key       : constant Value := Integer_Value_Of (Integer_64 (Id));
      Handle    : Object_Handle;
      Status    : Pyro.Tables.Set_Status;
   begin
      Result := Nil;
      Success := False;
      Lemma_Value (Pyro.Heap.Kinds (Heap), Registry, Functions_Place);
      if Functions.Kind /= Object_Value
        or else Pyro.Heap.Kind_Of (Heap, Functions.Object) /= Table_Object
      then
         return;
      end if;
      Result := Pyro.Heap.Table_Get (Heap, Functions.Object, Key);
      Lemma_Heap_Live (Heap, Result);
      if Result.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (Heap, Result.Object) = Host_Function_Object
      then
         Success := True;
         return;
      end if;
      Result := Nil;
      Pyro.Heap.New_Object (Heap, Budget, Host_Function_Object, Natural (Id), 0, Handle);
      if Handle = No_Object then
         return;
      end if;
      Pyro.Heap.Table_Set (Heap, Budget, Functions.Object, Key, Object_Value_Of (Handle), Status);
      Result := Object_Value_Of (Handle);
      Lemma_Heap_Live (Heap, Result);
      Success := Status = Pyro.Tables.Done;
   end Function_Value;

   procedure Register
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Name    : String;
      Id      : Host_Id;
      Success : out Boolean)
   is
      Item    : Value;
      Key     : Object_Handle;
      Status  : Pyro.Tables.Set_Status;
      Globals : constant Value := M.Registry (Globals_Place);
      Before  : Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Lemma_Value (Objects (M), M.Registry.all, Globals_Place);
      Function_Value (M.Heap, M.Registry.all, Budget, Id, Item, Success);
      Lemma_Roots_Grow (Before, M);
      if not Success then
         return;
      end if;
      Success := False;
      Before := Objects (M);
      Pyro.Heap.New_String (M.Heap, Budget, To_Bytes (Name), Key);
      Lemma_Roots_Grow (Before, M);
      if Key = No_Object then
         return;
      end if;
      Lemma_Value (Objects (M), M.Registry.all, Globals_Place);
      if Globals.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, Globals.Object) = Table_Object
        and then Item.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, Item.Object) = Host_Function_Object
      then
         Pyro.Heap.Table_Set
           (M.Heap, Budget, Globals.Object, Object_Value_Of (Key), Item, Status);
         Success := Status = Pyro.Tables.Done;
      end if;
   end Register;

   procedure Run (M : in out Machine; Budget : in out Memory_Budget; Status : out Run_Status) is
   begin
      if M.State = Waiting then
         Status := Host_Call;
         return;
      end if;
      for Count in 1 .. Slice loop
         pragma Loop_Invariant (Is_Valid (M) and then Is_Loaded (M));
         pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
         exit when M.State /= Ready;
         if M.Options.Step_Limit /= 0 and then M.Steps >= M.Options.Step_Limit then
            Status := Step_Limit_Reached;
            return;
         end if;
         if M.Steps < Unsigned_64'Last then
            M.Steps := M.Steps + 1;
         end if;
         --  The safe point: no handle lives outside the machine's roots.
         M.Retried := M.Retry;
         if M.Options.Stress or else M.Retry or else M.Pressure
           or else Used (Budget) > M.Threshold
         then
            Collect_Garbage (M, Budget);
            M.Threshold := Doubled (Budget);
            M.Retry := False;
            M.Pressure := False;
         end if;
         Pyro.Virtual_Machine.Execution.Step (M, Budget);
      end loop;
      Status :=
        (case M.State is
           when Waiting => Host_Call,
           when Done    => (if M.Failed then Errored else Finished),
           when others  => Paused);
   end Run;

   ----------------------------------------------------------------------------------------
   --  The host-function protocol
   ----------------------------------------------------------------------------------------

   function Host_Function (M : Machine) return Host_Id
   is (M.Frames (M.Depth).Host);

   function Continuation (M : Machine) return Natural
   is (M.Frames (M.Depth).Context);

   function Argument_Count (M : Machine) return Natural is
   begin
      Lemma_Frame (M, M.Depth);
      return M.Frames (M.Depth).Top - M.Frames (M.Depth).Func - 1;
   end Argument_Count;

   function Argument (M : Machine; Position : Positive) return Value is
      Place : Positive;
   begin
      Lemma_Frame (M, M.Depth);
      if Position > M.Frames (M.Depth).Top - M.Frames (M.Depth).Func - 1 then
         return Nil;
      end if;
      Place := M.Frames (M.Depth).Func + Position;
      Lemma_Value (Objects (M), M.Stack.all, Place);
      Lemma_Live_Heap (M.Heap, M.Stack (Place));
      return M.Stack (Place);
   end Argument;

   function Host_Call_Name (M : Machine) return String is
      Name : Found_Name;
   begin
      if M.Depth < 2 then
         return "";
      end if;
      Name := Call_Name (M, M.Depth - 1, At_Call => True);
      return Name.Text (1 .. Name.Length);
   end Host_Call_Name;

   function Host_Called_As_Method (M : Machine) return Boolean
   is (M.Depth >= 2 and then Call_Name (M, M.Depth - 1, At_Call => True).Kind = Method_Name);

   function Called_Function (M : Machine) return Value is
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Value (Objects (M), M.Stack.all, M.Frames (M.Depth).Func);
      Lemma_Live_Heap (M.Heap, M.Stack (M.Frames (M.Depth).Func));
      return M.Stack (M.Frames (M.Depth).Func);
   end Called_Function;

   function Globals (M : Machine) return Value is
   begin
      Lemma_Value (Objects (M), M.Registry.all, Globals_Place);
      Lemma_Live_Heap (M.Heap, M.Registry (Globals_Place));
      return M.Registry (Globals_Place);
   end Globals;

   function Call_Succeeded (M : Machine) return Boolean
   is (M.Succeeded);

   function Result_Count (M : Machine) return Natural
   is (M.Result_Size);

   function Result (M : Machine; Position : Positive) return Value is
   begin
      if Position > M.Result_Size then
         return Nil;
      end if;
      Lemma_Value (Objects (M), M.Stack.all, M.Results_At + Position - 1);
      Lemma_Live_Heap (M.Heap, M.Stack (M.Results_At + Position - 1));
      return M.Stack (M.Results_At + Position - 1);
   end Result;

   procedure Return_Values
     (M : in out Machine; Budget : in out Memory_Budget; Values : Value_List)
   is
      F       : constant Frame := M.Frames (M.Depth);
      Last    : constant Stack_Size := M.Stack'Last;
      Success : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Reserve (M.Stack, M.Heap, Budget, F.Func + Values'Length + Extra_Stack, Success);
      Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
      M.State := Ready;
      if not Success then
         Throw_Message (M, Budget, "stack overflow");
         return;
      end if;
      Store_Values (M.Stack.all, M.Heap, F.Func, Values);
      Finish_Return (M, Budget, F.Func, Values'Length);
   end Return_Values;

   procedure Raise_Error (M : in out Machine; Budget : in out Memory_Budget; Error : Value) is
   begin
      Lemma_Heap_Live (M.Heap, Error);
      M.State := Ready;
      Throw (M, Budget, Error);
   end Raise_Error;

   procedure Raise_Message
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Message : String;
      Level   : Natural)
   is
   begin
      M.State := Ready;
      Throw_Message
        (M, Budget,
         (if Level = 0 or else Level >= M.Depth then "" else Position_Of (M, Level + 1))
         & Message);
   end Raise_Message;

   procedure Call
     (M            : in out Machine;
      Budget       : in out Memory_Budget;
      Callee       : Value;
      Arguments    : Value_List;
      Continuation : Positive;
      Protect      : Boolean)
   is
      F       : constant Frame := M.Frames (M.Depth);
      Last    : constant Stack_Size := M.Stack'Last;
      Success : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Reserve (M.Stack, M.Heap, Budget, F.Top + Arguments'Length + Extra_Stack, Success);
      Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
      M.State := Ready;
      if not Success then
         Throw_Message (M, Budget, "stack overflow");
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Callee);
      Store_Value (M.Stack.all, M.Heap, F.Top, Callee);
      Store_Values (M.Stack.all, M.Heap, F.Top + 1, Arguments);
      Lemma_Frame (M, M.Depth);
      Set_Top_Frame
        (M.Frames.all, M.Depth,
         (F with delta Context => Continuation, Protect => Protect), M.Stack'Last,
         M.Program.all);
      Call_At (M, Budget, F.Top, Arguments'Length, -1);
   end Call;

   procedure New_String
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Text    : String;
      Result  : out Value;
      Success : out Boolean)
   is
      Handle : Object_Handle;
      Before : Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Result := Nil;
      Success := False;
      Pyro.Heap.New_String (M.Heap, Budget, To_Bytes (Text), Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         --  [puc lmem.c:tryagain] Collect, keeping the host function's frame, and try again.
         Collect_Garbage (M, Budget);
         Before := Objects (M);
         Pyro.Heap.New_String (M.Heap, Budget, To_Bytes (Text), Handle);
         Lemma_Roots_Grow (Before, M);
      end if;
      if Handle /= No_Object then
         Result := Object_Value_Of (Handle);
         Success := True;
      end if;
   end New_String;

   procedure New_Function
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Id      : Host_Id;
      Result  : out Value;
      Success : out Boolean)
   is
      Before : Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Function_Value (M.Heap, M.Registry.all, Budget, Id, Result, Success);
      Lemma_Roots_Grow (Before, M);
      if not Success then
         --  [puc lmem.c:tryagain] Collect, keeping the host function's frame, and try again.
         Collect_Garbage (M, Budget);
         Before := Objects (M);
         Function_Value (M.Heap, M.Registry.all, Budget, Id, Result, Success);
         Lemma_Roots_Grow (Before, M);
      end if;
      Lemma_Live_Heap (M.Heap, Result);
   end New_Function;

   procedure Clear (M : in out Machine; Budget : in out Memory_Budget) is
   begin
      Pyro.Heap.Clear (M.Heap, Budget);
      if M.Program /= null then
         Pyro.Bytecode.Clear (M.Program.all, Budget);
      end if;
      Free_Chunk (M.Program);
      if M.Names /= null then
         Pyro.Symbols.Clear (M.Names.all, Budget);
      end if;
      Free_Symbols (M.Names);
      if M.Constants /= null then
         Release (Budget, Value_Bytes * Byte_Count (M.Constants'Length));
      end if;
      if M.Bases /= null then
         Release (Budget, Base_Bytes * Byte_Count (M.Bases'Length));
      end if;
      if M.Registry /= null then
         Release (Budget, Value_Bytes * Byte_Count (M.Registry'Length));
      end if;
      if M.Stack /= null then
         Release (Budget, Value_Bytes * Byte_Count (M.Stack'Length));
      end if;
      if M.Frames /= null then
         Release (Budget, Frame_Bytes * Byte_Count (M.Frames'Length));
      end if;
      if M.Open /= null then
         Release (Budget, Value_Bytes * Byte_Count (M.Open'Length));
      end if;
      if M.Closing /= null then
         Release (Budget, Base_Bytes * Byte_Count (M.Closing'Length));
      end if;
      Free_Values (M.Constants);
      Free_Bases (M.Bases);
      Free_Values (M.Registry);
      Free_Values (M.Stack);
      Free_Frames (M.Frames);
      Free_Values (M.Open);
      Free_Places (M.Closing);
      M.State := Unloaded;
      M.Depth := 0;
   end Clear;

end Pyro.Virtual_Machine;
