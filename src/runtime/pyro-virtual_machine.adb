--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The virtual machine: runs a compiled chunk on one thread, calling host functions through
--  the host-function protocol.

with Ada.Unchecked_Deallocation;
with Pyro.Floats;
with Pyro.Integer_Arithmetic;
with Pyro.Virtual_Machine.Execution;

package body Pyro.Virtual_Machine with SPARK_Mode => On is

   use Pyro.Bytecode;
   use type Pyro.Tables.Set_Status;

   procedure Free_Values is new Ada.Unchecked_Deallocation (Root_Array, Root_Array_Access);
   procedure Free_Bases is new Ada.Unchecked_Deallocation (Base_Array, Base_Array_Access);
   procedure Free_Frames is new Ada.Unchecked_Deallocation (Frame_Array, Frame_Array_Access);
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

   --  The places of the registry: the globals, the error being raised, and the message for
   --  running out of memory.
   Globals_Place : constant := 1;
   Error_Place   : constant := 2;
   Memory_Place  : constant := 3;
   Registry_Size : constant := 3;

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
                     and then F.Extra < F.Func,
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

   --  [proof] What the state says of the frames: a Lua frame runs when Ready, a host frame
   --  waits when Waiting.
   function State_Valid (M : Machine) return Boolean
   is (case M.State is
         when Ready   => M.Depth >= 1 and then M.Frames (M.Depth).Kind = Lua_Frame,
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
     Post   => Values_Live (Pyro.Heap.Kinds (Heap), Items) and then Items (Place) = Item
   is
      Before : constant Root_Array := Items with Ghost;
   begin
      Items (Place) := Item;
      Lemma_Store (Pyro.Heap.Kinds (Heap), Before, Items, Place);
   end Store_Value;

   --  Makes the places of Items from From hold the values of List.
   procedure Store_List
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
   end Store_List;

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
     Post   => Values_Live (Pyro.Heap.Kinds (Heap), Items)
   is
   begin
      for Index in 0 .. Count - 1 loop
         Store_Value (Items, Heap, From + Index, Nil);
         pragma Loop_Invariant (Values_Live (Pyro.Heap.Kinds (Heap), Items));
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

   function String_Text (M : Machine; Item : Value) return String is
      Length : constant Natural :=
        Natural'Min (Pyro.Heap.String_Length (M.Heap, Item.Object),
                     Pyro.Heap.Maximum_String_Length);
      Result : String (1 .. Length);
   begin
      for Position in Result'Range loop
         Result (Position) :=
           Pyro.Heap.String_Byte (M.Heap, Item.Object, Byte_Position (Position));
      end loop;
      return Result;
   end String_Text;

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
   --  when it is not a Lua frame.
   function Current_Line (M : Machine; Level : Positive) return Natural
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
      return Natural (Line_At (M.Program.all, F.Prototype, F.PC));
   end Current_Line;

   --  "name:line: " for frame Level, or "" when it is not a Lua frame.
   function Position_Of (M : Machine; Level : Positive) return String
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   => Position_Of'Result'First = 1 and then Position_Of'Result'Length <= 128
   is
      Line : constant Natural := Current_Line (M, Level);
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
   --  Errors
   ----------------------------------------------------------------------------------------

   --  Unwinds the frames after an error, the error value in the registry: down to a host
   --  function that asked for a protected call, which then waits with the error; with none,
   --  the machine is done and failed.
   procedure Unwind (M : in out Machine)
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   => Is_Valid (M) and then M.State in Waiting | Done
   is
      Callee : Positive;
      F      : Frame;
   begin
      while M.Depth > 0 loop
         pragma Loop_Invariant (Core_Valid (M));
         pragma Loop_Variant (Decreases => M.Depth);
         Lemma_Frames_Pop (M.Frames.all, M.Depth, M.Stack'Last, M.Program.all);
         M.Depth := M.Depth - 1;
         if M.Depth > 0
           and then M.Frames (M.Depth).Kind = Host_Frame
           and then M.Frames (M.Depth).Protect
         then
            F := M.Frames (M.Depth);
            Callee := F.Top;
            Close_Upvalues (M.Heap, M.Open.all, M.Open_Count, M.Stack.all, Callee);
            if Callee in M.Stack'Range then
               Lemma_Value (Objects (M), M.Registry.all, Error_Place);
               Store_Value (M.Stack.all, M.Heap, Callee, M.Registry (Error_Place));
               M.Results_At := Callee;
               M.Result_Size := 1;
               M.Succeeded := False;
               Lemma_Frame (M, M.Depth);
               Set_Top_Frame
                 (M.Frames.all, M.Depth, (F with delta Protect => False), M.Stack'Last,
                  M.Program.all);
               M.State := Waiting;
               return;
            end if;
         end if;
      end loop;
      Close_Upvalues (M.Heap, M.Open.all, M.Open_Count, M.Stack.all, 1);
      M.Failed := True;
      M.State := Done;
   end Unwind;

   --  Raises Error.
   procedure Throw (M : in out Machine; Error : Value)
   with
     Global => null,
     Pre    =>
       Core_Valid (M)
       and then Is_Canonical (Error)
       and then Pyro.Heap.Live_In (Objects (M), Error),
     Post   => Is_Valid (M) and then M.State in Waiting | Done
   is
   begin
      Store_Value (M.Registry.all, M.Heap, Error_Place, Error);
      Unwind (M);
   end Throw;

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

   --  Raises the string Text.
   procedure Throw_Message (M : in out Machine; Budget : in out Memory_Budget; Text : String)
   with
     Global => null,
     Pre    => Core_Valid (M),
     Post   =>
       Is_Valid (M)
       and then M.State in Waiting | Done
       and then Limit (Budget) = Limit (Budget)'Old
   is
      Error  : Value;
      Before : constant Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Make_String (M.Heap, M.Registry.all, Budget, Text, Error);
      Lemma_Roots_Grow (Before, M);
      Throw (M, Error);
   end Throw_Message;

   procedure Raise_Runtime_Error
     (M : in out Machine; Budget : in out Memory_Budget; Text : String) is
   begin
      Throw_Message (M, Budget, Position_Of (M, 1) & Text);
   end Raise_Runtime_Error;

   procedure Raise_Memory_Error (M : in out Machine) is
      Error : constant Value := M.Registry (Memory_Place);
   begin
      Lemma_Value (Objects (M), M.Registry.all, Memory_Place);
      Throw (M, Error);
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

   --  [puc ldo.c:luaD_poscall] The top frame returns Count results, which start at First:
   --  they go to its origin, as many as its caller wanted (nil for the missing ones).
   procedure Finish_Return (M : in out Machine; First : Positive; Count : Natural)
   with
     Global => null,
     Pre    =>
       Core_Valid (M)
       and then M.Depth >= 1
       and then First >= M.Frames (M.Depth).Origin
       and then Count <= M.Stack'Last + 1 - First,
     Post   => Is_Valid (M) and then Is_Loaded (M)
   is
      F      : constant Frame := M.Frames (M.Depth);
      Target : constant Positive := F.Origin;
      Wanted : Natural;
      Moved  : Natural;
   begin
      Lemma_Frame (M, M.Depth);
      Wanted := (if F.Results < 0 then Count else F.Results);
      Moved := Natural'Min (Count, Wanted);
      Copy (M.Stack.all, M.Heap, First, Target, Moved);
      Fill_Nil (M.Stack.all, M.Heap, Target + Moved, Wanted - Moved);
      M.Top := Target + Wanted;
      Lemma_Frames_Pop (M.Frames.all, M.Depth, M.Stack'Last, M.Program.all);
      M.Depth := M.Depth - 1;
      if M.Depth = 0 then
         M.State := Done;
      elsif M.Frames (M.Depth).Kind = Host_Frame then
         M.Results_At := Target;
         M.Result_Size := Wanted;
         M.Succeeded := True;
         M.State := Waiting;
      else
         M.State := Ready;
      end if;
   end Finish_Return;

   --  The function value Callee can be called: a closure or a host function.
   function Is_Callable (M : Machine; Callee : Value) return Boolean
   is (Callee.Kind = Object_Value
       and then Pyro.Heap.Kind_Of (M.Heap, Callee.Object)
                in Closure_Object | Host_Function_Object);

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
      Callee     : constant Value := M.Stack (Func);
      Last       : constant Stack_Size := M.Stack'Last;
      P          : Prototype_Index;
      Parameters : Natural;
      Size       : Natural;
      Success    : Boolean;
   begin
      Lemma_Value (Objects (M), M.Stack.all, Func);
      if Callee.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, Callee.Object) = Closure_Object
      then
         P := Prototype_Index (Natural'Min (Pyro.Heap.Tag_Of (M.Heap, Callee.Object),
                                            Natural (Prototype_Index'Last)));
         if P not in 1 .. Prototype_Count (M.Program.all) then
            Throw_Message (M, Budget, Position_Of (M, 1) & "internal error: bad closure");
            return;
         end if;
         Lemma_Valid_Prototype (M.Program.all, P);
         Parameters := Natural (Header (M.Program.all, P).Parameter_Count);
         Size := Natural (Header (M.Program.all, P).Stack_Size);
         Reserve
           (M.Stack, M.Heap, Budget,
            Func + Natural'Max (Size, Natural'Max (Arguments, Results)) + Extra_Stack, Success);
         Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
         if not Success then
            Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
            return;
         end if;
         if Arguments < Parameters then
            Fill_Nil (M.Stack.all, M.Heap, Func + 1 + Arguments, Parameters - Arguments);
         end if;
         M.Top := Func + 1 + Natural'Max (Arguments, Parameters);
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
             Protect   => False),
            M.Stack'Last, M.Program.all, Success);
         if not Success then
            Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
         end if;
      elsif Callee.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, Callee.Object) = Host_Function_Object
      then
         Reserve
           (M.Stack, M.Heap, Budget,
            Func + Natural'Max (Arguments, Results) + Extra_Stack, Success);
         Lemma_Frames_Larger (M.Frames.all, M.Depth, Last, M.Stack'Last, M.Program.all);
         if not Success then
            Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
            return;
         end if;
         Push_Frame
           (M.Frames, M.Depth, Budget,
            (Kind      => Host_Frame,
             Origin    => Func,
             Func      => Func,
             Top       => Func + 1 + Arguments,
             Prototype => 0,
             PC        => 0,
             Results   => Results,
             Extra     => 0,
             Host      => Host_Id (Natural'Max (1, Natural'Min
                                    (Pyro.Heap.Tag_Of (M.Heap, Callee.Object),
                                     Natural (Host_Id'Last)))),
             Context   => 0,
             Protect   => False),
            M.Stack'Last, M.Program.all, Success);
         if not Success then
            Throw_Message (M, Budget, Position_Of (M, 1) & "stack overflow");
            return;
         end if;
         M.State := Waiting;
      else
         Throw_Message
           (M, Budget, Position_Of (M, 1) & "attempt to call a " & Type_Name (M, Callee)
                       & " value");
      end if;
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
      Count   : constant Natural := Argument_Number (M, Place, Arguments);
      Last    : constant Stack_Size := M.Stack'Last;
      Callee  : constant Value := M.Stack (Place);
      Success : Boolean;
   begin
      Lemma_Frame (M, M.Depth);
      Lemma_Value (Objects (M), M.Stack.all, Place);
      if not Is_Callable (M, Callee) then
         Throw_Message
           (M, Budget, Position_Of (M, 1) & "attempt to call a " & Type_Name (M, Callee)
                       & " value");
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
     (M     : in out Machine;
      First : Natural;
      Count : Integer;
      Close : Boolean)
   is
      F     : constant Frame := M.Frames (M.Depth);
      Place : Positive;
      Size  : Natural;
   begin
      Lemma_Frame (M, M.Depth);
      Place := F.Func + 1 + First;
      Size :=
        (if Count >= 0 then Natural'Min (Count, M.Stack'Last + 1 - Place)
         elsif M.Top > Place then M.Top - Place
         else 0);
      if Close then
         Close_Upvalues (M.Heap, M.Open.all, M.Open_Count, M.Stack.all, F.Func + 1);
      end if;
      Finish_Return (M, Place, Size);
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
         Raise_Memory_Error (M);
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
               Raise_Memory_Error (M);
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
                      + Frame_Bytes * Initial_Frames + Base_Bytes * Byte_Count (Count), Success);
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
      Pyro.Heap.New_String (M.Heap, Budget, To_Bytes ("not enough memory"), Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         return;
      end if;
      Lemma_Heap_Live (M.Heap, Object_Value_Of (Handle));
      Store_Value (M.Registry.all, M.Heap, Memory_Place, Object_Value_Of (Handle));

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
      Call_At (M, Budget, 1, 0, -1);
      Success := M.State = Ready;
   end Load;

   procedure Register
     (M       : in out Machine;
      Budget  : in out Memory_Budget;
      Name    : String;
      Id      : Host_Id;
      Success : out Boolean)
   is
      Handle  : Object_Handle;
      Key     : Object_Handle;
      Status  : Pyro.Tables.Set_Status;
      Globals : constant Value := M.Registry (Globals_Place);
      Before  : Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Success := False;
      Lemma_Value (Objects (M), M.Registry.all, Globals_Place);
      Pyro.Heap.New_Object (M.Heap, Budget, Host_Function_Object, Natural (Id), 0, Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle = No_Object then
         return;
      end if;
      Before := Objects (M);
      Pyro.Heap.New_String (M.Heap, Budget, To_Bytes (Name), Key);
      Lemma_Roots_Grow (Before, M);
      if Key = No_Object then
         return;
      end if;
      Lemma_Value (Objects (M), M.Registry.all, Globals_Place);
      if Globals.Kind = Object_Value
        and then Pyro.Heap.Kind_Of (M.Heap, Globals.Object) = Table_Object
        and then Pyro.Heap.Kind_Of (M.Heap, Handle) = Host_Function_Object
      then
         Pyro.Heap.Table_Set
           (M.Heap, Budget, Globals.Object, Object_Value_Of (Key), Object_Value_Of (Handle),
            Status);
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
      Store_List (M.Stack.all, M.Heap, F.Func, Values);
      Finish_Return (M, F.Func, Values'Length);
   end Return_Values;

   procedure Raise_Error (M : in out Machine; Budget : in out Memory_Budget; Error : Value) is
      pragma Unreferenced (Budget);
   begin
      Lemma_Heap_Live (M.Heap, Error);
      M.State := Ready;
      Throw (M, Error);
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
      Store_List (M.Stack.all, M.Heap, F.Top + 1, Arguments);
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
      Before : constant Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
   begin
      Result := Nil;
      Success := False;
      Pyro.Heap.New_String (M.Heap, Budget, To_Bytes (Text), Handle);
      Lemma_Roots_Grow (Before, M);
      if Handle /= No_Object then
         Result := Object_Value_Of (Handle);
         Success := True;
      end if;
   end New_String;

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
      Free_Values (M.Constants);
      Free_Bases (M.Bases);
      Free_Values (M.Registry);
      Free_Values (M.Stack);
      Free_Frames (M.Frames);
      Free_Values (M.Open);
      M.State := Unloaded;
      M.Depth := 0;
   end Clear;

end Pyro.Virtual_Machine;
