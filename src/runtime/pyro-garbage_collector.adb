--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [puc lgc.c] The garbage collector: stop-the-world mark and sweep over the heap.

package body Pyro.Garbage_Collector with SPARK_Mode => On is

   --  [proof] The tricolour invariant: every child of a black object (in C, with the children
   --  of G) is an object that is not white.
   function Black_Closed (C : Color_Sequences.Sequence; G : Graph_Sequences.Sequence)
     return Boolean
   is (for all Handle in 1 .. Graph_Sequences.Last (G) =>
         (if Handle <= Color_Sequences.Last (C) and then Color_Sequences.Get (C, Handle) = Black
          then (for all Position in 1 .. Value_Sequences.Last (Graph_Sequences.Get (G, Handle)) =>
                  Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position).Kind
                  /= Object_Value
                  or else
                    (Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position).Object
                     in 1 .. Color_Sequences.Last (C)
                     and then Color_Sequences.Get
                                (C, Value_Sequences.Get
                                      (Graph_Sequences.Get (G, Handle), Position).Object)
                              /= White))))
   with Ghost;

   --  [proof] No object of C is gray.
   function No_Gray (C : Color_Sequences.Sequence) return Boolean
   is (for all Handle in 1 .. Color_Sequences.Last (C) => Color_Sequences.Get (C, Handle) /= Gray)
   with Ghost;

   --  [proof] Every object Before shows not white, After shows not white, and After shows black
   --  only what Before showed black or Grown: what shading and blackening do.
   function Grows (Before, After : Color_Sequences.Sequence; Grown : Object_Handle)
     return Boolean
   is (Color_Sequences.Last (After) = Color_Sequences.Last (Before)
       and then (for all Handle in 1 .. Color_Sequences.Last (Before) =>
                   (if Color_Sequences.Get (Before, Handle) /= White
                    then Color_Sequences.Get (After, Handle) /= White)
                   and then (if Handle /= Grown and then Color_Sequences.Get (After, Handle) = Black
                             then Color_Sequences.Get (Before, Handle) = Black)))
   with Ghost;

   --  [proof] Child Position of object Handle in G is not white in C.
   function Child_Marked
     (C : Color_Sequences.Sequence; G : Graph_Sequences.Sequence; Handle : Valid_Handle;
      Position : Positive) return Boolean
   is (Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position).Kind /= Object_Value
       or else
         (Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position).Object
          in 1 .. Color_Sequences.Last (C)
          and then Color_Sequences.Get
                     (C, Value_Sequences.Get (Graph_Sequences.Get (G, Handle), Position).Object)
                   /= White))
   with
     Ghost,
     Pre => Handle <= Graph_Sequences.Last (G)
            and then Position <= Value_Sequences.Last (Graph_Sequences.Get (G, Handle));

   --  [proof] Colours that only grow keep the tricolour invariant, when the one object that
   --  turns black has every child marked.
   procedure Lemma_Grows
     (Before, After : Color_Sequences.Sequence;
      G             : Graph_Sequences.Sequence;
      Grown         : Object_Handle)
   with
     Ghost,
     Global => null,
     Pre    =>
       Black_Closed (Before, G)
       and then Grows (Before, After, Grown)
       and then (if Grown in 1 .. Graph_Sequences.Last (G)
                 then (for all Position in
                         1 .. Value_Sequences.Last (Graph_Sequences.Get (G, Grown)) =>
                         Child_Marked (After, G, Grown, Position))),
     Post   => Black_Closed (After, G)
   is
   begin
      null;
   end Lemma_Grows;

   procedure Lemma_Path_Kept
     (K1    : Kind_Sequences.Sequence;
      G1    : Graph_Sequences.Sequence;
      K2    : Kind_Sequences.Sequence;
      Roots : Root_Array;
      P     : Handle_Sequences.Sequence)
   is
      Last : constant Positive := Handle_Sequences.Last (P);
   begin
      for I in 1 .. Last loop
         if I = 1 then
            pragma Assert
              (for some R in Roots'Range =>
                 Roots (R).Kind = Object_Value
                 and then Roots (R).Object = Handle_Sequences.Get (P, 1)
                 and then Live_In (K2, Roots (R)));
         else
            --  The child of the object before, which is kept, so its children are.
            pragma Assert
              (for some Position in
                 1 .. Value_Sequences.Last
                        (Graph_Sequences.Get (G1, Handle_Sequences.Get (P, I - 1))) =>
                 Value_Sequences.Get
                   (Graph_Sequences.Get (G1, Handle_Sequences.Get (P, I - 1)), Position).Object
                 = Handle_Sequences.Get (P, I)
                 and then Value_Sequences.Get
                            (Graph_Sequences.Get (G1, Handle_Sequences.Get (P, I - 1)),
                             Position).Kind = Object_Value
                 and then Live_In
                            (K2, Value_Sequences.Get
                                   (Graph_Sequences.Get (G1, Handle_Sequences.Get (P, I - 1)),
                                    Position)));
         end if;
         pragma Loop_Invariant
           (for all Earlier in 1 .. I =>
              Handle_Sequences.Get (P, Earlier) <= Kind_Sequences.Last (K2)
              and then Kind_Sequences.Get (K2, Handle_Sequences.Get (P, Earlier)) /= Free_Object
              and then Kind_Sequences.Get (K2, Handle_Sequences.Get (P, Earlier))
                       = Kind_Sequences.Get (K1, Handle_Sequences.Get (P, Earlier)));
      end loop;
   end Lemma_Path_Kept;

   --  [proof] Freeing the objects C shows white, when the others are closed under children,
   --  keeps what Keeps_Closed says.
   procedure Lemma_Swept
     (K1, K2 : Kind_Sequences.Sequence;
      G      : Graph_Sequences.Sequence;
      C      : Color_Sequences.Sequence)
   with
     Ghost,
     Global => null,
     Pre    =>
       Graph_Live (K1, G)
       and then Closed (C, G)
       and then Graph_Sequences.Last (G) = Kind_Sequences.Last (K1)
       and then Color_Sequences.Last (C) = Kind_Sequences.Last (K1)
       and then Kind_Sequences.Last (K2) = Kind_Sequences.Last (K1)
       and then (for all Handle in 1 .. Kind_Sequences.Last (K1) =>
                   Kind_Sequences.Get (K2, Handle)
                   = (if Color_Sequences.Get (C, Handle) = White then Free_Object
                      else Kind_Sequences.Get (K1, Handle))),
     Post   => Keeps_Closed (K1, G, K2)
   is
   begin
      null;
   end Lemma_Swept;

   --  [proof] Freeing nothing keeps what Keeps_Closed says.
   procedure Lemma_Unchanged (K : Kind_Sequences.Sequence; G : Graph_Sequences.Sequence)
   with
     Ghost,
     Global => null,
     Pre    => Graph_Live (K, G) and then Graph_Sequences.Last (G) = Kind_Sequences.Last (K),
     Post   => Keeps_Closed (K, G, K)
   is
   begin
      null;
   end Lemma_Unchanged;

   function Marking (H : Pyro.Heap.Heap) return Boolean
   is (Black_Closed (Colors (H), Graph (H)));

   procedure Start (H : in out Pyro.Heap.Heap) is
   begin
      Whiten (H);
      pragma Assert (Black_Closed (Colors (H), Graph (H)));
   end Start;

   procedure Mark_Roots (H : in out Pyro.Heap.Heap; Roots : Root_Array) is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0 : constant Color_Sequences.Sequence := Colors (H) with Ghost;
      C  : Color_Sequences.Sequence with Ghost;
   begin
      for R in Roots'Range loop
         if Roots (R).Kind = Object_Value then
            C := Colors (H);
            Shade (H, Roots (R).Object);
            Lemma_Grows (C, Colors (H), G0, No_Object);
         end if;
         pragma Loop_Invariant (Is_Valid (H) and then Kinds (H) = K0 and then Graph (H) = G0);
         pragma Loop_Invariant (Black_Closed (Colors (H), G0));
         pragma Loop_Invariant (Grown (C0, Colors (H)));
         pragma Loop_Invariant
           (for all Earlier in Roots'First .. R =>
              Roots (Earlier).Kind /= Object_Value
              or else Color_Of (H, Roots (Earlier).Object) /= White);
      end loop;
   end Mark_Roots;

   --  Blackens gray objects until none is left, shading their children first. Complete is
   --  False when the gray list ran past one entry per object (it cannot, since an object is
   --  put on it only when it turns gray) or a gray object was left off it; then some object
   --  that can be reached may be white.
   procedure Propagate (H : in out Pyro.Heap.Heap; Complete : out Boolean)
   with
     Global => null,
     Pre    => Is_Valid (H) and then Marking (H),
     Post   =>
       Is_Valid (H)
       and then Kinds (H) = Kinds (H)'Old
       and then Graph (H) = Graph (H)'Old
       and then Grown (Colors (H)'Old, Colors (H))
       and then (if Complete then Closed (Colors (H), Graph (H)))
   is
      K0   : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0   : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0   : constant Color_Sequences.Sequence := Colors (H) with Ghost;
      C    : Color_Sequences.Sequence with Ghost;
      Fuel : Natural := Natural (Slot_Count (H)) + 1;
      Next : Object_Handle;
      Item : Value;
   begin
      Complete := False;
      loop
         pragma Loop_Invariant (Is_Valid (H) and then Kinds (H) = K0 and then Graph (H) = G0);
         pragma Loop_Invariant (Black_Closed (Colors (H), G0));
         pragma Loop_Invariant (Grown (C0, Colors (H)));
         pragma Loop_Variant (Decreases => Fuel);
         Take_Gray (H, Next);
         exit when Next = No_Object or else Fuel = 0;
         Fuel := Fuel - 1;
         for Position in 1 .. Child_Count (H, Next) loop
            Item := Child_At (H, Next, Position);
            if Item.Kind = Object_Value then
               C := Colors (H);
               Shade (H, Item.Object);
               Lemma_Grows (C, Colors (H), G0, No_Object);
            end if;
            pragma Loop_Invariant (Is_Valid (H) and then Kinds (H) = K0 and then Graph (H) = G0);
            pragma Loop_Invariant (Black_Closed (Colors (H), G0));
            pragma Loop_Invariant (Grown (C0, Colors (H)));
            pragma Loop_Invariant (Kind_Of (H, Next) /= Free_Object);
            pragma Loop_Invariant
              (for all Earlier in 1 .. Position => Child_Marked (Colors (H), G0, Next, Earlier));
         end loop;
         C := Colors (H);
         Blacken (H, Next);
         Lemma_Grows (C, Colors (H), G0, Next);
      end loop;
      if Fuel = 0 and then Next /= No_Object then
         return;
      end if;

      --  The gray list is empty: check that no object is gray.
      for Handle in 1 .. Slot_Count (H) loop
         if Color_Of (H, Handle) = Gray then
            return;
         end if;
         pragma Loop_Invariant
           (for all Earlier in 1 .. Handle => Color_Of (H, Earlier) /= Gray);
      end loop;
      pragma Assert (No_Gray (Colors (H)));
      Complete := True;
   end Propagate;

   procedure Finish
     (H        : in out Pyro.Heap.Heap;
      Budget   : in out Memory_Budget;
      Complete : out Boolean)
   is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
      G0 : constant Graph_Sequences.Sequence := Graph (H) with Ghost;
      C0 : constant Color_Sequences.Sequence := Colors (H) with Ghost;
      C  : Color_Sequences.Sequence with Ghost;
   begin
      Lemma_Graph_Live (H);
      pragma Assert (Graph_Live (K0, G0));
      Propagate (H, Complete);
      if Complete then
         C := Colors (H);
         pragma Assert (Closed (C, G0));
         pragma Assert (Grown (C0, C));
         Sweep (H, Budget);
         pragma Assert
           (for all Handle in 1 .. Slot_Count (H) =>
              Kind_Sequences.Get (Kinds (H), Handle)
              = (if Color_Sequences.Get (C, Handle) = White then Free_Object
                 else Kind_Sequences.Get (K0, Handle)));
         Lemma_Swept (K0, Kinds (H), G0, C);
      else
         Whiten (H);
         Lemma_Unchanged (K0, G0);
      end if;
   end Finish;

   procedure Collect
     (H        : in out Pyro.Heap.Heap;
      Budget   : in out Memory_Budget;
      Roots    : Root_Array;
      Complete : out Boolean)
   is
      K0 : constant Kind_Sequences.Sequence := Kinds (H) with Ghost;
   begin
      pragma Assert (Roots_Live (K0, Roots));
      Start (H);
      Mark_Roots (H, Roots);
      pragma Assert
        (for all R in Roots'Range =>
           Roots (R).Kind /= Object_Value
           or else Color_Sequences.Get (Colors (H), Roots (R).Object) /= White);
      Finish (H, Budget, Complete);
   end Collect;

end Pyro.Garbage_Collector;
