--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  [puc lgc.c] The garbage collector: stop-the-world mark and sweep over the heap.

with Pyro.Graph_Sequences;
with Pyro.Handle_Sequences;
with Pyro.Heap;           use Pyro.Heap;
with Pyro.Kind_Sequences;
with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with Pyro.Value_Sequences;
with Pyro.Values;         use Pyro.Values;

package Pyro.Garbage_Collector with SPARK_Mode => On, Always_Terminates is

   use type Graph_Sequences.Sequence;
   use type Kind_Sequences.Sequence;
   use type Value_Sequences.Sequence;

   --  The values the collector starts from: what the program can still use.
   type Root_Array is array (Positive range <>) of Value;

   --  [proof] Every object Roots refers to is one K shows.
   function Roots_Live (K : Kind_Sequences.Sequence; Roots : Root_Array) return Boolean
   is (for all R in Roots'Range => Live_In (K, Roots (R)))
   with Ghost;

   --  [proof] P is a path in G from the roots: its first object is one Roots refers to, and
   --  each next one is a child (in G) of the one before.
   function Is_Path
     (G : Graph_Sequences.Sequence; Roots : Root_Array; P : Handle_Sequences.Sequence)
     return Boolean
   is (Handle_Sequences.Last (P) >= 1
       and then (for some R in Roots'Range =>
                   Roots (R).Kind = Object_Value
                   and then Roots (R).Object = Handle_Sequences.Get (P, 1))
       and then (for all I in 1 .. Handle_Sequences.Last (P) - 1 =>
                   Handle_Sequences.Get (P, I) <= Graph_Sequences.Last (G)
                   and then
                     (for some Position in
                        1 .. Value_Sequences.Last
                               (Graph_Sequences.Get (G, Handle_Sequences.Get (P, I))) =>
                        Value_Sequences.Get
                          (Graph_Sequences.Get (G, Handle_Sequences.Get (P, I)), Position).Kind
                        = Object_Value
                        and then Value_Sequences.Get
                                   (Graph_Sequences.Get (G, Handle_Sequences.Get (P, I)),
                                    Position).Object
                                 = Handle_Sequences.Get (P, I + 1))))
   with Ghost;

   --  [proof] What K2 keeps of K1, with K1's children in G1: every object K2 shows is one K1
   --  showed, of the same kind, and its children are objects K2 shows.
   function Keeps_Closed
     (K1 : Kind_Sequences.Sequence;
      G1 : Graph_Sequences.Sequence;
      K2 : Kind_Sequences.Sequence) return Boolean
   is (Kind_Sequences.Last (K2) = Kind_Sequences.Last (K1)
       and then Graph_Sequences.Last (G1) = Kind_Sequences.Last (K1)
       and then (for all Handle in 1 .. Kind_Sequences.Last (K1) =>
                   (if Kind_Sequences.Get (K2, Handle) /= Free_Object
                    then Kind_Sequences.Get (K2, Handle) = Kind_Sequences.Get (K1, Handle)
                         and then (for all Position in
                                     1 .. Value_Sequences.Last (Graph_Sequences.Get (G1, Handle)) =>
                                     Live_In (K2, Value_Sequences.Get
                                                    (Graph_Sequences.Get (G1, Handle),
                                                     Position))))))
   with Ghost;

   --  [proof] The collector never frees a reachable object: when K2 keeps of K1 what
   --  Keeps_Closed says, and every root, every object on a path from the roots is kept,
   --  with its kind.
   procedure Lemma_Path_Kept
     (K1    : Kind_Sequences.Sequence;
      G1    : Graph_Sequences.Sequence;
      K2    : Kind_Sequences.Sequence;
      Roots : Root_Array;
      P     : Handle_Sequences.Sequence)
   with
     Ghost,
     Global => null,
     Pre    => Keeps_Closed (K1, G1, K2) and then Roots_Live (K2, Roots)
               and then Is_Path (G1, Roots, P),
     Post   =>
       Handle_Sequences.Get (P, Handle_Sequences.Last (P)) <= Kind_Sequences.Last (K2)
       and then Kind_Sequences.Get (K2, Handle_Sequences.Get (P, Handle_Sequences.Last (P)))
                /= Free_Object
       and then Kind_Sequences.Get (K2, Handle_Sequences.Get (P, Handle_Sequences.Last (P)))
                = Kind_Sequences.Get (K1, Handle_Sequences.Get (P, Handle_Sequences.Last (P)));

   --  [puc lgc.c:fullgc] Frees the objects that cannot be reached from Roots: marks what
   --  can (with the gray list, no recursion), then sweeps the rest. Complete is False when
   --  marking could not finish, and then nothing is freed. What is kept, Keeps_Closed says;
   --  Lemma_Path_Kept turns it into "every reachable object is kept".
   procedure Collect
     (H        : in out Pyro.Heap.Heap;
      Budget   : in out Memory_Budget;
      Roots    : Root_Array;
      Complete : out Boolean)
   with
     Global => null,
     Pre    => Is_Valid (H) and then (for all R in Roots'Range => Is_Live (H, Roots (R))),
     Post   =>
       Is_Valid (H)
       and then Limit (Budget) = Limit (Budget)'Old
       and then Roots_Live (Kinds (H), Roots)
       and then Keeps_Closed (Kinds (H)'Old, Graph (H)'Old, Kinds (H))
       and then (for all Handle in 1 .. Slot_Count (H) =>
                   (if Kind_Of (H, Handle) /= Free_Object
                    then Children (H, Handle) = Graph_Sequences.Get (Graph (H)'Old, Handle)))
       and then (if not Complete then Kinds (H) = Kinds (H)'Old);

end Pyro.Garbage_Collector;
