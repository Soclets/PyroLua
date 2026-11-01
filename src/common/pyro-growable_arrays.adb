--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Proven growable array: owned heap chunks added on demand, with a ghost sequence model.

with Ada.Unchecked_Deallocation;

package body Pyro.Growable_Arrays with SPARK_Mode => On is

   procedure Free_Chunk is new Ada.Unchecked_Deallocation (Element_Array, Chunk_Access);
   procedure Free_Table is new Ada.Unchecked_Deallocation (Chunk_Table, Table_Access);

   --  Length of a first allocation of the first chunk.
   Initial_Length : constant Index := Index'Min (16, Chunk_Length);

   --  Elements in a chunk, as a byte count.
   Chunk_Bytes : constant Byte_Count := Byte_Count (Chunk_Length);

   --  Bytes charged for one entry of the chunk table (a pointer to an unconstrained array).
   Entry_Bytes : constant Byte_Count := 16;

   --  [proof] Positions differ exactly when their chunk or their place in it differs: the
   --  provers derive it from Position - 1 = Chunk_Length * Chunk_Of + Offset_Of - 1.
   procedure Lemma_Distinct (Left, Right : Index)
   with
     Ghost,
     Global => null,
     Pre    => Left /= Right,
     Post   => Chunk_Of (Left) /= Chunk_Of (Right) or else Offset_Of (Left) /= Offset_Of (Right)
   is
   begin
      pragma Assert
        (Left - 1 = Chunk_Length * Index'Base (Chunk_Of (Left)) + Offset_Of (Left) - 1);
      pragma Assert
        (Right - 1 = Chunk_Length * Index'Base (Chunk_Of (Right)) + Offset_Of (Right) - 1);
   end Lemma_Distinct;

   --  [proof] The positions other than Position have another chunk or place.
   procedure Lemma_Others (Position : Index; Last : Extended_Index)
   with
     Ghost,
     Global => null,
     Post   =>
       (for all Other in 1 .. Last =>
          (if Other /= Position
           then Chunk_Of (Other) /= Chunk_Of (Position)
                or else Offset_Of (Other) /= Offset_Of (Position)))
   is
   begin
      for Other in 1 .. Last loop
         if Other /= Position then
            Lemma_Distinct (Other, Position);
         end if;
         pragma Loop_Invariant
           (for all Earlier in 1 .. Other =>
              (if Earlier /= Position
               then Chunk_Of (Earlier) /= Chunk_Of (Position)
                    or else Offset_Of (Earlier) /= Offset_Of (Position)));
      end loop;
   end Lemma_Others;

   function Model (Container : Growable_Array) return Models.Sequence is
      Result : Models.Sequence;
   begin
      for Position in 1 .. Container.Last loop
         Result := Models.Add (Result, Element (Container, Position));
         pragma Loop_Invariant (Models.Last (Result) = Position);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              Models.Get (Result, Earlier) = Element (Container, Earlier));
      end loop;
      return Result;
   end Model;

   --  Replaces the first chunk with one twice as long (up to Chunk_Length), or allocates it,
   --  keeping every element: the places it gains read Default_Element before and after.
   procedure Grow_First
     (Container : in out Growable_Array; Budget : in out Memory_Budget; Success : out Boolean)
   with
     Pre  => All_Allocated (Container),
     Post =>
       All_Allocated (Container)
       and then
       Limit (Budget) = Limit (Budget)'Old
       and then Container.Last = Container.Last'Old
       and then (for all Position in 1 .. Models.Last (Model (Container)'Old) =>
                   Element (Container, Position) = Models.Get (Model (Container)'Old, Position))
   is
      Old_Length : constant Extended_Index :=
        (if Container.First = null or else Container.First'First /= 1
            or else Container.First'Last < 1
         then 0
         elsif Container.First'Last > Chunk_Length then Chunk_Length
         else Container.First'Last);
      New_Length : constant Index :=
        (if Old_Length = 0 then Initial_Length
         elsif Old_Length > Chunk_Length / 2 then Chunk_Length
         else 2 * Old_Length);
      New_Chunk  : Chunk_Access;
      Old_Chunk  : Chunk_Access;
   begin
      Charge (Budget, Element_Bytes * Byte_Count (New_Length), Success);
      if not Success then
         return;
      end if;
      New_Chunk := new Element_Array'(1 .. New_Length => Default_Element);
      pragma Assert (New_Chunk'First = 1 and then New_Chunk'Last = New_Length);
      pragma Assert (New_Length >= Old_Length);
      if Container.First /= null then
         for Position in 1 .. Old_Length loop
            if Position in Container.First'Range then
               New_Chunk (Position) := Container.First (Position);
            end if;
            pragma Loop_Invariant (New_Chunk'First = 1 and then New_Chunk'Last = New_Length);
            pragma Loop_Invariant
              (for all Earlier in 1 .. Position =>
                 New_Chunk (Earlier)
                 = (if Earlier in Container.First'Range then Container.First (Earlier)
                    else Default_Element));
            pragma Loop_Invariant
              (for all Later in 1 .. New_Length =>
                 (if Later > Position then New_Chunk (Later) = Default_Element));
         end loop;
      end if;
      Old_Chunk := Container.First;
      Container.First := New_Chunk;
      if Old_Chunk /= null then
         Release (Budget, Element_Bytes * Byte_Count'Min (Old_Chunk'Length, Chunk_Bytes));
      end if;
      Free_Chunk (Old_Chunk);
   end Grow_First;

   --  Allocates chunk Chunk (after the first), and the table first if needed, keeping every
   --  element: the chunk's places read Default_Element before and after.
   procedure Add_Chunk
     (Container : in out Growable_Array;
      Chunk     : Positive;
      Budget    : in out Memory_Budget;
      Success   : out Boolean)
   with
     Pre  => All_Allocated (Container),
     Post =>
       All_Allocated (Container)
       and then
       Limit (Budget) = Limit (Budget)'Old
       and then Container.Last = Container.Last'Old
       and then (for all Position in 1 .. Models.Last (Model (Container)'Old) =>
                   Element (Container, Position) = Models.Get (Model (Container)'Old, Position))
   is
      New_Chunk : Chunk_Access;
   begin
      if Container.Table = null then
         Charge (Budget, Entry_Bytes * Byte_Count (Maximum_Chunks), Success);
         if not Success then
            return;
         end if;
         Container.Table := new Chunk_Table'(1 .. Maximum_Chunks => null);
      end if;
      if Chunk not in Container.Table'Range or else Container.Table (Chunk) /= null then
         --  Not reached: the table has a place for every chunk, and a chunk there has room.
         Success := False;
         return;
      end if;
      Charge (Budget, Element_Bytes * Byte_Count (Chunk_Length), Success);
      if not Success then
         return;
      end if;
      New_Chunk := new Element_Array'(1 .. Chunk_Length => Default_Element);
      pragma Assert (Container.Table /= null and then Container.Table (Chunk) = null);
      Container.Table (Chunk) := New_Chunk;
   end Add_Chunk;

   procedure Append
     (Container : in out Growable_Array;
      New_Item  : Element_Type;
      Budget    : in out Memory_Budget;
      Success   : out Boolean)
   is
      Old_Model : constant Models.Sequence := Model (Container) with Ghost;
      Target    : Index;
   begin
      if Container.Last = Index'Last then
         Success := False;
         return;
      end if;
      Target := Container.Last + 1;
      if not Allocated (Container, Target) then
         if Chunk_Of (Target) = 0 then
            Grow_First (Container, Budget, Success);
         else
            Add_Chunk (Container, Chunk_Of (Target), Budget, Success);
         end if;
         --  Every element is kept.
         pragma Assert
           (for all Position in 1 .. Container.Last =>
              Element (Container, Position) = Models.Get (Old_Model, Position));
         if not Success or else not Allocated (Container, Target) then
            --  The second test is never true: growing gives position Target its place.
            Success := False;
            return;
         end if;
      end if;
      Lemma_Others (Target, Container.Last);
      if Chunk_Of (Target) = 0 then
         Container.First (Offset_Of (Target)) := New_Item;
      else
         Container.Table (Chunk_Of (Target)) (Offset_Of (Target)) := New_Item;
      end if;
      Container.Last := Target;
      Success := True;
   end Append;

   procedure Replace_Element
     (Container : in out Growable_Array; Position : Index; New_Item : Element_Type) is
   begin
      Lemma_Others (Position, Container.Last);
      if not Allocated (Container, Position) then
         --  Not reached: every position up to Length has its place.
         return;
      end if;
      if Chunk_Of (Position) = 0 then
         Container.First (Offset_Of (Position)) := New_Item;
      else
         Container.Table (Chunk_Of (Position)) (Offset_Of (Position)) := New_Item;
      end if;
   end Replace_Element;

   procedure Truncate (Container : in out Growable_Array; New_Length : Extended_Index) is
   begin
      Container.Last := New_Length;
   end Truncate;

   procedure Swap (Left, Right : in out Growable_Array) is
      Held : Growable_Array;
   begin
      Held := Left;
      Left := Right;
      Right := Held;
   end Swap;

   procedure Clear (Container : in out Growable_Array; Budget : in out Memory_Budget) is
   begin
      Container.Last := 0;
      if Container.Table /= null then
         --  Each chunk and the table are released as they are freed.
         for Position in Container.Table'Range loop
            if Container.Table (Position) /= null then
               Release
                 (Budget,
                  Element_Bytes * Byte_Count'Min (Container.Table (Position)'Length,
                                                  Chunk_Bytes));
            end if;
            Free_Chunk (Container.Table (Position));
            pragma Loop_Invariant (Limit (Budget) = Limit (Budget)'Loop_Entry);
            pragma Loop_Invariant
              (for all Earlier in Container.Table'First .. Position =>
                 Container.Table (Earlier) = null);
         end loop;
         Release
           (Budget, Entry_Bytes * Byte_Count'Min (Container.Table'Length,
                                                  Byte_Count (Maximum_Chunks)));
         Free_Table (Container.Table);
      end if;
      if Container.First /= null then
         Release
           (Budget, Element_Bytes * Byte_Count'Min (Container.First'Length, Chunk_Bytes));
      end if;
      Free_Chunk (Container.First);
   end Clear;

end Pyro.Growable_Arrays;
