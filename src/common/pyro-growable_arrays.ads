--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Proven growable array: owned heap chunks added on demand, with a ghost sequence model.

with Pyro.Memory_Budgets; use Pyro.Memory_Budgets;
with SPARK.Containers.Functional.Vectors;

generic
   --  Positions in the array. The first position is 1, and the last value of the type is the
   --  largest length the array may reach, which bounds the memory it can use.
   type Index is range <>;

   --  The stored elements.
   type Element_Type is private;

   --  Value used to fill capacity that does not hold an element yet.
   Default_Element : Element_Type;

   --  Bytes one element occupies, charged to the memory budget for each unit of capacity.
   Element_Bytes : Byte_Count;

package Pyro.Growable_Arrays with SPARK_Mode => On, Always_Terminates is

   pragma Compile_Time_Error (Index'First /= 1, "growable array indices must start at 1");
   pragma Compile_Time_Error (Element_Bytes = 0, "elements must occupy memory");
   pragma Compile_Time_Error
     (Byte_Count (Index'Last) > Byte_Count'Last / Element_Bytes,
      "the largest array must have a size in bytes that fits Byte_Count");

   --  A length: 0 for an empty array, up to Index'Last.
   subtype Extended_Index is Index'Base range 0 .. Index'Last;

   --  An array of elements that grows as elements are appended. It owns heap memory, so it
   --  must be released with Clear before it goes out of scope.
   type Growable_Array is limited private
   with
     Default_Initial_Condition =>
       Length (Growable_Array) = 0 and then Is_Released (Growable_Array);

   --  The number of elements stored.
   function Length (Container : Growable_Array) return Extended_Index
   with Global => null;

   --  The element at Position.
   function Element (Container : Growable_Array; Position : Index) return Element_Type
   with Global => null, Pre => Position <= Length (Container);

   --  Ghost view of the contents as a sequence. Pyro stores only elements whose predefined
   --  equality is logical equality (no floating-point components: floats are kept as bits).
   package Models is new SPARK.Containers.Functional.Vectors
     (Index_Type => Index, Element_Type => Element_Type, Use_Logical_Equality => True);
   use type Models.Sequence;

   --  [proof] The contents as a sequence, so postconditions can say what is preserved.
   function Model (Container : Growable_Array) return Models.Sequence
   with
     Ghost,
     Global => null,
     Post   =>
       Models.Last (Model'Result) = Length (Container)
       and then (for all Position in 1 .. Length (Container) =>
                   Models.Get (Model'Result, Position) = Element (Container, Position));

   --  Adds New_Item after the last element. When the array is full, its capacity grows, and the
   --  new memory is charged to Budget first. Fails, leaving the array unchanged, when the array
   --  already holds Index'Last elements or Budget cannot pay for the growth.
   procedure Append
     (Container : in out Growable_Array;
      New_Item  : Element_Type;
      Budget    : in out Memory_Budget;
      Success   : out Boolean)
   with
     Global => null,
     Post   =>
       Limit (Budget) = Limit (Budget)'Old
       and then (if Success
                 then Length (Container)'Old < Index'Last
                      and then Length (Container) = Length (Container)'Old + 1
                      and then Element (Container, Length (Container)) = New_Item
                      and then Model (Container)'Old < Model (Container)
                 else Model (Container) = Model (Container)'Old);

   --  Replaces the element at Position.
   procedure Replace_Element
     (Container : in out Growable_Array; Position : Index; New_Item : Element_Type)
   with
     Global => null,
     Pre    => Position <= Length (Container),
     Post   =>
       Length (Container) = Length (Container)'Old
       and then Element (Container, Position) = New_Item
       and then (for all Other in 1 .. Length (Container) =>
                   (if Other /= Position
                    then Element (Container, Other) = Models.Get (Model (Container)'Old, Other)));

   --  Removes the elements after New_Length. The memory is kept for reuse.
   procedure Truncate (Container : in out Growable_Array; New_Length : Extended_Index)
   with
     Global => null,
     Pre    => New_Length <= Length (Container),
     Post   =>
       Length (Container) = New_Length
       and then Model (Container) <= Model (Container)'Old;

   --  Exchanges the contents (and memory) of Left and Right.
   procedure Swap (Left, Right : in out Growable_Array)
   with
     Global => null,
     Post   =>
       Length (Left) = Length (Right)'Old
       and then Length (Right) = Length (Left)'Old
       and then Model (Left) = Model (Right)'Old
       and then Model (Right) = Model (Left)'Old
       and then Is_Released (Left) = Is_Released (Right)'Old
       and then Is_Released (Right) = Is_Released (Left)'Old;

   --  Removes every element, frees the memory and releases it from Budget.
   procedure Clear (Container : in out Growable_Array; Budget : in out Memory_Budget)
   with
     Global => null,
     Post   =>
       Length (Container) = 0
       and then Is_Released (Container)
       and then Limit (Budget) = Limit (Budget)'Old;

   --  True when the array holds no heap memory, which is what SPARK requires of an owner
   --  before it goes out of scope.
   function Is_Released (Container : Growable_Array) return Boolean
   with Global => null;

private

   --  The elements live in chunks of Chunk_Length elements (about 1 MiB): growing adds a chunk,
   --  so elements are never copied and memory is never doubled. The first chunk is apart: it
   --  starts small and doubles up to Chunk_Length, so small arrays stay small. The other chunks
   --  are found through a table allocated once, at its full size, when the second is needed.
   Chunk_Length : constant Index :=
     Index (Byte_Count'Max (16, Byte_Count'Min (2 ** 20 / Element_Bytes,
                                                Byte_Count (Index'Last))));

   --  Chunks after the first, at most.
   Maximum_Chunks : constant Natural := Natural (Index'Last / Chunk_Length);

   --  The chunk (0 for the first) and the place in it (from 1) of Position.
   function Chunk_Of (Position : Index) return Natural
   is (Natural ((Position - 1) / Chunk_Length))
   with Post => Chunk_Of'Result <= Maximum_Chunks;

   function Offset_Of (Position : Index) return Index
   is ((Position - 1) mod Chunk_Length + 1)
   with Post => Offset_Of'Result <= Chunk_Length;

   type Element_Array is array (Index range <>) of Element_Type;
   type Chunk_Access is access Element_Array;
   type Chunk_Table is array (Positive range <>) of Chunk_Access;
   type Table_Access is access Chunk_Table;

   --  Whether every position up to the length has its place: the invariant of the type.
   function All_Allocated (Container : Growable_Array) return Boolean;

   --  Every access checks that its chunk is there: a place without a chunk reads as
   --  Default_Element, as a new chunk's places do. The invariant is that every element has
   --  its place.
   type Growable_Array is record
      First : Chunk_Access := null;
      Table : Table_Access := null;
      Last  : Extended_Index := 0;
   end record
   with Type_Invariant => All_Allocated (Growable_Array);

   --  Whether position Position has an allocated place (every position up to Last has one).
   function Allocated (Container : Growable_Array; Position : Index) return Boolean
   is (if Chunk_Of (Position) = 0
       then Container.First /= null and then Offset_Of (Position) in Container.First'Range
       else Container.Table /= null
            and then Chunk_Of (Position) in Container.Table'Range
            and then Container.Table (Chunk_Of (Position)) /= null
            and then Offset_Of (Position) in Container.Table (Chunk_Of (Position))'Range);

   function Length (Container : Growable_Array) return Extended_Index is (Container.Last);

   function All_Allocated (Container : Growable_Array) return Boolean
   is (for all Position in 1 .. Container.Last => Allocated (Container, Position));

   function Element (Container : Growable_Array; Position : Index) return Element_Type
   is (if not Allocated (Container, Position) then Default_Element
       elsif Chunk_Of (Position) = 0 then Container.First (Offset_Of (Position))
       else Container.Table (Chunk_Of (Position)) (Offset_Of (Position)));

   function Is_Released (Container : Growable_Array) return Boolean
   is (Container.First = null and then Container.Table = null);

   --  Clients reason through Model and the contracts: the chunks stay out of their proofs.
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Allocated);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", All_Allocated);
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Element);

end Pyro.Growable_Arrays;
