--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Proven growable array: an owned heap array that doubles on demand, with a ghost sequence model.

with Ada.Unchecked_Deallocation;

package body Pyro.Growable_Arrays with SPARK_Mode => On is

   procedure Free is new Ada.Unchecked_Deallocation (Element_Array, Array_Access);

   --  Capacity of a first allocation.
   Initial_Capacity : constant := 16;

   --  The capacity currently allocated.
   function Capacity (Container : Growable_Array) return Extended_Index
   is (if Container.Data = null then 0 else Container.Data'Last);

   --  Bytes charged for a capacity.
   function Bytes_For (Capacity : Extended_Index) return Byte_Count
   is (Byte_Count (Capacity) * Element_Bytes)
   with Pre => Byte_Count (Capacity) <= Byte_Count'Last / Element_Bytes;

   function Model (Container : Growable_Array) return Models.Sequence is
      Result : Models.Sequence;
   begin
      for Position in 1 .. Container.Last loop
         Result := Models.Add (Result, Container.Data (Position));
         pragma Loop_Invariant (Models.Last (Result) = Position);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              Models.Get (Result, Earlier) = Container.Data (Earlier));
      end loop;
      return Result;
   end Model;

   --  Replaces a full (or absent) allocation with one about twice as large, keeping the
   --  elements.
   procedure Grow
     (Container : in out Growable_Array; Budget : in out Memory_Budget; Success : out Boolean)
   with
     Pre  => Container.Last = Capacity (Container) and then Container.Last < Index'Last,
     Post =>
       Limit (Budget) = Limit (Budget)'Old
       and then Container.Last = Container.Last'Old
       and then (for all Position in 1 .. Container.Last =>
                   Element (Container, Position) = Models.Get (Model (Container)'Old, Position))
       and then (if Success then Container.Last < Capacity (Container));

   procedure Grow
     (Container : in out Growable_Array; Budget : in out Memory_Budget; Success : out Boolean)
   is
      Old_Capacity : constant Extended_Index := Capacity (Container);
      New_Capacity : Index;
      New_Data     : Array_Access;
   begin
      if Old_Capacity = 0 then
         New_Capacity := Index'Min (Initial_Capacity, Index'Last);
      elsif Old_Capacity > Index'Last / 2 then
         New_Capacity := Index'Last;
      else
         New_Capacity := 2 * Old_Capacity;
      end if;
      Charge (Budget, Bytes_For (New_Capacity), Success);
      if not Success then
         return;
      end if;
      New_Data := new Element_Array'(1 .. New_Capacity => Default_Element);
      for Position in 1 .. Container.Last loop
         New_Data (Position) := Container.Data (Position);
         pragma Loop_Invariant (Container.Data /= null and then Container.Data'Last >= Position);
         pragma Loop_Invariant (New_Data'First = 1 and then New_Data'Last = New_Capacity);
         pragma Loop_Invariant
           (for all Earlier in 1 .. Position =>
              New_Data (Earlier) = Container.Data (Earlier));
      end loop;
      declare
         Old_Data : Array_Access := Container.Data;
      begin
         Container.Data := New_Data;
         Free (Old_Data);
      end;
      Release (Budget, Bytes_For (Old_Capacity));
   end Grow;

   procedure Append
     (Container : in out Growable_Array;
      New_Item  : Element_Type;
      Budget    : in out Memory_Budget;
      Success   : out Boolean) is
   begin
      if Container.Last = Index'Last then
         Success := False;
         return;
      end if;
      if Container.Last = Capacity (Container) then
         Grow (Container, Budget, Success);
         if not Success then
            return;
         end if;
      end if;
      Container.Last := Container.Last + 1;
      Container.Data (Container.Last) := New_Item;
      Success := True;
   end Append;

   procedure Replace_Element
     (Container : in out Growable_Array; Position : Index; New_Item : Element_Type) is
   begin
      Container.Data (Position) := New_Item;
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
      Old_Capacity : constant Extended_Index := Capacity (Container);
   begin
      Container.Last := 0;
      Free (Container.Data);
      Release (Budget, Bytes_For (Old_Capacity));
   end Clear;

end Pyro.Growable_Arrays;
