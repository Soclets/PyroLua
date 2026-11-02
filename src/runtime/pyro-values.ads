--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua values: nil, booleans, integers, floats (as their bits) and handles to heap objects.

with Interfaces; use Interfaces;
with Pyro.Integer_Arithmetic;

package Pyro.Values with SPARK_Mode => On, Always_Terminates is

   --  The most heap objects that can exist at once.
   Maximum_Objects : constant := 2 ** 26 - 1;

   --  A heap object, by its slot in the heap; No_Object for none.
   type Object_Handle is range 0 .. Maximum_Objects;
   No_Object : constant Object_Handle := 0;
   subtype Valid_Handle is Object_Handle range 1 .. Object_Handle'Last;

   --  What a heap slot holds. A free slot holds nothing.
   type Object_Kind is (Free_Object, String_Object, Table_Object);

   --  The collector's mark of a heap object: white when not reached (yet), gray when reached
   --  with its children still to visit, black when they have been.
   type Object_Color is (White, Gray, Black);

   type Value_Kind is (Nil_Value, Boolean_Value, Integer_Value, Float_Value, Object_Value);

   --  A Lua value. Its fields are canonical for its kind (Is_Canonical): a boolean is 0 or 1
   --  in Bits, an integer is its two's complement bits, a float its IEEE bits, and an object
   --  its handle. Predefined equality is then identity: integers, booleans and objects compare
   --  as Lua's raw equality does, and floats by their bits.
   type Value is record
      Kind   : Value_Kind := Nil_Value;
      Bits   : Unsigned_64 := 0;
      Object : Object_Handle := No_Object;
   end record;

   function Is_Canonical (Item : Value) return Boolean
   is (case Item.Kind is
         when Nil_Value => Item.Bits = 0 and then Item.Object = No_Object,
         when Boolean_Value => Item.Bits <= 1 and then Item.Object = No_Object,
         when Integer_Value | Float_Value => Item.Object = No_Object,
         when Object_Value => Item.Bits = 0 and then Item.Object /= No_Object);

   Nil : constant Value := (Kind => Nil_Value, Bits => 0, Object => No_Object);

   function Boolean_Value_Of (Item : Boolean) return Value
   is ((Kind => Boolean_Value, Bits => (if Item then 1 else 0), Object => No_Object))
   with Post => Is_Canonical (Boolean_Value_Of'Result);

   --  The integer an integer value holds.
   function Integer_Of (Item : Value) return Integer_64
   is (Pyro.Integer_Arithmetic.To_Signed (Item.Bits))
   with Pre => Item.Kind = Integer_Value;

   --  Clients reason through the contracts of Integer_Value_Of and Lemma_Integer_Value, not
   --  the bits, which would otherwise unfold into every quantified invariant on integer keys.
   pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Integer_Of);

   function Integer_Value_Of (Item : Integer_64) return Value
   with
     Global => null,
     Post   =>
       Integer_Value_Of'Result
       = (Kind   => Integer_Value,
          Bits   => Pyro.Integer_Arithmetic.To_Unsigned (Item),
          Object => No_Object)
       and then Is_Canonical (Integer_Value_Of'Result)
       and then Integer_Of (Integer_Value_Of'Result) = Item;

   --  [proof] An integer value is the value of its integer.
   procedure Lemma_Integer_Value (Item : Value)
   with
     Ghost,
     Global => null,
     Pre    => Item.Kind = Integer_Value and then Is_Canonical (Item),
     Post   => Integer_Value_Of (Integer_Of (Item)) = Item;

   function Float_Value_Of (Bits : Unsigned_64) return Value
   is ((Kind => Float_Value, Bits => Bits, Object => No_Object))
   with Post => Is_Canonical (Float_Value_Of'Result);

   function Object_Value_Of (Handle : Valid_Handle) return Value
   is ((Kind => Object_Value, Bits => 0, Object => Handle))
   with Post => Is_Canonical (Object_Value_Of'Result);

   --  The handle an object value holds, or No_Object for any other value.
   function Handle_Of (Item : Value) return Object_Handle
   is (if Item.Kind = Object_Value then Item.Object else No_Object);

   --  A value that can be a table key as it is: not nil, not a NaN, and not a float with an
   --  integral value (those are keyed by the integer, Normalize_Key).
   function Is_Key (Item : Value) return Boolean
   with
     Global => null,
     Post   =>
       (if Item.Kind = Nil_Value then not Is_Key'Result)
       and then (if Item.Kind in Boolean_Value | Integer_Value | Object_Value
                 then Is_Key'Result);

   --  [puc ltable.c:luaH_get, luaV_flttointns] Item as a table key: a float with an integral
   --  value in the integer range becomes that integer (2.0 is 2, -0.0 is 0). Valid is False
   --  for nil and NaN, which cannot be keys.
   procedure Normalize_Key (Item : Value; Key : out Value; Valid : out Boolean)
   with
     Global => null,
     Pre    => Is_Canonical (Item),
     Post   =>
       (if Valid then Is_Key (Key) and then Is_Canonical (Key) else Key = Nil)
       and then (if Item.Kind in Boolean_Value | Integer_Value | Object_Value
                 then Valid and then Key = Item)
       and then (if Item.Kind /= Object_Value then Key.Kind /= Object_Value);

   --  Item as a table key (Normalize_Key), or Nil when it cannot be one.
   function Key_Of (Item : Value) return Value
   with
     Global => null,
     Pre    => Is_Canonical (Item),
     Post   =>
       (Key_Of'Result = Nil
        or else (Is_Key (Key_Of'Result) and then Is_Canonical (Key_Of'Result)))
       and then (if Item.Kind in Boolean_Value | Integer_Value | Object_Value
                 then Key_Of'Result = Item)
       and then (if Item.Kind /= Object_Value then Key_Of'Result.Kind /= Object_Value);

end Pyro.Values;
