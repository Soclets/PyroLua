--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua values: nil, booleans, integers, floats (as their bits) and handles to heap objects.

with Pyro.Floats;

package body Pyro.Values with SPARK_Mode => On is

   function Integer_Value_Of (Item : Integer_64) return Value is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Integer_Of);
      Bits : constant Unsigned_64 := Pyro.Integer_Arithmetic.To_Unsigned (Item);
   begin
      if Item >= 0 then
         pragma Assert (Pyro.Integer_Arithmetic.To_Unsigned (Item) = Unsigned_64 (Item));
         pragma Assert (Unsigned_64 (Item) <= Unsigned_64 (Integer_64'Last));
         pragma Assert (Integer_64 (Unsigned_64 (Item)) = Item);
         pragma Assert (Bits = Unsigned_64 (Item));
         pragma Assert (Pyro.Integer_Arithmetic.To_Signed (Unsigned_64 (Item)) = Item);
         pragma Assert (Pyro.Integer_Arithmetic.To_Signed (Bits) = Item);
      else
         pragma Assert (Bits = Unsigned_64'Last - Unsigned_64 (-(Item + 1)));
         pragma Assert (Bits > Unsigned_64 (Integer_64'Last));
         pragma Assert (Unsigned_64'Last - Bits = Unsigned_64 (-(Item + 1)));
         pragma Assert (Pyro.Integer_Arithmetic.To_Signed (Bits) = Item);
      end if;
      return (Kind => Integer_Value, Bits => Bits, Object => No_Object);
   end Integer_Value_Of;

   procedure Lemma_Integer_Value (Item : Value) is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Integer_Of);
      Bits : constant Unsigned_64 := Item.Bits;
   begin
      if Bits <= Unsigned_64 (Integer_64'Last) then
         pragma Assert (Integer_Of (Item) = Integer_64 (Bits));
         pragma Assert (Pyro.Integer_Arithmetic.To_Unsigned (Integer_64 (Bits)) = Bits);
      else
         declare
            Rest : constant Unsigned_64 := Unsigned_64'Last - Bits;
         begin
            pragma Assert (Rest <= Unsigned_64 (Integer_64'Last));
            pragma Assert (Integer_Of (Item) = -Integer_64 (Rest) - 1);
            pragma Assert (-(Integer_Of (Item) + 1) = Integer_64 (Rest));
            pragma Assert (Unsigned_64 (Integer_64 (Rest)) = Rest);
            pragma Assert (Integer_Of (Item) < 0);
            pragma Assert
              (Pyro.Integer_Arithmetic.To_Unsigned (Integer_Of (Item))
               = Unsigned_64'Last - Unsigned_64 (-(Integer_Of (Item) + 1)));
            pragma Assert (Unsigned_64 (-(Integer_Of (Item) + 1)) = Rest);
            pragma Assert
              (Pyro.Integer_Arithmetic.To_Unsigned (Integer_Of (Item)) = Unsigned_64'Last - Rest);
            pragma Assert (Unsigned_64'Last - Rest = Bits);
         end;
      end if;
      pragma Assert (Pyro.Integer_Arithmetic.To_Unsigned (Integer_Of (Item)) = Bits);
   end Lemma_Integer_Value;

   function Is_Key (Item : Value) return Boolean is
      Ignored  : Integer_64;
      Integral : Boolean;
   begin
      if Item.Kind = Nil_Value then
         return False;
      elsif Item.Kind /= Float_Value then
         return True;
      elsif Pyro.Floats.Is_NaN (Item.Bits) then
         return False;
      end if;
      Pyro.Floats.To_Integer (Item.Bits, Ignored, Integral);
      return not Integral;
   end Is_Key;

   procedure Normalize_Key (Item : Value; Key : out Value; Valid : out Boolean) is
      Integer_Key : Integer_64;
      Integral    : Boolean;
   begin
      Key := Nil;
      Valid := False;
      case Item.Kind is
         when Nil_Value =>
            return;
         when Float_Value =>
            if Pyro.Floats.Is_NaN (Item.Bits) then
               return;
            end if;
            Pyro.Floats.To_Integer (Item.Bits, Integer_Key, Integral);
            if Integral then
               Key := Integer_Value_Of (Integer_Key);
            else
               Key := Item;
            end if;
         when Boolean_Value | Integer_Value | Object_Value =>
            Key := Item;
      end case;
      Valid := Is_Key (Key);
      if not Valid then
         --  Not reached: an integral float became an integer, and any other float is a key.
         Key := Nil;
      end if;
   end Normalize_Key;

   function Key_Of (Item : Value) return Value is
      Key     : Value;
      Ignored : Boolean;
   begin
      Normalize_Key (Item, Key, Ignored);
      return Key;
   end Key_Of;

end Pyro.Values;
