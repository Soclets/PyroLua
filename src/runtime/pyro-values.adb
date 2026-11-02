--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Lua values: nil, booleans, integers, floats (as their bits) and handles to heap objects.

with Pyro.Floats;

package body Pyro.Values with SPARK_Mode => On is

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

end Pyro.Values;
