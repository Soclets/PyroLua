--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the comparison and test instructions.

with Pyro.Floats;

package body Pyro.Virtual_Machine.Comparisons with SPARK_Mode => On is

   use Pyro.Bytecode;

   function Is_Number (Item : Value) return Boolean
   is (Item.Kind in Integer_Value | Float_Value);

   function Is_False (Item : Value) return Boolean
   is (Item.Kind = Nil_Value or else Item = Boolean_Value_Of (False));

   --  The integers 2 ** 53 and below in magnitude convert to floats exactly (l_intfitsf).
   Exact_Float_Limit : constant := 2 ** 53;

   function Fits_Float (Item : Integer_64) return Boolean
   is (Item in -Exact_Float_Limit .. Exact_Float_Limit);

   --  The float bits of 0.0.
   Zero : constant Pyro.Floats.Float_Bits := 0;

   --  Float F rounded down (Up False) or up to an integer, when that integer is in range.
   procedure Round
     (F : Pyro.Floats.Float_Bits; Up : Boolean; Result : out Integer_64; Success : out Boolean)
   with Global => null
   is
      One     : constant Pyro.Floats.Float_Bits := Pyro.Floats.From_Integer (1);
      Rounded : Pyro.Floats.Float_Bits;
   begin
      if Up then
         --  ceil (F) = -floor (-F)
         Rounded :=
           Pyro.Floats.Arithmetic
             (Pyro.Floats.Negate,
              Pyro.Floats.Arithmetic
                (Pyro.Floats.Floor_Divide,
                 Pyro.Floats.Arithmetic (Pyro.Floats.Negate, F, Zero), One),
              Zero);
      else
         Rounded := Pyro.Floats.Arithmetic (Pyro.Floats.Floor_Divide, F, One);
      end if;
      Pyro.Floats.To_Integer (Rounded, Result, Success);
   end Round;

   --  [puc lvm.c:LTintfloat, LEintfloat] Integer I < (or <=, Or_Equal) float F, exactly.
   function Integer_Below (I : Integer_64; F : Pyro.Floats.Float_Bits; Or_Equal : Boolean)
     return Boolean
   with Global => null
   is
      Bound : Integer_64;
      Found : Boolean;
   begin
      if Fits_Float (I) then
         return Pyro.Floats.Compare
                  ((if Or_Equal then Pyro.Floats.Less_Equal else Pyro.Floats.Less_Than),
                   Pyro.Floats.From_Integer (I), F);
      end if;
      --  I < F <=> I < ceil (F), and I <= F <=> I <= floor (F).
      Round (F, Up => not Or_Equal, Result => Bound, Success => Found);
      if Found then
         return (if Or_Equal then I <= Bound else I < Bound);
      end if;
      return Pyro.Floats.Compare (Pyro.Floats.Less_Than, Zero, F);
   end Integer_Below;

   --  [puc lvm.c:LTfloatint, LEfloatint] Float F < (or <=) integer I, exactly.
   function Float_Below (F : Pyro.Floats.Float_Bits; I : Integer_64; Or_Equal : Boolean)
     return Boolean
   with Global => null
   is
      Bound : Integer_64;
      Found : Boolean;
   begin
      if Fits_Float (I) then
         return Pyro.Floats.Compare
                  ((if Or_Equal then Pyro.Floats.Less_Equal else Pyro.Floats.Less_Than),
                   F, Pyro.Floats.From_Integer (I));
      end if;
      --  F < I <=> floor (F) < I, and F <= I <=> ceil (F) <= I.
      Round (F, Up => Or_Equal, Result => Bound, Success => Found);
      if Found then
         return (if Or_Equal then Bound <= I else Bound < I);
      end if;
      return Pyro.Floats.Compare (Pyro.Floats.Less_Than, F, Zero);
   end Float_Below;

   --  [puc lvm.c:LTnum, LEnum] Number Left < (or <=) number Right.
   function Number_Below (Left, Right : Value; Or_Equal : Boolean) return Boolean
   is (if Left.Kind = Integer_Value and then Right.Kind = Integer_Value
       then (if Or_Equal then Integer_Of (Left) <= Integer_Of (Right)
             else Integer_Of (Left) < Integer_Of (Right))
       elsif Left.Kind = Integer_Value
       then Integer_Below (Integer_Of (Left), Right.Bits, Or_Equal)
       elsif Right.Kind = Integer_Value
       then Float_Below (Left.Bits, Integer_Of (Right), Or_Equal)
       else Pyro.Floats.Compare
              ((if Or_Equal then Pyro.Floats.Less_Equal else Pyro.Floats.Less_Than),
               Left.Bits, Right.Bits))
   with Pre => Is_Number (Left) and then Is_Number (Right);

   --  [puc ldebug.c:luaG_ordererror] Left and Right cannot be compared.
   procedure Order_Error
     (M : in out Machine; Budget : in out Memory_Budget; Left, Right : Value)
   with
     Global => null,
     Pre    => Is_Valid (M) and then Is_Loaded (M),
     Post   => Is_Valid (M) and then Is_Loaded (M) and then Limit (Budget) = Limit (Budget)'Old
   is
      First  : constant String := Type_Name (M, Left);
      Second : constant String := Type_Name (M, Right);
   begin
      if First = Second then
         Raise_Runtime_Error (M, Budget, "attempt to compare two " & First & " values");
      else
         Raise_Runtime_Error (M, Budget, "attempt to compare " & First & " with " & Second);
      end if;
   end Order_Error;

   --  [puc lvm.c:luaV_lessthan, luaV_lessequal] Left < (or <=) Right without metamethods:
   --  Comparable is False when they are not two numbers or two strings.
   procedure Order
     (M          : Machine;
      Left       : Value;
      Right      : Value;
      Or_Equal   : Boolean;
      Result     : out Boolean;
      Comparable : out Boolean)
   with Global => null, Pre => Is_Valid (M)
   is
   begin
      Result := False;
      Comparable := True;
      if Is_Number (Left) and then Is_Number (Right) then
         Result := Number_Below (Left, Right, Or_Equal);
      elsif Is_String (M, Left) and then Is_String (M, Right) then
         Result :=
           (if Or_Equal then String_Order (M, Left, Right) <= 0
            else String_Order (M, Left, Right) < 0);
      else
         Comparable := False;
      end if;
   end Order;

   procedure Execute
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   is
      A          : constant Natural range 0 .. 255 := Natural (I.A);
      B          : constant Natural range 0 .. 255 := Natural (I.B);
      Left       : Value;
      Right      : Value;
      Condition  : Boolean := False;
      Comparable : Boolean := True;
      Handler    : Value;
   begin
      Lemma_View (M);
      case Test_Opcode (I.Operation) is
         when Equal =>
            Left := Register (M, A);
            Right := Register (M, B);
            Condition := Raw_Equal (Left, Right);
            if not Condition and then Is_Table (M, Left) and then Is_Table (M, Right) then
               --  [puc lvm.c:luaV_equalobj] The first table's __eq, else the second's.
               Handler := Metafield (M, Left, Equal_Event);
               if Handler = Nil then
                  Handler := Metafield (M, Right, Equal_Event);
               end if;
               if Handler /= Nil then
                  Call_Metamethod (M, Budget, Handler, [Left, Right], Test_Result, 0, I.K);
                  return;
               end if;
            end if;
         when Equal_Constant =>
            Condition := Raw_Equal (Register (M, A), Constant_At (M, B));
         when Equal_Integer =>
            Condition := Raw_Equal (Register (M, A), Integer_Value_Of (Integer_64 (B) - Offset_sC));
         when Less_Than | Less_Equal =>
            Left := Register (M, A);
            Right := Register (M, B);
            Order (M, Left, Right, I.Operation = Less_Equal, Condition, Comparable);
         when Less_Than_Integer .. Greater_Equal_Integer =>
            Left := Register (M, A);
            Right :=
              (if I.C /= 0
               then Float_Value_Of (Pyro.Floats.From_Integer (Integer_64 (B) - Offset_sC))
               else Integer_Value_Of (Integer_64 (B) - Offset_sC));
            if I.Operation in Greater_Than_Integer | Greater_Equal_Integer then
               --  R[A] > sB is sB < R[A], with the operands swapped for the error too.
               Left := Right;
               Right := Register (M, A);
            end if;
            if Is_Number (Register (M, A)) then
               Condition :=
                 Number_Below
                   (Left, Right, I.Operation in Less_Equal_Integer | Greater_Equal_Integer);
            else
               Comparable := False;
            end if;
         when Test =>
            Condition := not Is_False (Register (M, A));
         when Test_Set =>
            Right := Register (M, B);
            Condition := not Is_False (Right);
            if Condition = I.K then
               Set_Register (M, A, Right);
            end if;
      end case;
      if not Comparable then
         --  [puc ltm.c:luaT_callorderTM] The first operand's metamethod, else the second's.
         Handler :=
           Metafield
             (M, Left,
              (if I.Operation in Less_Equal | Less_Equal_Integer | Greater_Equal_Integer
               then Less_Equal_Event else Less_Than_Event));
         if Handler = Nil then
            Handler :=
              Metafield
                (M, Right,
                 (if I.Operation in Less_Equal | Less_Equal_Integer | Greater_Equal_Integer
                  then Less_Equal_Event else Less_Than_Event));
         end if;
         if Handler /= Nil then
            Call_Metamethod (M, Budget, Handler, [Left, Right], Test_Result, 0, I.K);
            return;
         end if;
         if I.Operation in Less_Equal | Less_Equal_Integer | Greater_Equal_Integer then
            --  [puc ltm.c:luaT_callorderTM] With LUA_COMPAT_LT_LE, which the reference build
            --  has (LUA_COMPAT_5_3): Left <= Right is not (Right < Left), through the second
            --  operand's __lt, else the first's; the test expects the opposite result.
            Handler := Metafield (M, Right, Less_Than_Event);
            if Handler = Nil then
               Handler := Metafield (M, Left, Less_Than_Event);
            end if;
            if Handler /= Nil then
               Call_Metamethod (M, Budget, Handler, [Right, Left], Test_Result, 0, not I.K);
               return;
            end if;
         end if;
         Order_Error (M, Budget, Left, Right);
      elsif Condition = I.K then
         Next (M);
      else
         Next (M, 1);
      end if;
   end Execute;

end Pyro.Virtual_Machine.Comparisons;
