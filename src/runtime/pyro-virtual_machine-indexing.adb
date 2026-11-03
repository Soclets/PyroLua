--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The handlers of the table instructions: indexing, new tables, lists and lengths.

package body Pyro.Virtual_Machine.Indexing with SPARK_Mode => On is

   use Pyro.Bytecode;

   --  [puc lopcodes.h:MAXARG_C] One more than the largest C operand: the unit of the extra
   --  argument of NEWTABLE and SETLIST.
   Operand_Range : constant := 256;

   --  The largest extra argument these handlers use, so that sizes stay in range.
   Maximum_Extra : constant := 2 ** 20;

   --  2 ** N, for the hash sizes NEWTABLE gives as their log2.
   Powers : constant array (0 .. 26) of Natural :=
     [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1_024, 2_048, 4_096, 8_192, 16_384, 32_768,
      65_536, 131_072, 262_144, 524_288, 1_048_576, 2_097_152, 4_194_304, 8_388_608,
      16_777_216, 33_554_432, 67_108_864];

   procedure Execute
     (M : in out Machine; Budget : in out Memory_Budget; I : Pyro.Bytecode.Instruction)
   is
      A : constant Natural range 0 .. 255 := Natural (I.A);
      B : constant Natural range 0 .. 255 := Natural (I.B);
      C : constant Natural range 0 .. 255 := Natural (I.C);
   begin
      Lemma_View (M);
      case Indexing_Instruction (I.Operation) is
         when Get_Table_Upvalue =>
            Get_Index (M, Budget, Upvalue (M, B), Constant_At (M, C), A, Upvalue_Of (B));
         when Get_Table =>
            Get_Index (M, Budget, Register (M, B), Register (M, C), A, Register_Of (B));
         when Get_Integer =>
            Get_Index
              (M, Budget, Register (M, B), Integer_Value_Of (Integer_64 (C)), A, Register_Of (B));
         when Get_Field =>
            Get_Index (M, Budget, Register (M, B), Constant_At (M, C), A, Register_Of (B));
         when Set_Table_Upvalue =>
            Set_Index
              (M, Budget, Upvalue (M, A), Constant_At (M, B),
               (if I.K then Constant_At (M, C) else Register (M, C)), Upvalue_Of (A));
         when Set_Table =>
            Set_Index
              (M, Budget, Register (M, A), Register (M, B),
               (if I.K then Constant_At (M, C) else Register (M, C)), Register_Of (A));
         when Set_Integer =>
            Set_Index
              (M, Budget, Register (M, A), Integer_Value_Of (Integer_64 (B)),
               (if I.K then Constant_At (M, C) else Register (M, C)), Register_Of (A));
         when Set_Field =>
            Set_Index
              (M, Budget, Register (M, A), Constant_At (M, B),
               (if I.K then Constant_At (M, C) else Register (M, C)), Register_Of (A));
         when New_Table =>
            --  [puc lvm.c:OP_NEWTABLE] B is the log2 of the hash size, plus one (0: none); C
            --  the array size, with the extra argument's multiples of Operand_Range.
            Make_Table
              (M, Budget, A,
               Array_Size =>
                 C + (if I.K then Natural'Min (Extra_Argument (M), Maximum_Extra) * Operand_Range
                      else 0),
               Hash_Size  => (if B = 0 then 0 elsif B > 27 then Natural'Last else Powers (B - 1)));
         when Self =>
            declare
               Object : constant Value := Register (M, B);
               Key    : constant Value :=
                 (if I.K then Constant_At (M, C) else Register (M, C));
               Before : constant Pyro.Kind_Sequences.Sequence := Objects (M) with Ghost;
            begin
               Lemma_Live_In (M, Object);
               Lemma_Live_In (M, Key);
               Set_Register (M, A + 1, Object);
               Lemma_Still_Live (Before, M, Object);
               Lemma_Still_Live (Before, M, Key);
               Get_Index (M, Budget, Object, Key, A, Register_Of (B));
            end;
         when Set_List =>
            Store_List
              (M, Budget, A,
               Count => (if B = 0 then -1 else B),
               First =>
                 Integer_64 (C)
                 + (if I.K
                    then Integer_64 (Natural'Min (Extra_Argument (M), Maximum_Extra))
                         * Operand_Range
                    else 0),
               Skip  => (if I.K then 1 else 0));
         when Length =>
            declare
               Operand : constant Value := Register (M, B);
               Handler : Value;
            begin
               if Is_String (M, Operand) then
                  Set_Register (M, A, Integer_Value_Of (Raw_Length (M, Operand)));
                  Next (M);
                  return;
               end if;
               Handler := Metafield (M, Operand, Length_Event);
               if Handler /= Nil then
                  Call_Metamethod
                    (M, Budget, Handler, [Operand, Operand], Store_Result, A, False);
               elsif Is_Table (M, Operand) then
                  Set_Register (M, A, Integer_Value_Of (Raw_Length (M, Operand)));
                  Next (M);
               else
                  Raise_Runtime_Error
                    (M, Budget, "attempt to get length of a " & Type_Name (M, Operand)
                                & " value" & Variable_Info (M, Register_Of (B)));
               end if;
            end;
      end case;
   end Execute;

end Pyro.Virtual_Machine.Indexing;
