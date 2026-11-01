--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  The pyro command-line program: reads a Lua file and inspects or checks it.

--  [trusted] File and console I/O and argument handling, outside the proven library.
pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Text_IO;

procedure Pyro_Program is
   use Ada.Command_Line;

   procedure Usage is
   begin
      Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error,
                            "usage: pyro (--tokens | --ast | --check) file.lua");
      Set_Exit_Status (2);
   end Usage;
begin
   if Argument_Count /= 2 then
      Usage;
      return;
   end if;
   Ada.Text_IO.Put_Line (Ada.Text_IO.Standard_Error, "pyro: not implemented yet");
   Set_Exit_Status (Failure);
end Pyro_Program;
