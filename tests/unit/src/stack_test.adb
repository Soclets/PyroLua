--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Parses and resolves each file given in a task whose stack is Pyro.Minimum_Stack_Size, so a
--  front end that needs more stack than Pyro promises fails here.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Direct_IO;
with Ada.Text_IO;
with Pyro;
with Pyro.Diagnostic_Lists;
with Pyro.Memory_Budgets;
with Pyro.Parser;
with Pyro.Resolver;
with Pyro.Sources;
with Pyro.Symbols;
with Pyro.Syntax_Trees;

procedure Stack_Test is
   use Ada.Command_Line;

   type Source_Access is access Pyro.Sources.Source;

   function Load (Path : String) return Source_Access is
      Size   : constant Natural := Natural (Ada.Directories.Size (Path));
      Result : constant Source_Access :=
        new Pyro.Sources.Source (Name_Size => Path'Length + 1, Length => Size);
      subtype Content is String (1 .. Size);
      package Content_IO is new Ada.Direct_IO (Content);
      File : Content_IO.File_Type;
   begin
      Result.Name := "@" & Path;
      Content_IO.Open (File, Content_IO.In_File, Path);
      Content_IO.Read (File, Result.Text);
      Content_IO.Close (File);
      return Result;
   end Load;

   task type Worker is
      pragma Storage_Size (Pyro.Minimum_Stack_Size);
      entry Start (Path : String);
   end Worker;

   task body Worker is
      Source   : Source_Access;
      Budget   : Pyro.Memory_Budgets.Memory_Budget :=
        Pyro.Memory_Budgets.Create (Pyro.Memory_Budgets.Default_Limit);
      Symbols  : Pyro.Symbols.Symbol_Table;
      Tree     : Pyro.Syntax_Trees.Syntax_Tree;
      Problems : Pyro.Diagnostic_Lists.Growable_Array;
      Root     : Pyro.Syntax_Trees.Node_Index;
      Bindings : Pyro.Resolver.Binding_Table;
   begin
      accept Start (Path : String) do
         Source := Load (Path);
      end Start;
      Pyro.Parser.Parse (Source.all, Symbols, Budget, Tree, Problems, Root);
      Pyro.Resolver.Resolve (Tree, Root, Symbols, Budget, Problems, Bindings);
      Ada.Text_IO.Put_Line
        (Source.Name & ":" & Pyro.Diagnostic_Lists.Length (Problems)'Image & " errors");
   end Worker;
begin
   for Index in 1 .. Argument_Count loop
      declare
         Item : Worker;
      begin
         Item.Start (Argument (Index));
      end;
   end loop;
end Stack_Test;
