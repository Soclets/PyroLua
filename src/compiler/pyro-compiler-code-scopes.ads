--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
--
--  Functions, blocks, local variables, upvalues, labels and gotos as PUC Lua's lparser.c keeps
--  them while it generates code.

package Pyro.Compiler.Code.Scopes with SPARK_Mode => On, Always_Terminates is

   --  [puc lparser.c:open_func] Opens a function defined on Line (0 for the main function)
   --  as a child of the open one, with its outermost block.
   procedure Open_Function (State : in out Compiler_State; Line : Natural)
   with Global => null;

   --  [puc lparser.c:close_func] Closes the open function: adds its final return, finishes
   --  its code, and moves it to the chunk as a new prototype, a child of the function now open.
   procedure Close_Function
     (State : in out Compiler_State; Result : in out Chunk; Last_Line : Natural)
   with Global => null, Pre => Is_Well_Formed (Result), Post => Is_Well_Formed (Result);

   --  [puc lparser.c:enterblock].
   procedure Enter_Block (State : in out Compiler_State; Is_Loop : Boolean)
   with Global => null;

   --  [puc lparser.c:leaveblock].
   procedure Leave_Block (State : in out Compiler_State)
   with Global => null;

   --  Whether the open block has an upvalue (bl->upval).
   function Block_Has_Upvalue (State : Compiler_State) return Boolean
   with Global => null;

   --  Whether the open block is inside a to-be-closed scope (bl->insidetbc).
   function Inside_To_Be_Closed (State : Compiler_State) return Boolean
   with Global => null;

   --  [puc lparser.c:new_localvar] Declares a variable, not yet active; Index is its index
   --  among the open function's variables.
   procedure New_Local (State : in out Compiler_State; Name : Symbol_Index; Index : out Natural)
   with Global => null;

   --  Sets the kind (and constant value) of variable Index of the open function.
   procedure Set_Variable
     (State : in out Compiler_State; Index : Natural; Kind : Variable_Kind;
      Value : Constant_Value)
   with Global => null;

   --  [puc lparser.c:adjustlocalvars] Activates the next Count declared variables.
   procedure Adjust_Locals (State : in out Compiler_State; Count : Natural)
   with Global => null;

   --  Counts one more active variable without giving it a register (a compile-time constant).
   procedure Activate_Constant (State : in out Compiler_State)
   with Global => null;

   --  [puc lparser.c:localdebuginfo] Sets the start of the debug record of variable Index.
   procedure Set_Debug_Start (State : in out Compiler_State; Index : Natural; Start : Natural)
   with Global => null;

   --  [puc lparser.c:singlevar] The expression for a name: a local, an upvalue, a compile-time
   --  constant, or _ENV indexed by the name. Name_Short says whether the name is a short
   --  string.
   procedure Single_Variable
     (State : in out Compiler_State; Name : Symbol_Index; Name_Short : Boolean;
      Item : out Expression)
   with Global => null;

   --  [puc lparser.c:marktobeclosed].
   procedure Mark_To_Be_Closed (State : in out Compiler_State)
   with Global => null;

   --  [puc lparser.c:setvararg].
   procedure Set_Vararg (State : in out Compiler_State; Parameters : Natural)
   with Global => null;

   --  [puc lparser.c:newgotoentry] A pending goto (or break) at the jump at PC.
   procedure New_Goto
     (State : in out Compiler_State; Name : Symbol_Index; Line : Line_Number; PC : Jump_List)
   with Global => null;

   --  [puc lparser.c:findlabel] The visible label Name, if any (Found).
   procedure Find_Label
     (State : Compiler_State; Name : Symbol_Index; Label : out Label_Entry; Found : out Boolean)
   with Global => null;

   --  [puc lparser.c:createlabel]: Needed_Close is whether a CLOSE was coded.
   procedure Create_Label
     (State : in out Compiler_State;
      Name : Symbol_Index;
      Line : Line_Number;
      Last : Boolean;
      Needed_Close : out Boolean)
   with Global => null;

end Pyro.Compiler.Code.Scopes;
