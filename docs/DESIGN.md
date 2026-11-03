# Pyro Lua design

This document describes how Pyro is built and why. It covers the whole interpreter;
parts that belong to later milestones are marked as such and can be refined when
those milestones start. Proof obligations are summarised here and specified in
[PROOFS.md](PROOFS.md).

## Pipeline

```
source bytes
   │  Pyro.Lexer                tokens
   ▼
   │  Pyro.Parser               syntax tree (Pyro.Syntax_Trees)
   ▼
   │  Pyro.Resolver             scopes, locals/upvalues, labels/goto, const checks
   ▼
   │  Pyro.Compiler             register bytecode (Pyro.Bytecode)        [M2]
   ▼
   │  Pyro.Virtual_Machine      execution over Pyro.Heap / Pyro.Tables   [M4]
   ▼
results / Lua errors
```

PUC Lua compiles in a single pass: its parser emits bytecode directly, with no syntax
tree. Pyro deliberately splits this into separate passes. Each pass has a small,
provable contract, can be tested on its own, and has an inspectable output
(`--tokens`, `--ast`, `--bytecode`). It costs memory and code size, which is
acceptable.

## General principles

**No pointers to the heap, handles instead.** Every dynamically sized structure (AST
nodes, heap objects, table slots, stacks) lives in an arena indexed by a typed
handle (`Node_Index`, `Object_Handle`, …). Handles are plain integers, so SPARK can reason
about them with ordinary arithmetic, and validity becomes an invariant ("every
handle stored anywhere refers to an allocated slot") rather than a pointer-ownership
problem.

**One growable-array generic.** Arenas and stacks need to grow. Pyro implements one
generic, `Pyro.Growable_Arrays`, on top of SPARK's pointer ownership, proves it once
and reuses it everywhere. The elements live in owned chunks of about 1 MiB: growing
adds a chunk, so elements are never copied and memory never doubles; only the first
chunk starts small and doubles up to that size, so small arrays stay small. Its
contract exposes the contents as a ghost sequence so clients can state invariants
about them.

**Memory accounting.** Every growth goes through a single allocator that checks a
configurable memory limit first. The limit lives in a `Memory_Budget` record
(`Pyro.Memory_Budgets`: limit and bytes used) that is passed `in out` to every growth,
from the front end on, so a chunk loaded at runtime counts against its state's limit.
Each growable array also has a maximum length (the range of its index type). Exceeding the limit is an ordinary error result
(and, at runtime, a Lua "not enough memory" error). Running out of OS memory before
reaching the limit is outside what Pyro can prove; see
[PROOFS.md](PROOFS.md#assumptions).

**No exceptions.** Library code never raises or handles Ada exceptions. Operations
that can fail return a status. Lua-level errors are handled by the VM unwinding its
own frame stack (see [Errors](#errors)).

**No unbounded recursion.** The parser and every tree walk carry an explicit depth
and stop with an error at a fixed limit, as PUC Lua does (`LUAI_MAXCCALLS` = 200).
The VM does not recurse at all for Lua-to-Lua calls.

**Bytes, not characters.** Lua strings are arbitrary byte sequences, including
`NUL`. Pyro treats source and string data as bytes (`Character` used as an 8-bit
byte, or an `Unsigned_8` array). Names are ASCII only, matching PUC Lua in the C
locale.

## Package layout

| Package | Milestone | Role |
| --- | --- | --- |
| `Pyro` | M1 | Root: limits and configuration constants |
| `Pyro.Memory_Budgets` | M1 | Memory limit and the bytes charged against it |
| `Pyro.Growable_Arrays` | M1 | Proven generic growable array |
| `Pyro.Sources` | M1 | Source buffer, positions, line numbers, chunk name |
| `Pyro.Diagnostics` | M1 | Error records, rich and Lua-style message formatting |
| `Pyro.Graphemes` | M1 | Grapheme cluster boundaries (UAX #29) from generated Unicode tables |
| `Pyro.Tokens` | M1 | Token kinds and token records |
| `Pyro.Lexer` | M1 | Tokenizer |
| `Pyro.Numbers` | M1 | Integer and float literal conversion |
| `Pyro.Floats` | M1 | IEEE float operations on raw bits (trusted body) |
| `Pyro.Symbols` | M1 | Interned names and string literals |
| `Pyro.Syntax_Trees` | M1 | Syntax tree arena |
| `Pyro.Parser` | M1 | Recursive-descent parser |
| `Pyro.Resolver` | M1 | Scope analysis and compile-time semantic errors |
| `Pyro.Bytecode` | M2 | Instruction set, prototypes, validity predicate |
| `Pyro.Compiler` | M2 | AST to bytecode |
| `Pyro.Values` | M3 | Lua value representation |
| `Pyro.Heap` | M3 | Object arena, allocation, handles |
| `Pyro.Kind_Sequences` | M3 | [proof] The kind of every slot, as a ghost sequence |
| `Pyro.Strings` | M3 | String bytes, the seed, SipHash-1-3 (strings are interned by `Pyro.Heap`) |
| `Pyro.Tables` | M3 | Lua tables |
| `Pyro.Value_Maps`, `Pyro.Value_Sequences` | M3 | [proof] A table's contents and the values it holds, as ghost containers |
| `Pyro.Garbage_Collector` | M3 | Mark and sweep collector |
| `Pyro.Color_Sequences`, `Pyro.Graph_Sequences`, `Pyro.Handle_Sequences` | M3 | [proof] The collector's marks, what each object holds, and paths through the heap, as ghost sequences |
| `Pyro.Virtual_Machine` | M4 | Interpreter loop, call frames, metamethods |
| `Pyro.Embedding` | M6 | Embedding API for Ada/SPARK hosts |
| `pyrolua.h` and its layer | M6 | The C API for C and C++ hosts (primary), over the same core |

Source folders, file naming and the rules for private and public packages are in
[STYLE.md](STYLE.md#packages-and-files).

The `pyrolua` executable (`cli/`) is ordinary Ada. It handles files, command-line
arguments and output, and calls into the library.

## Front end (M1)

### Sources

A chunk is a byte array with a chunk name (used in messages, like PUC Lua's
`@file.lua` / `=stdin` convention). Positions are indices into it. Line numbers
follow `llex.c`: each of `\n`, `\r`, `\n\r` and `\r\n` counts as one line break.

As in `luaL_loadfile`, a first line starting with `#` is skipped (shebang). That is a
loader feature, not a lexer one, so it lives in the loading code, not in
`Pyro.Lexer`.

### Lexer

`Pyro.Lexer` produces one token at a time from a lexer state (source, position,
line). A token has a kind, a span (first/last position), a line, and a payload:

- names and string literals: a `Symbol_Index` into `Pyro.Symbols` (bytes are decoded:
  escapes resolved, long-bracket leading newline dropped);
- numerals: a Lua integer or a float (as raw bits, see [Numbers](#numbers)).

It must reproduce `llex.c` exactly, including:

- the 22 keywords and all Lua 5.4 symbols (`//`, `>>`, `<<`, `~`, `~=`, `::`, `...`,
  `..`, `&`, `|`, …);
- short strings with every escape: `\a \b \f \n \r \t \v \\ \" \'`, escaped real
  newline, `\z`, `\xXX`, decimal `\ddd` (at most 255), and `\u{XXX}` up to
  2^31 − 1 (encoded as extended UTF-8, up to 6 bytes);
- long brackets of any level, for strings and comments;
- numerals read greedily as `llex.c` does (a numeral consumes any following
  alphanumerics and `.`, plus exponent signs, then converts), so `3..2` is a
  "malformed number";
- decimal integers that overflow become floats; hexadecimal integers wrap modulo
  2^64; hex floats with `p` exponents.

Each error also carries what PUC Lua would print for it (message, line and "near"
text), for the Lua-style report (see [Diagnostics](#diagnostics)).

### Numbers

Lua integers are 64-bit two's complement with wrap-around arithmetic. Pyro stores
them as `Interfaces.Integer_64` and does wrapping arithmetic through
`Interfaces.Unsigned_64` (modular, so no overflow checks) with unchecked conversion
between the two.

Lua floats are IEEE 754 doubles and must support infinities and NaN (`1/0`,
`0/0`). SPARK assumes every floating-point object holds a finite, valid value, so
storing an infinity in a SPARK `Long_Float` would make the proofs unsound. Pyro
therefore stores floats as **raw bits** (`Unsigned_64`) everywhere in SPARK code. All
float arithmetic, comparison and conversion goes through `Pyro.Floats`, whose spec is
SPARK and whose body is trusted (`SPARK_Mode => Off`) and relies on IEEE hardware
behaviour. This is one of the few trusted boundaries; see
[PROOFS.md](PROOFS.md#trusted-code).

Literal conversion:

- integers and hex floats are converted by proven SPARK code (hex floats are exact:
  scale the mantissa by a power of two);
- decimal floats need correct rounding, which is hard to prove. They are converted
  in `Pyro.Floats` (trusted), from a normalised decimal string.

Float-to-string conversion (`%.14g` with Lua's ".0" rule for integral floats) is
needed from M4 and also lives in the trusted float package.

### Syntax tree

`Pyro.Syntax_Trees` is an arena of nodes indexed by `Node_Index`. Each node has a kind, a span,
a line, up to three child slots, an optional child list (a slice of a separate list
arena), and kind-specific payload (symbol, integer, float bits, operator, attribute).
Clients see one `Node` record; the arena stores each node in 32 bytes: the fields every
node has, and four slots whose meaning depends on the kind. A node whose fields do not
fit its kind's slots (rare: a label followed by `;`, say) is stored whole in a side
table instead.

**Key invariant:** a node's children always have smaller ids than the node itself.
Nodes are only created after their children, so this holds by construction, and it
makes the tree acyclic and every walk well-founded, which simplifies termination
proofs for all later passes. A list (the statements of a block, the arguments of a
call) is gathered on a stack in the tree while its items are parsed, and copied into
the list arena when its node is created.

### Parser

Recursive descent over the grammar in §9 of the reference manual, with operator
precedence climbing for expressions. Precedence, lowest to highest:

```
or
and
<  >  <=  >=  ~=  ==
|
~
&
<<  >>
..            (right associative)
+  -
*  /  //  %
unary: not  #  -  ~
^             (right associative, binds tighter than unary on its left: -2^2 == -4)
```

The parser carries a nesting depth and fails with an error at the same limit as PUC
Lua (200 levels). It recovers from a syntax error only where the damage is certainly
enclosed, as described in [Diagnostics](#diagnostics); otherwise it stops there.

Points where Lua's grammar needs care:

- an expression statement must be a function call; assignment targets must be
  variables (`a.b`, `a[b]`, names), not calls or parenthesised expressions;
- `f\n(g)` is a call in 5.4 (5.1's "ambiguous syntax" error no longer exists);
- `local` attributes are only `<const>` and `<close>`, with at most one
  to-be-closed variable per `local` list;
- `repeat … until cond`: `cond` sees the loop body's locals;
- `return` must be the last statement of a block (optionally followed by `;`).

### Resolver

PUC Lua reports some errors at compile time that are not grammar errors.
`luac -p` reports them, so `pyrolua --check` must too. `Pyro.Resolver` walks the tree
with a scope stack and reports:

- `break` outside a loop;
- `goto` with no visible label, a duplicate label in the same function, and a
  `goto` that jumps into the scope of a local (including Lua's special rule that a
  label at the end of a block counts as outside the scope of that block's locals);
- assignment to a `<const>` or `<close>` variable.

`...` used outside a vararg function, unknown local attributes and two `<close>`
variables in one list are reported by the parser itself, which is where PUC Lua finds
them; parsing goes on after them (design session, M1).

It also binds each name use to its declaration: a local of the same function, an
upvalue (a local of an enclosing function) or a global (`_ENV.name`), which the
compiler needs. The walk keeps its own stack (no recursion), since the depth of a tree
is not bounded by the parser's nesting limit (`1 + 1 + ... + 1` nests to the left
without counting levels).


The "too many locals/upvalues/registers" limits are code generation limits in PUC
Lua and are checked by the compiler in M2.

### Diagnostics

Owner's decision (M1). Errors are reported in two forms.

**Rich messages**, for what the `pyrolua` program or a host prints, in the layout of
Radium's messages (Soclets/Radium DECISIONS.md D116–D119, D121–D123):

```
refused: two.lua:2:1, line 2 column 1
 2 | x = 2
   | ^
 what: `x` is assigned, but it is declared <const>
 why:  a <const> variable can't be assigned after its declaration (Lua 5.4 manual §3.3.7)
 because: two.lua:1:7, line 1 column 7
 1 | local x <const> = 1
   |       ^
     `x` is declared <const> here
```

- The first word is the kind: `refused:` (a chunk fails to load) or `error:` (an
  uncaught Lua error at runtime, from M4).
- The place is given twice: `file:line:column` with the column in bytes from 1, for
  tools, then `line N column M` with the column in grapheme clusters, for people. On a
  line that is not valid UTF-8 the human column counts bytes.
- Then the source line with its number in the margin, `^` under the exact span
  (counted in grapheme clusters), and lined-up labels: `what:`, `why:` (the rule and
  its section of the Lua 5.4 manual), or `fix:` in place of `what:` when there is
  exactly one possible fix (`!=` gives the fix `~=`).
- `because:` links follow, in the order things happened: a place, its code line and
  pointer, and one fact (`` `if` opened here `` for a missing `end`, which is luac's
  "to close 'if' at line 1").
- Only certain facts: no fix when more than one fix is possible, no "maybe caused by".
- Grapheme cluster boundaries follow Unicode's UAX #29 with tables generated by
  `tools/generate-grapheme-tables` from Unicode's data files, pinned at **Unicode 18.0.0**
  (with SHA-256 sums). `tests/unit` checks the result against that version's
  `GraphemeBreakTest.txt`, which is the authority on the rules. The structured diagnostics, the renderer and the tables are in
  the library, in SPARK, since hosts need them.

**Several errors per run, certain ones only.** Every semantic error is reported
(const assignment, goto and labels, `break`, `...`, attributes). After a syntax error
the parser keeps going only where the damage is certainly enclosed: the error lies
inside `( )`, `[ ]` or `{ }` whose matching closing bracket is intact (found by bracket
matching over the following tokens); it skips to that bracket and carries on. It stops
at the first syntax error that is not enclosed like that (an unclosed bracket, a
missing `end`, any lexical error). Errors print in source order.

**Lua-style.** Lua error values stay Lua's one-line strings (`chunk:line: message`),
since scripts see them through `pcall`. `pyrolua --check --lua-style` prints exactly what
`luac -p` prints: the single error PUC Lua would detect first, in its exact text and
line. Every diagnostic therefore records its PUC detection point (the token PUC's
parser would be looking at when it raises the error, for example the token after a
function's `end` for an undefined `goto`), and the Lua-style report picks the one with
the earliest detection point. To find semantic errors that precede the first syntax
error, the parser keeps the partial tree it built before stopping; the resolver skips
the checks PUC makes when a block closes for blocks that never closed.

## Compiler and bytecode (M2)

Pyro uses Lua 5.4's register-based instruction set (`lopcodes.h`), with each
instruction a typed record (opcode, A, B, C, k and one wide operand for Bx, sBx, Ax or
sJ) rather than a packed 32-bit word. The compiler is a faithful port of `lcode.c` and of
the code generation in `lparser.c`, driven by a walk of the tree in the order PUC's parser
reads the source, so it produces the same instructions, registers, constants and line
info as `luac`. `pyrolua --bytecode --lua-style` prints them in `luac -l -l`'s format, which
makes the compiler testable against luac before the VM exists.

A **prototype** holds the instructions, constants, nested prototypes, upvalue
descriptors, parameter count, vararg flag, maximum stack size, line info and local
variable debug info. The prototypes of a chunk live in one arena; a nested function's
prototype is finished before its parent's, so it has a smaller index.

`Pyro.Bytecode` defines the predicate `Is_Valid`: every register operand is below the
prototype's stack size, every jump target is inside the code, every
constant/prototype/upvalue index is in range (with the constant kinds the opcode
needs), instructions that the VM pairs with the next one (tests and their jump,
arithmetic and its metamethod fallback, extra arguments) come in those pairs, and the
code cannot fall off the end. It is executable: the compiler runs it on what it
built as its last step and reports an internal error if it fails, so every prototype
the compiler returns is proven valid without proving the code generator itself. That
the internal error never happens is tested (corpus, official tests, fuzzing). The VM
requires `Is_Valid` and relies on it through the postconditions of `Pyro.Bytecode`'s
accessors to skip checks at runtime.

Limits follow PUC Lua: at most 200 locals per function, 255 upvalues, 255 registers.

## Values, heap and tables (M3)

### Values

A Lua value (`Pyro.Values`) is a small record of 16 bytes: a kind
(`nil | boolean | integer | float | object`), 64 bits (the boolean, the integer's two's
complement, or the float's IEEE bits) and an `Object_Handle`. Its fields are always
canonical for its kind, so predefined equality is identity: integers, booleans and
objects compare as Lua's raw equality does, floats by their bits. Strings, tables,
closures, prototypes, upvalue cells, coroutines and host userdata are heap objects
referenced by `Object_Handle`. Light userdata (a host-supplied opaque integer) can be
added as an immediate case if the API needs it.

A table key is normalised first (`Normalize_Key`): a float with an integral value becomes
that integer (`2.0` is `2`, `-0.0` is `0`), and nil and NaN are not keys.

### Heap

`Pyro.Heap` is an arena of object slots with a free list. Every slot is either free
or holds one object of a known kind. The central invariant, `Is_Valid (Heap)`, says every
`Object_Handle` stored in any live object or root (VM stacks, registry, open upvalues,
the host's handles) refers to an allocated slot of the expected kind. Every heap
operation preserves `Is_Valid (Heap)` (Gold).

A slot is a small record: its kind, the next free slot when it is free, and owned
pointers to what its object owns (a string's bytes, a table's parts). Slots live in
chunks of 4096, found through a table of chunks allocated once, so a chunk is never
copied and the objects its slots own never move; a handle's chunk and place come from a
function whose only proven property is that they give the handle back, so proofs never
see the division. The free list is threaded through the free slots, and a slot taken
from it is checked to be free, so it needs no invariant of its own. Everything the heap
allocates is charged to the same `Memory_Budget` as the front end, and running out is an
ordinary result (`No_Object`). Clients see the heap through its operations: its private
part is hidden from their proofs (PROOFS.md, Assumptions).

Besides strings and tables, the heap holds the VM's closures (a prototype of the loaded
chunk and its upvalues), upvalues (open: a place in the thread's stack; closed: a value)
and host functions (a number the host chose). Every slot may own a short array of
references, the values the object refers to besides a table's entries (a table's
metatable, a closure's upvalues, a closed upvalue's value), and a number (a closure's
prototype, an open upvalue's place in the stack, a host function's number). The
collector's graph is a table's entries followed by its references, so one set of proofs
covers every kind.

A slot's validity is hidden from the heap's own proofs: writing one slot then leaves every
other slot's validity as it was without the provers unfolding it, and each write reads the
slot's facts and rebuilds them (`Lemma_Slot_Facts`, `Lemma_Slot_From_Facts`).

### Strings

Strings are immutable heap objects with a cached hash: SipHash-1-3 of all their bytes,
keyed by the state's random seed (`Pyro.Strings`, see Sandbox limits). Every string is
interned, long ones too, so two strings are equal exactly when their handles are, and
tables and the VM compare strings without reading them. PUC Lua stopped interning long
strings because its hash sampled their bytes, which made collisions cheap; a keyed hash
over every byte removes that reason, and creating a string already costs time
proportional to its length to copy it.

The intern set is an open-addressing set of string handles in the heap, probed linearly
and rebuilt when its used and deleted entries pass three quarters of it. It does not keep
strings alive: the collector removes the strings it frees from it, and
`Is_Valid (Heap)` includes that every entry in use refers to a string.

### Tables

A table (`Pyro.Tables`) has an array part (keys `1..N`) and a hash part of nodes with
linear probing. Key rules from the manual: `nil` and NaN keys are errors on assignment,
and keys are normalised before hashing (`t[2.0]` is `t[2]`, `-0.0` is `0`). A key's hash
is SipHash-1-3 of its bits and kind under the table's seed, so a string's hash does not
depend on its bytes being read again, and two tables order the same keys differently from
each other and from PUC Lua.

Sizing follows `ltable.c`: when an insert finds no room, the table counts its integer
keys by powers of two and picks the largest array size that is more than half full
(`computesizes`), then puts the rest in a hash part of the next power of two
(`luaH_resize`). `#` returns a border by the same search as `luaH_getn`: a binary search
in the array part when its last slot is empty, otherwise an unbounded doubling search in
the hash part. Any border is a correct answer when the sequence has holes, and the proof
says the result is one.

Setting an existing field to `nil` turns its node into a tombstone and keeps its key, so
`next` can continue from a key set to `nil` during traversal, as Lua allows. Setting the
key again revives its node, a new key takes the first dead or empty node on its probe
sequence, and a rehash drops the rest. The table keeps one
counter, the nodes that are used or dead; it is only a trigger: a new key is inserted in
place while that counter is under three quarters of the hash part, and the table is
rehashed otherwise (and also when a probe finds no free node, which is the fallback the
proof relies on, not the counter). Tests churn inserts and deletes with adversarial
integer and string keys and check the longest probe stays short (`Longest_Probe`).

The keys of tombstones are strong in M3: the collector marks them, so an object stays
alive while a dead node names it. M5 revisits this with weak tables and `__gc`.

The order of `next` differs from PUC Lua (other hashes, other probing), so the M4
differential tests must not depend on the order of `pairs`.

### Garbage collector

`Pyro.Collector` is a stop-the-world mark and sweep over the roots the caller gives (in M4,
the VM's stacks, registry and open upvalues). Incremental or generational collection is a
later optimisation and not required for correctness.

- **Mark** colours objects white, gray or black, as `lgc.c` does. The roots turn gray;
  then each gray object taken off the gray list has its children shaded and turns black.
  The gray list is threaded through the slots' link field, which free slots use for the
  free list, so marking allocates nothing and works when memory has run out. A slot taken
  off the gray list is checked to be gray, so the list needs no invariant; once it is
  empty, a pass over the slots checks that none is gray. If one is, or the list runs past
  one entry per object (neither can happen), marking is incomplete and nothing is freed.
- **Sweep** frees every white object, takes freed strings out of the intern set, returns
  their memory to the budget, and makes every object white again.
- A collection runs in three steps, `Start`, `Mark_Roots` (once per array of roots) and
  `Finish`, so the VM shades its stack and constants where they are instead of gathering
  them. `Finish` keeps every object that was not white when it started: the VM's roots are
  known to survive a collection, and nothing else is.
- Weak tables (`__mode`) and finalisers (`__gc`) come in M5. Until then, a table's dead
  keys are strong (see Tables).

Gold properties: when marking is complete, the roots are not white and every child of an
object that is not white is not white either (the tricolour invariant, with no gray left);
sweep frees exactly the white objects; `Is_Valid (Heap)` holds after collection. Together:
every object on a path from the roots survives with its kind and contents (a lemma by
induction on the path, a ghost sequence of handles).

## Virtual machine (M4)

### Execution model

The VM is a **single loop that never recurses** for Lua-level control flow. Each
coroutine (thread) has its own value stack and frame stack; a Lua call pushes a
frame, a return pops one. Consequences:

- deep Lua recursion is limited by a configurable frame limit, reported as a Lua
  "stack overflow" error, never by the Ada stack;
- coroutines are just thread objects: resume and yield switch which thread the loop
  is running;
- metamethods that are Lua functions (`__index`, `__add`, `__eq`, `__lt`, `__concat`,
  `__close`, …) are called by pushing a frame marked with a **continuation**: what to
  do with the result when it returns (store into register R, invert a comparison and
  jump, continue a concatenation, …). This is the same idea as `luaV_finishOp` in
  PUC Lua.

The stack and the frames follow `lstate.h`. A frame records where its function is
(`Func`), where its registers end (`Top`), its prototype and program counter, how many
results its caller wants, and its origin: the place its results go. A vararg function
moves its function above its arguments (`luaT_adjustvarargs`), keeping the extra ones
below it, so its origin and its function differ; returns and tail calls use the origin,
not the RETURN instruction's operand. The frame invariant (PROOFS.md) says every frame
lies in the stack and starts above the function of the frame below it; growing the stack
keeps it, and passing the stack or frame limit raises "stack overflow" as a Lua error.

The dispatch loop (`Pyro.Virtual_Machine.Execution`) decodes one instruction and calls
its handler. The handlers work through a small core in the parent package (registers,
constants, upvalues, calls, returns, errors), whose contracts are stated over a view of
the running frame, so they prove against those contracts and never see the machine's
representation. The core passes the parts of the machine it changes (the stack, the
frames, the heap) to its helpers, so that what it does not pass is known unchanged.

### Metamethods

A metamethod that is a function is called like any function, by pushing its frame: the
loop never recurses into itself. The Lua frame that called it records what to do when it
returns (`luaV_finishOp`'s job): store the result in a register (`__index`, arithmetic,
`__len`, `__unm`, ...), or skip the jump after a comparison unless the result's truth is
the one its k flag asks for (`__eq`, `__lt`, `__le`); `__newindex` wants no result. The
frame invariant says the register is one of the frame's. `__index` and `__newindex` chains
of tables are followed in place, at most `MAXTAGLOOP` (2000) of them. `__call` puts its
metamethod below the arguments, as `luaD_tryfuncTM` does.

Table constructors do not presize their tables (tests/known-differences.md): a table's
parts grow as keys arrive. The VM reads tables (next, length) through
`Pyro.Heap.Table_Reads`, a child of the heap, so that the heap's own proofs do not grow.

Only tables have metatables for now: the string metatable comes with the string library
(M5), and pyrolua's runtime corpus runs reference Lua without one. Metamethod names are
interned when a chunk is loaded and kept in the registry, so a lookup allocates nothing.

### Host functions

A host function is called from the dispatch loop without the loop calling back into the
host: `Run` returns to its caller with the status `Host_Call`, and the host reads the call
(`Host_Function`, `Argument_Count`, `Argument`) and answers with one of:

- `Return_Values`: return these values;
- `Raise_Error` or `Raise_Message`: raise this error value, or this message after the
  position of a calling function (as `luaL_error` and `error` do);
- `Call`: call this function with these arguments, then continue me with its results.
  With `Protect`, an error in that call is caught and continues me with the error
  instead (`Call_Succeeded` is then false).

The host function's frame stays on the stack, holding its arguments, while the call it
asked for runs; when the call returns, `Run` reports the same frame again with the
continuation number the host gave (`Continuation`), its arguments and the call's results
(`Result_Count`, `Result`). This is `lua_callk`'s continuation: `pcall` is a host function
that asks for a protected call and returns `true` and the results, or `false` and the
error. A host function keeps no handle across answers except in its frame, so the
collector's roots cover everything a host function holds. `Run` also returns `Paused`
after a slice of instructions, so that every call of it returns, and `Step_Limit_Reached`
when the step limit set at `Load` is reached.

### Errors

A Lua error (from a failed operation or raised by a host function) is a value, kept in the
registry while the VM unwinds frames down to a host function that asked for a protected
call (`pcall`'s), which then continues with the error. With none, `Run` returns `Errored`
and `Error_Text` gives the message.

The to-be-closed variables above the frame that catches the error are closed first
(`luaD_closeprotected`): each `__close` is called with the error, as a call of the host
function that caught it, still protected, so that an error in a `__close` replaces the
error and the next one still runs; the unwinding goes on when each returns. An error no
frame catches closes every variable the same way before the machine is done. On normal
exits (CLOSE, a RETURN that closes, the generic for's closing value) the frame runs its
instruction again after each `__close`, one variable per pass, and a RETURN keeps its
results where they are while it does.

Error messages are PUC Lua's, with the position of the instruction that failed
(`chunk:line:`) and, where `ldebug.c` gives one, the name of the value at fault: the
handlers say which register or upvalue each operand came from, and `getobjname`,
`findsetreg` and `funcnamefromcode` are ported to read the chunk's debug information
(locals, upvalue names, constants) and its code, as PUC Lua does: "(global 'x')", "(field
'y')", "(local 'z')", "(upvalue 'w')", "(constant 'k')", "(method 'm')", "(for iterator
'for iterator')", "(metamethod 'index')". A frame that called is at the instruction
before its program counter, as `currentpc` finds it, for the line of `error (msg, 2)`.

### Semantics to get right

These are where differential tests matter most:

- integer vs. float arithmetic: `/` and `^` always produce floats, `//` and `%`
  use floor semantics, integer `//` or `%` by zero is an error while float division
  by zero gives inf/NaN, the minimum integer `// -1` wraps;
- bitwise operators on floats with exact integer values, shifts ≥ 64 give 0,
  negative shifts shift the other way;
- comparisons between integers and floats are exact (no rounding through float);
- string/number coercions: number-to-string in concatenation only (see the README
  for string arithmetic);
- numeric `for` loops: overflow-safe iteration count computed up front, float
  loops, zero step is an error;
- metamethod lookup is raw (`rawget` on the metatable), `__index`/`__newindex`
  chains have a loop limit (as PUC Lua's `MAXTAGLOOP`);
- `__eq` is only tried for two tables or two userdata; `__lt`/`__le` (no `__le`
  emulation via `__lt` in 5.4);
- `<close>` variables are closed on normal exit, `break`, `goto`, `return` and
  errors, in reverse order;
- varargs, multiple returns and truncation/extension of value lists;
- `tostring`-style formatting of numbers (`%.14g`, `-nan`/`nan`, `inf`, `1e+15`
  vs. `1e15`, integral floats print with `.0`).

## Embedding API (M6)

Pyro Lua is for hosts that run scripts they do not trust, and most such hosts are written
in C or C++ (game engines, servers, rules engines). Its primary embedding API is therefore
a C API, `pyrolua.h`, built as a static and a shared library; `Pyro.Embedding` gives the
same operations to Ada and SPARK hosts. Both are thin layers over the same proven core,
and neither adds behaviour of its own.

What a host can do, in either API:

- create and destroy a state, with limits (memory, instruction budget, call depth) and a
  hash seed;
- load a chunk from bytes, getting a function or a syntax error;
- call a function, protected (errors come back as a value, never an exception or a jump);
- create and inspect values: numbers, strings, tables (get/set/next), metatables;
- register host functions;
- coroutines: create, resume, query status; host functions can yield;
- handles to Lua values held by the host count as GC roots.

The C API's shape follows from what the proofs need:

- **Opaque handles**, for the state and for values, never raw stack slots. A host cannot
  name a slot that does not exist, and the stack's layout stays the core's business.
- **Errors as return codes**, never `longjmp`. Every call that can fail says so in its
  result, and the core's own errors never unwind through host frames.
- **Host functions as C function pointers**, registered with the state and called
  through the same protected-call machinery as Lua functions.

Host code is outside the proofs: a C host that passes a dangling handle or a buffer of
the wrong size can still corrupt its own memory, and a host function can do whatever C
can do. The proofs cover what the core does with whatever arrives through the API, and the
API checks what it can (handle validity, sizes) before passing it on.

The thread that calls Pyro needs `Pyro.Minimum_Stack_Size` bytes of stack (PROOFS.md,
Assumptions); a host whose threads may have less runs Pyro in a thread or Ada task with
that much stack, as the `pyrolua` program does.

Pyro has no standard library, so these primitives are how a host exposes things like
`setmetatable`, `pcall`, `error`, `pairs` or `coroutine.resume` to scripts, if it
wants to.

### Threat model

The attacker controls the source of the scripts the host loads and everything they do at
run time; the attacker does not control the host or the functions it registers. Against
that attacker:

- **Memory corruption** of the interpreter (overflows, out-of-bounds reads, use after
  free, type confusion) is ruled out by the proofs.
- **Crashes** of the interpreter are ruled out by the proofs (no runtime errors) and by
  the limits below (no stack exhaustion).
- **Denial of service** is bounded by the instruction budget, the memory limit and the
  depth limits, and by a per-state random hash seed: a script cannot craft string keys
  that all land in the same bucket of a table, because it cannot know the seed.

What a script can still do is fail with a Lua error, run until its budget runs out, and
call the functions its host chose to give it.

### Sandbox limits

- **Instruction budget:** the VM counts instructions and stops with a
  "budget exceeded" error when the budget runs out (the host can refill it and
  resume, or abort).
- **Memory limit:** enforced by the single allocator described above.
- **Depth limits:** call depth, C-call nesting, parser nesting.
- **Hash seed:** each state hashes strings with a random seed that the host gives when
  it creates the state (the `pyrolua` program takes one from the operating system), so a
  script cannot predict which keys collide in a table.

Together with the proofs, these mean a script can neither crash the interpreter nor
take over the host process. It can only fail with a Lua error.
