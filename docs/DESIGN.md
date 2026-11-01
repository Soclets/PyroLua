# Pyro design

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
generic, `Pyro.Growable_Arrays`, on top of SPARK's pointer ownership (an owned access
to an array, reallocated on growth), proves it once and reuses it everywhere. Its
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
| `Pyro.Strings` | M3 | String objects, hashing, interning |
| `Pyro.Tables` | M3 | Lua tables |
| `Pyro.Garbage_Collector` | M3 | Mark and sweep collector |
| `Pyro.Virtual_Machine` | M4 | Interpreter loop, call frames, metamethods |
| `Pyro.Embedding` | M6 | Embedding API for Ada/SPARK hosts |

Source folders, file naming and the rules for private and public packages are in
[STYLE.md](STYLE.md#packages-and-files).

The `pyro` executable (`cli/`) is ordinary Ada. It handles files, command-line
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
`luac -p` reports them, so `pyro --check` must too. `Pyro.Resolver` walks the tree
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

**Rich messages**, for what the `pyro` program or a host prints, in the layout of
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
since scripts see them through `pcall`. `pyro --check --lua-style` prints exactly what
`luac -p` prints: the single error PUC Lua would detect first, in its exact text and
line. Every diagnostic therefore records its PUC detection point (the token PUC's
parser would be looking at when it raises the error, for example the token after a
function's `end` for an undefined `goto`), and the Lua-style report picks the one with
the earliest detection point. To find semantic errors that precede the first syntax
error, the parser keeps the partial tree it built before stopping; the resolver skips
the checks PUC makes when a block closes for blocks that never closed.

## Compiler and bytecode (M2)

Pyro has its own register-based instruction set, modelled on Lua 5.4's (`lopcodes.h`)
but not binary-compatible with it. A **prototype** holds the instructions,
constants, nested prototypes, upvalue descriptors, parameter count, vararg flag,
maximum stack size and line info.

`Pyro.Bytecode` defines a ghost predicate `Is_Valid (Prototype)`: every register operand is
below the prototype's stack size, every jump target is inside the code, every
constant/prototype/upvalue index is in range, and the code cannot fall off the end.
The compiler's postcondition is `Is_Valid` for every prototype it produces, and the
VM's precondition requires it. The VM can then skip these checks at runtime.

Limits follow PUC Lua: at most 200 locals per function, 255 upvalues, 255 registers.

`pyro --bytecode file.lua` prints a listing.

## Values, heap and tables (M3)

### Values

A Lua value is a small discriminated record:
`nil | boolean | integer (Integer_64) | float (raw bits) | object (Object_Handle)`.
Strings, tables, closures, prototypes, upvalue cells, coroutines and host userdata
are heap objects referenced by `Object_Handle`. Light userdata (a host-supplied opaque
integer) can be added as an immediate case if the API needs it.

### Heap

`Pyro.Heap` is an arena of object slots with a free list. Every slot is either free
or holds one object of a known kind. The central invariant, `Is_Valid (Heap)`, says every
`Object_Handle` stored in any live object or root (VM stacks, registry, open upvalues,
the host's handles) refers to an allocated slot of the expected kind. Every heap
operation preserves `Is_Valid (Heap)` (Gold).

### Strings

Strings are immutable heap objects with a cached hash. Short strings (40 bytes or
less, as in PUC Lua) are interned so equality is a handle comparison. Long strings
are compared by content.

### Tables

A table has an array part (keys `1..N`) and a hash part (open addressing). Key rules
from the manual: `nil` and NaN keys are errors on assignment; float keys with an
integral value are normalised to integers (`t[2.0]` is `t[2]`).

`next`-style traversal must keep working when existing fields are set to `nil`
during traversal, as Lua allows. Deleting therefore leaves a tombstone, and rehashing
happens only when a new key is inserted.

The invariant `Is_Valid (Table)` (Gold) says: every key in the hash part can be found
along its probe sequence, element counts are consistent, no key appears twice, and
array-part keys are never also stored in the hash part. Get, set, delete, resize and
next are proven to preserve it, and get is proven to return what the last set
stored for that key.

The length operator `#` follows Lua's border semantics (any border is acceptable
when the sequence has holes), so it doesn't have to match the reference exactly.

### Garbage collector

Stop-the-world mark and sweep first. Incremental or generational collection is a
later optimisation and not required for correctness.

- **Mark** uses an explicit gray stack (no recursion), bounded by the number of
  objects.
- **Sweep** frees unmarked objects and returns their slots to the free list.
- Weak tables (`__mode`) and finalisers (`__gc`) are part of Lua 5.4 semantics and
  come after the basic collector is proven.

Gold properties: after marking, every object reachable from the roots is marked;
sweep frees only unmarked objects; `Is_Valid (Heap)` holds after collection. Together:
the collector never frees a reachable object. Reachability is defined as a ghost
function over the heap.

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

Host functions (registered through the API) are Ada subprograms called from the
loop. If a host function needs to call back into Lua, it can either request a call
with a continuation (preferred, keeps the loop flat) or re-enter the VM, which is
allowed up to a fixed nesting depth.

### Errors

A Lua error (from a failed operation or raised by a host function) is a value. The
VM unwinds frames until it reaches a protected-call frame, running `__close`
handlers on the way, and resumes there with the error value. With no protected
frame, the error is returned to the host. Error messages include the source
position (`chunk:line:`) as PUC Lua's do.

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

`Pyro.Embedding` gives an Ada/SPARK host what the Lua C API gives a C host, in a typed
form instead of a raw stack:

- create and destroy a state, with limits (memory, instruction budget, call depth);
- load a chunk from bytes, getting a function or a syntax error;
- call a function, protected (errors come back as a value, never an exception);
- create and inspect values: numbers, strings, tables (get/set/next), metatables;
- register host functions (access-to-subprogram types with contracts);
- coroutines: create, resume, query status; host functions can yield;
- handles to Lua values held by the host count as GC roots.

The thread that calls Pyro needs `Pyro.Minimum_Stack_Size` bytes of stack (PROOFS.md,
Assumptions); a host whose threads may have less runs Pyro in an Ada task with that
`Storage_Size`, as the `pyro` program does.

Pyro has no standard library, so these primitives are how a host exposes things like
`setmetatable`, `pcall`, `error`, `pairs` or `coroutine.resume` to scripts, if it
wants to.

### Sandbox limits

- **Instruction budget:** the VM counts instructions and stops with a
  "budget exceeded" error when the budget runs out (the host can refill it and
  resume, or abort).
- **Memory limit:** enforced by the single allocator described above.
- **Depth limits:** call depth, C-call nesting, parser nesting.

Together with the proofs, these mean a script can neither crash the interpreter nor
take over the host process. It can only fail with a Lua error.
