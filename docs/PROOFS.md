# Pyro Lua proofs

This document states what Pyro proves, what it trusts without proof, and what it only
tests. It is the authority on proof policy: if code and this document disagree,
one of them is wrong and must be fixed.

## Proof levels

SPARK groups assurance into levels:

| Level | Meaning |
| --- | --- |
| Stone | Code is in the SPARK subset |
| Bronze | Flow analysis passes: no uninitialised reads, contracts on data flow hold |
| Silver | Absence of runtime errors: no overflow, range, index, division, discriminant or null-pointer check can fail |
| Gold | Functional properties stated as contracts are proven |

Pyro's target:

- **Silver for every unit** except the trusted ones listed below.
- **Gold for the properties below**, chosen because a bug there would be a memory
  safety bug (use-after-free, out-of-bounds access, type confusion) rather than a
  wrong answer.

## Gold properties

### Growable arrays (M1)

`Pyro.Growable_Arrays` is proven to behave like a sequence: append, set and truncate
have postconditions in terms of a ghost model, and growth preserves existing
contents. Everything else builds on this. Its type invariant says every element has
its place in an allocated chunk; the definitions behind it (`Allocated`,
`All_Allocated`, `Element`) are hidden from clients, which reason through the model
alone and so do not carry the chunk arithmetic.

### Syntax tree well-formedness (M1)

Every child id in a node is smaller than the node's own id and refers to an existing
node; child list slices are in range. Proven as a postcondition of every AST
construction operation, which gives acyclicity and termination of tree walks. The
property is stated on the nodes as `Get` returns them, whatever their stored form: a
node is kept in its compact form only when that form reads back as the same node
(checked when it is added), and otherwise in the side table, so the proofs need no
lemma about the encoding.

### Lexer and parser totality (M1)

For every input byte sequence (up to the configured maximum size), the lexer and
parser terminate and return either a result or an error. This is mostly Silver plus
termination (`Subprogram_Variant` on recursive subprograms, loop variants on loops).

### Bytecode validity (M2)

Predicate `Pyro.Bytecode.Is_Valid`: register operands below the prototype's stack size,
jump targets inside the code, constant, nested prototype and upvalue indices in range,
instruction pairs the VM relies on in place, and no execution path falls off the end of
the code. It is executable SPARK, so it serves as its own validator: the compiler checks
its result with it and returns an internal error otherwise. Every prototype the compiler
returns is therefore proven `Is_Valid`; that the internal error never fires is tested,
not proven (see "Tested, not proven"). The VM requires `Is_Valid` and relies on it to
omit runtime checks.

### Heap validity (M3)

Invariant `Is_Valid (Heap)`: every `Object_Handle` stored in any live object or in any root
refers to an allocated slot of the expected object kind. Every heap operation
(allocate, store into an object, free) is proven to preserve it. It also covers what the
heap owns: every slot owns what its kind says (a free slot nothing, a string its bytes, a
table a valid table), slots past the last one own nothing, every entry in use in the
intern set is a string, so the set never refers to a freed slot, and every value a table
holds (its entries, dead keys included) refers to an object the heap holds. That last part
is stated over the ghost `Kinds` and `Graph` and hidden behind `Refs_Live`, so that only the
operations that change objects reason about it. `Pyro.Strings` (SipHash-1-3) is Silver
and checked against the reference vectors in `tests/unit`.

### Garbage collector (M3)

The heap's ghost view is `Kinds (H)` (what each slot holds), `Colors (H)` and `Graph (H)`
(the values each object holds: a table's entries). A path is a ghost sequence of handles
whose first is a root and each next one a child of the one before.

1. When marking completes, every root is not white and the set of objects that are not
   white is closed under children (`Closed`). This comes from the tricolour invariant (no
   child of a black object is white), kept by every shading and blackening, and the check
   that no object is left gray.
2. Sweep frees exactly the white objects and keeps the others with their contents.
3. `Is_Valid (Heap)` holds after collection: every value in a kept object refers to a kept
   object, and the intern set refers only to kept strings.

`Collect`'s postcondition states 1 and 2 as what the heap keeps (`Keeps_Closed`), and
`Lemma_Path_Kept` proves, by induction along any path from the roots, that its last object
is kept with its kind: the collector never frees a reachable object.

### Tables (M3)

Invariant `Is_Valid (Table)`: the array part is 1-based and its values canonical, every
node in use or dead holds a canonical key that can be found along its probe sequence
from its hash (no empty node before it), no key is stored twice, and keys in the
array part's range are not stored in the hash part. It keeps no counts: the one counter
only decides when to rehash, and safety never depends on it.

The table's meaning is a ghost map (`Model`), and every operation is specified against it:

- `Get` returns the model's value for the normalised key, or nil;
- `Set` stores the value for the key (nil removes it), leaves every other key as it was,
  and reports an invalid key or running out of memory without changing the model;
- `Resize` and rehashing keep the model;
- `Next` returns only pairs of the model;
- `Length` returns a border: zero or a key in the model, and one past it is not;
- `Clear` empties the model and returns its memory to the budget.

For the heap and the collector, every object a table names (in a key, a dead key or a
value) is in its ghost `Entries`, and `Set` is proven to add only its key and value to them.

### VM stack and frames (M4)

Frames on a thread's stack never overlap: each frame's register window lies inside
the thread's value stack and starts at or after the previous frame's base. Stack
growth keeps all frame windows valid, and exceeding the frame or stack limit produces
a Lua error, not a failed check.

## Trusted code

Units whose bodies are `SPARK_Mode => Off`, with the reason for each. Their specs are
SPARK and carry contracts; those contracts are assumed, not proven, so they must be
kept small and conservative.

| Unit | Reason | Since |
| --- | --- | --- |
| `Pyro.Floats` (body) and its C helper `src/common/pyro_floats.c` | IEEE 754 arithmetic with infinities and NaN, correctly rounded decimal-to-float conversion, `%.14g` formatting. SPARK assumes floats are finite, so these must operate on raw bits outside SPARK. Decimal conversion is libc's `strtod_l` with an explicit "C" locale, so a host calling `setlocale` cannot change how numerals are read. Constant folding (M2) uses libc's `pow`, `fmod` and `floor` as luac does, so folded constants are bit-identical to luac's. | M1, M2 |
| `cli/` (`pyrolua` executable) | File and console I/O, command-line handling, bytecode listings (with `%.14g` from libc in `cli/src/pyro_cli_floats.c`). Not part of the library. | M1 |

Any new entry needs a reason here and should be as small as possible.

Also counted as trust, and listed here when used:

- `pragma Assume`: none allowed without an entry in this section.
- `pragma Annotate (GNATprove, False_Positive | Intentional, …)`: each must have a
  justification string and be listed here.

`pragma Annotate (GNATprove, Hide_Info | Unhide_Info, …)` only keeps a definition out
of proofs (they then rely on contracts alone), so it is not trust and needs no entry.
Likewise the two `pragma Warnings (GNATprove, Off, …)` in `src/runtime/pyro-value_maps.adc`,
which `pyro_lua.gpr` applies to that one unit, the instance of SPARKlib's functional maps
that models tables: they hide the warnings that lemmas of the instance never used have
contracts that are always False (keys compare by `"="`, so there is no equivalence to
handle, and a parameter check's precondition is `Use_Logical_Equality`, which the maps
generic sets to False). A pragma in the unit itself does not reach messages placed in the
generic. They hide no check, and nothing in Pyro's own code.

Current list of assumptions and justified checks:

The ownership annotations below exist so that a type's private part (its growable
arrays and their pointers) can be hidden from its clients' proofs. The trust they add
concerns leak checking only: GNATprove takes the type's `Is_Released` to mean "holds no
heap memory". Each `Is_Released` is the conjunction of `Is_Released` of every array in the
object, each proven to mean exactly that, and nothing about runtime safety depends on it.

- `Pyro.Compiler.Code.Compiler_State` carries the ownership annotation
  `Needs_Reclamation`, with `Is_Released` as its `Is_Reclaimed` function, so that its
  private part (seventeen growable arrays) can be hidden from the compiler's proofs (M2).
- `Pyro.Syntax_Trees.Syntax_Tree`, likewise: four growable arrays, hidden from the
  parser's, resolver's and compiler's proofs (front-end memory work, after M2).
- `Pyro.Symbols.Symbol_Table`, likewise: three growable arrays (same).
- `Pyro.Bytecode.Chunk`, likewise: seven growable arrays, hidden from the compiler's
  proofs (same).
- `Pyro.Heap.Heap`, likewise: a chunked store of slots owning their objects, hidden from
  every client's proofs (M3). Its `Is_Released` is that the chunk table is gone, which
  `Clear` reaches only after freeing every slot's objects and every chunk.
- `Pyro.Tables.Table`, likewise: an array part and a hash part, hidden from the heap's
  proofs (M3). Its `Is_Released` is that both parts are gone.

## Assumptions

These are outside what SPARK can prove and are accepted:

- The compiler (GNAT), the Ada runtime and the hardware behave as specified,
  including IEEE 754 floating point.
- Memory allocation succeeds as long as Pyro stays within its own memory limit.
  The OS can still run out of memory first (for example when the limit is set too
  high or other processes use the memory); Pyro's limit makes this unlikely but
  cannot rule it out.
- The thread that calls Pyro has at least `Pyro.Minimum_Stack_Size` (4 MiB) of stack.
  Only the parser recurses, to its fixed nesting limit (200 levels); tree walks keep
  their own stacks on the heap. The number was measured by `tests/unit` `stack_test`,
  which parses every deeply nesting construct at the limit and one level beyond in a task
  with exactly that stack, built with GNAT's stack usage report (`gnatbind -u`): at most
  about 220 KB (macOS arm64, GNAT 16.1, development build). `tests/run` fails when the
  measured use passes a quarter of the constant, leaving a fourfold margin for other
  compilers, optimisation levels and targets. The `pyrolua` executable runs its work in a
  task with that stack plus 1 MiB for its own frames, so the main thread's stack (on
  Linux, `ulimit -s`) does not matter.

## Tested, not proven

Covered by tests (see [ROADMAP.md](ROADMAP.md) for the test suites), not proofs:

- **Conformance to Lua 5.4:** syntax accepted/rejected, error lines and messages,
  and runtime behaviour, by differential testing against PUC Lua 5.4.
- **Decimal float conversion, constant folding arithmetic and number formatting** (in
  the trusted float unit, which calls the C library as PUC Lua does).
- **The compiler never fails its own validity check:** the compiler's output is proven
  `Is_Valid` through the executable predicate, but that the check never rejects it (an
  internal error) is shown by compiling the corpus, the official tests and fuzzed
  sources, not proven.
- **Performance.**

## Running the proofs

```bash
alr exec -- gnatprove -P pyro_lua.gpr
```

Proof settings live in the `Prove` package of `pyro_lua.gpr` so everyone uses the same
ones:

- `--level=2` with `--prover=cvc5,z3`. Alt-ergo was dropped: it ran for more than 13
  minutes on single lexer VCs despite its `--steps-bound`, while cvc5 and z3 proved
  everything in 38 s. Re-adding a prover needs the same evidence: it stays within its
  steps bound on the whole code base and proves something the others don't;
- `--steps=30000` and `--timeout=0` (no wall-clock timeout), so a proof that is too
  hard fails the same way every time, whatever the machine load. The steps value was
  chosen during M1 setup and is raised only with the owner's OK;
- `--counterexamples=off`, so runs do not spend time on counterexamples;
- `--checks-as-errors=on` and `--warnings=error`, so an unproved check fails the run;
- `--proof-warnings=on` to catch dead code and inconsistent assumptions;
- `-j0` to use all cores.

Rules:

- `main` always proves completely with these settings.
- Proofs fit the time limits in [STYLE.md](STYLE.md#time-limits). If a unit
  becomes too slow to prove, restructure it (smaller subprograms, lemmas, child
  packages); raising limits needs the owner's OK.
- A proof that will not close is never forced through; see
  [STYLE.md](STYLE.md#proofs-that-will-not-close).
- Lemmas go in `Pyro.*.Lemmas` child packages as ghost procedures, so proof-only
  code stays out of executable units, except lemmas about a predicate completed in a
  package body, which are declared in that package (STYLE.md, Contracts).
- Validity predicates are completed in package bodies, so clients prove with the
  contracts only; gnatprove would otherwise unfold their definitions into every
  client's proofs (parser alone about 4,000 CPU-s before, whole library 1,600 CPU-s
  after). In M4 the VM relies on `Is_Valid (Prototype)` through the postconditions of
  `Pyro.Bytecode`'s accessors, which carry the bounds it needs.
- Runtime checks stay enabled in debug builds. A release build may suppress checks
  that are proven, never others.

### Proof time

The uncached proof (`tests/run --full`'s proof stage) took 587 s of its 900 s cap with
tables (584 s after the front-end memory work, and 632 s in another forced run on that
commit, so allow a few percent between runs; M2 ended at 484 s). The runtime units prove
in parallel with the compiler's, which set the wall time. Keep it at about two thirds of the cap or
below: past that, restructure before adding proofs.

When it grows, find where by unit rather than guessing:

- Run `alr exec -- gnatprove -P pyro_lua.gpr -f` with no cache, after removing
  `obj/*/gnatprove` (as the stage does). Without `-f`, gnatprove reuses earlier sessions'
  results, and a check can fail or pass depending on what ran before.
- Sum the `time` of every proof attempt in each unit's `obj/*/gnatprove/<unit>.spark`
  (JSON, under `proof`) and compare per unit with the same figures at an earlier commit
  (a worktree). Compare check counts too: more time for the same checks means a heavier
  context; more checks means more code or more instances.
- The heavy context usually comes from a private part clients can see, such as owning
  arrays with their pointer models. After the chunked arrays, the parser went from 333 s to
  751 s with the same 491 checks. With the private parts of `Syntax_Tree`, `Symbol_Table`
  and `Chunk` hidden it took 182 s.
- Every instance of `Pyro.Growable_Arrays` proves the generic body again (267 checks,
  about 9 s of prover time each; about 37 instances).

## Status

| Area | Level | Status |
| --- | --- | --- |
| Growable arrays | Gold | proven |
| Lexer | Silver + totality | proven |
| Parser, AST | Silver + well-formedness | proven |
| Resolver | Silver | proven |
| Compiler / bytecode validity | Gold | proven (output checked by the proven `Is_Valid`) |
| Heap | Gold | proven |
| Tables | Gold | proven |
| GC | Gold | proven |
| VM | Silver + frame invariant | not started |
| API | Silver | not started |
