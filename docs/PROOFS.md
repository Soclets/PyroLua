# Pyro proofs

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
contents. Everything else builds on this.

### Syntax tree well-formedness (M1)

Every child id in a node is smaller than the node's own id and refers to an existing
node; child list slices are in range. Proven as a postcondition of every AST
construction operation, which gives acyclicity and termination of tree walks.

### Lexer and parser totality (M1)

For every input byte sequence (up to the configured maximum size), the lexer and
parser terminate and return either a result or an error. This is mostly Silver plus
termination (`Subprogram_Variant` on recursive subprograms, loop variants on loops).

### Bytecode validity (M2)

Ghost predicate `Pyro.Bytecode.Is_Valid (Prototype)`: register operands below the
prototype's stack size, jump targets inside the code, constant, nested prototype
and upvalue indices in range, and no execution path falls off the end of the code.
The compiler's postcondition is `Is_Valid` for every prototype it produces. The VM
requires `Is_Valid` and relies on it to omit runtime checks.

### Heap validity (M3)

Invariant `Is_Valid (Heap)`: every `Object_Handle` stored in any live object or in any root
refers to an allocated slot of the expected object kind. Every heap operation
(allocate, store into an object, free) is proven to preserve it.

### Garbage collector (M3)

With reachability defined as a ghost function over the heap and the root set:

1. after the mark phase, every object reachable from the roots is marked;
2. sweep frees only unmarked objects;
3. `Is_Valid (Heap)` holds after collection.

Together these say the collector never frees a reachable object.

### Tables (M3)

Invariant `Is_Valid (Table)`: every hash-part key can be found along its probe sequence,
no key is stored twice, counts are consistent, array-part keys are not also in the
hash part. Get, set, delete, resize and next preserve it. Get after set returns the
stored value for that key (a functional model of the table as a ghost map).

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
| `Pyro.Floats` (body) | IEEE 754 arithmetic with infinities and NaN, correctly rounded decimal-to-float conversion, `%.14g` formatting. SPARK assumes floats are finite, so these must operate on raw bits outside SPARK. | M1 |
| `cli/` (`pyro` executable) | File and console I/O, command-line handling. Not part of the library. | M1 |

Any new entry needs a reason here and should be as small as possible.

Also counted as trust, and listed here when used:

- `pragma Assume`: none allowed without an entry in this section.
- `pragma Annotate (GNATprove, False_Positive | Intentional, …)`: each must have a
  justification string and be listed here.

Current list of assumptions and justified checks: *none*.

## Assumptions

These are outside what SPARK can prove and are accepted:

- The compiler (GNAT), the Ada runtime and the hardware behave as specified,
  including IEEE 754 floating point.
- Memory allocation succeeds as long as Pyro stays within its own memory limit.
  The OS can still run out of memory first (for example when the limit is set too
  high or other processes use the memory); Pyro's limit makes this unlikely but
  cannot rule it out.
- The Ada stack is large enough for Pyro's bounded recursion depth (parser and tree
  walks). The bounds are fixed constants, so the required stack size is fixed too;
  the `pyro` executable sets an adequate stack size.

## Tested, not proven

Covered by tests (see [ROADMAP.md](ROADMAP.md) for the test suites), not proofs:

- **Conformance to Lua 5.4:** syntax accepted/rejected, error lines and messages,
  and runtime behaviour, by differential testing against PUC Lua 5.4.
- **Decimal float conversion and number formatting** (in the trusted float unit).
- **Performance.**

## Running the proofs

```bash
alr exec -- gnatprove -P pyro.gpr
```

Proof settings live in the `Prove` package of `pyro.gpr` so everyone uses the same
ones. Planned defaults:

- `--level=2`;
- an explicit `--steps` limit and no wall-clock `--timeout`, so a proof that is too
  hard fails the same way every time, whatever the machine load. The value is chosen
  during M1 setup, recorded here, and raised only with the owner's OK;
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
  code stays out of executable units.
- Runtime checks stay enabled in debug builds. A release build may suppress checks
  that are proven, never others.

## Status

| Area | Level | Status |
| --- | --- | --- |
| Growable arrays | Gold | not started |
| Lexer | Silver + totality | not started |
| Parser, AST | Silver + well-formedness | not started |
| Resolver | Silver | not started |
| Compiler / bytecode validity | Gold | not started |
| Heap | Gold | not started |
| Tables | Gold | not started |
| GC | Gold | not started |
| VM | Silver + frame invariant | not started |
| API | Silver | not started |
