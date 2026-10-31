# Pyro roadmap

Each milestone ends with a working, fully proven state: `gnatprove` reports zero
unproved checks and all tests pass. A milestone is done when every item in its
**Done when** list is true. Proof targets for each area are in
[PROOFS.md](PROOFS.md).

## Test infrastructure

Shared by all milestones:

- **Reference Lua:** PUC Lua 5.4 (`brew install lua@5.4`, currently 5.4.9), used
  through explicit paths to its `lua` and `luac` binaries. Never the default `lua`,
  which is 5.5.
- **Corpus:** the official Lua 5.4 test suite (`lua-5.4.x-tests.tar.gz` from
  lua.org), downloaded by a script in `tools/` rather than committed, plus Pyro's own
  files in `tests/corpus/` (one feature or edge case per file, with intentionally
  invalid files for error cases).
- **Golden files:** expected `--tokens` / `--ast` / `--bytecode` output for the own
  corpus, regenerated deliberately and reviewed as diffs.
- **Differential runs:** the same file through Pyro and the reference, comparing the
  result.
- **Mutation fuzzing:** random mutations of corpus files fed to both Pyro and
  reference `luac -p`, comparing accept/reject. The proofs already rule out crashes;
  fuzzing finds disagreements with the reference.

## M1: Front end

Project setup, lexer, parser and resolver, all proven.

- Alire library crate `pyro` with proof settings in `pyro.gpr`, nested crate
  `cli/` for the `pyro` executable, `tests/` and `tools/` scripts.
- `Pyro.Growable_Arrays`, `Pyro.Sources`, `Pyro.Diagnostics`, `Pyro.Symbols`.
- `Pyro.Lexer`, `Pyro.Numbers`, `Pyro.Floats` (decimal conversion only, for now).
- `Pyro.AST`, `Pyro.Parser`, `Pyro.Resolver`.
- `pyro --tokens`, `pyro --ast`, `pyro --check`.

**Done when:**

- `gnatprove` proves everything at the M1 targets in PROOFS.md (Silver everywhere,
  Gold for growable arrays and AST well-formedness, termination of lexer and
  parser).
- For every `.lua` file in the official 5.4 test suite and the own corpus,
  `pyro --check` and reference `luac -p` agree on accept/reject, and on the error
  line for rejected files. Differences in message wording are listed in
  `tests/known-differences.md` with a reason, and the list is short.
- Mutation fuzzing runs for an agreed number of iterations with no accept/reject
  disagreement.
- Golden files exist for tokens and AST of the own corpus.
- README status and the PROOFS.md status table are updated.

## M2: Compiler and bytecode

- `Pyro.Bytecode` instruction set, prototypes, ghost `Valid` predicate.
- `Pyro.Compiler`: AST to bytecode for the whole language, including closures,
  upvalues, varargs, `goto`, `<const>` constant folding, `<close>`, numeric and
  generic `for`.
- Compile-time limits (locals, upvalues, registers) with PUC Lua's errors.
- `pyro --bytecode`.

**Done when:** the compiler is proven to produce `Valid` prototypes; the corpus
compiles; files that hit compile-time limits are rejected in agreement with
`luac -p`; golden bytecode listings exist for the own corpus.

## M3: Values, heap, tables, GC

- `Pyro.Values`, `Pyro.Heap`, `Pyro.Strings`, `Pyro.Tables`, `Pyro.GC`.
- Mark and sweep collector, without weak tables and finalisers.

**Done when:** `Heap_Valid`, `Table_Valid` and the GC properties are proven; unit
tests in `tests/` exercise tables (including traversal while deleting) and
collection with synthetic root sets; stress tests allocate and collect large object
graphs within the memory limit.

## M4: Virtual machine

- `Pyro.VM` executing compiled chunks: arithmetic, comparisons, concatenation,
  tables, closures and upvalues, varargs, metatables and all metamethods, Lua
  errors with source positions, protected calls, `<close>`.
- `Pyro.Floats` gains float formatting.
- The GC runs during execution.
- `pyro file.lua`, with a fixed set of host functions for testing (`print` plus
  whatever the test corpus needs: `setmetatable`, `pcall`, `error`, `type`,
  `select`, …). These live in `cli/`, not in the library.

**Done when:** the VM frame invariant is proven and the VM is Silver; a runtime
corpus of Lua scripts (written to use only the test host functions) produces
byte-identical output under Pyro and reference Lua 5.4; errors match in position and,
where practical, message.

## M5: Coroutines, weak tables, finalisers

- Coroutines as thread objects: create, resume, yield, status, wrap semantics;
  yielding across metamethods and host functions with continuations.
- Weak tables (`__mode`), finalisers (`__gc`), and the generational/incremental
  collector work if profiling shows it's needed.

**Done when:** proven at the same levels as M4, GC properties still proven with weak
references (a weakly referenced object may be collected; a strongly reachable one
may not); differential tests for coroutine and GC-related scripts pass.

## M6: Embedding API and sandbox

- `Pyro.API` as described in DESIGN.md.
- Instruction budget, memory limit, depth limits.
- An example host program in `examples/`.

**Done when:** the API is Silver; a script cannot exceed its limits, which is shown
by tests that run hostile scripts (infinite loops, unbounded allocation, deep
recursion, string bombs) and get clean Lua errors; the README documents embedding.

## Later

- Performance work: profiling, instruction specialisation, table and string fast
  paths, faster collector. Proofs stay complete.
- More Gold where it pays off, for example proving the lexer against a formal token
  grammar.
- Optional companion crate implementing parts of the standard library on top of
  `Pyro.API`, outside the core.
