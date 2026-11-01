# Pyro Lua implementation style

How Pyro's code is written, tested, committed and worked on. These rules apply to
everyone working on Pyro, human or Claude. [DESIGN.md](DESIGN.md) says *what* is
built, [PROOFS.md](PROOFS.md) what must be proven; this document says *how*.

Changing a rule here is a decision for the owner (see [Asking](#asking)).

## Formatting

- Standard Ada style: `Mixed_Case_With_Underscores` for identifiers, lowercase
  keywords, 3-space indentation, lines of at most 100 characters.
- Enforced by the compiler: GNAT style checks are switched on in `pyro_lua.gpr` with
  warnings as errors, so badly formatted code does not build.
- Types are named for what they are (`Token_Kind`, `Node_Index`), with no `T_`
  prefix or `_Type` suffix.

## Naming

**No abbreviations in code.** Words are written in full: `Position`, not `Pos`;
`Length`, not `Len`; `Maximum_Depth`, not `Max_Depth`; `Prototype`, not `Proto`;
`Environment`, not `Env`. This includes loop indices: `Position`, `Slot`, `Index`,
not `I`, `J`, `K`.

The only exceptions are **names**:

- names of standards and encodings, written as they are named: `IEEE`, `ASCII`,
  `UTF_8`, `NaN`;
- Lua's own vocabulary from the reference manual: `Upvalue`, `Vararg`, `Metatable`,
  `Metamethod`.

The rule applies to code. Prose in docs and comments may say "AST", "VM" or "GC".

Package names follow the same rule: `Pyro.Syntax_Trees`, `Pyro.Virtual_Machine`,
`Pyro.Garbage_Collector`, `Pyro.Embedding`.

Index and handle types say what they index: `Node_Index` is a slot in an arena,
`Object_Handle` is a reference to a heap object.

## Comments

- **Specs (`.ads`) carry the documentation.** Every public declaration has a comment
  in full sentences saying what it is or does. Contracts are part of that
  documentation, so comments explain meaning and intent rather than repeating
  `Pre`/`Post`.
- **Bodies (`.adb`) are commented sparingly.** Comments explain *why*, never *what*.
- **Proof code gets a reason.** Each lemma and each non-obvious loop invariant has a
  line saying what it establishes and why the prover needs it.
- **Every file starts the same way:** the SPDX line, then one sentence on what the
  unit is for.

  ```ada
  --  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
  --
  --  Tokenizer for Lua 5.4 source text.
  ```

- No commented-out code. No `TODO`s on `main`: unfinished work goes in
  [ROADMAP.md](ROADMAP.md), behaviour gaps in `tests/known-differences.md`.
- GNAT comment format: `--`, two spaces, text.

### Tags

Comments that point at something use a tag, so scripts can find them. A tag starts
the comment and is written exactly as below.

| Tag | Meaning | Example |
| --- | --- | --- |
| `[lua §N]` | Implements this section of the Lua 5.4 reference manual | `--  [lua §3.4.1] Arithmetic operators.` |
| `[puc file:function]` | Mirrors this part of PUC Lua's source | `--  [puc llex.c:read_numeral]` |
| `[limit NAME]` | Enforces a Lua limit | `--  [limit LUAI_MAXCCALLS] Parser nesting.` |
| `[differs]` | Deliberately differs from PUC Lua | `--  [differs] Names are ASCII only.` |
| `[proof]` | Lemma, invariant or ghost code, and why it is needed | `--  [proof] Keeps children below their parent.` |
| `[trusted]` | Code that is not proven, and why | `--  [trusted] IEEE arithmetic with inf and NaN.` |

`tools/where` searches them:

```bash
tools/where lua §3.4.1      # every file:line implementing that manual section
tools/where puc llex.c      # everything mirroring llex.c
tools/where trusted         # every unproven spot
```

`tests/run` checks that tags and docs agree, and fails otherwise:

- every `SPARK_Mode => Off` and every `pragma Annotate` carries a `[trusted]` tag;
- every `[trusted]` spot is listed in [PROOFS.md](PROOFS.md#trusted-code);
- every `[differs]` spot is listed in `tests/known-differences.md`.

## Contracts and ghost code

- **No global mutable state in the library.** All state is passed explicitly, so
  nearly every subprogram is `Global => null`. Several Lua states can then live side
  by side in one host.
- **Distinct types, not subtypes, for different kinds of index** (`Node_Index`,
  `Object_Handle`, `Register`, …), so the compiler rejects mixing them. Raw
  `Integer` and `Natural` do not appear in public interfaces.
- **Validity as named predicate functions** (`Is_Valid (Heap)`,
  `Is_Well_Formed (Tree)`) used in `Pre`/`Post`, not `Type_Invariant`.
  `Dynamic_Predicate` is fine for simple constraints on a single value.
- **Validity predicates are declared in the spec and completed in the package
  body.** Clients reason through the package's contracts, never through the
  definition: gnatprove unfolds an expression function completed in a private part
  into every client's proofs (the parser alone took about 4,000 CPU-s with them
  there; the whole library proves in 1,600 CPU-s with them in the bodies). Simple
  accessors (`Length`, `Count`) stay expression functions in the private part.
- **Export what clients need from a predicate,** preferably as a postcondition on the
  accessor (for example an operand accessor whose `Post` says it is below
  `Stack_Size` when `Is_Valid` holds), otherwise as a ghost lemma procedure declared
  in the same package and proven in its body, where the definition is visible.
- **Inside the package, hide large predicate bodies too** (`pragma Annotate (GNATprove,
  Hide_Info, "Expression_Function_Body", …)`) and unhide them only in the subprograms
  that need their contents. Give predicates used inside a quantifier preconditions
  rather than guards, and avoid calling other preconditioned expression functions in a
  quantified definition: gnatprove then fails to instantiate the quantifier.
- **State records with many owning components get a hidden private part**
  (`Hide_Info, "Private_Part"`, with the `Ownership` annotation it requires): otherwise
  every client proof carries the pointer model of each component, and checks as simple
  as a literal's length run out of steps (the compiler's walker: about 60 unproved
  checks before, none after).
- **`Contract_Cases`** where behaviour splits into clear cases (success, each kind of
  error).
- **Termination is always proven:** `Always_Terminates` on subprograms,
  `Loop_Variant` on every `while` loop, `Subprogram_Variant` on every recursive
  subprogram.
- **Models come from SPARKlib.** Ghost views of data structures use SPARKlib's
  functional containers (sequences, maps, sets), not hand-written ones. `sparklib`
  is an Alire dependency.
- **Lemmas live in `.Lemmas` child packages** as ghost procedures, never in
  executable units. The exception is a lemma about a predicate completed in a package
  body: a child cannot see that body, so the lemma is declared in the package itself.
- **`pragma Assert` only as a short proof hint.** A hint longer than a couple of
  lines becomes a named lemma.

## Packages and files

- GNAT's default file naming: `Pyro.Syntax_Trees` is `pyro-syntax_trees.ads` and
  `pyro-syntax_trees.adb`.
- Source folders by pipeline stage, all included by `pyro_lua.gpr`:

  | Folder | Contents |
  | --- | --- |
  | `src/common/` | Growable arrays, sources, diagnostics, symbols, floats |
  | `src/front_end/` | Lexer, parser, syntax trees, resolver |
  | `src/compiler/` | Bytecode, compiler |
  | `src/runtime/` | Values, heap, strings, tables, garbage collector, virtual machine |
  | `src/embedding/` | Host API |

- **Private types by default.** Representation goes in the private part; clients
  see operations and predicates.
- **Private child packages for internals** (`private package Pyro.Lexer.Numerals`),
  so other units cannot depend on implementation details.
- **Only `Pyro.Embedding` is the stable public API.** The `pyrolua` executable may use
  internal packages (it needs the lexer for `--tokens`); hosts use only
  `Pyro.Embedding`.
- **Split by proof time, not line count.** When a unit is slow to prove or hard to
  follow, split it into child packages. A body over about 1000 lines is due for a
  look. Split long subprograms too: each check in straight-line code carries every
  earlier call's postcondition, so proof cost grows roughly quadratically with the
  length of a sequence of calls.
- **Generic instantiations are library-level units of their own**
  (`Pyro.Node_Arrays is new Pyro.Growable_Arrays (…)`), proven once and shared.

## Commits

- **Message format** (as in CyborgPL): `type.area.topic: summary`, with the owner's
  call in parentheses when there was one, and a body only when there is something to
  say.
  - Types: `feature`, `fix`, `proof`, `test`, `design`, `decision`, `refactor`.
  - Areas: the pipeline stage or unit (`lexer`, `parser`, `heap`, `tables`, …), or
    `house` for repository-wide changes.
  - Example: `feature.lexer.strings: long brackets of any level, with the leading
    newline dropped`
- **Co-author trailer by role:** `Co-Authored-By: design claude
  <noreply@anthropic.com>` for the design session, `Co-Authored-By: implementation
  claude <noreply@anthropic.com>` for the implementing one.
- **Every commit on `main` is green:** `tests/run` passes. No work-in-progress
  commits.
- **One commit per coherent step:** "lexer reads all numerals", not "all of M1" and
  not ten "fix typo" commits. Proofs, tests and doc updates go in the same commit as
  the code they belong to.
- **Commit straight to `main` and push after every green commit.** No branches or
  pull requests while one session implements; revisit if several work in parallel.

## Testing

- **`tests/run` checks everything:** build, gnatprove, tag/doc agreement, golden
  files, differential tests against Lua 5.4.9, a short fuzzing run. A commit is
  green when it passes.
- **Every feature commit adds tests** in `tests/corpus/<area>/`, one feature or edge
  case per file. Files that must be rejected are named for the error they should
  produce (`unfinished_long_string.lua`).
- **Every bug fix adds a test that failed before the fix.**
- **Golden files are updated deliberately:** `tests/run --update` regenerates them,
  and the change is reviewed in the commit diff.
- **Most testing goes through `pyrolua`** (golden and differential). Ada unit tests, in a
  nested `tests/unit` crate, are only for what the command line cannot reach.
- **Fuzzing at two speeds:** a short fixed-seed run in every `tests/run`, long runs
  in `tests/run --full` at the end of a milestone.
- **Scripts are POSIX `sh` or Python 3 standard library only.** No pip packages. The
  test runner is Python.
- **The reference Lua** is called by full path (`PYRO_REF_LUA`, default
  `/opt/homebrew/opt/lua@5.4/bin`), never as plain `lua`, which is 5.5.

### Time limits

Every command has a known maximum duration. A hang is a failure with a name, never a
silent stall.

| Limit | Value |
| --- | --- |
| One `pyrolua`, `lua` or `luac` process in a test | 10 seconds |
| `tests/run` (every commit) | 5 minutes |
| `tests/run --full` (end of milestone) | 30 minutes |

- Each stage (build, proof, tags, golden, differential, fuzz) also has its own
  wall-clock cap within the total.
- Hitting any limit kills the process tree, fails the run and reports which stage and
  which file was running. Going over budget is a failure like a broken test: fix it by
  splitting slow units, adding lemmas or trimming redundant tests.
- Proofs are bounded by gnatprove's `--steps`, not wall-clock `--timeout`, so a hard
  proof fails the same way every time regardless of machine load. The value is set in
  `pyro_lua.gpr`.
- The runner prints only failures plus one timing table at the end, with timestamps
  per stage. Full logs go to a file, read only for what failed.
- Raising any limit or the steps value needs the owner's OK.

### Running commands

- `tests/run` runs in the **foreground**, with the command timeout set a little above
  its 5-minute cap. One call, one result.
- `tests/run --full` runs in the **background**, and the harness reports when it
  exits. Start it, then do other work or end the turn. **Never poll:** no `sleep`, no
  `tail` of its log, no checking on it.
- **No retry loops.** A failure or timeout is investigated, not rerun in the hope it
  passes.

## Working rules

### Proofs that will not close

1. Try the normal moves: intermediate `pragma Assert`s, a named lemma, splitting the
   subprogram, restructuring the loop or its invariant.
2. After a handful of real attempts, **stop and ask**, giving the exact check
   (`file:line` and message) and what was tried.

Never make a proof pass by cheating: no `pragma Assume`, no `pragma Annotate`, no
weakened contract, no `SPARK_Mode => Off`, no steps value above the agreed one. Each
of those is a design decision.

### Asking

Questions go to the **design session** first. It answers what the docs already
settle and technical calls such as proof strategy, and passes anything that is the
owner's decision on to the owner.

Ask before:

- changing a decision written in DESIGN, PROOFS or STYLE;
- adding trusted code, a dependency or a naming exception;
- deliberately diverging from PUC Lua (a new `[differs]`);
- raising a time limit or the steps value.

Everything else within these documents is done without asking, including choosing
the next step from [ROADMAP.md](ROADMAP.md).

Questions to the owner are asked in plain chat, one at a time.

### Lua behaviour

When unsure how Lua behaves, run it through reference `lua`/`luac` 5.4.9 first, then
read PUC Lua's source (`llex.c`, `lparser.c`, `lvm.c`, …). Never rely on memory.

### Reporting

Never call something proven or passing without a `tests/run` that says so. Quote
failures as they are. Say plainly what is unfinished.
