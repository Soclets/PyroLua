# Pyro

Pyro is an implementation of the **Lua 5.4** core language written in **SPARK** (the
formally verifiable subset of Ada). The goal is an embeddable Lua interpreter with a
machine-checked proof that the interpreter itself cannot crash or corrupt memory,
whatever script it is given.

- **Language:** Lua 5.4, as defined by the
  [Lua 5.4 Reference Manual](https://www.lua.org/manual/5.4/).
- **Core only:** no standard library (`string`, `table`, `math`, `io`, `os`, …). The
  host program decides which functions a script can call. See
  [Scope](#scope).
- **Proof:** absence of runtime errors (SPARK *Silver*) for all of Pyro, plus
  functional proofs (*Gold*) for the parts where a bug would mean memory unsafety:
  the heap and garbage collector, bytecode validity, the VM stack and tables. See
  [docs/PROOFS.md](docs/PROOFS.md).
- **Behaviour vs. reference Lua:** checked by differential testing against the
  reference implementation (PUC Lua 5.4), not by proof.

## Status

M1 (front end) is done: the lexer, parser and resolver are proven (Silver everywhere,
Gold for growable arrays and syntax-tree well-formedness, termination of lexer and
parser). `pyro --tokens`, `pyro --ast` and `pyro --check` work, with Radium-style
messages. `pyro --check --lua-style` prints exactly what `luac -p` 5.4.9 prints on the
official test suite and Pyro's corpus, and agrees with it on accepting or rejecting
every mutated file of the fuzzing runs. Next milestone: **M2,
compiler and bytecode**. See [docs/ROADMAP.md](docs/ROADMAP.md).

## Documentation

| Document | Contents |
| --- | --- |
| [docs/DESIGN.md](docs/DESIGN.md) | Architecture, data representation, key design decisions |
| [docs/PROOFS.md](docs/PROOFS.md) | What is proven, what is trusted, what is only tested, proof rules |
| [docs/ROADMAP.md](docs/ROADMAP.md) | Milestones and their completion criteria |
| [docs/STYLE.md](docs/STYLE.md) | How code is written, tested and committed; working rules |

## Scope

In scope:

- The full Lua 5.4 language: syntax, semantics, metatables and metamethods,
  integer/float numbers, closures and upvalues, varargs, `goto`, coroutines,
  `<const>` and `<close>` variables, garbage collection.
- An Ada/SPARK embedding API: load a chunk, call functions, exchange values, register
  host functions, and reach the primitives a host needs (metatables, protected calls,
  coroutine resume/yield, table traversal).
- Sandbox limits: instruction budget and memory limit, so untrusted scripts can be
  stopped cleanly.
- A small `pyro` command-line program for running and inspecting `.lua` files.

Out of scope:

- The Lua standard library. A host may implement any of it on top of the embedding
  API, but Pyro does not ship it.
- The Lua C API and binary compatibility with PUC Lua (bytecode format, `.luac`
  files, C modules).
- Proving that Pyro's behaviour matches the reference manual in full. That is what
  differential testing is for.

A consequence worth knowing: in Lua 5.4, automatic string-to-number coercion in
arithmetic (`"10" + 1`) is implemented by the *string library's* metamethods, not the
core. Pyro follows the core, so `"10" + 1` raises an error unless the host installs a
string metatable that provides it. Number-to-string coercion in concatenation
(`1 .. ""`) is core behaviour and works.

## Requirements

- [Alire](https://alire.ada.dev) 2.x (`alr`), which provides:
  - GNAT native toolchain (developed with GNAT 16.1)
  - gprbuild
  - gnatprove (developed with 16.1)
- Reference Lua 5.4 (for tests only): `brew install lua@5.4` (5.4.9). Note that the
  plain `lua` Homebrew formula is now 5.5, which is **not** a valid reference: 5.5
  changes syntax and semantics. The `lua@5.4` binaries are shadowed by 5.5's on
  `PATH`, so always call them by full path: `/opt/homebrew/opt/lua@5.4/bin/lua`
  and `/opt/homebrew/opt/lua@5.4/bin/luac` (or `$(brew --prefix lua@5.4)/bin/…`).
  Test scripts take the folder holding `lua` and `luac` from `PYRO_REF_LUA`,
  defaulting to `/opt/homebrew/opt/lua@5.4/bin`.

## Building, proving, testing

Layout and commands:

```bash
alr build                                   # build the library
cd cli && alr build                         # build the pyro executable
alr exec -- gnatprove -P pyro.gpr           # run the proofs (settings live in pyro.gpr)
tests/run                                   # everything: build, proofs, tests (5 min cap)
tests/run --full                            # clean proofs and long fuzzing (30 min cap)
```

Command-line program (M1 subset):

```bash
pyro --tokens file.lua    # dump the token stream
pyro --ast file.lua       # dump the syntax tree
pyro --check file.lua     # syntax and scope check, every certain error in Pyro's layout
pyro --check --lua-style file.lua   # the one error `luac -p` would print, in its words
```

Before the first `tests/run`, fetch the official Lua test suite and Unicode's grapheme
break test:

```bash
tools/fetch-lua-tests
tools/generate-grapheme-tables
```

Later milestones add `pyro --bytecode file.lua` and `pyro file.lua` (run).

## Repository layout

```
pyro.gpr, alire.toml   Library crate (all SPARK code lives here)
src/                   Library sources, packages named Pyro.*, one folder per
                       pipeline stage (common, front_end, compiler, runtime,
                       embedding)
cli/                   Nested crate for the `pyro` executable
tests/                 Test runner, corpus, golden files
tools/                 Helper scripts (reference Lua setup, corpus download, fuzzing)
docs/                  Design, proof and roadmap documents
```

## Development rules

The full rules are in [docs/STYLE.md](docs/STYLE.md). The essentials:

- Every library unit is `SPARK_Mode => On`. The only exceptions are the trusted
  units listed in [docs/PROOFS.md](docs/PROOFS.md#trusted-code), and adding one means
  adding it to that list with a reason.
- `gnatprove` must report **zero unproved checks** on `main`. A change that leaves a
  check unproved is not finished.
- No exceptions are raised or handled in library code. Errors are values (status
  records) or, at Lua level, VM unwinding. See [docs/DESIGN.md](docs/DESIGN.md#errors).
- No unbounded recursion on the Ada stack. Every recursive subprogram carries a depth
  parameter with a proven bound.
- When behaviour is in doubt, the reference is PUC Lua 5.4 (`lua@5.4`), then the
  reference manual. The source of PUC Lua (`llex.c`, `lparser.c`, `lvm.c`, …) is the
  best guide to edge cases.
- Documentation is part of the change: when a design decision changes, update
  `docs/` in the same commit.

## License

- **Code:** [Apache License 2.0 with LLVM Exceptions](LICENSE.txt)
  (SPDX: `Apache-2.0 WITH LLVM-exception`).
- **Documentation** (this README and everything under `docs/`):
  [Creative Commons Attribution 4.0 International](LICENSE-docs.txt)
  (SPDX: `CC-BY-4.0`).

Every source file starts with an SPDX line:

```ada
--  SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
```
