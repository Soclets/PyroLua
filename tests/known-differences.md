# Known differences from PUC Lua 5.4.9

Where Pyro Lua deliberately or knowingly differs from reference Lua (`luac -p` 5.4.9 for the
front end). Every `[differs]` tag in the sources is listed here with its file. Files whose
`--check --lua-style` message may differ from luac's are listed by path, in backquotes.

## Precompiled chunks are not loaded

Source: `src/front_end/pyro-diagnostics.adb`.

A file starting with the escape byte of Lua's binary signature is a precompiled chunk.
`luac -p` loads it; Pyro rejects it with "precompiled chunks are not supported" and no
line, since the bytecode format is out of scope (README, Scope).

## Chunks over 256 MiB are refused

Source: `cli/src/pyro_program.adb`.

Pyro's sources, positions and line numbers are bounded by `Pyro.Maximum_Source_Length`
(2^28 bytes), so the proofs have fixed ranges. A larger file is refused with "not enough
memory" without being read; luac reads it.

## Listings show made-up addresses

Source: `cli/src/bytecode_listing.adb`.

`luac -l -l` prints the memory address of each prototype (in a function's header, before
its constants, locals and upvalues, and after each CLOSURE). `pyrolua --bytecode --lua-style`
prints a made-up address in the same places, so the listings differ there; `tests/run`
masks every `0x…` number before comparing them. Everything else in the listing matches.

## No stack tracebacks

Accepted by the owner on 2026-11-03.

Source: `cli/src/pyro_program.adb`.

lua.c prints a stack traceback after the message of an error no protected call catches,
and its message handler adds it to the error before the to-be-closed variables close.
pyrolua prints the message alone ("pyrolua: file.lua:3: message"), and a `__close` that
runs then sees the message without a traceback. The runtime corpus compares the first line
of the standard error, without the program's name.

## No limit on nested host calls

Accepted by the owner on 2026-11-03.

Source: `src/runtime/pyro-virtual_machine.ads`.

PUC Lua runs a host function, and each metamethod or `pcall`, as a C call, and stops
after about 200 nested ones (`LUAI_MAXCCALLS`) with "C stack overflow", to keep the C
stack from overflowing. Pyro's virtual machine calls them by pushing frames, never by
recursion, so it has no C stack to protect: such calls nest until the Lua stack's limit
(`LUAI_MAXSTACK`, a million places), as Lua function calls do in both, and end in "stack
overflow". A script that nests between about 200 calls and that limit fails in reference
Lua and runs in Pyro.
