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

## Tables are not presized

Source: `src/runtime/pyro-virtual_machine.adb`.

NEWTABLE and SETLIST give the sizes a table constructor needs, and PUC Lua sizes the
table's array and hash parts with them (`luaH_resize`, `luaH_resizearray`). Pyro ignores
them: a table's parts grow as keys arrive, sized as PUC Lua's rehash sizes them. Results
are the same except for `#t` on a table with holes, where Lua allows any border and the two
may find different ones, and for speed. Sizing tables in the heap made its proofs, which
sit close to the steps limit, fail; it can come back once they have more room.

## No stack tracebacks

Source: `cli/src/pyro_program.adb`.

lua.c prints a stack traceback after the message of an error no protected call catches,
and its message handler adds it to the error before the to-be-closed variables close.
pyrolua prints the message alone ("pyrolua: file.lua:3: message"), and a `__close` that
runs then sees the message without a traceback. The runtime corpus compares the first line
of the standard error, without the program's name.
