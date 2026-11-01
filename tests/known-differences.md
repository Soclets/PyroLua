# Known differences from PUC Lua 5.4.9

Where Pyro deliberately or knowingly differs from reference Lua (`luac -p` 5.4.9 for the
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
its constants, locals and upvalues, and after each CLOSURE). `pyro --bytecode --lua-style`
prints a made-up address in the same places, so the listings differ there; `tests/run`
masks every `0x…` number before comparing them. Everything else in the listing matches.
