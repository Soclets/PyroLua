# Runtime corpus

Lua scripts that `tests/run` runs under `pyrolua` and under reference Lua 5.4.9, comparing
the exit status, the standard output byte for byte, and the error message (the first line
of the standard error without the program's name; reference Lua then prints a stack
traceback, which `pyrolua` does not: [known differences](../../known-differences.md)).
`tests/run --full` runs each again under `pyrolua --gc-stress`, which collects garbage at
every safe point, and compares that too. The [CVE proofs of concept](../../cve/README.md)
are run the same way.

Like every corpus file, each script also has golden `--tokens`, `--ast`, `--check` and
`--bytecode` output in `tests/golden/runtime/`, and its listing is compared with `luac -l
-l`. `luac -p` must accept it: a script that does not compile fails the same way under both
and tests nothing.

## Writing a script

- Use only the test host functions (`cli/src/host_functions.adb`): `print`,
  `setmetatable`, `getmetatable`, `pcall`, `error`, `type`, `select`, `tostring`, `rawget`,
  `rawset`, `rawequal`, `rawlen`, `next`, `pairs`, `ipairs` and `assert`. Reference Lua
  runs a prelude first (`REFERENCE_PRELUDE` in `tests/run`) that removes every other
  global and the string metatable, so a script that uses the standard library by accident
  fails under both.
- Do not print anything that depends on the order of `next` or `pairs`. The two
  implementations place keys differently in a table's hash part, so the order differs:
  collect the keys, sort them (an insertion sort in the script, since there is no
  `table.sort`), and print in that order; or print only what does not depend on it (a
  count, a sum).
- Do not print addresses: `tostring` of a table or function gives each implementation's
  own. Print `type (x)` or compare values instead.
- Keep within reference Lua's limit of about 200 nested calls through `pcall` or
  metamethods: past it they end in "C stack overflow" there, and Pyro has no such limit
  ([known differences](../../known-differences.md)).
- A script whose recursion is so deep that collecting at every step takes too long says
  so on a line containing `-- no gc-stress`, and `--full` skips its stress run.

## Layout

One directory per area: `arithmetic`, `calls`, `closures`, `comparisons`, `errors`,
`gc`, `loops`, `strings`, `tables`.
