# CVE regression suite

One file per public CVE in PUC Lua 5.x that a Lua script can trigger, written as a short
proof of concept from the public advisory and bug reports. Each file starts with a header:
the CVE id, the affected PUC Lua versions, a one-line description, what Pyro Lua is
expected to do with it, and the sources.

`tests/run` treats these files as corpus files: `pyrolua --check` and `pyrolua --bytecode
--lua-style` must agree with `luac -p` and `luac -l -l` 5.4.9 (where each bug is fixed),
and their `--tokens`, `--ast`, `--check` and `--bytecode` output has golden files in
`tests/golden/cve/`. Once the virtual machine exists (M4), each file is also run and must
end as its header says.

A file here shows that Pyro handles that one proof of concept as expected. It is not a
claim of immunity to anything beyond it; what the proofs cover is in
[docs/PROOFS.md](../../docs/PROOFS.md).

## In the suite

| CVE | Affected | Where | File |
| --- | --- | --- | --- |
| CVE-2022-28805 | 5.4.0 to 5.4.3 | parser (`singlevar`, `lparser.c`) | [CVE-2022-28805.lua](CVE-2022-28805.lua) |

## Pending

Runtime CVEs, added as the milestone that can run them lands. Descriptions follow NVD.

| CVE | Affected | Where | Milestone |
| --- | --- | --- | --- |
| [CVE-2014-5461](https://nvd.nist.gov/vuln/detail/CVE-2014-5461) | 5.1 to 5.2.2 | varargs with many fixed parameters (`ldo.c`) | M4 |
| [CVE-2020-15888](https://nvd.nist.gov/vuln/detail/CVE-2020-15888) | up to 5.4.0 | stack resizes during garbage collection | M4 |
| [CVE-2020-24342](https://nvd.nist.gov/vuln/detail/CVE-2020-24342) | up to 5.4.0 | C stack overflow while building an error message (`luaO_pushvfstring`) | M4 |
| [CVE-2022-33099](https://nvd.nist.gov/vuln/detail/CVE-2022-33099) | up to 5.4.4 | heap overflow on a recursive error (`luaG_runerror`) | M4 |
| [CVE-2021-44647](https://nvd.nist.gov/vuln/detail/CVE-2021-44647) | 5.4.3 and later | type confusion naming a function in an error (`funcnamefromcode`) | M4 |
| [CVE-2020-24371](https://nvd.nist.gov/vuln/detail/CVE-2020-24371) | 5.4.0 | barriers during the sweep phase (`lgc.c`) | M4 (the M3 collector is stop-the-world: no sweep runs between script steps, so there is no barrier to get wrong; the proof of concept runs once the VM does) |
| [CVE-2020-15889](https://nvd.nist.gov/vuln/detail/CVE-2020-15889) | 5.4.0 | generational collection (`youngcollection`, `lgc.c`) | M5 |
| [CVE-2021-44964](https://nvd.nist.gov/vuln/detail/CVE-2021-44964) | 5.4.0 to 5.4.3 | use after free with finalizers (`lgc.c`) | M5 |
| [CVE-2021-45985](https://nvd.nist.gov/vuln/detail/CVE-2021-45985) | 5.4.3 | finalizer called during a tail call | M5 |
| [CVE-2021-43519](https://nvd.nist.gov/vuln/detail/CVE-2021-43519) | 5.1 to 5.4.4 | C stack overflow through recursive coroutines (`lua_resume`) | M5 |

Not applicable: these need the `debug` library, which Pyro does not provide (a host
could expose similar functions, but outside the proven core):
[CVE-2019-6706](https://nvd.nist.gov/vuln/detail/CVE-2019-6706) (`debug.upvaluejoin`),
[CVE-2020-15945](https://nvd.nist.gov/vuln/detail/CVE-2020-15945),
[CVE-2020-24369](https://nvd.nist.gov/vuln/detail/CVE-2020-24369) (line hooks) and
[CVE-2020-24370](https://nvd.nist.gov/vuln/detail/CVE-2020-24370) (`debug.getlocal`).

The list comes from NVD's entries for the product `lua:lua` (November 2026). Of those,
CVE-2022-28805 is the only one in the front end.
