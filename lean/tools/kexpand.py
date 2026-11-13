#!/usr/bin/env python3
"""Rewrites each theorem proved by `ksplit k from A to B using hk1 hk2 <;> (body)` in the given files as one theorem
`<name>_<k>` per value of `k` (`obtain rfl : k = K`, then `body`) and `<name>` over the range (`by_cases`): one
proof term per `k`, so the kernel checks one at a time (eight or more in one term: out of memory, runs a84, a103).
Run from `lean/`: `python3 -I tools/kexpand.py FV7z/Im4/H0a.lean ...`."""
import re
import sys

HEAD = re.compile(r"(?P<opts>(?:set_option [^\n]* in\n)*)theorem (?P<name>\w+) \(k : Nat\) \(hk1 : (?P<a>\d+) ≤ k\) "
                  r"\(hk2 : k ≤ (?P<b>\d+)\) : (?P<concl>[^\n]*) := by\n(?P<pre>(?:  [^\n]*\n)*?)"
                  r"  ksplit k from (?P=a) to (?P=b) using hk1 hk2 <;>\n(?P<body>(?:  [^\n]*\n)+)")


def expand(m: re.Match) -> str:
    name, a, b = m["name"], int(m["a"]), int(m["b"])
    out = []
    for k in range(a, b + 1):
        out.append(f"{m['opts']}theorem {name}_{k} (k : Nat) (hk1 : {k} ≤ k) (hk2 : k ≤ {k}) : {m['concl']} := by\n"
                   f"{m['pre']}  obtain rfl : k = {k} := by omega\n{m['body']}\n")
    cases = [f"  by_cases h{k} : k ≤ {k}\n  · exact {name}_{k} k (by omega) h{k}" for k in range(a, b)]
    cases.append(f"  exact {name}_{b} k (by omega) hk2")
    out.append(f"theorem {name} (k : Nat) (hk1 : {a} ≤ k) (hk2 : k ≤ {b}) : {m['concl']} := by\n"
               + "\n".join(cases) + "\n")
    return "".join(out)


for path in sys.argv[1:]:
    text = open(path, encoding="utf-8").read()
    new, n = HEAD.subn(expand, text)
    assert n > 0, path
    for i, line in enumerate(new.splitlines(), 1):
        assert len(line) <= 120, (path, i)
    open(path, "w", encoding="utf-8").write(new)
    print(path, n)
