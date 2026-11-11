#!/usr/bin/env python3
"""Function-level difference between two builds of 7zzs (PLAN.md §11: a new upstream release).

Both binaries are stripped, statically linked `ET_EXEC`; a new release moves every function and every datum. A
function is *the same code* in both when its instructions are equal after relocation: equal mnemonics and operands,
and every address an instruction names (a branch or call target, a `rip`-relative or absolute operand in the image)
goes to the address the map sends the old one to. The map takes code to the paired function at the same offset (a
changed function: its entry only) and data to the address the paired functions use in its place (learned from all
of them; it must be one-to-one).

Pairing: functions in address order, by the hash of their instructions with addresses masked (`difflib` over the two
sequences, so a pair keeps its place among its neighbours); then the address check above.

Output (TSV): old_start  new_start  size_old  size_new  verdict  name
  verdict = same     equal after relocation (every named address maps as the pairing says)
            moved    equal with addresses masked, but some named address goes elsewhere than the map says (last column)
            changed  paired by position (between two paired neighbours), instructions differ
            removed / added   in one binary only
Usage: reldiff.py OLD_BIN OLD.objdump.tsv OLD.funcs.tsv NEW_BIN NEW.objdump.tsv NEW.funcs.tsv [OLD.codemap.tsv [DATAMAP.tsv]]
       > out.tsv     (DATAMAP.tsv: old data address, new address, uses that agree, uses)
"""
import bisect, difflib, hashlib, re, subprocess, sys

LO, HI = 0x400000, 0x800000
HEX = re.compile(r'0x([0-9a-f]+)')


def sections(path):
    out = subprocess.run(["readelf", "-S", "-W", path], capture_output=True, text=True, check=True).stdout
    secs = []
    for l in out.splitlines():
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+[0-9a-f]+\s+([0-9a-f]+)", l)
        if m and int(m.group(2), 16):
            secs.append((m.group(1), int(m.group(2), 16), int(m.group(3), 16)))
    return secs


def load(objdump, funcs):
    fs = []
    for l in open(funcs):
        a, n, k, s = l.rstrip("\n").split("\t")
        fs.append((int(a, 16), int(n), k, s))
    fs.sort()
    starts = [f[0] for f in fs]
    ins = [[] for _ in fs]
    for l in open(objdump):
        a, n, _, t = l.rstrip("\n").split("\t")[:4]
        a = int(a, 16)
        i = bisect.bisect_right(starts, a) - 1
        if i >= 0 and a < fs[i][0] + fs[i][1]:
            ins[i].append((a, int(n), riprel(t)))
    return fs, ins


def riprel(t):
    """objdump's text with a `rip`-relative displacement replaced by the address it names (objdump's comment)."""
    t, _, c = t.partition(" #")
    m = re.search(r'0x([0-9a-f]+)', c)
    if m and "(%rip)" in t:
        t = re.sub(r'-?(0x)?[0-9a-f]*\(%rip\)', f"0x{m.group(1)}(%rip)", t, count=1)
    return t.strip()


def addrs(t):
    """The image addresses an instruction's text names, in order."""
    return [int(x, 16) for x in HEX.findall(t) if LO <= int(x, 16) < HI]


def masked(t):
    return HEX.sub(lambda m: "A" if LO <= int(m.group(1), 16) < HI else m.group(0), t)


def key(f, ins):
    h = hashlib.sha1()
    for a, n, t in ins:
        h.update(f"{a - f[0]}:{n}:{masked(t)}\n".encode())
    return h.hexdigest()


def main(obin, oobj, ofun, nbin, nobj, nfun, codemap=None):
    of, oi = load(oobj, ofun)
    nf, ni = load(nobj, nfun)
    names = {}
    if codemap:
        for l in open(codemap):
            c = l.rstrip("\n").split("\t")
            if c[0] != "start":
                names[int(c[0], 16)] = f"{c[3]}\t{c[4]}"
    ok = [key(f, i) for f, i in zip(of, oi)]
    nk = [key(f, i) for f, i in zip(nf, ni)]
    sm = difflib.SequenceMatcher(None, ok, nk, autojunk=False)
    pair, rows = {}, []          # old index -> new index (masked-equal)
    changed = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "equal":
            for d in range(i2 - i1):
                pair[i1 + d] = j1 + d
        else:
            # between two paired runs: pair what is left in order, as `changed`; the rest is removed/added
            k = min(i2 - i1, j2 - j1)
            for d in range(k):
                changed.append((i1 + d, j1 + d))
            for i in range(i1 + k, i2):
                rows.append((of[i][0], None, of[i][1], None, "removed", ""))
            for j in range(j1 + k, j2):
                rows.append((None, nf[j][0], None, nf[j][1], "added", ""))
    # The address map. Code: a paired function at the same offset; a changed function only at its entry.
    # Data: learned from the paired functions themselves (old address -> the new addresses used in its place);
    # it has to be a one-to-one function, and a pair that disagrees with the majority is reported.
    ostarts = [f[0] for f in of]
    cpair = dict(changed)

    def cmap(a):
        i = bisect.bisect_right(ostarts, a) - 1
        if i >= 0 and a < of[i][0] + of[i][1]:
            if i in pair:
                return nf[pair[i]][0] + (a - of[i][0])
            if i in cpair and a == of[i][0]:
                return nf[cpair[i]][0]
            return -1
        return None                                  # not code

    votes = {}
    for i, j in pair.items():
        for (_, _, t), (_, _, u) in zip(oi[i], ni[j]):
            for x, y in zip(addrs(t), addrs(u)):
                if cmap(x) is None:
                    votes.setdefault(x, {}).setdefault(y, 0)
                    votes[x][y] += 1
    dmap = {x: max(v, key=v.get) for x, v in votes.items()}
    back = {}
    for x, y in dmap.items():
        back.setdefault(y, []).append(x)
    clash = {x for y, xs in back.items() if len(xs) > 1 for x in xs}
    why = {}
    for i, j in pair.items():
        for (a, _, t), (b, _, u) in zip(oi[i], ni[j]):
            for x, y in zip(addrs(t), addrs(u)):
                c = cmap(x)
                e = dmap[x] if c is None else c
                if e != y or x in clash:
                    why.setdefault(i, f"{a:x}: {x:x} -> {y:x}, expected {e:x}" + (" (not one-to-one)" if x in clash else ""))
    for i, j in pair.items():
        rows.append((of[i][0], nf[j][0], of[i][1], nf[j][1], "moved" if i in why else "same", why.get(i, "")))
    if len(sys.argv) > 8:                            # the data map, for porting pinned addresses
        with open(sys.argv[8], "w") as f:
            for x in sorted(dmap):
                f.write(f"{x:x}\t{dmap[x]:x}\t{votes[x][dmap[x]]}\t{sum(votes[x].values())}\n")
    for i, j in changed:
        rows.append((of[i][0], nf[j][0], of[i][1], nf[j][1], "changed", ""))
    rows.sort(key=lambda r: (r[0] if r[0] is not None else 1 << 62, r[1] or 0))
    for o, n, zo, zn, v, w in rows:
        print("\t".join(["" if o is None else f"{o:x}", "" if n is None else f"{n:x}", str(zo or ""), str(zn or ""),
                         v, names.get(o, "\t"), w]))


if __name__ == "__main__":
    main(*sys.argv[1:8])
