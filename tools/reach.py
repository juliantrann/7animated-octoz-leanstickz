#!/usr/bin/env python3
"""Which functions of a release binary the entry point may reach (PLAN.md G2, "CFG").

An over-approximation by function, from the G0 artefacts (tools/g0.sh, tools/codemap.py) and the ELF file itself:
  * a function reaches the functions its code jumps to or calls directly, the one it falls into at its end (not
    after a direct call that is its last instruction: the compiler ends a function so when the callee does not
    return; these callees are listed in build/NAME.reach.noreturn.tsv), and the functions whose start its
    instructions mention as a constant (their address is taken there);
  * every function whose start is a 64-bit word of a data section (at a multiple of 8 from the section's start) is
    taken as reached: the tables of pointers, the vtables, `.init_array`, the addends of `.rela.plt`.
What it leaves out is what control-flow integrity (P5, G6) has to give: an indirect call or jump goes to a function
whose address was taken, or stays within its function (the tables of a `switch`).

A measurement, not a proof. Usage: reach.py NAME ELF      e.g. reach.py 7zzs release/26.06/7zzs
Writes build/NAME.reach.tsv and prints the summary. Run with `python3 -I`: the ELF file is untrusted data.
"""
import bisect, collections, re, struct, sys

NOPS = ("nop", "nopw", "nopl", "data16", "cs", "xchg %ax,%ax", "int3")
STOP = ("jmp", "jmpq", "ret", "retq", "ud2", "hlt", "repz", "bnd")  # an instruction control does not pass
HEX = re.compile(r"0x([0-9a-f]+)")
DIRECT = re.compile(r"(?:notrack |bnd |addr32 |ds |cs )*(j[a-z]+|call|callq|jmpq|loop[a-z]*|jr?cxz|xbegin)\s+0x([0-9a-f]+)$")

def rows(path, skip=0):
    with open(path) as f:
        for i, l in enumerate(f):
            if i >= skip and not l.startswith("#"):
                yield l.rstrip("\n").split("\t")

def sections(elf):
    """(name, type, flags, addr, bytes) of the ELF64 file's sections."""
    assert elf[:6] == b"\x7fELF\x02\x01", "not a little-endian ELF64 file"
    shoff, = struct.unpack_from("<Q", elf, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", elf, 0x3a)
    hs = [struct.unpack_from("<IIQQQQIIQQ", elf, shoff + i * shentsize) for i in range(shnum)]
    stab = elf[hs[shstrndx][4]:hs[shstrndx][4] + hs[shstrndx][5]]
    for name, typ, flags, addr, off, size, *_ in hs:
        n = stab[name:stab.index(b"\0", name)].decode()
        yield n, typ, flags, addr, (b"" if typ == 8 else elf[off:off + size])

def main(name, elfpath):
    b = f"build/{name}"
    fns = [(int(r[0], 16), int(r[1])) for r in rows(f"{b}.funcs.tsv")]
    info = {int(r[0], 16): r for r in rows(f"{b}.codemap.tsv", 1)}
    starts = [a for a, _ in fns]
    end = {a: a + n for a, n in fns}
    def fn_of(x):
        i = bisect.bisect_right(starts, x) - 1
        return starts[i] if i >= 0 and x < end[starts[i]] else None
    elf = open(elfpath, "rb").read()
    entry, = struct.unpack_from("<Q", elf, 0x18)

    # the code's edges
    direct, taken, mid = collections.defaultdict(set), collections.defaultdict(set), collections.Counter()
    last = {}                                   # function -> its last instruction that is not padding
    insns = []
    for r in rows(f"{b}.objdump.tsv"):
        a = int(r[0], 16); text = r[3]
        insns.append((a, int(r[1]), text))
        f = fn_of(a)
        if f is None:
            continue
        if not text.startswith(NOPS):
            last[f] = (a, int(r[1]), text)
        m = DIRECT.match(text)
        if m:
            g = fn_of(int(m.group(2), 16))
            if g is not None and g != f:
                direct[f].add(g)
            continue
        for h in HEX.findall(text):
            c = int(h, 16)
            if c in end:
                if c != f:
                    taken[f].add(c)
            elif fn_of(c) not in (None, f):
                mid[f] += 1
    # falling off a function's end into the next one
    iaddr = [a for a, _, _ in insns]
    fall, noret = {}, collections.Counter()
    for f, (a, n, text) in last.items():
        if text.split(" ")[0] in STOP or re.match(r"(notrack |bnd )*jmpq? ", text):
            continue
        m = re.match(r"callq? 0x([0-9a-f]+)$", text)
        if m and fn_of(int(m.group(1), 16)) is not None:
            noret[fn_of(int(m.group(1), 16))] += 1     # the compiler ends a function with a call that does not return
            continue
        x = a + n
        while True:
            g = fn_of(x)
            if g is not None:
                if g != f:
                    fall[f] = g
                break
            i = bisect.bisect_left(iaddr, x)
            if i >= len(insns) or insns[i][0] != x or not insns[i][2].startswith(NOPS):
                break
            x += insns[i][1]

    # the data's pointers to functions
    data, unaligned, skipped = collections.defaultdict(set), 0, []
    for n, typ, flags, addr, bs in sections(elf):
        if not flags & 2 or flags & 4 or not bs:      # allocated, not code
            continue
        if n in (".eh_frame", ".gcc_except_table") or typ == 7:   # relative encodings; notes
            skipped.append(n)
            continue
        for o in range(0, len(bs) - 7):
            v, = struct.unpack_from("<Q", bs, o)
            if v in end:
                if o % 8 == 0:
                    data[v].add(n)
                else:
                    unaligned += 1

    # the closure
    why = {entry: "entry"}
    for g in data:
        why.setdefault(g, "data " + ",".join(sorted(data[g])))
    work = list(why)
    while work:
        f = work.pop()
        for kind, gs in (("direct", direct[f]), ("taken", taken[f]), ("fall", [fall[f]] if f in fall else [])):
            for g in gs:
                if g not in why:
                    why[g] = f"{kind} {f:x}"
                    work.append(g)

    by = collections.defaultdict(lambda: [0, 0, 0, 0, 0, 0, 0, 0])
    with open(f"{b}.reach.tsv", "w") as t:
        t.write("start\tsize\torigin\tname\treached\tissues_full\tissues_min\n")
        for a, n in fns:
            r = info[a]; o = r[3]; hit = a in why
            t.write(f"{a:x}\t{n}\t{o}\t{r[4]}\t{why.get(a, '-')}\t{r[6]}\t{r[7]}\n")
            v = by[o]; k = 0 if hit else 4
            v[k] += 1; v[k + 1] += n; v[k + 2] += int(r[6]); v[k + 3] += int(r[7])
    print(f"{name}: {len(fns)} functions, {len(why)} reached from the entry 0x{entry:x} "
          f"({sum(1 for w in why.values() if w.startswith('data'))} by a pointer in the data, "
          f"{sum(1 for w in why.values() if w.startswith('taken'))} by an address in reached code, "
          f"{sum(1 for w in why.values() if w.startswith('fall'))} by falling into them)")
    print(f"pointers to a function's start off the 8-byte grid of a data section (not counted): {unaligned}; "
          f"constants in code that point into another function, not at its start (not counted): {sum(mid.values())}; "
          f"sections not scanned: {', '.join(skipped)}")
    with open(f"{b}.reach.noreturn.tsv", "w") as t:
        t.write("callee\tsites\torigin\tname\n")
        for g, c in sorted(noret.items(), key=lambda kv: -kv[1]):
            t.write(f"{g:x}\t{c}\t{info[g][3]}\t{info[g][4]}\n")
    print(f"functions that end with a direct call (taken as not returning, so nothing falls into the next function): "
          f"{sum(noret.values())}, to {len(noret)} callees ({b}.reach.noreturn.tsv)")
    print("origin\treached: functions\tbytes\tissues full\tissues min\tnot reached: functions\tbytes\tissues full\tissues min")
    tot = [0] * 8
    for o, v in sorted(by.items(), key=lambda kv: -kv[1][1] - kv[1][5]):
        print(o + "\t" + "\t".join(map(str, v)))
        tot = [x + y for x, y in zip(tot, v)]
    print("total\t" + "\t".join(map(str, tot)))

if __name__ == "__main__":
    main(*sys.argv[1:3])
