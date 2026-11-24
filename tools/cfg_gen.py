#!/usr/bin/env python3
"""The control-flow graph of part (A) of `Confined` (lean/FV7z/Statement/Cfg.lean), from the binary, and its check
on real runs (PLAN.md §M, "cfg_gen.py").

  gen OBJDUMP.TSV ELF OUT.TSV
                            one line per instruction: its address and its edges (`Edge` of Cfg.lean), from the
                            disassembly (build/7zzs.objdump.tsv, tools/g0.sh):
                              go:Q        the next instruction, a jcc's two targets, a direct jmp, a syscall's return;
                                          an instruction with a rep prefix also goes to itself (one iteration a step)
                              call:Q:RA   a direct call of Q returning to RA
                              ret         a return
                              icall:RA    an indirect call returning to RA: its targets are still to be listed
                              ijmp        an indirect jmp: its targets are still to be listed
                              jt:Q        a target of a switch table's jmp (GCC's `lea T(%rip); movslq (T,i,4);
                                          add T; jmp`, entries 0..K from the `cmp $K` and `ja` before), read from
                                          the file; every target an instruction near the jmp, or the site is left
                                          an ijmp
                            ud2 and hlt have no edge. Prints how many indirect sites are left to resolve.
  check CFG.TSV TRACE       a trace of the addresses a run executes (one hex address per line, or the
                            `Trace …[…/ADDR/…]` lines of `qemu-x86_64 -d exec,nochain -one-insn-per-tb`) against
                            the graph, with the ghost stack of `Cfg.Walk`: every step follows an edge, every return
                            goes to the address its call pushed. An indirect site's targets seen in the trace are
                            printed (seeds for the target sets). Exit 1 at the first step that follows no edge.

Version 1: direct edges and switch tables; the other indirect targets (vtables, function pointers, IFUNC slots), the
landing pads (.gcc_except_table) and the unwinder's jump are to come. Not evidence for a theorem: the artifact the
statement names is checked by the proofs; this checks it on runs before.
"""
import bisect
import re
import struct
import sys

HEX = re.compile(r"0x([0-9a-f]+)")


def edges_of(addr, size, mnem, text):
    nxt = addr + size
    m = mnem.split()
    op = m[-1]  # drop the prefixes: notrack, bnd, rep, repz, repnz
    pre = m[:-1]
    tgt = HEX.search(text.split(None, len(m))[-1]) if "*" not in text else None
    if op in ("ud2", "hlt"):
        return []
    if op == "ret":
        return ["ret"]
    if op == "call":
        return [f"call:{int(tgt.group(1), 16):x}:{nxt:x}"] if tgt else [f"icall:{nxt:x}"]
    if op == "jmp":
        return [f"go:{int(tgt.group(1), 16):x}"] if tgt else ["ijmp"]
    if op.startswith("j") or op.startswith("loop"):  # jcc, jrcxz, loop
        return [f"go:{int(tgt.group(1), 16):x}", f"go:{nxt:x}"]
    e = [f"go:{nxt:x}"]
    if any(p.startswith("rep") for p in pre):
        e.append(f"go:{addr:x}")
    return e


def segments(elf):
    """The file's PT_LOAD segments: (vaddr, file bytes)."""
    b = open(elf, "rb").read()
    phoff, = struct.unpack_from("<Q", b, 0x20)
    phentsize, phnum = struct.unpack_from("<HH", b, 0x36)
    segs = []
    for i in range(phnum):
        typ, _, off, va, _, fsz = struct.unpack_from("<IIQQQQ", b, phoff + i * phentsize)
        if typ == 1:
            segs.append((va, b[off:off + fsz]))
    return segs


def read32(segs, a):
    for va, data in segs:
        if va <= a and a + 4 <= va + len(data):
            return struct.unpack_from("<i", data, a - va)[0]
    return None


LEA = re.compile(r"lea 0x[0-9a-f]+\(%rip\),(%\w+) # 0x([0-9a-f]+)")
MOVSLQ = re.compile(r"movslq \((%\w+),(%\w+),4\),(%\w+)")
CMP = re.compile(r"cmp[bwlq]? \$0x([0-9a-f]+),")


def switch_targets(ins, i, segs, addrs, func):
    """The targets of the switch-table jmp ins[i], or None if the pattern or a check fails. The entries are 0..K with
    K from the `cmp $K` before the table's `lea` in the same stretch of code; where the bound is checked in another
    block, the entries up to the first one that is not an instruction of the jmp's function (`func`: its bounds), at
    most 4096: every real entry is one, so this can only add targets, never miss one."""
    reg = ins[i][3].split("*")[-1]
    base = None
    lo, hi = func
    for j in range(i - 1, max(i - 12, -1), -1):
        t = ins[j][3]
        m = MOVSLQ.search(t)
        if m and m.group(3) == reg:
            base = m.group(1)
        m = LEA.search(t)
        if not (m and base and m.group(1) == base):
            continue
        tab = int(m.group(2), 16)
        k = None
        for jj in range(j - 1, max(j - 20, -1), -1):
            if ins[jj][2].split()[-1] in ("ret", "jmp") or ins[jj][0] in LABELS:
                break
            c = CMP.search(ins[jj][3])
            if c:
                k = int(c.group(1), 16)
                break
        out = []
        for n in range((k + 1) if k is not None and k <= 4096 else 4097):
            off = read32(segs, tab + 4 * n)
            q = None if off is None else (tab + off) & (2**64 - 1)
            if q is None or q not in addrs or not lo <= q < hi:
                if k is not None:
                    return None
                break
            out.append(q)
        return sorted(set(out)) or None
    return None


LABELS = set()


def gen(src, elf, out):
    ins = []
    for ln in open(src):
        p = ln.rstrip("\n").split("\t")
        if len(p) >= 4 and p[1].isdigit():
            ins.append((int(p[0], 16), int(p[1]), p[2], p[3]))
    addrs = {x[0] for x in ins}
    segs = segments(elf)
    # jump targets: a bound check is not looked for across one
    for a, size, mnem, text in ins:
        for e in edges_of(a, size, mnem, text):
            if e.startswith("go:") and int(e[3:], 16) != a + size:
                LABELS.add(int(e[3:], 16))
    # the function of each instruction (build/7zzs.funcs.tsv, next to the disassembly)
    fs = sorted((int(p[0], 16), int(p[1])) for p in (ln.split("\t") for ln in open(src.replace("objdump", "funcs")))
                if p[0][:1] in "0123456789abcdef")
    starts = [f[0] for f in fs]
    n = ic = ij = sw = 0
    with open(out, "w") as o:
        for i, (a, size, mnem, text) in enumerate(ins):
            e = edges_of(a, size, mnem, text)
            if e == ["ijmp"]:
                f = fs[bisect.bisect_right(starts, a) - 1]
                t = switch_targets(ins, i, segs, addrs, (f[0], f[0] + f[1]))
                if t:
                    e = [f"jt:{q:x}" for q in t]
                    sw += 1
            n += 1
            ic += any(x.startswith("icall") for x in e)
            ij += "ijmp" in e
            o.write(f"{a:x}\t{','.join(e)}\n")
    print(f"{n} instructions; switch tables resolved: {sw}; indirect sites left: {ic} calls, {ij} jmps")


def load(cfg):
    g = {}
    for ln in open(cfg):
        a, e = ln.rstrip("\n").split("\t")
        g[int(a, 16)] = e.split(",") if e else []
    return g


VDSO = 0x7F0000000000  # above every address of the file and its heap
QEMU = re.compile(r"\[[0-9a-f]+/([0-9a-f]+)/")


def trace(path):
    for ln in open(path):
        m = QEMU.search(ln)
        if m:
            yield int(m.group(1), 16)
        elif re.fullmatch(r"(0x)?[0-9a-f]+\s*", ln):
            yield int(ln, 16)


def check(cfg, path):
    g = load(cfg)
    stk = []
    seen = {}
    prev = None
    n = vd = 0
    for q in trace(path):
        n += 1
        if prev is None:
            prev = q
            continue
        p, ok = prev, False
        if p >= VDSO:
            # inside the vDSO (the real kernel maps one; the theorems assume none, `vdso = false`, and glibc then
            # makes the system call): an opaque function, left at the return address its call pushed
            if stk and q == stk[-1]:
                stk.pop()
            elif q < VDSO:
                print(f"step {n}: {p:x} -> {q:x} leaves the vDSO but not to the return address")
                sys.exit(1)
            prev = q
            vd += 1
            continue
        for e in g.get(p, []):
            k = e.split(":")
            if k[0] in ("go", "jt") and int(k[1], 16) == q:
                ok = True
            elif k[0] == "call" and int(k[1], 16) == q:
                stk.append(int(k[2], 16)); ok = True
            elif k[0] == "ret" and stk and stk[-1] == q:
                stk.pop(); ok = True
            elif k[0] == "icall":
                stk.append(int(k[1], 16)); ok = True
                seen.setdefault(p, set()).add(q)
            elif k[0] == "ijmp":
                ok = True
                seen.setdefault(p, set()).add(q)
            if ok:
                break
        if not ok:
            print(f"step {n}: {p:x} -> {q:x} follows no edge of {p:x} ({','.join(g.get(p, [])) or 'no instruction'});"
                  f" ghost stack top {stk[-1]:x}" if stk else f"step {n}: {p:x} -> {q:x} follows no edge")
            sys.exit(1)
        prev = q
    print(f"ok: {n} steps follow the graph ({vd} in the vDSO); ghost stack depth {len(stk)} at the end")
    print(f"indirect sites seen: {len(seen)}, targets {sum(map(len, seen.values()))}")
    for p in sorted(seen)[:20]:
        print(f"  {p:x}: {' '.join(f'{q:x}' for q in sorted(seen[p]))}")


if __name__ == "__main__":
    if sys.argv[1:2] == ["gen"] and len(sys.argv) == 5:
        gen(*sys.argv[2:])
    elif sys.argv[1:2] == ["check"] and len(sys.argv) == 4:
        check(*sys.argv[2:])
    else:
        sys.exit(__doc__)
