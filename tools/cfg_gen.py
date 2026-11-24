#!/usr/bin/env python3
"""The control-flow graph of part (A) of `Confined` (lean/FV7z/Statement/Cfg.lean), from the binary, and its check
on real runs (PLAN.md §M, "cfg_gen.py").

  gen OBJDUMP.TSV OUT.TSV   one line per instruction: its address and its edges (`Edge` of Cfg.lean), from the
                            disassembly (build/7zzs.objdump.tsv, tools/g0.sh):
                              go:Q        the next instruction, a jcc's two targets, a direct jmp, a syscall's return;
                                          an instruction with a rep prefix also goes to itself (one iteration a step)
                              call:Q:RA   a direct call of Q returning to RA
                              ret         a return
                              icall:RA    an indirect call returning to RA: its targets are still to be listed
                              ijmp        an indirect jmp: its targets are still to be listed
                            ud2 and hlt have no edge. Prints how many indirect sites are left to resolve.
  check CFG.TSV TRACE       a trace of the addresses a run executes (one hex address per line, or the
                            `Trace …[…/ADDR/…]` lines of `qemu-x86_64 -d exec,nochain -one-insn-per-tb`) against
                            the graph, with the ghost stack of `Cfg.Walk`: every step follows an edge, every return
                            goes to the address its call pushed. An indirect site's targets seen in the trace are
                            printed (seeds for the target sets). Exit 1 at the first step that follows no edge.

Version 0: direct edges only; the indirect targets (vtables, switch tables, function pointers, IFUNC slots), the
landing pads (.gcc_except_table) and the unwinder's jump are to come. Not evidence for a theorem: the artifact the
statement names is checked by the proofs; this checks it on runs before.
"""
import re
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


def gen(src, out):
    n = ic = ij = 0
    with open(out, "w") as o:
        for ln in open(src):
            p = ln.rstrip("\n").split("\t")
            if len(p) < 4 or not p[1].isdigit():
                continue
            a = int(p[0], 16)
            e = edges_of(a, int(p[1]), p[2], p[3])
            n += 1
            ic += any(x.startswith("icall") for x in e)
            ij += "ijmp" in e
            o.write(f"{a:x}\t{','.join(e)}\n")
    print(f"{n} instructions; indirect sites to resolve: {ic} calls, {ij} jmps")


def load(cfg):
    g = {}
    for ln in open(cfg):
        a, e = ln.rstrip("\n").split("\t")
        g[int(a, 16)] = e.split(",") if e else []
    return g


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
    n = 0
    for q in trace(path):
        n += 1
        if prev is None:
            prev = q
            continue
        p, ok = prev, False
        for e in g.get(p, []):
            k = e.split(":")
            if k[0] == "go" and int(k[1], 16) == q:
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
    print(f"ok: {n} steps follow the graph; ghost stack depth {len(stk)} at the end")
    print(f"indirect sites seen: {len(seen)}, targets {sum(map(len, seen.values()))}")
    for p in sorted(seen)[:20]:
        print(f"  {p:x}: {' '.join(f'{q:x}' for q in sorted(seen[p]))}")


if __name__ == "__main__":
    if len(sys.argv) != 4 or sys.argv[1] not in ("gen", "check"):
        sys.exit(__doc__)
    (gen if sys.argv[1] == "gen" else check)(sys.argv[2], sys.argv[3])
