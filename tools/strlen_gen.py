#!/usr/bin/env python3
"""Generate lean/FV7z/Strlen/Code.lean: the bytes of `__strlen_sse2` in 7zzs 26.06 (0x6546d0, 412 bytes), what each
instruction decodes to (`Dec`, by evaluation), and its straight-line stretches as `BlkV` (FV7z/Lemmas/Sse2.lean).

Usage (from the repository root):  python3 -I tools/strlen_gen.py build/dec/sl2.txt > lean/FV7z/Strlen/Code.lean
The decoder listing is `decshow`'s (R1 names: `pminub` is R2's `pminu 8`).
"""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
src = open(__file__.rsplit('/', 1)[0] + '/blk_gen.py').read().split('def main():')[0]
exec(src)

N = 412
bs, ins = parse(sys.argv[1], N)
NEG = lambda k: 2 ** 64 - k
# stretches: (start, end) of straight-line code; the rest (jcc, jmp, bsf, ret) are steps of their own
BLKS = [(0, 40), (42, 56), (62, 66), (66, 128), (144, 148), (148, 221), (240, 256), (256, 286), (288, 292),
        (292, 321), (336, 340), (340, 401), (405, 411)]
SINGLE = {40, 56, 58, 61, 128, 130, 134, 221, 223, 227, 286, 321, 323, 401, 411}

def gpr(o):
    m = re.fullmatch(r'reg \{ w(\d+), n(\d+), ?\}', o); return int(m[1]), int(m[2])

def memd(o):
    m = MEM.fullmatch(o); assert m and m[1] == 'some 0' and m[2] == 'none' and m[3] == '1' and m[6] == '128', o
    return int(m[4])

def vop(off, mn, sz, ol, ln):
    """(Lean instruction, VOp, VOpI proof)"""
    if mn == 'endbr64': return "FV7z.mk .endbr64 32 [] 4", "VOp.op Op.nop", "OpI.endbr"
    if mn == 'nop':
        ops = [operand(o)[1] for o in ol]
        return f"FV7z.mk .nop {sz} [{', '.join(ops)}] {ln}", "VOp.op Op.nop", "OpI.nop"
    m = re.fullmatch(r'sse \(SseMn\.(\w+)\)', mn)
    if m:
        sm = m[1]
        if sm == 'pminub': sm, lmn = 'pminub', "(.sse (.pminu 8))"
        else: lmn = f"(.sse .{sm})"
        if ol[0].startswith('reg'):
            w, r = gpr(ol[0]); n = int(ol[1].split()[1])
            return f"FV7z.mk {lmn} {sz} [gr {w} {r}, .xmm {n}] {ln}", f"VOp.{sm} {r} {n}", f"VOpI.{sm}"
        n = int(ol[0].split()[1])
        if ol[1].startswith('xmm'):
            q = int(ol[1].split()[1])
            return f"FV7z.mk {lmn} {sz} [.xmm {n}, .xmm {q}] {ln}", f"VOp.{sm} {n} {q}", f"VOpI.{sm}"
        d = memd(ol[1])
        return (f"FV7z.mk {lmn} {sz} [.xmm {n}, .mem (mbd 0 {d} 128)] {ln}", f"VOp.{sm}_m {n} 0 {d}",
                f"VOpI.{sm}_m")
    terms, op, pf = effect(mn, sz, ol)
    return f"FV7z.mk {mnl(mn)} {sz} {terms} {ln}", f"VOp.op ({op})", pf

def single(off, mn, sz, ol, ln):
    terms = "[" + ", ".join(operand(o)[1] for o in ol) + "]"
    return f"FV7z.mk {mnl(mn)} {sz} {terms} {ln}"

at = {i[0]: i for i in ins}
out = []
out.append('''import FV7z.Lemmas.Sse2
import FV7z.Lemmas.BlkOps3
import FV7z.Lemmas.BlkOps2
/-!
# The code of `__strlen_sse2` (PLAN.md G2, the PLT contracts of `launch_to_main`)

glibc 2.31's `__strlen_sse2` (`sysdeps/x86_64/multiarch/strlen-sse2.S`, `strlen-vec.S`) at `0x6546d0` in `7zzs`, the
variant of `strlen` that the IFUNC resolver picks on a processor without AVX2: its bytes (`sl2`), what each instruction
decodes to on every processor (`d<offset>`, by evaluation), and its straight-line stretches as `BlkV`s
(`b<start>`). Generated from the decoder's output (`decshow`) by `tools/strlen_gen.py`.
-/
namespace FV7z.Strlen
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The bytes of `__strlen_sse2`. -/
def sl2 : List Byte := [
''' + rows(bs) + "]\n\ntheorem sl2_length : sl2.length = 412 := rfl\n")
for (off, mn, sz, ol, ln) in ins:
    if mn == 'nop' and off not in (252,): continue
    if off in SINGLE: inst = single(off, mn, sz, ol, ln)
    else: inst = vop(off, mn, sz, ol, ln)[0]
    line = f"theorem d{off} : ∀ feat, Dec feat sl2 {off} ({inst}) := by dec_rfl"
    if len(line) > 120:
        line = f"theorem d{off} : ∀ feat, Dec feat sl2 {off}\n    ({inst}) := by dec_rfl"
    out.append(line)
out.append("")
for (a, b) in BLKS:
    k = a; vs = []; ps = []
    while k < b:
        off, mn, sz, ol, ln = at[k]
        inst, v, pf = vop(off, mn, sz, ol, ln)
        vs.append(v); ps.append((k, pf, inst)); k += ln
    assert k == b, (a, b, k)
    out.append(f"/-- The stretch from `{a}` to `{b}`. -/")
    out.append(f"def o{a} : List VOp := [\n  " + ",\n  ".join(vs) + "]\n")
    out.append(f"theorem b{a} (prof : Profile) : BlkV prof sl2 {a} {b} o{a} :=")
    for (k, pf, inst) in ps:
        if k in (252,):
            out.append(f"  .cons (d{k} _) {pf} (by decide) <|")
        else:
            out.append(f"  .cons (d{k} _) ({pf}) (by decide) <|")
    out.append(f"  .nil {b}\n")
out.append("end FV7z.Strlen")
txt = "\n".join(out) + "\n"
print(txt, end='')
