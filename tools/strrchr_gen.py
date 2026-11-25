#!/usr/bin/env python3
"""Generate lean/FV7z/Strrchr/Code.lean: the bytes of `__strrchr_sse2` in 7zzs 26.06 (0x654200, 754 bytes), what each
instruction decodes to (`Dec`, by evaluation), and its straight-line stretches as `BlkV` (FV7z/Lemmas/Sse2.lean,
Sse2b.lean), each cut into pieces of at most 6 instructions (one simp over more register ops grows like a tree).

Usage (from the repository root):  python3 -I tools/strrchr_gen.py build/dec/sr2.txt > lean/FV7z/Strrchr/Code.lean
The decoder listing is `decshow`'s (R1 names: `pminub` is R2's `pminu 8`).
"""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
src = open(__file__.rsplit('/', 1)[0] + '/blk_gen.py').read().split('def main():')[0]
exec(src)

N = 754
bs, ins = parse(sys.argv[1], N)
# straight-line code between the steps of their own (jcc, jmp, bsr, ret); the loop's entry `303` is a cut
STRETCHES = [(0, 35), (41, 72), (74, 84), (94, 97), (112, 226), (228, 238), (248, 252), (256, 262), (268, 280),
             (288, 303), (303, 424), (430, 504), (508, 512), (528, 535), (544, 546), (560, 724), (730, 740),
             (750, 753)]
SINGLE = {35, 72, 84, 90, 97, 226, 238, 244, 252, 262, 280, 424, 504, 512, 535, 546, 724, 740, 746, 753}
PIECE = 6

def gpr(o):
    m = re.fullmatch(r'reg \{ w(\d+), n(\d+), ?\}', o); return int(m[1]), int(m[2])

def memd(o):
    m = MEM.fullmatch(o)
    assert m and m[1].startswith('some ') and m[2] == 'none' and m[3] == '1' and m[6] == '128', o
    return int(m[1].split()[1]), int(m[4])

def vop(off, mn, sz, ol, ln):
    """(Lean instruction, VOp, VOpI proof)"""
    if mn == 'endbr64': return "FV7z.mk .endbr64 32 [] 4", "VOp.op Op.nop", "OpI.endbr"
    m = re.fullmatch(r'sse \(SseMn\.(\w+)\)', mn)
    if m:
        sm = m[1]
        lmn = "(.sse (.pminu 8))" if sm == 'pminub' else f"(.sse .{sm})"
        if ol[0].startswith('reg'):   # pmovmskb r32, xmm
            w, r = gpr(ol[0]); n = int(ol[1].split()[1])
            return f"FV7z.mk {lmn} {sz} [gr {w} {r}, .xmm {n}] {ln}", f"VOp.{sm} {r} {n}", f"VOpI.{sm}"
        n = int(ol[0].split()[1])
        if ol[1].startswith('reg'):   # movd xmm, r32
            w, r = gpr(ol[1]); assert sm == 'movd' and w == 32
            return f"FV7z.mk {lmn} {sz} [.xmm {n}, gr 32 {r}] {ln}", f"VOp.movd {n} {r}", "VOpI.movd"
        if ol[1].startswith('xmm'):
            q = int(ol[1].split()[1])
            if len(ol) == 3:   # pshufd xmm, xmm, imm8
                k = int(ol[2].split()[2]); assert sm == 'pshufd'
                return (f"FV7z.mk {lmn} {sz} [.xmm {n}, .xmm {q}, .imm 8 {k}] {ln}", f"VOp.pshufd {n} {q} {k}",
                        "VOpI.pshufd")
            return f"FV7z.mk {lmn} {sz} [.xmm {n}, .xmm {q}] {ln}", f"VOp.{sm} {n} {q}", f"VOpI.{sm}"
        b, d = memd(ol[1])
        return (f"FV7z.mk {lmn} {sz} [.xmm {n}, .mem (mbd {b} {d} 128)] {ln}", f"VOp.{sm}_m {n} {b} {d}",
                f"VOpI.{sm}_m")
    terms, op, pf = effect(mn, sz, ol)
    return f"FV7z.mk {mnl(mn)} {sz} {terms} {ln}", f"VOp.op ({op})", pf

def single(off, mn, sz, ol, ln):
    terms = "[" + ", ".join(operand(o)[1] for o in ol) + "]"
    return f"FV7z.mk {mnl(mn)} {sz} {terms} {ln}"

at = {i[0]: i for i in ins}
inblk = set()
BLKS = []
for (a, b) in STRETCHES:
    k = a; offs = []
    while k < b:
        offs.append(k); inblk.add(k); k += at[k][4]
    assert k == b, (a, b, k)
    for i in range(0, len(offs), PIECE):
        BLKS.append((offs[i], offs[i + PIECE] if i + PIECE < len(offs) else b))
out = []
out.append('''import FV7z.Lemmas.Sse2b
import FV7z.Lemmas.BlkOps3
import FV7z.Lemmas.BlkOps2
/-!
# The code of `__strrchr_sse2` (PLAN.md G2, the PLT contracts of `launch_to_main`)

glibc 2.31's `__strrchr_sse2` (`sysdeps/x86_64/multiarch/strrchr-sse2.S`, `strrchr.S`) at `0x654200` in `7zzs`, the
variant of `strrchr` that the IFUNC resolver picks on a processor without AVX2: its bytes (`sr2`), what each
instruction decodes to on every processor (`d<offset>`, by evaluation), and its straight-line stretches as `BlkV`s
(`b<start>`), in pieces of at most 6 instructions. Generated from the decoder's output (`decshow`) by
`tools/strrchr_gen.py`.
-/
namespace FV7z.Strrchr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The bytes of `__strrchr_sse2`. -/
def sr2 : List Byte := [
''' + rows(bs) + f"]\n\ntheorem sr2_length : sr2.length = {N} := rfl\n")
for (off, mn, sz, ol, ln) in ins:
    if off not in SINGLE and off not in inblk: continue   # padding between the stretches
    if off in SINGLE: inst = single(off, mn, sz, ol, ln)
    else: inst = vop(off, mn, sz, ol, ln)[0]
    line = f"theorem d{off} : ∀ feat, Dec feat sr2 {off} ({inst}) := by dec_rfl"
    if len(line) > 120:
        line = f"theorem d{off} : ∀ feat, Dec feat sr2 {off}\n    ({inst}) := by dec_rfl"
    out.append(line)
out.append("")
for (a, b) in BLKS:
    k = a; vs = []; ps = []
    while k < b:
        off, mn, sz, ol, ln = at[k]
        inst, v, pf = vop(off, mn, sz, ol, ln)
        vs.append(v); ps.append((k, pf)); k += ln
    assert k == b, (a, b, k)
    out.append(f"/-- The stretch from `{a}` to `{b}`. -/")
    out.append(f"def o{a} : List VOp := [\n  " + ",\n  ".join(vs) + "]\n")
    out.append(f"theorem b{a} (prof : Profile) : BlkV prof sr2 {a} {b} o{a} :=")
    for (k, pf) in ps:
        out.append(f"  .cons (d{k} _) ({pf}) (by decide) <|")
    out.append(f"  .nil {b}\n")
out.append("end FV7z.Strrchr")
txt = "\n".join(out) + "\n"
for l in txt.split('\n'): assert len(l) <= 120, l
sys.stdout.write(txt)
