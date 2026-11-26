#!/usr/bin/env python3
"""Generate the code files of `__strncmp_sse2` in 7zzs 26.06 (0x63a420, 6233 bytes): lean/FV7z/Strncmp/Code.lean,
AshrT.lean, Ashr1.lean .. Ashr5.lean.

- Code.lean: the bytes (`scm`), what each instruction outside the 15 shifted loops decodes to (`d<offset>`, by
  evaluation), their straight-line stretches as `BlkV`s (`b<start>`, pieces of at most 6 instructions), and `JccAt`,
  `JmpAt`: a jump at an offset to a target.
- AshrT.lean: the 15 shifted loops at `400 + 384 * (k - 1)`, `k = 1 .. 15`, share one layout and differ only in
  immediates (`16 - k`, `k`, `65536 - 2 ^ k`) and, for `k = 15`, in the end of the last piece: the template's pieces
  as `VOp` lists of `k` (`A<offset>`, the offset in the loop's code), and `AshrC prof k c`, what the loop at `c` is.
- Ashr<g>.lean: the loops' instances `ashr<k> : AshrC prof k (400 + 384 * (k - 1))`, three to a file.

Usage (from the repository root):  python3 -I tools/strncmp_gen.py build/dec/scm.txt lean/FV7z/Strncmp
The decoder listing is `decshow`'s for `63a420 6233`.
"""
import re, sys
sys.path.insert(0, __file__.rsplit('/', 1)[0])
src = open(__file__.rsplit('/', 1)[0] + '/blk_gen.py').read().split('def main():')[0]
exec(src)

N = 6233
BASE = 400
CH = 384
bs, ins = parse(sys.argv[1], N)
OUT = sys.argv[2]
at = {i[0]: i for i in ins}
PIECE = 6

# ---------------------------------------------------------------- instructions

def memo(o):
    """(base, index or None, disp, width) of a memory operand with scale 1"""
    m = MEM.fullmatch(o)
    assert m and m[1].startswith('some ') and m[3] == '1' and m[5] == 'false', o
    b = int(m[1].split()[1]); i = None if m[2] == 'none' else int(m[2].split()[1])
    return b, i, int(m[4]), int(m[6])


def gpr(o):
    m = re.fullmatch(r'reg \{ w(\d+), n(\d+), ?\}', o); return int(m[1]), int(m[2])


def vop(off, mn, sz, ol, ln):
    """(Lean instruction, VOp, VOpI proof) of an instruction of a straight-line stretch"""
    if mn == 'endbr64': return "FV7z.mk .endbr64 32 [] 4", "VOp.op Op.nop", "OpI.endbr"
    m = re.fullmatch(r'sse \(SseMn\.(\w+)\)', mn)
    if m:
        sm = m[1]
        lmn = f"(.sse .{sm})"
        if ol[0].startswith('reg'):   # pmovmskb r32, xmm
            w, r = gpr(ol[0]); n = int(ol[1].split()[1]); assert sm == 'pmovmskb' and w == 32
            return f"FV7z.mk {lmn} {sz} [gr 32 {r}, .xmm {n}] {ln}", f"VOp.pmovmskb {r} {n}", "VOpI.pmovmskb"
        n = int(ol[0].split()[1])
        if ol[1].startswith('xmm'):
            q = int(ol[1].split()[1])
            assert sm in ('pxor', 'pcmpeqb', 'psubb', 'por', 'movdqa'), sm
            return f"FV7z.mk {lmn} {sz} [.xmm {n}, .xmm {q}] {ln}", f"VOp.{sm} {n} {q}", f"VOpI.{sm}"
        if ol[1].startswith('imm'):
            k = int(ol[1].split()[2]); assert ol[1].split()[1] == '8' and sm in ('psrldq', 'pslldq')
            return f"FV7z.mk {lmn} {sz} [.xmm {n}, .imm 8 {k}] {ln}", f"VOp.{sm} {n} {k}", f"VOpI.{sm}"
        b, i, d, w = memo(ol[1])
        if sm in ('movlpd', 'movhpd'):
            assert i is None and w == 64
            return (f"FV7z.mk {lmn} {sz} [.xmm {n}, .mem (mbd {b} {d} 64)] {ln}", f"VOp.{sm}_m {n} {b} {d}",
                    f"VOpI.{sm}_m")
        assert w == 128 and sm in ('movdqa', 'pcmpeqb'), (sm, ol)
        if i is None:
            return (f"FV7z.mk {lmn} {sz} [.xmm {n}, .mem (mbd {b} {d} 128)] {ln}", f"VOp.{sm}_m {n} {b} {d}",
                    f"VOpI.{sm}_m")
        assert d == 0 and sm == 'movdqa'
        return (f"FV7z.mk {lmn} {sz} [.xmm {n}, .mem (mbi {b} {i} 0 128)] {ln}", f"VOp.movdqa_mi {n} {b} {i}",
                "VOpI.movdqa_mi")
    if mn == 'xchg':
        (w, r), (w2, q) = gpr(ol[0]), gpr(ol[1]); assert w == w2 == sz
        return (f"FV7z.mk .xchg {sz} [gr {w} {r}, gr {w} {q}] {ln}", f"VOp.op (Op.xchg {w} {r} {q})",
                f"OpI.xchg {hw2(w)}")
    terms, op, pf = effect(mn, sz, ol)
    assert pf.startswith('OpI.'), (off, pf)
    return f"FV7z.mk {mnl(mn)} {sz} {terms} {ln}", f"VOp.op ({op})", pf


def single(off, mn, sz, ol, ln):
    terms = "[" + ", ".join(operand(o)[1] for o in ol) + "]"
    return f"FV7z.mk {mnl(mn)} {sz} {terms} {ln}"


def target(off):
    """the target offset of the jump at `off`"""
    o, mn, sz, ol, ln = at[off]
    return (off + ln + operand(ol[0])[2][0]) % 2 ** 64


def wrap(line, ind="    "):
    """a theorem's line cut before its statement's instruction if longer than 120"""
    if len(line) <= 120: return line
    i = line.index(" (FV7z.mk")
    return line[:i] + "\n" + ind + line[i + 1:]


# the bytes in 17 pieces (`ch<j>`): the head, the 15 shifted loops, the end; `scm` is their concatenation, and what
# an instruction decodes to is evaluated in its piece (evaluating in all 6233 bytes runs out of recursion depth)
CS = [0] + [400 + 384 * c for c in range(15)] + [6144]
CE = CS[1:] + [N]
def chunk(off): return max(j for j in range(17) if CS[j] <= off)


def dec_line(off, inst):
    j = chunk(off)
    hk = "" if j == 16 else f"(by rw [ch{j}_length]; decide) "
    return (wrap(f"theorem d{off} : ∀ feat, Dec feat scm {off} ({inst}) :=") +
            f"\n  fun _ => lift{j} (k := {off - CS[j]}) {hk}(by intro f; rfl)")


def pieces(stretches):
    out = []
    for (a, b) in stretches:
        k = a; offs = []
        while k < b:
            offs.append(k); k += at[k][4]
        assert k == b, (a, b, k)
        for i in range(0, len(offs), PIECE):
            out.append((offs[i], offs[i + PIECE] if i + PIECE < len(offs) else b))
    return out


def blk(a, b, name, opsname):
    """the `BlkV` of the piece from `a` to `b`, its ops list named `opsname` (none: inline)"""
    k = a; vs = []; ps = []
    while k < b:
        inst, v, pf = vop(*at[k])
        vs.append(v); ps.append((k, pf)); k += at[k][4]
    return vs, ps


HEADER = '''/-!
# {title}

{body}
Generated from the decoder's output (`decshow`) by `tools/strncmp_gen.py`.
-/
namespace FV7z.Strncmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf
'''

def check(txt):
    for l in txt.split('\n'): assert len(l) <= 120, l
    return txt

# ---------------------------------------------------------------- Code.lean

HEAD_ST = [(0, 7), (13, 17), (23, 41), (43, 46), (48, 92), (98, 102), (108, 128), (128, 152), (156, 163), (163, 170),
           (177, 185), (192, 225), (231, 239), (245, 248), (254, 288), (288, 320), (326, 330), (336, 340),
           (340, 372), (378, 382), (388, 392)]
HEAD_SG = [7, 17, 41, 46, 92, 102, 152, 154, 170, 185, 225, 239, 248, 320, 330, 372, 382, 392]
TAIL_ST = [(6144, 6160), (6160, 6165), (6165, 6176), (6178, 6192),
           (6196, 6199), (6201, 6211), (6212, 6214), (6224, 6232)]
TAIL_SG = [6176, 6192, 6199, 6211, 6214, 6232]

code = ['import FV7z.Lemmas.Sse2d\nimport FV7z.Lemmas.BlkOps21\nimport FV7z.Lemmas.BlkOps2\n' + HEADER.format(
    title="The code of `__strncmp_sse2` (PLAN.md G3, `strncmp`)",
    body="""glibc 2.31's `__strncmp_sse2` (`sysdeps/x86_64/multiarch/strcmp-sse2.S`, `strcmp.S` with `USE_AS_STRNCMP`) at
`0x63a420` in `7zzs`, the variant of `strncmp` that the IFUNC resolver picks on a processor without SSSE3: its bytes
(`scm`), what each instruction outside the 15 shifted loops (`AshrT.lean`) decodes to on every processor
(`d<offset>`, by evaluation in its piece `ch<j>`: in all of them it runs out of recursion depth), and
their straight-line stretches as `BlkV`s (`b<start>`), in pieces of at most 6
instructions: the entry and the first 16 bytes (`0` to `128`), the alignment and the jump by the table at `0x6f0df0`
(`128` to `192`), the loop of strings with the same offset in their 16 bytes (`192` to `400`), the shared end of the
shifted loops (`6144`) and the exits (`6160` to `6233`).""") + '''
''' + "".join(
    f"/-- The bytes from `{CS[j]}` to `{CE[j]}`. -/\ndef ch{j} : List Byte := [\n" + rows(bs[CS[j]:CE[j]]) +
    f"]\n\ntheorem ch{j}_length : ch{j}.length = {CE[j] - CS[j]} := rfl\n\n" for j in range(17)) +
    "/-- The bytes of `__strncmp_sse2`. -/\ndef scm : List Byte :=\n  " +
    "".join(f"ch{j} ++ (" for j in range(8)) + "\n    " + "".join(f"ch{j} ++ (" for j in range(8, 16)) + "ch16" +
    ")" * 16 + "\n\n" +
    "theorem scm_length : scm.length = 6233 := by\n  simp only [scm, List.length_append, " +
    ", ".join(f"ch{j}_length" for j in range(6)) + ",\n    " +
    ", ".join(f"ch{j}_length" for j in range(6, 15)) + ",\n    " + ", ".join(f"ch{j}_length" for j in range(15, 17)) + "]\n\n" + '''theorem lt_scm {j : Nat} (h : j < 6233) : j < scm.length := scm_length ▸ h

/-- The bytes `X`, then `Y`, beyond them `f`: the bytes `X`, beyond them those of `X ++ Y`. -/
theorem fetchFrom_app (X Y : List Byte) (f : Nat → Option Byte) :
    fetchFrom (X ++ Y) f = fetchFrom X (fetchFrom (X ++ Y) f) := by
  funext n
  simp only [fetchFrom, List.length_append]
  by_cases h : n < X.length
  · simp only [h, ↓reduceIte, List.getElem?_append_left h, show n < X.length + Y.length by omega]
  · simp only [h, ↓reduceIte]

theorem drop_app (A B : List Byte) (n : Nat) : (A ++ B).drop n = A.drop n ++ B.drop (n - A.length) := by
  induction A generalizing n with
  | nil => simp
  | cons a A ih =>
    cases n with
    | zero => simp
    | succ n => simp [ih]

/-- What `A` decodes to at `k` is what `A ++ B` does. -/
theorem dec_appL {feat : Features} {A B : List Byte} {k : Nat} {i : Inst} (hk : k ≤ A.length) (h : Dec feat A k i) :
    Dec feat (A ++ B) k i := fun f => by
  rw [drop_app, Nat.sub_eq_zero_of_le hk, List.drop_zero, fetchFrom_app]
  exact h _

/-- What `B` decodes to at `k` is what `A ++ B` does at `k + A.length`. -/
theorem dec_appR {feat : Features} {A B : List Byte} {a k n : Nat} {i : Inst} (hA : A.length = a) (hn : k + a = n)
    (h : Dec feat B k i) : Dec feat (A ++ B) n i := fun f => by
  rw [drop_app, List.drop_eq_nil_of_le (as := A) (i := n) (by omega), List.nil_append, hA,
    show n - a = k by omega]
  exact h f
''' + "".join(
    f"\ntheorem lift{j} {{feat : Features}} {{k : Nat}} {{i : Inst}} " +
    ("" if j == 16 else f"(hk : k ≤ ch{j}.length) ") + f"(h : Dec feat ch{j} k i) :\n" +
    f"    Dec feat scm {'k' if j == 0 else f'(k + {CS[j]})'} i :=\n" +
    "".join(f"  dec_appR (n := k + {CS[j] - CS[i]}) ch{i}_length (by omega) <|\n" for i in range(j)) +
    ("  h\n" if j == 16 else "  dec_appL hk h\n") for j in range(17)) + '''
/-- A conditional jump at `j` of `len` bytes to `tgt`. -/
def JccAt (prof : Profile) (cc : Cond) (j len tgt : Nat) : Prop :=
  ∃ rel, Dec prof.feat scm j (FV7z.mk (.jcc cc) 64 [.rel rel] len) ∧ (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64

/-- A jump at `j` of `len` bytes to `tgt`. -/
def JmpAt (prof : Profile) (j len tgt : Nat) : Prop :=
  ∃ rel, Dec prof.feat scm j (FV7z.mk .jmp 64 [.rel rel] len) ∧ (j + len + rel) % 2 ^ 64 = tgt % 2 ^ 64
''']

hp = pieces(HEAD_ST + TAIL_ST)
inblk = {k for (a, b) in hp for k in range(a, b) if k in at}
for (off, mn, sz, ol, ln) in ins:
    if off in HEAD_SG or off in TAIL_SG:
        code.append(dec_line(off, single(off, mn, sz, ol, ln)))
    elif off in inblk:
        code.append(dec_line(off, vop(off, mn, sz, ol, ln)[0]))
code.append("")
for (a, b) in hp:
    vs, ps = blk(a, b, None, None)
    code.append(f"/-- The stretch from `{a}` to `{b}`. -/")
    code.append(f"def o{a} : List VOp := [\n  " + ",\n  ".join(vs) + "]\n")
    code.append(f"theorem b{a} (prof : Profile) : BlkV prof scm {a} {b} o{a} :=")
    for (k, pf) in ps:
        code.append(f"  .cons (d{k} _) ({pf}) (lt_scm (by decide)) <|")
    code.append(f"  .nil {b}\n")
code.append("end FV7z.Strncmp")
open(f"{OUT}/Code.lean", "w").write(check("\n".join(code) + "\n"))

# ---------------------------------------------------------------- the shifted loops

# the template's stretches and steps, offsets in a loop's code
T_ST = [(0, 42), (48, 60), (66, 69), (75, 128), (128, 132), (138, 188), (194, 198), (204, 216), (218, 268),
        (274, 278), (284, 292), (304, 318), (320, 324), (326, 337)]
T_SG = [42, 60, 69, 132, 188, 198, 216, 268, 278, 292, 318, 324, 337]
# the end: `352` to `367` and a jump to `6144` (k < 15); `352` to `368`, `368 = 6144 - c` (k = 15)
TAIL_A = (352, 367)
TAIL_B = (352, 368)
def cstart(k): return BASE + CH * (k - 1)
# for k = 15 the `jne` at 268 is short (2 bytes, not 6): what follows it up to the padding before 304 is 4 bytes
# earlier; `e` (4, or 0 for k = 15) is the difference
def E(k): return 4 if k < 15 else 0
def sh(k, t): return t if t <= 268 or t >= 304 else t - 4 + E(k)
def px(t): return "c" if t == 0 else f"({lx(t)})"
def lx(t): return "c" if t == 0 else f"c + {t}" if t <= 268 or t >= 304 else f"c + {t - 4} + e"
assert cstart(15) + 368 == 6144

def kexpr(vals):
    """a Lean expression of `k` with values `vals[k - 1]`"""
    for e, f in (("k", lambda k: k), ("(16 - k)", lambda k: 16 - k), ("(65536 - 2 ^ k)", lambda k: 65536 - 2 ** k)):
        if all(f(k) == v for k, v in vals): return e
    if len({v for _, v in vals}) == 1: return str(vals[0][1])
    raise Exception(vals)

def templ(strs):
    """one string with the integers that vary over `strs` (`(k, s)` pairs) as expressions of `k`"""
    toks = [(k, re.split(r'(\d+)', s)) for k, s in strs]
    t0 = toks[0][1]
    for _, t in toks: assert len(t) == len(t0) and all(a == b for a, b in zip(t[0::2], t0[0::2])), strs
    out = []
    for j, x in enumerate(t0):
        if j % 2 == 0: out.append(x)
        else:
            vals = [(k, int(t[j])) for k, t in toks]
            out.append(kexpr(vals) if len({v for _, v in vals}) > 1 else x)
    return "".join(out)

tp = pieces([(cstart(1) + a, cstart(1) + b) for a, b in T_ST])
tp = [(a - cstart(1), b - cstart(1)) for a, b in tp]
KS = list(range(1, 16))
# the ops of each piece, as a list of `k`
A = {}
for (a, b) in tp:
    per = []
    for k in KS:
        c = cstart(k)
        vs, _ = blk(c + sh(k, a), c + sh(k, b), None, None)
        per.append((k, "[\n  " + ",\n  ".join(vs) + "]"))
    A[a] = templ(per)
tailA = templ([(k, "[\n  " + ",\n  ".join(blk(cstart(k) + 352, cstart(k) + 367, None, None)[0]) + "]")
               for k in range(1, 15)])
tailB = templ([(15, "[\n  " + ",\n  ".join(blk(cstart(15) + 352, cstart(15) + 368, None, None)[0]) + "]")])
tailB = tailB.replace("15", "k")   # only k's immediates are 15 in it
def kdep(a): return re.search(r'\bk\b', A[a]) is not None
def aref(a, k): return f"(A{a} {k})" if kdep(a) else f"A{a}"
# the steps: each loop's alike
SG = {}
for s in T_SG:
    per = set()
    for k in KS:
        c = cstart(k); off, mn, sz, ol, ln = at[c + sh(k, s)]
        assert mn.startswith('jcc') or mn == 'jmp', (k, s, mn)
        t = target(c + sh(k, s))
        tt = f"c + {t - c}" if c <= t < c + CH else str(t)
        if s == 268: assert ln == 2 + E(k); ln = "(2 + e)"
        per.add((mn, ln, tt))
    assert len(per) == 1, (s, per)
    SG[s] = per.pop()
for k in range(1, 15):
    c = cstart(k); off, mn, sz, ol, ln = at[c + 367]
    assert mn == 'jmp' and ln == 5 and target(c + 367) == 6144, k
assert at[cstart(15) + 367][1] == 'nop' and at[cstart(15) + 367][4] == 1

def jfield(s):
    mn, ln, tt = SG[s]
    if mn == 'jmp': return f"JmpAt prof ({lx(s)}) {ln} ({tt})"
    return f"JccAt prof {mn.split()[1]} ({lx(s)}) {ln} ({tt})"

FIELDS = []
for (a, b) in tp: FIELDS.append(("p", a, b))
for s in T_SG: FIELDS.append(("j", s, None))
FIELDS.sort(key=lambda f: f[1])

at_ = ['import FV7z.Strncmp.Code\nimport FV7z.Lemmas.Sse2b\n' + HEADER.format(
    title="The shifted loops of `__strncmp_sse2` (PLAN.md G3, `strncmp`)",
    body="""When the two strings' offsets in their 16 bytes differ, `__strncmp_sse2` swaps them so that `rsi`'s is the greater, by
`k = 16 - (rsi's - rdi's)` jumps by its table to one of 15 loops at `c = 400 + 384 * (k - 1)`, and compares `rsi`'s
aligned vectors with `rdi`'s shifted by `16 - k` bytes (`psrldq`, `pslldq`, `por`). The loops share one layout: the
template's straight-line pieces as `VOp` lists of `k` (`A<offset>`, the offset in the loop's code), its jumps
(`JccAt`, `JmpAt`), and its end (`TailC`: for `k < 15` a jump to the shared end at `6144`, for `k = 15` the shared end
itself); `AshrC prof k c e` gathers them, `e` 4 (0 for `k = 15`, whose `jne` at 268 is short and what follows
it up to 304 four bytes earlier).""") + '\n']
for (a, b) in tp:
    at_.append(f"/-- The template's piece from `{a}` to `{b}`. -/")
    at_.append(f"def A{a}{' (k : Nat)' if kdep(a) else ''} : List VOp := {A[a]}\n")
at_.append("/-- The end from `352` for `k < 15`: then a jump to `6144`. -/")
at_.append(f"def T352 (k : Nat) : List VOp := {tailA}\n")
at_.append("/-- The end from `352` for `k = 15`: on to `6144`. -/")
at_.append(f"def T352s (k : Nat) : List VOp := {tailB}\n")
at_.append("""/-- The end of the loop at `c`. -/
def TailC (prof : Profile) (k c : Nat) : Prop :=
  (BlkV prof scm (c + 352) (c + 367) (T352 k) ∧ JmpAt prof (c + 367) 5 6144) ∨
    (BlkV prof scm (c + 352) (c + 368) (T352s k) ∧ c + 368 = 6144)
""")
at_.append("/-- The loop at `c` shifting by `k`. -/\nstructure AshrC (prof : Profile) (k c e : Nat) : Prop where")
for kind, a, b in FIELDS:
    if kind == "p": at_.append(f"  p{a} : BlkV prof scm {px(a)} ({lx(b)}) {aref(a, 'k')}")
    else: at_.append(f"  j{a} : {jfield(a)}")
at_.append("  tail : TailC prof k c\n")
at_.append("end FV7z.Strncmp")
open(f"{OUT}/AshrT.lean", "w").write(check("\n".join(at_) + "\n"))

# ---------------------------------------------------------------- the instances

GROUPS = [(1, 2, 3), (4, 5, 6), (7, 8, 9), (10, 11, 12), (13, 14, 15)]
for g, ks in enumerate(GROUPS, 1):
    out = ['import FV7z.Strncmp.AshrT\n' + HEADER.format(
        title=f"The shifted loops `k = {ks[0]}` to `{ks[-1]}` of `__strncmp_sse2` (PLAN.md G3, `strncmp`)",
        body="What each instruction of the loops decodes to (`d<offset>`, by evaluation) and their `AshrC`s.") + '\n']
    for k in ks:
        c = cstart(k)
        tl = TAIL_A if k < 15 else TAIL_B
        stp = [(c + sh(k, a), c + sh(k, b)) for a, b in tp] + [(c + tl[0], c + tl[1])]
        sg = [c + sh(k, s) for s in T_SG] + ([c + 367] if k < 15 else [])
        inb = {o for (a, b) in stp for o in range(a, b) if o in at}
        for o in sorted(inb | set(sg)):
            off, mn, sz, ol, ln = at[o]
            out.append(dec_line(o, single(*at[o]) if o in sg else vop(*at[o])[0]))
        out.append("")
        def bterm(a, b, ops):
            _, ps = blk(a, b, None, None)
            s = [f"  have b{a} : BlkV prof scm {a} {b} ({ops}) :="]
            for (o, pf) in ps:
                s.append(f"    .cons (d{o} _) ({pf}) (lt_scm (by decide)) <|")
            s.append(f"    .nil {b}")
            return s
        out.append(f"/-- The loop at `{c}`, `k = {k}`. -/")
        out.append(f"theorem ashr{k} (prof : Profile) : AshrC prof {k} {c} {E(k)} := by")
        for (a, b) in tp:
            out += bterm(c + sh(k, a), c + sh(k, b), aref(a, k)[1:-1] if kdep(a) else aref(a, k))
        out += bterm(c + tl[0], c + tl[1], f"{'T352' if k < 15 else 'T352s'} {k}")
        fs = []
        for kind, a, b in FIELDS:
            if kind == "p": fs.append(f"b{c + sh(k, a)}")
            else: fs.append(f"⟨_, d{c + sh(k, a)} _, rfl⟩")
        if k < 15: fs.append(f"(.inl ⟨b{c + 352}, _, d{c + 367} _, rfl⟩)")
        else: fs.append(f"(.inr ⟨b{c + 352}, rfl⟩)")
        line = "  exact ⟨"; lines = []
        for f in fs:
            if len(line) + len(f) + 2 > 118: lines.append(line.rstrip()); line = "    "
            line += f + ", "
        lines.append(line[:-2] + "⟩")
        out += lines
        out.append("")
    out.append("end FV7z.Strncmp")
    open(f"{OUT}/Ashr{g}.lean", "w").write(check("\n".join(out) + "\n"))
