#!/usr/bin/env python3
# Emit lean/FV7z/Tdm/{Ctx,Vc1,Vc2,Vc3}.lean from cuts.py and ctx_head.lean.
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cuts import C, ORDER

OUT = sys.argv[1]
HERE = os.path.dirname(os.path.abspath(__file__))
G = "⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩"
FIN = {354, 765}
CUTS = [k for k in ORDER if k != 0]  # the disjuncts of Inv after the entry


def conj(k):
    I = C[k][2]
    if not I:
        return "True"
    return " ∧ ".join(f"({e})" if "∨" in e else e for e, _ in I)


def wrap(i, n, x):
    s = x if i == n - 1 else f"Or.inl {x}"
    for _ in range(i):
        s = f"Or.inr ({s})"
    return s


def xbody(i, n, x):
    o = ["  refine Or.inl ⟨_, hm, Or.inr ⟨hc, ?_⟩⟩"]
    if i > 0:
        o.append(f"  iterate {i} right")
    o.append(f"  exact {x}" if i == n - 1 else f"  exact Or.inl {x}")
    return o


def ctx():
    o = [open(os.path.join(HERE, "ctx_head.lean")).read().rstrip("\n"), ""]
    o.append("set_option linter.unusedVariables false\n")
    for k in CUTS:
        if k != 343:
            o.append(f"/-- The condition at {k}. -/")
            body = conj(k)
            line = f"def I{k} (K : Ctx) (g : Gprs) : Prop := {body}"
            if len(line) > 118:
                o.append(f"def I{k} (K : Ctx) (g : Gprs) : Prop :=")
                parts = [f"({e})" if "∨" in e else e for e, _ in C[k][2]]
                cur = "  "
                for j, p in enumerate(parts):
                    piece = p + (" ∧" if j < len(parts) - 1 else "")
                    if len(cur) + len(piece) + 1 > 118:
                        o.append(cur.rstrip())
                        cur = "    "
                    cur += piece + " "
                o.append(cur.rstrip())
            else:
                o.append(line)
        o.append(f"def M{k} (g : Gprs) : Nat := {C[k][3]}")
        o.append("")
    # Inv
    o.append("/-- The invariant: the entry, or `Cm` and one cut point's condition and measure. -/")
    o.append("def Inv (K : Ctx) (ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=")
    o.append("  (ℓ = 0 ∧ m = 6300 ∧ g = K.g0 ∧ V = K.V0) ∨ (Cm K g ∧ (")
    ds = []
    for k in CUTS:
        if k == 343:
            ds.append("(ℓ = 343 ∧ I343 K g V ∧ m = M343 g)")
        else:
            ds.append(f"(ℓ = {k} ∧ V = K.V1 ∧ I{k} K g ∧ m = M{k} g)")
    for j, d in enumerate(ds):
        o.append("    " + d + (" ∨" if j < len(ds) - 1 else "))"))
    o.append("")
    o.append("/-- At the `ret`s. -/")
    o.append("def Fz (K : Ctx) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop := (j = 354 ∨ j = 765) ∧ FinR K g V")
    o.append("/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/")
    o.append("def Nx (K : Ctx) (m : Nat) : Post := fun j g _ V => (∃ m' < m, Inv K j m' g V) ∨ Fz K j g V")
    o.append("")
    o.append("/-! ## The exits -/")
    o.append("")
    o.append("variable {m : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}")
    o.append("")
    n = len(CUTS)
    for i, k in enumerate(CUTS):
        if k == 343:
            o.append(f"theorem x343 (hc : Cm K g) (hI : I343 K g V) (hm : M343 g < m) : Nx K m 343 g f V := by")
            o += xbody(i, n, "⟨rfl, hI, rfl⟩")
        else:
            o.append(f"theorem x{k} (hc : Cm K g) (hV : V = K.V1) (hI : I{k} K g) (hm : M{k} g < m) : "
                     f"Nx K m {k} g f V := by")
            o += xbody(i, n, "⟨rfl, hV, hI, rfl⟩")
        o.append("")
    o.append("theorem xFin {j : Nat} (hj : j = 354 ∨ j = 765) (h : FinR K g V) : Nx K m j g f V := Or.inr ⟨hj, h⟩")
    o.append("")
    o.append("end FV7z.Tdm")
    return "\n".join(o) + "\n"


FOOT = {
    "w": ["exact hE.w1", "exact hE.w2", "exact hE.w3", "exact hE.w4", "exact hE.w5"],
    "hbo": ["exact hE.hbo"], "wbo": ["exact hE.wbo"],
    "f": ["exact hE.f0", "exact hE.f1", "exact hE.f2", "exact hE.f3", "exact hE.f4"],
    "fA": ["with_reducible exact fA hE.hp (by omega)"], "fA0": ["with_reducible exact fA0 hE.hp (by omega)"],
    "fIn": ["exact fIn hE (by tfo) (by tfo)"], "fP": ["exact fP hK hE (by tfo) (by tfo)"],
    "fD": ["exact fD hE (by tfo) (by tfo)"],
}
OKF = ["have := hK.hP1", "have := hK.hP2", "have := hK.hnl", "have := hK.hnl1"]
PRE = {
    0: ["have := mask16 _ (ofBytesLE 32 (List.map K.V1 (byteAddrs (K.g0.rdi + 64#64) 4))) hK.hpb",
        "have := hK.hst", "have := hK.hB"],
    103: ["have := hK.edbs", "have := hK.hdp", "have := hK.hD"],
    180: ["have hx := h3 (ofBytesLE 8 (List.map K.V1 (byteAddrs (K.D + rcx) 1)))", "have := hK.hD"],
    210: ["have := hK.edbs", "have := hK.hdp", "have := hK.hrep", "have := hK.hD"],
    648: ["have hs := slot_sa (BitVec.setWidth 32 (rbx + 18446744073709551552#64))"],
    794: ["have := hK.hD"],
    833: ["have ha := and_cases (BitVec.setWidth 32 r10) (BitVec.setWidth 32 rbx + BitVec.setWidth 32 rbx) (by tfo)"],
    880: ["have hx := xor_cases (BitVec.setWidth 32 r10) (BitVec.setWidth 32 rbp) (by tfo)"],
}
WX = {0: ["← hK.eV1", "hK.eB", "hK.eP"], 103: ["hK.eD"], 210: ["hK.eD"]}
SPLIT = {594}
# Generalized after `wpx`: the literal context at 180 (its bound `hx` is from `CtxOk`).
POST = {180: ["generalize BitVec.setWidth 32 rbx + BitVec.setWidth 32 (ofBytesLE 8 (List.map K.V1 (byteAddrs (K.D + rcx)",
              "  1))) >>> ((BitVec.setWidth 8 (8#32 - BitVec.setWidth 32 r12)).toNat % 32) = cv at hx ⊢"]}
# Triage only: `src:dst` exits whose closers show their goals (TDM_DBG="320:340,794:833").
DBG = {tuple(map(int, x.split(":"))) for x in os.environ.get("TDM_DBG", "").split(",") if x}


def dbg(src, j, s):
    if (src, j) not in DBG:
        return s
    return s.replace("by tcm)", "by tcmd)").replace("tfs)", "tfsd)").replace("by tfo)", "by tfod)")


def exit_closer(src, j, case=None):
    return dbg(src, j, exit_closer0(src, j, case))


def exit_closer0(src, j, case):
    if j in FIN:
        return f"exact xFin (by decide) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by tfo, by tfo, by tfv{case}⟩"
    if j == 343:
        t = "t343b" if src == 340 else "t343a"
        return f"exact x343 (by tcm) (by dsimp only [I343]; {t}) (by dsimp only [M343] <;> tfo)"
    if (src, j) == (103, 180):
        return ("exact x180 (by tcm) rfl (by dsimp only [I180]; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>\n"
                "            (first | (with_reducible exact ctx_ok' hK _) | tfs)) (by dsimp only [M180] <;> tfo)")
    return f"exact x{j} (by tcm) rfl (by dsimp only [I{j}] <;> tfs) (by dsimp only [M{j}] <;> tfo)"


def loop(k, case=None):
    unf, exits, I, M, tags = C[k]
    alts = ["split"] if k in SPLIT else []
    for t in tags:
        alts += FOOT[t]
    alts += [exit_closer(k, j, case) for j in exits]
    alts += ["(with_reducible rfl)", "apply And.intro", "intro _"]
    o = ["  repeat' (first"]
    for a in alts:
        o.append("    | " + a)
    o[-1] += ")"
    return o


def wpx(k, extra):
    unf = C[k][0]
    ls = unf + ([f"M{k}"] if k != 0 else []) + ["Op.not32", "Op.cmpmi", "BitVec.xor_self", "BitVec.and_self"] + extra
    o, cur = [], "  wpx ["
    for j, x in enumerate(ls):
        piece = x + (", " if j < len(ls) - 1 else "]")
        if len(cur) + len(piece) > 118:
            o.append(cur.rstrip())
            cur = "    "
        cur += piece
    o.append(cur)
    return o


def vc(k):
    o = ["set_option maxHeartbeats 4000000 in"]
    if k == 0:
        o.append("/-- The entry. -/")
        o.append("theorem vc_0 (hK : Ok K) (hE : Env K F Wl) : W_0 F Wl (Nx K 6300) K.g0 f K.V0 := by")
        o.append("  show W_0 F Wl _ ⟨K.g0.rax, K.g0.rcx, K.g0.rdx, K.g0.rbx, K.g0.rsp, K.g0.rbp, K.g0.rsi, K.g0.rdi, "
                 "K.g0.r8,")
        o.append("    K.g0.r9, K.g0.r10, K.g0.r11, K.g0.r12, K.g0.r13, K.g0.r14, K.g0.r15⟩ f K.V0")
        o += ["  " + x for x in OKF + PRE[0]]
        o += wpx(0, WX[0])
        o += loop(0)
        return o
    V = "V" if k == 343 else "K.V1"
    hI = "I343 K g V" if k == 343 else f"I{k} K g"
    o.append(f"/-- {k}. -/")
    o.append(f"theorem vc_{k} (hK : Ok K) (hE : Env K F Wl) (hc : Cm K g) (hI : {hI}) :")
    o.append(f"    W_{k} F Wl (Nx K (M{k} g)) g f {V} := by")
    o.append(f"  obtain {G} := g")
    o.append("  obtain ⟨hsp, hdx, hr9, hr15, hs1, hs2⟩ := hc")
    o.append("  dsimp only at hsp hdx hr9 hr15 hs1 hs2")
    o.append("  subst hsp hdx hr9 hr15")
    if k == 343:
        o.append("  dsimp only [I343] at hI")
        o.append("  rcases hI with ⟨h0, rfl⟩ | ⟨⟨h0, h1⟩, rfl⟩")
        for case in "ab":
            body = ["  " + x for x in OKF] + wpx(k, []) + loop(k, case)
            o.append("  ·" + body[0][1:])
            o += ["  " + x for x in body[1:]]
        return o
    I = C[k][2]
    if I:
        o.append(f"  dsimp only [I{k}] at hI")
        pats = ["rfl" if s == "s" else f"h{i}" for i, (_, s) in enumerate(I)]
        if len(pats) == 1:
            o.append(f"  obtain {pats[0]} := hI")
        else:
            o.append(f"  obtain ⟨{', '.join(pats)}⟩ := hI")
    o += ["  " + x for x in OKF + PRE.get(k, [])]
    o += wpx(k, WX.get(k, []))
    o += ["  " + x for x in POST.get(k, [])]
    o += loop(k)
    return o


HDR = """import FV7z.Tdm.Ctx
/-!
# `LzmaDec_TryDummy`: the cut points {lo}–{hi} (PLAN.md §M, M1)

Each cut point's condition through its stretch to the next cut points (`vc_*`): `wpx`, then the reads by `fP`, `fIn`,
`fD`, `fA` and the exits by `x*`. Generated by `tools/tdm_gen/gen.py`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tdm
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {{K : Ctx}} {{F : Footprint}} {{Wl : List Rgn}} {{g : Gprs}} {{f : Rflags}} {{V : Addr → Byte}}
"""


def vcfile(ks):
    o = [HDR.format(lo=ks[0], hi=ks[-1])]
    for k in ks:
        o += vc(k)
        o.append("")
    o.append("end FV7z.Tdm")
    return "\n".join(o) + "\n"


def check(path, s):
    for i, l in enumerate(s.split("\n")):
        if len(l) > 120:
            print(f"{path}:{i+1}: {len(l)} columns")


files = {
    "Ctx.lean": ctx(),
    "Vc1.lean": vcfile([k for k in ORDER if k <= 343]),
    "Vc2.lean": vcfile([k for k in ORDER if 343 < k <= 751]),
    "Vc3.lean": vcfile([k for k in ORDER if k > 751]),
}
for n, s in files.items():
    p = os.path.join(OUT, n)
    open(p, "w").write(s)
    check(p, s)
print("ok")
