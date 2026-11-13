import FV7z.Im5.Cuts
import FV7z.Im2.Frame
import FV7z.Lemmas.Ksplit
/-!
# `_int_malloc` from the entry to 2549 for a largebin size `16 k`: the statement (PLAN.md G3, `malloc`)

The requests `1001 ≤ n ≤ 4096`: `nb = 16 k`, `64 ≤ k ≤ 257`, a largebin size. The way: `0 → 304 → 320 → 340 → 352`,
`482` (`have_fastchunks` 0) to 512, the largebin `lbi k` empty, `1069 → 1099 → 1115`, the unsorted bin empty, the
binmap's blocks 2 and 3 empty, `2012 → 2048 → 2480/2505` to `use_top` at 2549. At 2549 `rbx` is `av`, `r13` is `nb`,
`rsp` is `S` and the bytes are the frame `Im2.Fr` of the entry (the code from 2549 on: `Im2.im_from2549`).

- `lbi k`: `largebin_index_64 (16 k)`: `48 + nb / 64` up to `nb / 64 = 48`, then `91 + nb / 512`.
- `lwp`, `lcl`: one piece of the way (`wpx` with the reads of the bins and the frame) and the goals it leaves (the
  frame by `Fr.vst` then `Fr.base`, the footprints, `lwp` again before any flag is taken as a hypothesis). `lcl` names
  the hypotheses of `vc_L*` (`p1` … `hm3`, `hS`, `hsw`, `hsd`, `hgf`, `htf`, `D`).
- `P5 k`: the verification condition, proved for six ranges of `k` (`Im5/L1.lean` … `L6.lean`, `tools/im5_gen.py`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im5

/-- `largebin_index_64` of `16 k` (`k ≤ 320`). -/
def lbi (k : Nat) : Nat := if 16 * k / 64 ≤ 48 then 48 + 16 * k / 64 else 91 + 16 * k / 512

theorem lbi_le (k : Nat) (hk : k ≤ 257 := by omega) : lbi k ≤ 99 := by
  unfold lbi
  split <;> omega

/-- `wpx` with the reads and rewrites of the largebin way; the blocks of one piece as the extra lemmas. -/
macro "lwp" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [Op.cmpma, Op.cmpmif, Op.cmpmra, Op.shr64, rd_off, rd_off_self, BitVec.and_self,
    BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceSetWidth, BitVec.reduceHShiftRight, BitVec.reduceHShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceShiftLeft, BitVec.reduceBEq, BitVec.reduceEq, BitVec.reduceToNat,
    BitVec.reduceSub, BitVec.reduceMul, BitVec.reduceLT, BitVec.reduceULT, BitVec.reduceOr, BitVec.reduceXOr,
    Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, decide_false, decide_true, Bool.or_false, Bool.false_or,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, false_imp_iff, true_imp_iff, Bool.or_self, Bool.true_or,
    Bool.or_true, false_implies, true_implies, and_true, true_and, reduceIte, or_true, true_or, or_false, false_or,
    ne_eq, Nat.reduceEqDiff, not_false_eq_true, ofBytesLE_toBytesLE, Bool.true_eq_false, $ls,*])

set_option hygiene false in
/-- The goals a piece leaves: the frame, the footprints, what `simp` has yet to reduce (before any `intro`: a flag
equation or `LogF` taken as a hypothesis is not reduced), the cases of the flags (the hypotheses by name). -/
macro "lcl" : tactic => `(tactic| repeat' first
    | apply And.intro
    | refine Im2.Fr.vst _ hS ?_ (by decide) (by decide)
    | exact Im2.Fr.base _ _ hS
    | rfl
    | with_reducible exact stk_f hsw (by decide)
    | with_reducible exact stk_f hsd (by decide)
    | with_reducible exact hgf
    | with_reducible exact htf
    | with_reducible exact D _ _ (by decide) (by decide)
    | (lwp [eaG]; with_reducible exact D _ _ (by decide) (by decide))
    | lwp [p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb,
        htc, hun, hm2, hm3]
    | intro (_ : Rflags)
    | intro (_ : Rflags.zf _ = false)
    | intro (_ : Rflags.zf _ = true)
    | decide)

/-- From the entry to 2549 for `nb = 16 k`, a largebin size: the fastbins flag 0, the largebin `lbi k`, the unsorted
bin and the binmap's blocks 2 and 3 empty. -/
def P5 (F : Footprint) (Wl : List Rgn) (k : Nat) : Prop :=
  ∀ {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = BitVec.ofNat 64 (16 * k) →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat →
    rdq(V, 8013224#64) = 128#64 → rdd(V, 7940680#64) = 0 →
    rdq(V, BitVec.ofNat 64 (7940768 + 16 * lbi k)) = BitVec.ofNat 64 (7940752 + 16 * lbi k) →
    rdq(V, fb + 18446744073709551576#64) ≠ 0#64 → rdq(V, 7940592#64) = 64#64 →
    rdq(V, 7940792#64) = 7940768#64 → rdd(V, 7942824#64) = 0 → rdd(V, 7942828#64) = 0 →
    (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a) →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ f₁ V₁ => j = 512 ∧ W_512 fb F Wl (fun j g₂ f₂ V₂ => j = 1115 ∧ W_1115 fb F Wl
      (fun j g₃ f₃ V₃ => j = 2012 ∧ W_2012 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g'.rbx = 7940672#64 ∧
        g'.r13 = BitVec.ofNat 64 (16 * k) ∧ g'.rsp = S ∧ Im2.Fr S g V V') g₃ f₃ V₃) g₂ f₂ V₂) g₁ f₁ V₁) g f V

end FV7z.Im5
