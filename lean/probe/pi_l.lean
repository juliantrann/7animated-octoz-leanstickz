import FV7z.Im5.Cuts
import FV7z.Im2.Frame
/-! Probe: the requests `1001 ≤ n ≤ 4096` (`nb` = `16 k`, a largebin size): from the entry of `_int_malloc` to 2549
through the cut points 512, 1115, 2012 of `Im5`, for `k` = 128 (index `48 + nb / 64`, the jump at 480) and `k` = 257
(index `91 + nb / 512`, the jump at 490), one `wpx` per piece; at 2549 `rbx` = `av`, `r13` = `nb`, `rsp` = `S` and
the frame `Im2.Fr`. What is left shown and given up. -/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im5
variable {F : Footprint} {Wl : List Rgn}

/-- `wpx` with the reads and rewrites of the probe; the blocks of one piece as the extra lemmas. -/
macro "wpl" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
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
macro "cl" : tactic => `(tactic| repeat' first
    | apply And.intro
    | refine Im2.Fr.vst _ hS ?_ (by decide) (by decide)
    | exact Im2.Fr.base _ _ hS
    | rfl
    | with_reducible exact stk_f hsw (by decide)
    | with_reducible exact stk_f hsd (by decide)
    | with_reducible exact hgf
    | with_reducible exact htf
    | with_reducible exact D _ _ (by decide) (by decide)
    | (wpl [eaG]; with_reducible exact D _ _ (by decide) (by decide))
    | wpl [p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb,
        htc, hun, hm2, hm3]
    | intro (_ : Rflags)
    | intro (_ : Rflags.zf _ = false)
    | intro (_ : Rflags.zf _ = true)
    | decide)

set_option maxHeartbeats 200000000 in
theorem vc_L128 {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (m : n.msb = false)
    (d1 : decide ((n + 23#64).toNat < 31) = false) (d2 : decide (n + 23#64 = 31#64) = false)
    (e : n + 23#64 &&& 18446744073709551600#64 = 2048#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64) (hfc : rdd(V, 7940680#64) = 0)
    (sk : rdq(V, 7942048#64) = 7942032#64)
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm2 : rdd(V, 7942824#64) = 0) (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) (hsd : ∀ i < 184, Foot F.data (Addr.add S i)) :
    W_0 fb F Wl (fun j g₁ f₁ V₁ => j = 512 ∧ W_512 fb F Wl (fun j g₂ f₂ V₂ => j = 1115 ∧ W_1115 fb F Wl
      (fun j g₃ f₃ V₃ => j = 2012 ∧ W_2012 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g'.rbx = 7940672#64 ∧
        g'.r13 = 2048#64 ∧ g'.rsp = S ∧ Im2.Fr S g V V') g₃ f₃ V₃) g₂ f₂ V₂) g₁ f₁ V₁) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have qk := rd_below (S := S) (x := 7942048#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (S := S) (x := 7940680#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q6 := rd_below (S := S) (x := 7940792#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q7 := rd_below (S := S) (x := 7942824#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q8 := rd_below (S := S) (x := 7942828#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  -- 0 → 512
  wpl [W_0, W_9, W_304, W_320, W_340, W_352, W_482, o0, o1, o2, o3, o4, o5, o6,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  -- 512 → 1115
  any_goals wpl [W_512, W_1069, W_1099, o7, o8, o9,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  -- 1115 → 2012
  any_goals wpl [W_1115, W_1138, W_1968, W_1977, o10, o11, o12, o13,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  -- 2012 → 2549
  any_goals wpl [W_2012, W_2048, W_2480, W_2488, W_2505, o14, o15, o16, o17, o18,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  all_goals (trace_state; sorry)

set_option maxHeartbeats 200000000 in
theorem vc_L257 {fb S n : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hrsp : g.rsp = S + 184#64)
    (hsi : g.rsi = n) (hdi : g.rdi = 7940672#64) (m : n.msb = false)
    (d1 : decide ((n + 23#64).toNat < 31) = false) (d2 : decide (n + 23#64 = 31#64) = false)
    (e : n + 23#64 &&& 18446744073709551600#64 = 4112#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64) (hfc : rdd(V, 7940680#64) = 0)
    (sk : rdq(V, 7942352#64) = 7942336#64)
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm2 : rdd(V, 7942824#64) = 0) (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 184, Foot Wl (Addr.add S i)) (hsd : ∀ i < 184, Foot F.data (Addr.add S i)) :
    W_0 fb F Wl (fun j g₁ f₁ V₁ => j = 512 ∧ W_512 fb F Wl (fun j g₂ f₂ V₂ => j = 1115 ∧ W_1115 fb F Wl
      (fun j g₃ f₃ V₃ => j = 2012 ∧ W_2012 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g'.rbx = 7940672#64 ∧
        g'.r13 = 4112#64 ∧ g'.rsp = S ∧ Im2.Fr S g V V') g₃ f₃ V₃) g₂ f₂ V₂) g₁ f₁ V₁) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have qk := rd_below (S := S) (x := 7942352#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (S := S) (x := 7940680#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (S := S) (n := 8) (hx := hfb) (hS := hS)
  have q5 := rd_below (S := S) (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q6 := rd_below (S := S) (x := 7940792#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q7 := rd_below (S := S) (x := 7942824#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q8 := rd_below (S := S) (x := 7942828#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  -- 0 → 512
  wpl [W_0, W_9, W_304, W_320, W_340, W_352, W_482, o0, o1, o2, o3, o4, o5, o6,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  -- 512 → 1115
  any_goals wpl [W_512, W_1069, W_1099, o7, o8, o9,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  -- 1115 → 2012
  any_goals wpl [W_1115, W_1138, W_1968, W_1977, o10, o11, o12, o13,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  -- 2012 → 2549
  any_goals wpl [W_2012, W_2048, W_2480, W_2488, W_2505, o14, o15, o16, o17, o18,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc, hun,
    hm2, hm3]
  cl
  all_goals (trace_state; sorry)

end FV7z.Im5
