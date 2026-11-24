import FV7z.Im6.Cuts
import FV7z.Im5.S0
/-!
# `_int_malloc` from the entry to 2549 for the request 72704 (PLAN.md G3, `malloc`; ctor 102)

`n` = 72704 (`0x11c00`): `nb` = 72720, `nb >> 6` = 1136 above 48, `nb >> 9` = 142 above 20, `nb >> 12` = 17 above 10
(492 → 2192), `nb >> 15` = 2 below 5: the largebin index `119 + 2` = 121 (2192), the way of `Im5.P5` from 512 on
(the binmap's block 3 empty, exit 2486). `P6`: the verification condition, `vc6`: its proof, one `lwp` per piece
(`Im5.lwp`, `Im5.lcl`).
-/
set_option Elab.async false
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im6

/-- From the entry to 2549 for `n` = 72704: the fastbins flag 0, the largebin 121, the unsorted bin and the binmap's
blocks 2 and 3 empty. -/
def P6 (F : Footprint) (Wl : List Rgn) : Prop :=
  ∀ {fb S : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = 72704#64 → g.rdi = 7940672#64 →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat →
    rdq(V, 8013224#64) = 128#64 → rdd(V, 7940680#64) = 0 →
    rdq(V, 7942704#64) = 7942688#64 →
    rdq(V, fb + 18446744073709551576#64) ≠ 0#64 → rdq(V, 7940592#64) = 64#64 →
    rdq(V, 7940792#64) = 7940768#64 → rdd(V, 7942824#64) = 0 → rdd(V, 7942828#64) = 0 →
    (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a) →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ f₁ V₁ => j = 512 ∧ W_512 fb F Wl (fun j g₂ f₂ V₂ => j = 1115 ∧ W_1115 fb F Wl
      (fun j g₃ f₃ V₃ => j = 2012 ∧ W_2012 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g'.rbx = 7940672#64 ∧
        g'.r13 = 72720#64 ∧ g'.rsp = S ∧ Im2.Fr S g V V') g₃ f₃ V₃) g₂ f₂ V₂) g₁ f₁ V₁) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vc6 {F : Footprint} {Wl : List Rgn} : P6 F Wl := by
  intro fb S g f V hrsp hsi hdi hS hlo hfb hgm hfc sk htc htb hun hm2 hm3 hW hgf htf hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have m : (72704#64 : Addr).msb = false := by decide
  have d1 : decide ((72704#64 + 23#64 : Addr).toNat < 31) = false := by decide
  have d2 : decide ((72704#64 + 23#64 : Addr) = 31#64) = false := by decide
  have e : (72704#64 + 23#64 &&& 18446744073709551600#64 : Addr) = 72720#64 := by decide
  have qk := rd_below (S := S) (x := 7942704#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
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
  -- 0 → 512 (through 492 and 2192)
  lwp [W_0, W_9, W_304, W_320, W_340, W_352, W_482, W_492, W_2192, o0, o1, o2, o3, o4, o5, o6, o7, o17,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc,
    hun, hm2, hm3]
  lcl
  -- 512 → 1115
  any_goals lwp [W_512, W_1069, W_1099, o8, o9, o10,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc,
    hun, hm2, hm3]
  lcl
  -- 1115 → 2012
  any_goals lwp [W_1115, W_1138, W_1968, W_1977, o11, o12, o13, o14,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc,
    hun, hm2, hm3]
  lcl
  -- 2012 → 2549
  any_goals lwp [W_2012, W_2048, W_2480, W_2488, W_2505, o15, o16, o18, o19, o20,
    p1, p2, p3, p4, p5, p6, p7, q1, q2, q3, q5, q6, q7, q8, sk, qk, hS, hS', m, d1, d2, e, hgm, hfc, htb, htc,
    hun, hm2, hm3]
  lcl

end FV7z.Im6
