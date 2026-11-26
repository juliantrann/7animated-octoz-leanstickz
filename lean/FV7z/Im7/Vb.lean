import FV7z.Im7.S
/-!
# `_int_malloc` from 512 to 2549 for a largebin index `I`, `nb` a variable (PLAN.md G3, `malloc`)

`Pb I`: at 512 the index `I` at `rsp + 0x28` (`97 ≤ I ≤ 126`), `rbx` the arena, `r13` = `nb` and the frame
`Im2.Fr` of the entry; the fastbins flag 0, the largebin `I` empty, the tcache there (`nb` past its bins), the unsorted
bin and the binmap's block 3 empty: `1069 → 1099 → 1115 → 1968 → 1977 → 2012 → 2048 → 2480` to `use_top` at 2549.
-/
set_option Elab.async false
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im7

/-- From 512 to 2549 for the largebin index `I`. -/
def Pb (F : Footprint) (Wl : List Rgn) (I : Nat) : Prop :=
  ∀ {fb S nb : Addr} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte},
    g.rbx = 7940672#64 → g.r13 = nb → g.rsp = S → rdd(V, S + 40#64) = BitVec.ofNat 32 I → Im2.Fr S g₀ V₀ V →
    decide (nb.toNat < 1023) = false → decide (nb = 1023#64) = false →
    decide (64 < ((nb + 18446744073709551599#64) >>> 4).toNat) = true →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat →
    rdd(V, 7940680#64) = 0 →
    rdq(V, BitVec.ofNat 64 (7940768 + 16 * I)) = BitVec.ofNat 64 (7940752 + 16 * I) →
    rdq(V, fb + 18446744073709551576#64) ≠ 0#64 → rdq(V, 7940592#64) = 64#64 →
    rdq(V, 7940792#64) = 7940768#64 → rdd(V, 7942828#64) = 0 →
    (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a) →
    (∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_512 fb F Wl (fun j g₂ f₂ V₂ => j = 1115 ∧ W_1115 fb F Wl (fun j g₃ f₃ V₃ => j = 2012 ∧
      W_2012 fb F Wl (fun j' g' _ V' => j' = 2549 ∧ g'.rbx = 7940672#64 ∧ g'.r13 = nb ∧ g'.rsp = S ∧
        Im2.Fr S g₀ V₀ V') g₃ f₃ V₃) g₂ f₂ V₂) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vcB100 {F : Footprint} {Wl : List Rgn} : Pb F Wl 100 := by
  intro fb S nb g₀ g f V₀ V hbx h13 hsp hix hF c340 z340 c1099 hS hlo hfb hfc sk htc htb hun hm3 hW htf hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx h13 hsp ⊢
  subst hbx h13 hsp
  simp only [Nat.reduceMul, Nat.reduceAdd] at sk hix
  have qk := rd_below (x := 7942368#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q2 := rd_below (x := 7940680#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q3 := rd_below (n := 8) (hx := hfb) (hS := hS)
  have q5 := rd_below (x := 7940592#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q6 := rd_below (x := 7940792#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have q8 := rd_below (x := 7942828#64) (n := 4) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' := hS
  simp only [Nat.reducePow] at hS'
  have D : ∀ (x : Addr) (n : Nat), 7940480 ≤ x.toNat → x.toNat + n ≤ 7943136 →
      ∀ i < n, Foot F.data (Addr.add x i) :=
    fun x n h1 h2 i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  -- 512 → 1115
  lwp [W_512, W_1069, W_1099, o9, o10, o11,
    q2, q3, q5, q6, q8, sk, qk, hix, hS, hS', c340, z340, c1099, hfc, htb, htc, hun, hm3, BitVec.xor_self]
  lc7 [q2, q3, q5, q6, q8, sk, qk, hix, hS, hS', c340, z340, c1099, hfc, htb, htc, hun, hm3, BitVec.xor_self]
  -- 1115 → 2012
  any_goals lwp [W_1115, W_1138, W_1968, W_1977, o12, o13, o14, o15,
    q2, q3, q5, q6, q8, sk, qk, hix, hS, hS', c340, z340, c1099, hfc, htb, htc, hun, hm3, BitVec.xor_self]
  lc7 [q2, q3, q5, q6, q8, sk, qk, hix, hS, hS', c340, z340, c1099, hfc, htb, htc, hun, hm3, BitVec.xor_self]
  -- 2012 → 2549
  any_goals lwp [W_2012, W_2048, W_2480, W_2488, W_2505, o16, o17, o19, o20, o21,
    q2, q3, q5, q6, q8, sk, qk, hix, hS, hS', c340, z340, c1099, hfc, htb, htc, hun, hm3, BitVec.xor_self]
  lc7 [q2, q3, q5, q6, q8, sk, qk, hix, hS, hS', c340, z340, c1099, hfc, htb, htc, hun, hm3, BitVec.xor_self]

end FV7z.Im7
