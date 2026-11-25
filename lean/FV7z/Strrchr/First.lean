import FV7z.Strrchr.Head
/-!
# `__strrchr_sse2`, the first 16 bytes (PLAN.md G2)

From `+41`, the 64 bytes from `p` on one page: the 16 bytes from `p` unaligned, compared with the spread character
(`xmm1`) into `ecx` and with 0 (`xmm2`, zeroed) into `edx`. A 0 among them: `tail74`; none: to `+112` with the
character mask in `rcx`.
-/
namespace FV7z.Strrchr
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

attribute [-simp] BitVec.getLsbD_eq_getElem

/-- Bit `i` of the mask of the 16 bytes at `B + d` compared with the spread `c`: whether byte `i + d` from `B` is
`c`'s low byte. -/
theorem cbit' (V : Addr → Byte) (B : Addr) (d i : Nat) (c : BitVec 64) :
    (pmsk (peqb (rd16 V (B + BitVec.ofNat 64 d)) (Bc c))).getLsbD i =
      (decide (i < 16) && decide (V (Addr.add B (i + d)) = c.setWidth 8)) := by
  rw [getLsbD_cmask]
  by_cases hi : i < 16
  · rw [lane_rd16 _ _ hi, show B + BitVec.ofNat 64 d = Addr.add B d from rfl, addr_add_add, Nat.add_comm d i]
  · rw [decide_eq_false hi, Bool.false_and, Bool.false_and]

/-- A 16-bit mask zero-extended to 64 bits. -/
theorem bits64 {m : BitVec 32} {f : Nat → Bool} (h : ∀ i, m.getLsbD i = (decide (i < 16) && f i)) (i : Nat) :
    (m.setWidth 64).getLsbD i = (decide (i < 16) && f i) := by
  rw [BitVec.getLsbD_setWidth, h]
  by_cases hi : i < 16
  · rw [decide_eq_true hi, decide_eq_true (show i < 64 by omega), Bool.true_and, Bool.true_and]
  · rw [decide_eq_false hi, Bool.false_and, Bool.and_false]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `+41`, `rdi = p`, `xmm1` the spread character, `p`'s place in its page at most `4032`. -/
theorem path41 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 41) (hkp : KpR g₀ X.cpu.gpr)
    (hdi : X.cpu.gpr.rdi = g₀.rdi) (hx1 : xsOf X.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi)
    (hq : g₀.rdi.toNat % 4096 ≤ 4032) (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (h112 : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 112 → KpR g₀ Y.cpu.gpr →
      Y.cpu.gpr.rdi = g₀.rdi →
      (∀ i, Y.cpu.gpr.rcx.getLsbD i = (decide (i < 16) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8))) →
      xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → xsOf Y.cpu.vec.zmm (xmmOf 2) = 0 → 16 ≤ n →
      GoG prof L o gev gP gE Y t')
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  have hp := g₀.rdi.isLt
  -- `movdqu xmm0, [rdi]`, `pxor xmm2, xmm2`, `movdqa xmm3, xmm0`, `pcmpeqb xmm0, xmm1`, `pcmpeqb xmm3, xmm2`,
  -- `pmovmskb ecx, xmm0`
  refine c.s_blkV hin (b41 prof) hK hA hrip ?_
  refine wpV_v (foot_pg hft (B := X.cpu.gpr.rdi) (d := 0) (by rw [hdi]; omega) (by rw [hdi]; omega)
    (by rw [hdi]; omega)) (fun h => nomatch h) (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_nil ?_))))))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  generalize hxd : xsOf X.cpu.vec.zmm = x at hg₁ hv₁ hx1
  simp (disch := decide) only [eaB, set_rcx, get7, xset_same, xset_ne, hx1, xor_self'] at hg₁ hv₁
  -- `pmovmskb edx, xmm3`, `test rdx, rdx`
  refine c.s_blkV hin (b65 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v0 (wpV_reg fun fl hP => wpV_nil ?_)
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ hv₂
  rw [hv₁] at hg₂
  simp (disch := decide) only [gv, Src.val, set_rdx, get2, xset_same, xset_ne, BitVec.setWidth_eq,
    BitVec.and_self] at hg₂ hP
  simp only [hg₁] at hg₂
  have hkp₂ : KpR g₀ Y₂.cpu.gpr := by simp only [KpR, hg₂]; exact hkp
  have hdi₂ : Y₂.cpu.gpr.rdi = g₀.rdi := by simp only [hg₂]; exact hdi
  have hcx : ∀ i, Y₂.cpu.gpr.rcx.getLsbD i =
      (decide (i < 16) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8)) := by
    intro i
    simp only [hg₂]
    rw [bits64 (fun i => cbit' V X.cpu.gpr.rdi 0 i g₀.rsi) i, Nat.add_zero, hdi]
  have hdx : ∀ i, Y₂.cpu.gpr.rdx.getLsbD i = (decide (i < 16) && decide (V (Addr.add g₀.rdi i) = 0)) := by
    intro i
    simp only [hg₂]
    rw [bits64 (fun i => zbit' V X.cpu.gpr.rdi 0 i) i, Nat.add_zero, hdi]
  have hc : fl.cond 4 = (Y₂.cpu.gpr.rdx == 0) := by rw [cond4_mask hP]; simp only [hg₂]
  refine c.s_jccV hK₂ hA₂ hin (by rw [sr2_length]; omega) hr₂ (d72 prof.feat) (tgt := 112) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- no 0 in the 16 bytes
    intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    rw [hf₂, hc] at htk
    have h0 := eq_of_beq htk
    have h16 : 16 ≤ n := Classical.byContradiction fun h => by
      have hb := hdx n
      rw [h0, getLsbD_zero', decide_eq_true (show n < 16 by omega), hz] at hb
      exact absurd hb (by decide)
    refine h112 Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃]; exact hdi₂) (by rw [hg₃]; exact hcx)
      ?_ ?_ h16
    · rw [hv₃, ← hv₂, hv₁]
      simp (disch := decide) only [xset_ne, hx1]
    · rw [hv₃, ← hv₂, hv₁]
      simp (disch := decide) only [xset_same, xset_ne, xor_self']
  · -- a 0: `tail74`
    intro hfa Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
    rw [hf₂, hc] at hfa
    have hne := ne_of_beq_false hfa
    have hn16 : n < 16 := Classical.byContradiction fun h => hne (by
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      rw [hdx, getLsbD_zero']
      by_cases hi : i < 16
      · rw [decide_eq_true hi, Bool.true_and]; exact decide_eq_false (hnz i (by omega))
      · rw [decide_eq_false hi, Bool.false_and])
    exact tail74 c hin hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃]; exact hdi₂) hn16
      (by rw [hg₃]; exact hcx) (by rw [hg₃]; exact hdx) hnz hz hch hR

end FV7z.Strrchr
