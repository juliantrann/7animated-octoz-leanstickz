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

/-- `and eax, 4095` of `rax = x`: `x`'s place in its page. -/
theorem and32_4095 (x : BitVec 64) :
    ((x.setWidth 32 &&& BitVec.ofNat 32 4095).setWidth 64).toNat = x.toNat % 4096 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    show 4095 % 2 ^ 32 = 2 ^ 12 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  have hx := x.isLt
  simp only [Nat.reducePow] at hx ⊢
  omega

/-- `ja` taken after `cmp a, b`. -/
theorem ja_true {a b : BitVec 64} (h : (!(decide (a.toNat < b.toNat) || decide (a = b))) = true) :
    b.toNat < a.toNat := by
  by_cases h1 : a.toNat < b.toNat
  · rw [decide_eq_true h1, Bool.true_or] at h; exact absurd h (by decide)
  · by_cases h2 : a = b
    · rw [decide_eq_true h2, Bool.or_true] at h; exact absurd h (by decide)
    · have h3 : a.toNat ≠ b.toNat := fun h3 => h2 (BitVec.eq_of_toNat_eq h3)
      omega

/-- `__strrchr_sse2` from its first byte, `rdi = p`, `rsi` the character: the spread into `xmm1` and `cmp` of `p`'s
place in its page with `4032`; above: to `+560`, else `path41`. -/
theorem entry (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 0) (hkp : KpR g₀ X.cpu.gpr)
    (hdi : X.cpu.gpr.rdi = g₀.rdi) (hsi : X.cpu.gpr.rsi = g₀.rsi) (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (h560 : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 560 → KpR g₀ Y.cpu.gpr →
      Y.cpu.gpr.rdi = g₀.rdi → xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → 4032 < g₀.rdi.toNat % 4096 →
      GoG prof L o gev gP gE Y t')
    (h112 : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 112 → KpR g₀ Y.cpu.gpr →
      Y.cpu.gpr.rdi = g₀.rdi →
      (∀ i, Y.cpu.gpr.rcx.getLsbD i = (decide (i < 16) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8))) →
      xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → xsOf Y.cpu.vec.zmm (xmmOf 2) = 0 → 16 ≤ n →
      GoG prof L o gev gP gE Y t')
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  -- `endbr64`, `movd xmm1, esi`, `mov rax, rdi`, `and eax, 4095`, `punpcklbw xmm1, xmm1`, `cmp rax, 4032`
  refine c.s_blkV hin (b0 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_v0 (wpV_reg fun fl hP => wpV_nil ?_))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  simp only [wr, gv, Src.val, set_rax, get0, get6, get7, BitVec.setWidth_eq] at hg₁ hP hv₁
  have hkp₁ : KpR g₀ Y₁.cpu.gpr := by simp only [KpR, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := by simp only [hg₁]; exact hdi
  -- `punpcklwd xmm1, xmm1`, `pshufd xmm1, xmm1, 0`
  refine c.s_blkV hin (b26 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v0 (wpV_v0 (wpV_nil ?_))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ hv₂
  have hkp₂ : KpR g₀ Y₂.cpu.gpr := by simp only [KpR, hg₂]; exact hkp₁
  have hdi₂ : Y₂.cpu.gpr.rdi = g₀.rdi := by simp only [hg₂]; exact hdi₁
  have hx1 : xsOf Y₂.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by
    rw [hv₂, hv₁, ← hsi]
    simp (disch := decide) only [xset_same, xset_ne]
  refine c.s_jccV hK₂ hA₂ hin (by rw [sr2_length]; omega) hr₂ (d35 prof.feat) (tgt := 560) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- crossing a page within 64 bytes
    intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    rw [hf₂, hf₁, hP, cond_7, subF_cf, subF_zf] at htk
    have hq := ja_true htk
    rw [and32_4095, hdi] at hq
    exact h560 Y₃ t₃ hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃]; exact hdi₂) (by rw [hv₃]; exact hx1) hq
  · intro hfa Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
    rw [hf₂, hf₁, hP, cond_7, subF_cf, subF_zf] at hfa
    have hq := ja_false hfa
    rw [and32_4095, hdi] at hq
    exact path41 c hin hK₃ hA₃ hr₃ (by rw [hg₃]; exact hkp₂) (by rw [hg₃]; exact hdi₂) (by rw [hv₃]; exact hx1) hq
      hov hnz hz hch hft h112 hR

end FV7z.Strrchr
