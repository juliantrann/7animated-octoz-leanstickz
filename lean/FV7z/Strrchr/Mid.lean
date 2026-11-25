import FV7z.Strrchr.First
/-!
# `__strrchr_sse2`, bytes 16 to 63 (PLAN.md G2)

From `+112`, no 0 among the first 16 bytes from `p`, all 64 on one page: the three 16-byte stretches at `p + 16`,
`p + 32`, `p + 48` compared with the spread character and with 0, the masks joined into `rsi` (the character, all 64
bytes, with `rcx`'s first 16) and `rax` (the 0s, bytes 16 to 63). No 0: to `+256` with `rsi`; else the matches up to
the first 0 (`+228`), none: `+544`, else the last (`bsr`, `lea rax, [rdi + rsi]`).
-/
namespace FV7z.Strrchr
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

attribute [-simp] BitVec.getLsbD_eq_getElem

/-- Whether byte `i` from `p` is `ch`. -/
abbrev Fb (V : Addr → Byte) (p : Addr) (ch : Byte) (i : Nat) : Bool := decide (V (Addr.add p i) = ch)

/-- Bits `[a, b)` of `x` say `f`, the others are 0. -/
def R (a b : Nat) (f : Nat → Bool) (x : BitVec 64) : Prop :=
  ∀ i, x.getLsbD i = (decide (a ≤ i) && decide (i < b) && f i)

theorem R_low {x : BitVec 64} {f : Nat → Bool} (h : ∀ i, x.getLsbD i = (decide (i < 16) && f i)) : R 0 16 f x := by
  intro i
  rw [h, decide_eq_true (Nat.zero_le i), Bool.true_and]

theorem R_shl {x : BitVec 64} {f : Nat → Bool} {k : Nat} (h : ∀ i, x.getLsbD i = (decide (i < 16) && f (i + k)))
    (hk : k + 16 ≤ 64) : R k (k + 16) f (x <<< k) := by
  intro i
  rw [BitVec.getLsbD_shiftLeft]
  by_cases h1 : k ≤ i
  · rw [h, Nat.sub_add_cancel h1, decide_eq_true h1, decide_eq_false (show ¬ i < k by omega)]
    by_cases h2 : i < k + 16
    · rw [decide_eq_true h2, decide_eq_true (show i < 64 by omega), decide_eq_true (show i - k < 16 by omega)]
      simp only [Bool.not_false, Bool.true_and]
    · rw [decide_eq_false h2, decide_eq_false (show ¬ i - k < 16 by omega)]
      simp only [Bool.and_false, Bool.false_and]
  · rw [decide_eq_false h1, decide_eq_true (show i < k by omega)]
    simp only [Bool.not_true, Bool.and_false, Bool.false_and]

theorem R_or {a b c : Nat} {f : Nat → Bool} {x y : BitVec 64} (hx : R a b f x) (hy : R b c f y) (hab : a ≤ b)
    (hbc : b ≤ c) : R a c f (x ||| y) := by
  intro i
  rw [BitVec.getLsbD_or, hx, hy]
  by_cases h : i < b
  · rw [decide_eq_true h, decide_eq_false (show ¬ b ≤ i by omega), decide_eq_true (show i < c by omega)]
    simp only [Bool.and_true, Bool.false_and, Bool.or_false]
  · rw [decide_eq_false h, decide_eq_true (show b ≤ i by omega), decide_eq_true (show a ≤ i by omega)]
    simp only [Bool.and_false, Bool.false_and, Bool.false_or, Bool.true_and]

theorem R_or' {a b c : Nat} {f : Nat → Bool} {x y : BitVec 64} (hx : R b c f x) (hy : R a b f y) (hab : a ≤ b)
    (hbc : b ≤ c) : R a c f (x ||| y) := by
  rw [BitVec.or_comm]
  exact R_or hy hx hab hbc

/-- A 16-bit mask, zero-extended and shifted left by `k`. -/
theorem R_m {m : BitVec 32} {f : Nat → Bool} {k : Nat} (h : ∀ i, m.getLsbD i = (decide (i < 16) && f (i + k)))
    (hk : k + 16 ≤ 64) : R k (k + 16) f (m.setWidth 64 <<< k) :=
  R_shl (bits64 h) hk

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `+228`, `rsi`'s bits the 64 bytes from `p` that are `ch`, `rax`'s the 0s among bytes 16 to 63, the string's
0 among them: `lea rcx, [rax - 1]`, `xor rcx, rax`, `and rsi, rcx` keep the matches before it; none: `+544`; else
`bsr rsi, rsi`, `lea rax, [rdi + rsi]`, `ret`. -/
theorem tail228 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 228) (hkp : KpR g₀ X.cpu.gpr)
    (hdi : X.cpu.gpr.rdi = g₀.rdi) (h16 : 16 ≤ n) (hn : n < 64)
    (hsi : R 0 64 (Fb V g₀.rdi (g₀.rsi.setWidth 8)) X.cpu.gpr.rsi) (hax : R 16 64 (Fb V g₀.rdi 0) X.cpu.gpr.rax)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  -- the zero mask: its lowest set bit `n`
  have h1 : X.cpu.gpr.rax.getLsbD n = true := by
    rw [hax, decide_eq_true h16, decide_eq_true hn, Fb, hz]
    rfl
  have h0 : ∀ i < n, X.cpu.gpr.rax.getLsbD i = false := fun i hi => by
    rw [hax, Fb, decide_eq_false (hnz i hi), Bool.and_false]
  have hZ0 : X.cpu.gpr.rax.toNat ≠ 0 := fun h => by
    rw [← BitVec.testBit_toNat, h, Nat.zero_testBit] at h1
    exact Bool.false_ne_true h1
  have hY := toNat_pred64 X.cpu.gpr.rax hZ0
  -- `lea rcx, [rax - 1]`, `xor rcx, rax`, `and rsi, rcx`
  refine c.s_blkV hin (b228 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [wr, gv, Src.val, eaG, optV, set_rcx, set_rsi, get0, get1, get6, BitVec.setWidth_eq, z_mul64,
    add_z64] at hg₁ hP
  have hsi₁ : Y₁.cpu.gpr.rsi =
      X.cpu.gpr.rsi &&& ((X.cpu.gpr.rax + BitVec.ofNat 64 18446744073709551615) ^^^ X.cpu.gpr.rax) := by
    simp only [hg₁] <;> rfl
  have hkp₁ : KpR g₀ Y₁.cpu.gpr := by simp only [KpR, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := by simp only [hg₁]; exact hdi
  have hKb : ∀ i, Y₁.cpu.gpr.rsi.getLsbD i =
      (decide (i < n) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8)) := by
    intro i
    rw [hsi₁, BitVec.getLsbD_and, getLsbD_blsmsk h1 h0 hY i, hsi, Fb]
    by_cases hi : i < n
    · rw [decide_eq_true hi, decide_eq_true (show i ≤ n by omega), decide_eq_true (show i < 64 by omega),
        decide_eq_true (Nat.zero_le i)]
      simp only [Bool.true_and, Bool.and_true]
    · rw [decide_eq_false hi]
      by_cases hin' : i = n
      · rw [hin', hz, decide_eq_false (fun h : (0 : Byte) = g₀.rsi.setWidth 8 => hch h.symm)]
        simp only [Bool.and_false, Bool.false_and]
      · rw [decide_eq_false (show ¬ i ≤ n by omega)]
        simp only [Bool.and_false, Bool.false_and]
  have hS := rok_mask (by omega) hKb
  have hc : fl.cond 4 = (Y₁.cpu.gpr.rsi == 0) := by rw [cond4_mask hP]; simp only [hg₁]
  refine c.s_jccV hK₁ hA₁ hin (by rw [sr2_length]; omega) hr₁ (d238 prof.feat) (tgt := 544) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- none before the 0
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc] at htk
    exact ret544 c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hkp₁) (hS.1.1 (eq_of_beq htk)) hR
  · -- the last: `bsr rsi, rsi`, `lea rax, [rdi + rsi]`, `ret`
    intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc] at hfa
    have hne : Y₁.cpu.gpr.rsi ≠ 0 := ne_of_beq_false hfa
    refine c.s_bsr64 hK₂ hA₂ hin (by rw [sr2_length]; omega) hr₂ (d244 prof.feat)
      (by simp only [rv, get6, BitVec.setWidth_eq, hg₂]; exact hne) ?_
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    simp only [rv, get6, BitVec.setWidth_eq, set_rsi, hg₂] at hg₃
    refine c.s_blkV hin (b248 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ _
    simp only [wr, eaG, optV, set_rax, get6, get7, BitVec.setWidth_eq, BitVec.mul_one, BitVec.add_zero] at hg₄
    simp only [hg₃] at hg₄
    have hkp₄ : KpR g₀ Y₄.cpu.gpr := by simp only [KpR, hg₄]; exact hkp₁
    have hax₄ : Y₄.cpu.gpr.rax = Addr.add g₀.rdi (highestSetBit Y₁.cpu.gpr.rsi) := by
      simp only [hg₄]
      rw [hdi₁]
      rfl
    exact ret_atR c hin (by rw [sr2_length]; omega) (d252 prof.feat) hK₄ hA₄ hr₄ hkp₄ (by rw [hax₄]; exact hS.2 hne)
      hR

/-- From `+112`: no 0 among the first 16 bytes from `p` (`16 ≤ n`), `rcx` their matches, the 64 bytes from `p` on
its page. -/
theorem path112 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 112) (hkp : KpR g₀ X.cpu.gpr)
    (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hcx : ∀ i, X.cpu.gpr.rcx.getLsbD i = (decide (i < 16) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8)))
    (hx1 : xsOf X.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi) (hx2 : xsOf X.cpu.vec.zmm (xmmOf 2) = 0) (h16 : 16 ≤ n)
    (hq : g₀.rdi.toNat % 4096 ≤ 4032)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (h256 : ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 256 → KpR g₀ Y.cpu.gpr →
      Y.cpu.gpr.rdi = g₀.rdi → R 0 64 (Fb V g₀.rdi (g₀.rsi.setWidth 8)) Y.cpu.gpr.rsi →
      xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → 64 ≤ n → GoG prof L o gev gP gE Y t')
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  have hp := g₀.rdi.isLt
  have hcxR : R 0 16 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) X.cpu.gpr.rcx := R_low fun i => by rw [hcx, hdi]
  -- `movdqu xmm4, [rdi + 16]`, `movdqa xmm5, xmm4`, `movdqu xmm3, [rdi + 32]`, `pcmpeqb xmm4, xmm1`,
  -- `pcmpeqb xmm5, xmm2`, `movdqu xmm0, [rdi + 48]`
  refine c.s_blkV hin (b112 prof) hK hA hrip ?_
  refine wpV_v (foot_pg hft (B := X.cpu.gpr.rdi) (d := 16) (by rw [hdi]; omega) (by rw [hdi]; omega)
    (by rw [hdi]; omega)) (fun h => nomatch h) (wpV_v0 (wpV_v (foot_pg hft (B := X.cpu.gpr.rdi) (d := 32)
    (by rw [hdi]; omega) (by rw [hdi]; omega) (by rw [hdi]; omega)) (fun h => nomatch h) (wpV_v0 (wpV_v0
    (wpV_v (foot_pg hft (B := X.cpu.gpr.rdi) (d := 48) (by rw [hdi]; omega) (by rw [hdi]; omega)
    (by rw [hdi]; omega)) (fun h => nomatch h) (wpV_nil ?_))))))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  generalize hxd : xsOf X.cpu.vec.zmm = x at hv₁ hx1 hx2
  simp (disch := decide) only [eaB, get7, xset_same, xset_ne, hx1, hx2] at hv₁
  have hg₁' : Y₁.cpu.gpr = X.cpu.gpr := by simp only [hg₁]
  have hkp₁ : KpR g₀ Y₁.cpu.gpr := by rw [hg₁']; exact hkp
  -- `pmovmskb edx, xmm5`, `movdqa xmm5, xmm3`, `pcmpeqb xmm3, xmm1`, `pcmpeqb xmm5, xmm2`, `pcmpeqb xmm2, xmm0`,
  -- `shl rdx, 16`
  refine c.s_blkV hin (b139 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_)))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ hv₂
  simp only [wr, gv, Src.val, set_rdx, get2, BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod] at hg₂
  have hkp₂ : KpR g₀ Y₂.cpu.gpr := by simp only [KpR, hg₂]; exact hkp₁
  have hx5₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 5) = peqb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 16)) 0 := by
    rw [hv₁]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hdx₂ : R 16 32 (Fb V X.cpu.gpr.rdi 0) Y₂.cpu.gpr.rdx := by
    simp only [hg₂]; rw [hx5₁]; exact R_m (fun i => zbit' V X.cpu.gpr.rdi 16 i) (by omega)
  -- `pmovmskb r8d, xmm3`, `pmovmskb eax, xmm5`, `pmovmskb esi, xmm2`, `shl r8, 32`, `shl rax, 32`,
  -- `pcmpeqb xmm0, xmm1`
  refine c.s_blkV hin (b163 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_v0 (wpV_nil ?_))))
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ hv₃
  simp only [wr, gv, Src.val, set_rax, set_rsi, set_r8, get0, get8, BitVec.setWidth_eq, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod] at hg₃
  have hkp₃ : KpR g₀ Y₃.cpu.gpr := by simp only [KpR, hg₃]; exact hkp₂
  have hx3₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 3) = peqb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 32)) (Bc g₀.rsi) := by
    rw [hv₂, hv₁]; simp (disch := decide) only [xset_same, xset_ne, hx1, hx2] <;> rfl
  have hx5₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 5) = peqb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 32)) 0 := by
    rw [hv₂, hv₁]; simp (disch := decide) only [xset_same, xset_ne, hx1, hx2] <;> rfl
  have hx2₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 2) = peqb 0 (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48)) := by
    rw [hv₂, hv₁]; simp (disch := decide) only [xset_same, xset_ne, hx1, hx2] <;> rfl
  have hr8₃ : R 32 48 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₃.cpu.gpr.r8 := by
    simp only [hg₃]; rw [hx3₂]; exact R_m (fun i => cbit' V X.cpu.gpr.rdi 32 i g₀.rsi) (by omega)
  have hax₃ : R 32 48 (Fb V X.cpu.gpr.rdi 0) Y₃.cpu.gpr.rax := by
    simp only [hg₃]; rw [hx5₂]; exact R_m (fun i => zbit' V X.cpu.gpr.rdi 32 i) (by omega)
  have hsi₃ : ∀ i, Y₃.cpu.gpr.rsi.getLsbD i = (decide (i < 16) && Fb V X.cpu.gpr.rdi 0 (i + 48)) := by
    simp only [hg₃]; rw [hx2₂]; exact bits64 (fun i => zbit V X.cpu.gpr.rdi 48 i)
  have hdx₃ : R 16 32 (Fb V X.cpu.gpr.rdi 0) Y₃.cpu.gpr.rdx := by simp only [hg₃]; exact hdx₂
  -- `or rax, rdx`, `mov rdx, rsi`, `pmovmskb esi, xmm4`, `shl rdx, 48`, `shl rsi, 16`, `or rsi, r8`
  refine c.s_blkV hin (b188 prof) hK₃ hA₃ hr₃ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
    wpV_nil ?_)
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ hv₄
  simp only [wr, gv, Src.val, set_rax, set_rdx, set_rsi, get0, get2, get6, get8, BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hg₄
  have hkp₄ : KpR g₀ Y₄.cpu.gpr := by simp only [KpR, hg₄]; exact hkp₃
  have hx4₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 4) = peqb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 16)) (Bc g₀.rsi) := by
    rw [hv₃, hv₂, hv₁]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hax₄ : R 16 48 (Fb V X.cpu.gpr.rdi 0) Y₄.cpu.gpr.rax := by
    simp only [hg₄]; exact R_or' hax₃ hdx₃ (by omega) (by omega)
  have hdx₄ : R 48 64 (Fb V X.cpu.gpr.rdi 0) Y₄.cpu.gpr.rdx := by
    simp only [hg₄]; exact R_shl hsi₃ (by omega)
  have hsi₄ : R 16 48 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₄.cpu.gpr.rsi := by
    simp only [hg₄]; rw [hx4₃]
    exact R_or (R_m (fun i => cbit' V X.cpu.gpr.rdi 16 i g₀.rsi) (by omega)) hr8₃ (by omega) (by omega)
  have hcx₄ : R 0 16 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₄.cpu.gpr.rcx := by
    simp only [hg₄, hg₃, hg₂, hg₁']; exact hcxR
  -- `or rsi, rcx`, `pmovmskb ecx, xmm0`, `shl rcx, 48`, `or rsi, rcx`, `or rax, rdx`
  refine c.s_blkV hin (b209 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_)
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hf₅ hv₅
  simp only [wr, gv, Src.val, set_rax, set_rcx, set_rsi, get0, get1, get2, get6, BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hg₅ hP
  have hkp₅ : KpR g₀ Y₅.cpu.gpr := by simp only [KpR, hg₅]; exact hkp₄
  have hdi₅ : Y₅.cpu.gpr.rdi = g₀.rdi := by simp only [hg₅, hg₄, hg₃, hg₂, hg₁']; exact hdi
  have hx0₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 0) = peqb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48)) (Bc g₀.rsi) := by
    rw [hv₄, hv₃, hv₂, hv₁]; simp (disch := decide) only [xset_same, xset_ne, hx1, hx2] <;> rfl
  have hx1₅ : xsOf Y₅.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by
    rw [hv₅, hv₄, hv₃, hv₂, hv₁]; simp (disch := decide) only [xset_ne, hx1]
  have hsi₅ : R 0 64 (Fb V g₀.rdi (g₀.rsi.setWidth 8)) Y₅.cpu.gpr.rsi := by
    rw [← hdi]; simp only [hg₅]; rw [hx0₄]
    exact R_or (R_or' hsi₄ hcx₄ (by omega) (by omega)) (R_m (fun i => cbit' V X.cpu.gpr.rdi 48 i g₀.rsi)
      (by omega)) (by omega) (by omega)
  have hax₅ : R 16 64 (Fb V g₀.rdi 0) Y₅.cpu.gpr.rax := by
    rw [← hdi]; simp only [hg₅]; exact R_or hax₄ hdx₄ (by omega) (by omega)
  have hc : fl.cond 4 = (Y₅.cpu.gpr.rax == 0) := by rw [cond4_mask hP]; simp only [hg₅]
  refine c.s_jccV hK₅ hA₅ hin (by rw [sr2_length]; omega) hr₅ (d226 prof.feat) (tgt := 256) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- no 0 among the 64 bytes
    intro htk Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆⟩
    rw [hf₅, hc] at htk
    have h0 := eq_of_beq htk
    have h64 : 64 ≤ n := Classical.byContradiction fun h => by
      have hb := hax₅ n
      rw [h0, getLsbD_zero', decide_eq_true h16, decide_eq_true (show n < 64 by omega), Fb, hz] at hb
      exact absurd hb (by decide)
    exact h256 Y₆ t₆ hK₆ hA₆ hr₆ (by rw [hg₆]; exact hkp₅) (by rw [hg₆]; exact hdi₅) (by rw [hg₆]; exact hsi₅)
      (by rw [hv₆]; exact hx1₅) h64
  · -- a 0: `tail228`
    intro hfa Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, _⟩
    rw [hf₅, hc] at hfa
    have hne := ne_of_beq_false hfa
    have hn64 : n < 64 := Classical.byContradiction fun h => hne (by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [hax₅, getLsbD_zero', Fb, decide_eq_false (hnz i (by omega)), Bool.and_false])
    exact tail228 c hin hK₆ hA₆ hr₆ (by rw [hg₆]; exact hkp₅) (by rw [hg₆]; exact hdi₅) h16 hn64
      (by rw [hg₆]; exact hsi₅) (by rw [hg₆]; exact hax₅) hnz hz hch hR

end FV7z.Strrchr
