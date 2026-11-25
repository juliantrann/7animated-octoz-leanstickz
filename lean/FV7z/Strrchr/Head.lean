import FV7z.Strrchr.Mask
import FV7z.Strrchr.Code
import FV7z.Strrchr.Steps
import FV7z.Strlen.Entry
import FV7z.Startup.StrAt
import FV7z.Lemmas.Wp
/-!
# `__strrchr_sse2`, the call and its returns (PLAN.md G2)

`RchrAt`'s continuation, from the registers `g₀` at the call (`RetR`): `rax` null if none of the `n` bytes from `p` is
the character `ch` (`sil`), else the address of the last (`ROk`); a mask whose bits say which bytes are `ch` gives it
by `bsr` (`rok_mask`). The returns: from `+544` (`xor eax, eax`), and from `+74`, where `rcx` and `rdx` hold the
character and zero masks of the 16 bytes from `p` and one of them is 0.
-/
namespace FV7z.Strrchr
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

attribute [-simp] BitVec.getLsbD_eq_getElem

/-- The character spread over 16 bytes, as `movd`, `punpcklbw`, `punpcklwd`, `pshufd 0` leave it. -/
abbrev Bc (c : BitVec 64) : BitVec 128 :=
  ofDwords fun j => lane 32 (ofWords (interleave 16 0
    (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128)))
    (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128))))) (0 / 4 ^ j % 4)

/-! ## What `rax` is to be -/

/-- `rax` as `RchrAt` asks: null if none of the `n` bytes from `p` is `ch`, else the address of the last. -/
def ROk (V : Addr → Byte) (p : Addr) (n : Nat) (ch : Byte) (a : Addr) : Prop :=
  ((∀ k < n, V (Addr.add p k) ≠ ch) → a = 0) ∧
    ∀ m < n, V (Addr.add p m) = ch → (∀ k, m < k → k < n → V (Addr.add p k) ≠ ch) → a = Addr.add p m

theorem rok_none {V : Addr → Byte} {p : Addr} {n : Nat} {ch : Byte} (h : ∀ k < n, V (Addr.add p k) ≠ ch) :
    ROk V p n ch 0 :=
  ⟨fun _ => rfl, fun m hm hc _ => absurd hc (h m hm)⟩

theorem rok_last {V : Addr → Byte} {p : Addr} {n m : Nat} {ch : Byte} (hm : m < n) (hc : V (Addr.add p m) = ch)
    (hl : ∀ k, m < k → k < n → V (Addr.add p k) ≠ ch) : ROk V p n ch (Addr.add p m) := by
  refine ⟨fun h => absurd hc (h m hm), fun m' hm' hc' hl' => ?_⟩
  rcases Nat.lt_trichotomy m m' with h | h | h
  · exact absurd hc' (hl m' h hm')
  · rw [h]
  · exact absurd hc (hl' m h hm)

/-- A mask whose bit `i` says whether byte `i < n` from `p` is `ch`: 0 iff none is, else `bsr` gives the last. -/
theorem rok_mask {V : Addr → Byte} {p : Addr} {n : Nat} {ch : Byte} {K : BitVec 64} (hn : n ≤ 64)
    (hK : ∀ i, K.getLsbD i = (decide (i < n) && decide (V (Addr.add p i) = ch))) :
    (K = 0 ↔ ∀ k < n, V (Addr.add p k) ≠ ch) ∧ (K ≠ 0 → ROk V p n ch (Addr.add p (highestSetBit K))) := by
  have hnone : (∀ k < n, V (Addr.add p k) ≠ ch) → K = 0 := fun h => by
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    rw [hK, getLsbD_zero']
    by_cases hi : i < n
    · rw [decide_eq_true hi, Bool.true_and]; exact decide_eq_false (h i hi)
    · rw [decide_eq_false hi, Bool.false_and]
  rcases Str.last_with (fun k => V (Addr.add p k) = ch) n with h | ⟨m, hm, hc, hl⟩
  · exact ⟨⟨fun _ => h, hnone⟩, fun hne => absurd (hnone h) hne⟩
  · have hb : K.getLsbD m = true := by
      rw [hK, decide_eq_true hm, decide_eq_true hc]
      rfl
    have hK0 : K ≠ 0 := fun h0 => by
      rw [h0, getLsbD_zero'] at hb
      exact Bool.false_ne_true hb
    refine ⟨⟨fun h0 => absurd h0 hK0, fun h' => absurd hc (h' m hm)⟩, fun _ => ?_⟩
    have hh : highestSetBit K = m := by
      apply highestSetBit_eq (by omega) hb
      intro i h1 _
      rw [hK]
      by_cases hi : i < n
      · rw [decide_eq_true hi, Bool.true_and]; exact decide_eq_false (hl i h1 hi)
      · rw [decide_eq_false hi, Bool.false_and]
    rw [hh]
    exact rok_last hm hc hl

theorem addR_ofNat (a : Addr) (m : Nat) : addR (BitVec.ofNat 64 m) a = Addr.add a m := by
  have h0 : (BitVec.ofBool false).setWidth 64 = (0 : BitVec 64) := by decide
  simp only [addR, h0, BitVec.add_zero, Addr.add]
  exact BitVec.add_comm _ _

/-! ## The call -/

/-- The registers a call keeps, as at the call. -/
def KpR (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

/-- What the call returns to, from registers `g₀` at the call: `RchrAt`'s continuation, its return address in code. -/
def RetR (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (g₀ : Gprs) (n : Nat) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add g₀.rsp i)) ∧ ∃ (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat), CodeIn L e₂ code₂ ∧
    j₂ < code₂.length ∧ ofBytesLE 64 ((byteAddrs g₀.rsp 8).map V) = e₂.add j₂ ∧
    ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = g₀.rsp + 8 →
      ROk V g₀.rdi n (g₀.rsi.setWidth 8) Z.cpu.gpr.rax → Z.cpu.gpr.rbx = g₀.rbx → Z.cpu.gpr.rbp = g₀.rbp →
      Z.cpu.gpr.r12 = g₀.r12 → Z.cpu.gpr.r13 = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 → Z.cpu.gpr.r15 = g₀.r15 →
      GoG prof L o gev gP gE Z t'

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- A `ret` with `rax` as `ROk` says. -/
theorem ret_atR (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {j : Nat} (hj : j < sr2.length)
    (hd : Dec prof.feat sr2 j (FV7z.mk .ret 64 [] 1)) {Y : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e'.add j) (hkp : KpR g₀ Y.cpu.gpr)
    (hax : ROk V g₀.rdi n (g₀.rsi.setWidth 8) Y.cpu.gpr.rax) (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hl, e₂, code₂, j₂, hin₂, h₂, hra, K⟩ := hR
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := hkp
  refine c.s_ret hK hA hin hj hrip hd (by rw [hsp]; exact hl) hin₂ h₂ (by rw [hsp]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine K Z t' hKZ hAZ hrZ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rw [hgZ]
  · exact congrArg (· + (8 : BitVec 64)) hsp
  · exact hax
  · exact hbx
  · exact hbp
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- From `+544`, none of the bytes `ch`: `xor eax, eax`, `ret`. -/
theorem ret544 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 544) (hkp : KpR g₀ X.cpu.gpr)
    (hno : ∀ k < n, V (Addr.add g₀.rdi k) ≠ g₀.rsi.setWidth 8) (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) :
    GoG prof L o gev gP gE X t := by
  refine c.s_blkV hin (b544 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, gv, Src.val, set_rax, get0, BitVec.xor_self, BitVec.setWidth_zero] at hg₁
  have hkp₁ : KpR g₀ Y₁.cpu.gpr := by simp only [KpR, hg₁]; exact hkp
  have hax : Y₁.cpu.gpr.rax = 0 := by simp only [hg₁] <;> rfl
  exact ret_atR c hin (by rw [sr2_length]; omega) (d546 prof.feat) hK₁ hA₁ hr₁ hkp₁ (by rw [hax]; exact rok_none hno)
    hR

/-- From `+74`: `rcx`'s and `rdx`'s bits say which of the 16 bytes from `p` are `ch` and 0, the string's 0 among them:
`lea rax, [rdx - 1]`, `xor rax, rdx`, `and rax, rcx` keep the matches before it; none: to `+544`; else `bsr`, `add rax,
rdi`, `ret`. -/
theorem tail74 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 74) (hkp : KpR g₀ X.cpu.gpr)
    (hdi : X.cpu.gpr.rdi = g₀.rdi) (hn : n < 16)
    (hcx : ∀ i, X.cpu.gpr.rcx.getLsbD i =
      (decide (i < 16) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8)))
    (hdx : ∀ i, X.cpu.gpr.rdx.getLsbD i = (decide (i < 16) && decide (V (Addr.add g₀.rdi i) = 0)))
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  -- the zero mask: its lowest set bit `n`, so `rdx - 1` is `rdx` less one
  have h1 : X.cpu.gpr.rdx.getLsbD n = true := by
    rw [hdx, decide_eq_true hn, hz]
    rfl
  have h0 : ∀ i < n, X.cpu.gpr.rdx.getLsbD i = false := fun i hi => by
    rw [hdx, decide_eq_true (show i < 16 by omega), Bool.true_and]
    exact decide_eq_false (hnz i hi)
  have hZ0 : X.cpu.gpr.rdx.toNat ≠ 0 := fun h => by
    rw [← BitVec.testBit_toNat, h, Nat.zero_testBit] at h1
    exact Bool.false_ne_true h1
  have hY : (X.cpu.gpr.rdx + BitVec.ofNat 64 18446744073709551615).toNat + 1 = X.cpu.gpr.rdx.toNat := by
    have := X.cpu.gpr.rdx.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  -- `lea rax, [rdx - 1]`, `xor rax, rdx`, `and rax, rcx`
  refine c.s_blkV hin (b74 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [wr, gv, Src.val, eaG, optV, set_rax, get0, get1, get2, BitVec.setWidth_eq, z_mul64, add_z64] at hg₁
    hP
  have hax : Y₁.cpu.gpr.rax =
      ((X.cpu.gpr.rdx + BitVec.ofNat 64 18446744073709551615) ^^^ X.cpu.gpr.rdx) &&& X.cpu.gpr.rcx := by
    simp only [hg₁] <;> rfl
  have hkp₁ : KpR g₀ Y₁.cpu.gpr := by simp only [KpR, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := by simp only [hg₁]; exact hdi
  have hKb : ∀ i, Y₁.cpu.gpr.rax.getLsbD i =
      (decide (i < n) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8)) := by
    intro i
    rw [hax, BitVec.getLsbD_and, getLsbD_blsmsk h1 h0 hY i, hcx]
    by_cases hi : i < n
    · rw [decide_eq_true hi, decide_eq_true (show i ≤ n by omega), decide_eq_true (show i < 16 by omega),
        Bool.true_and, Bool.true_and]
    · rw [decide_eq_false hi]
      by_cases hin' : i = n
      · rw [hin', hz, decide_eq_false (fun h : (0 : Byte) = g₀.rsi.setWidth 8 => hch h.symm), Bool.and_false,
          Bool.and_false]
      · rw [decide_eq_false (show ¬ i ≤ n by omega), Bool.false_and, Bool.false_and]
  have hS := rok_mask (by omega) hKb
  have hc : fl.cond 4 = (Y₁.cpu.gpr.rax == 0) := by rw [cond4_mask hP]; simp only [hg₁]
  refine c.s_jccV hK₁ hA₁ hin (by rw [sr2_length]; omega) hr₁ (d84 prof.feat) (tgt := 544) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- none before the 0
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc] at htk
    exact ret544 c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hkp₁) (hS.1.1 (eq_of_beq htk)) hR
  · -- the last: `bsr rax, rax`, `add rax, rdi`, `ret`
    intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc] at hfa
    have hne : Y₁.cpu.gpr.rax ≠ 0 := ne_of_beq_false hfa
    refine c.s_bsr64 hK₂ hA₂ hin (by rw [sr2_length]; omega) hr₂ (d90 prof.feat)
      (by simp only [rv, get0, BitVec.setWidth_eq, hg₂]; exact hne) ?_
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    simp only [rv, get0, BitVec.setWidth_eq, set_rax, hg₂] at hg₃
    refine c.s_blkV hin (b94 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ _
    simp only [wr, gv, Src.val, set_rax, get0, get7, BitVec.setWidth_eq] at hg₄
    simp only [hg₃] at hg₄
    have hkp₄ : KpR g₀ Y₄.cpu.gpr := by simp only [KpR, hg₄]; exact hkp₁
    have hax₄ : Y₄.cpu.gpr.rax = Addr.add g₀.rdi (highestSetBit Y₁.cpu.gpr.rax) := by
      simp only [hg₄]
      rw [hdi₁]
      exact addR_ofNat _ _
    exact ret_atR c hin (by rw [sr2_length]; omega) (d97 prof.feat) hK₄ hA₄ hr₄ hkp₄ (by rw [hax₄]; exact hS.2 hne)
      hR

end FV7z.Strrchr
