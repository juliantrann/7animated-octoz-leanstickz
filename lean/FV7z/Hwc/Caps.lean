import FV7z.Hwc.Lens
/-!
# `_dl_important_hwcaps`: the loop over the capabilities, 1448 → 1522 (PLAN.md G3, startup)

At 1448 with `rcx = n + 1` (the capability `n`, its mask `2^n`) and `rbx = R + 16 (n + 1)` (`&temp[n + 1]`, `temp`
at `R`): `vc_1448` (`rax = E`, `rdx = P`, `rsi = 2^n`), then the entries (`at1465` at 0, `lens78_08`): entry `j`
gets `temp[n].len + 1` if bit `n` of `E - 1 - j` is set (`addc`), `rbx - 16`; on to 1448 for `n` or, `n = 0`, to
1522. `one_cap`: one capability; `caps_loop`: all of them, by induction (`caps`: the lengths after them).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

theorem s16 (P : Addr) (j : Nat) : P + BitVec.ofNat 64 (16 * (j + 1)) - 16#64 = P + BitVec.ofNat 64 (16 * j) := by
  rw [← a16]
  exact BitVec.add_sub_cancel _ _

/-- `temp[j].len` (at `R + 16 j + 8`). -/
def tlen (V : Addr → Byte) (R : Addr) (j : Nat) : Addr := rdq(V, R + BitVec.ofNat 64 (16 * j + 8))

/-- The lengths after the capabilities `n - 1`, …, 0 (`Tl j = temp[j].len`). -/
def caps (E : Nat) (Tl : Nat → Addr) : Nat → (Nat → Addr) → (Nat → Addr)
  | 0, ℓ => ℓ
  | n + 1, ℓ => caps E Tl n (addc ℓ (BitVec.ofNat 64 (2 ^ n)) (Tl n) E)

theorem caps_zero (E : Nat) (Tl : Nat → Addr) (ℓ : Nat → Addr) : caps E Tl 0 ℓ = ℓ := rfl

theorem caps_succ (E : Nat) (Tl : Nat → Addr) (n : Nat) (ℓ : Nat → Addr) :
    caps E Tl (n + 1) ℓ = caps E Tl n (addc ℓ (BitVec.ofNat 64 (2 ^ n)) (Tl n) E) := rfl

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {g₂ : Gprs} {E C : Nat} {R : Addr} {σ : Nat → Addr} {V₀ : Addr → Byte}

/-- The capability `n` (`rcx = n + 1` at 1448): the lengths `addc`, to 1522 (`n = 0`) or 1448. -/
theorem one_cap (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hE0 : 0 < E) (hE : E < 2 ^ 32) (hC : C ≤ 4) (hr10 : g₂.r10 = BitVec.ofNat 64 E) (hrdi : g₂.rdi = 1#64)
    (hPR : g₂.r14.toNat + 16 * E ≤ R.toNat) (hRC : R.toNat + 16 * C ≤ 2 ^ 64)
    (hW : ∀ a : Addr, g₂.r14.toNat ≤ a.toNat → a.toNat < g₂.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a)
    (hFT : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * C → Foot F.data a)
    {n : Nat} (hn : n + 1 ≤ C) {ℓ : Nat → Addr}
    (k : ∀ Y t' (V' : Addr → Byte) (a8 a9 : Addr), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = hwc_at.add (if n = 0 then 1522 else 1448) →
      Y.cpu.gpr = { g₂ with
        rax := 0#64, rcx := BitVec.ofNat 64 n, rdx := g₂.r14 + BitVec.ofNat 64 (16 * E),
        rbx := R + BitVec.ofNat 64 (16 * n), rsi := BitVec.ofNat 64 (2 ^ n), r8 := a8, r9 := a9 } →
      Tab V' g₂.r14 E σ (addc ℓ (BitVec.ofNat 64 (2 ^ n)) (tlen V₀ R n) E) →
      Same V₀ V' (g₂.r14.toNat + 16 * E) (2 ^ 64) → Same V₀ V' 0 g₂.r14.toNat → GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t : Nat) (V : Addr → Byte) (a d si a8 a9 : Addr), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1448 →
      X.cpu.gpr = { g₂ with
        rax := a, rcx := BitVec.ofNat 64 (n + 1), rdx := d, rbx := R + BitVec.ofNat 64 (16 * (n + 1)),
        rsi := si, r8 := a8, r9 := a9 } →
      Tab V g₂.r14 E σ ℓ → Same V₀ V (g₂.r14.toNat + 16 * E) (2 ^ 64) → Same V₀ V 0 g₂.r14.toNat →
      GoG prof L o gev gP gE X t := by
  intro X t V a d si a8 a9 hK hA hrip hgx hT hS1 hS0
  have hRl := R.isLt
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : Gprs, g₁ = { g₂ with
      rcx := BitVec.ofNat 64 n, rbx := R + BitVec.ofNat 64 (16 * (n + 1)),
      rsi := BitVec.ofNat 64 (2 ^ n) } := ⟨_, rfl⟩
  have hg14 : g₁.r14 = g₂.r14 := by rw [hg₁]
  have hsi : g₁.rsi = BitVec.ofNat 64 (2 ^ n) := by rw [hg₁]
  have hb8 : g₁.rbx + 18446744073709551608#64 = R + BitVec.ofNat 64 (16 * n + 8) := by
    rw [hg₁]
    exact a8m R n
  have ea : (R + BitVec.ofNat 64 (16 * n + 8)).toNat = R.toNat + (16 * n + 8) := toNat_off (by omega)
  have hPE : g₁.r14.toNat + 16 * E ≤ 2 ^ 64 := by rw [hg14]; omega
  have hB : g₁.r14.toNat + 16 * E ≤ (g₁.rbx + 18446744073709551608#64).toNat := by
    rw [hg14, hb8, ea]
    omega
  have hB' : (g₁.rbx + 18446744073709551608#64).toNat + 8 ≤ 2 ^ 64 := by
    rw [hb8, ea]
    omega
  have hT0 : rdq(V₀, g₁.rbx + 18446744073709551608#64) = tlen V₀ R n := by
    rw [hb8, tlen]
  have hW' : ∀ a : Addr, g₁.r14.toNat ≤ a.toNat → a.toNat < g₁.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a := by
    rw [hg14]
    exact hW
  have hfT : ∀ k < 8, Foot F.data (Addr.add (g₁.rbx + 18446744073709551608#64) k) := by
    intro i hi
    rw [hb8]
    have e := toNat_add_of_fits (a := R + BitVec.ofNat 64 (16 * n + 8)) hi (by rw [ea]; omega)
    exact hFT _ (by rw [e, ea]; omega) (by rw [e, ea]; omega)
  have hrc : (if g₁.rcx = 0#64 then 1522 else 1448) = (if n = 0 then 1522 else 1448) := by
    have hrcx : g₁.rcx = BitVec.ofNat 64 n := by rw [hg₁]
    rw [hrcx]
    by_cases h0 : n = 0
    · subst h0
      simp
    · have h1 : BitVec.ofNat 64 n ≠ 0#64 := by
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
        omega
      rw [ite_eq_right h1, ite_eq_right h0]
  have hb16 : g₁.rbx - 16#64 = R + BitVec.ofNat 64 (16 * n) := by
    rw [hg₁]
    exact s16 R n
  obtain ⟨h78, h08⟩ := lens78_08 (g₁ := g₁) (σ := σ) (ℓ₀ := ℓ) (V₀ := V₀) (T := tlen V₀ R n) c hfs hin hsi hE hPE
    hB hB' hT0 hW' hfT (fun Y t' V' a8 a9 hKY hAY hrY hgY hT' hS1' hS0' => by
      rw [hrc] at hrY
      rw [hb16] at hgY
      rw [hg14] at hT' hS1' hS0'
      rw [hg₁] at hgY
      exact k Y t' V' a8 a9 hKY hAY hrY (hgY.trans rfl) hT' hS1' hS0') (E - 1) 0 (by omega)
  refine (c_1448 prof fb).run c hfs hin _ hK hA hrip
    (vc_1448 (c := n + 1) (by omega) (by rw [hgx]) (by rw [hgx]; exact hrdi)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  rw [← hg14] at hT hS1 hS0
  refine at1465 c hfs hin hsi hE (j := 0) hE0 h78 h08 Y t' _ ℓ a8 a9 hKY hAY hrY ?_ hT
    ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩ hS1 hS0
  rw [hgY, hgx, hg₁]
  simp only [Nat.add_sub_cancel, Nat.sub_zero, Nat.mul_zero, BitVec.add_zero, hr10]

/-- All the capabilities: from 1448 with `rcx = n + 1` to 1522 with the lengths `caps … (n + 1) ℓ`. -/
theorem caps_loop (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hE0 : 0 < E) (hE : E < 2 ^ 32) (hC : C ≤ 4) (hr10 : g₂.r10 = BitVec.ofNat 64 E) (hrdi : g₂.rdi = 1#64)
    (hPR : g₂.r14.toNat + 16 * E ≤ R.toNat) (hRC : R.toNat + 16 * C ≤ 2 ^ 64)
    (hW : ∀ a : Addr, g₂.r14.toNat ≤ a.toNat → a.toNat < g₂.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a)
    (hFT : ∀ a : Addr, R.toNat ≤ a.toNat → a.toNat < R.toNat + 16 * C → Foot F.data a) {ℓF : Nat → Addr}
    (k : ∀ Y t' (V' : Addr → Byte) (a8 a9 : Addr), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = hwc_at.add 1522 →
      Y.cpu.gpr = { g₂ with
        rax := 0#64, rcx := 0#64, rdx := g₂.r14 + BitVec.ofNat 64 (16 * E), rbx := R, rsi := 1#64,
        r8 := a8, r9 := a9 } →
      Tab V' g₂.r14 E σ ℓF → Same V₀ V' (g₂.r14.toNat + 16 * E) (2 ^ 64) → Same V₀ V' 0 g₂.r14.toNat →
      GoG prof L o gev gP gE Y t') :
    ∀ n, n + 1 ≤ C → ∀ ℓ : Nat → Addr, caps E (tlen V₀ R) (n + 1) ℓ = ℓF →
      ∀ (X : State) (t : Nat) (V : Addr → Byte) (a d si a8 a9 : Addr), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1448 →
      X.cpu.gpr = { g₂ with
        rax := a, rcx := BitVec.ofNat 64 (n + 1), rdx := d, rbx := R + BitVec.ofNat 64 (16 * (n + 1)),
        rsi := si, r8 := a8, r9 := a9 } →
      Tab V g₂.r14 E σ ℓ → Same V₀ V (g₂.r14.toNat + 16 * E) (2 ^ 64) → Same V₀ V 0 g₂.r14.toNat →
      GoG prof L o gev gP gE X t := by
  intro n
  induction n with
  | zero =>
    intro hn ℓ hF
    refine one_cap c hfs hin hE0 hE hC hr10 hrdi hPR hRC hW hFT hn ?_
    intro Y t' V' a8 a9 hKY hAY hrY hgY hT hS1 hS0
    rw [ite_eq_left rfl] at hrY
    rw [Nat.mul_zero, BitVec.add_zero, Nat.pow_zero] at hgY
    exact k Y t' V' a8 a9 hKY hAY hrY hgY (by rw [← hF, caps_succ, caps_zero]; exact hT) hS1 hS0
  | succ n ih =>
    intro hn ℓ hF
    refine one_cap c hfs hin hE0 hE hC hr10 hrdi hPR hRC hW hFT hn ?_
    intro Y t' V' a8 a9 hKY hAY hrY hgY hT hS1 hS0
    rw [ite_eq_right (show n + 1 ≠ 0 by omega)] at hrY
    exact ih (by omega) _ (by rw [← hF, caps_succ (n := n + 1)]) Y t' V' _ _ _ a8 a9 hKY hAY hrY hgY hT hS1 hS0

end FV7z.Hwc
