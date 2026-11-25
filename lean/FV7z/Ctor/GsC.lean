import FV7z.Ctor.Gs
import FV7z.Ctor.Cx90
import FV7z.Ctor.MixC
/-!
# The steps of `G` for the constructors that call a function (PLAN.md §M, assembly of `at_ctor`)

- `gB`, `g67`, `g77`: the constructors that `jmp` to or call a function that picks a function pointer by `cpuid`
  (5, 7, 9, 92; 67, 77): their stores (`wN`, the stack's window, a registrar's) are apart from what `Gs` reads
  (`hw5`, …).
- `Gn.reg`: `__cxa_atexit`'s stores give `Gn` with one more place; `g90`, `g94`, `g95`, `g99`, `gmc` (100, 101).
- `g98`, `g102`: the constructors that call `malloc`: `Hp` with the budget after it.
-/
namespace FV7z.Ctor
set_option maxRecDepth 100000
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Mal
open FV7z.Sbrk (rd_eq)

variable {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi n₀ k : Nat}

/-! ## Stores apart from what `Gs` reads -/

theorem hw5 : ∀ x, InR (wrOf w5) x → ¬ GRd hi x := fun x h1 h2 => by
  simp [wrOf, w5, InR] at h1
  unfold GRd at h2
  omega

theorem hw7 : ∀ x, InR (wrOf w7) x → ¬ GRd hi x := fun x h1 h2 => by
  simp [wrOf, w7, InR] at h1
  unfold GRd at h2
  omega

theorem hw9 : ∀ x, InR (wrOf w9) x → ¬ GRd hi x := fun x h1 h2 => by
  simp [wrOf, w9, InR] at h1
  unfold GRd at h2
  omega

theorem hw92 : ∀ x, InR (wrOf w92) x → ¬ GRd hi x := fun x h1 h2 => by
  simp [wrOf, w92, InR] at h1
  unfold GRd at h2
  omega

theorem hw67 : ∀ x, InR (wrOf w67) x → ¬ GRd hi x := fun x h1 h2 => by
  simp [wrOf, w67, InR] at h1
  unfold GRd at h2
  omega

theorem hw77 : ∀ x, InR (wrOf w77) x → ¬ GRd hi x := fun x h1 h2 => by
  simp [wrOf, w77, InR] at h1
  unfold GRd at h2
  omega

section steps
variable (hn : n₀ + 10 < 32) (hk : 16 ≤ k)
include hn hk

/-- `Gs` after stores to `w` and the stack's window. -/
theorem gB {m : Nat} {sp : Addr} {w : List Rgn} {W W' : Addr → Byte} (hsp : hi + 1024 ≤ sp.toNat)
    (hw : ∀ x, InR (wrOf w) x → ¬ GRd hi x) (e : nOf n₀ (m + 1) = nOf n₀ m ∧ kOf k (m + 1) = kOf k m)
    (ho : ∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w y → W' y = W y)
    (h : Gs F Wl fb hi n₀ k m W) : Gs F Wl fb hi n₀ k (m + 1) W' :=
  have := h.bnd hk
  Gs.step e (h.kept hn hk fun a ha => ho a (by unfold GRd at ha; omega) fun hf => hw _ (foot_wrOf hf) ha)

theorem g67 {sp : Addr} {cs : List (Nat × Nat)} {W U U' : Addr → Byte} (hsp : hi + 1024 ≤ sp.toNat)
    (hc : CallOut (sp - 64#64) cs W U)
    (ho : ∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w67 y → U' y = U y)
    (h : Gs F Wl fb hi n₀ k 67 W) : Gs F Wl fb hi n₀ k 68 U' :=
  have := h.bnd hk
  have e64 := subk_toNat (D := sp) (k := 64) (by omega)
  Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha => by
    rw [ho a (by unfold GRd at ha; omega) fun hf => hw67 _ (foot_wrOf hf) ha]
    exact CallOut.out_t (by rw [e64]; omega) (by unfold GRd at ha; simp only [tabs, InR, or_false]; omega)
      (by rw [e64]; unfold GRd at ha; omega) _ _ _ hc)

theorem g77 {sp : Addr} {cs : List (Nat × Nat)} {W U U' : Addr → Byte} (hsp : hi + 1024 ≤ sp.toNat)
    (ho : ∀ y : Addr, ¬ (sp.toNat - 1024 ≤ y.toNat ∧ y.toNat < sp.toNat + 8) → ¬ Foot w77 y → U y = W y)
    (hc : ChainOut (sp - 64#64) cs U U') (h : Gs F Wl fb hi n₀ k 77 W) : Gs F Wl fb hi n₀ k 78 U' :=
  have := h.bnd hk
  have e64 := subk_toNat (D := sp) (k := 64) (by omega)
  Gs.step ⟨by simp [nOf], by simp [kOf]⟩ (h.kept hn hk fun a ha => by
    rw [ChainOut.out_t (by rw [e64]; omega) (by unfold GRd at ha; simp only [tabs, InR, or_false]; omega)
      (by rw [e64]; unfold GRd at ha; omega) _ _ _ hc]
    exact ho a (by unfold GRd at ha; omega) fun hf => hw77 _ (foot_wrOf hf) ha)

end steps

/-! ## `__cxa_atexit` -/

/-- The tables for bytes that agree on them. -/
theorem Tb103.kept {W W' : Addr → Byte} (h : Tb103 W)
    (hW : ∀ a : Addr, 7282688 ≤ a.toNat → a.toNat < 7283008 → W' a = W a) : Tb103 W' := by
  have e1 : (0x6f2000#64 : Addr).toNat = 7282688 := rfl
  have e2 : (7282852#64 : Addr).toNat = 7282852 := rfl
  refine ⟨?_, ?_⟩
  · rw [rd_eq (by rw [e1]; omega) fun a h1 h2 => hW a (by rw [e1] at h1; omega) (by rw [e1] at h2; omega)]
    exact h.amd
  · rw [rd_eq (by rw [e2]; omega) fun a h1 h2 => hW a (by rw [e2] at h1; omega) (by rw [e2] at h2; omega)]
    exact h.own

/-- `__cxa_atexit`'s stores with its frame below `S` give `Gn` with one more place. -/
theorem Gn.reg {n K : Nat} {S : Addr} {fn arg dso : BitVec 64} {W W' : Addr → Byte} (h : Gn F Wl fb hi n K W)
    (hn : n + 1 < 32) (hK : 16 ≤ K) (hS : hi + 80 ≤ S.toNat)
    (hR : Cxa.Reg W W' S xl (xl + BitVec.ofNat 64 (16 + 32 * n)) n fn arg dso) : Gn F Wl fb hi (n + 1) K W' := by
  obtain ⟨f1, f2, f3⟩ := h.bnd hK
  obtain ⟨-, -, ep, -, -, -⟩ := Nef.l_n xl n (by omega) (by decide)
  have el : xl.toNat = 8010400 := rfl
  have hc := h.2.1.reg hR hn (by omega) (by decide) (.inl (by omega)) (by omega) (.inr (by rw [el]; omega))
    (.inr (by omega)) (by omega) (by rw [el]; omega) (.inl (by rw [el]; omega))
  have hW : ∀ a : Addr, (7282688 ≤ a.toNat ∧ a.toNat < 7283008 ∨ 7940480 ≤ a.toNat ∧ a.toNat < 7942880 ∨
      8013220 ≤ a.toNat ∧ a.toNat < 8013232 ∨ 8029888 ≤ a.toNat ∧ a.toNat < hi) → W' a = W a :=
    fun a ha => hR.out a (by omega) (by rw [el]; omega) (by rw [ep, el]; omega) (by omega)
  exact ⟨h.1.kept fun a h1 h2 => hW a (by omega), hc, h.2.2.mvS hK fun a ha => hW a (by unfold GlS at ha; omega)⟩

section cx
variable (hn : n₀ + 10 < 32) (hk : 16 ≤ k)
include hn hk

theorem g90 {sp : Addr} {f₁ a₁ d₁ f₂ a₂ d₂ : BitVec 64} {W V₁ V₂ V₃ V' : Addr → Byte}
    (hsp : hi + 1024 ≤ sp.toNat) (h : Gs F Wl fb hi n₀ k 90 W)
    (hv : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → V₁ a = ob90 W a)
    (hR₁ : Cxa.Reg V₁ V₂ (sp - 80#64) xl (xl + BitVec.ofNat 64 (16 + 32 * nOf n₀ 90)) (nOf n₀ 90) f₁ a₁ d₁)
    (hmo : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7990208 ≤ a.toNat ∧ a.toNat < 7990248) → V₃ a = V₂ a)
    (hR₂ : Cxa.Reg V₃ V' (sp - 64#64) xl (xl + BitVec.ofNat 64 (16 + 32 * (nOf n₀ 90 + 1))) (nOf n₀ 90 + 1)
      f₂ a₂ d₂) :
    Gs F Wl fb hi n₀ k 91 V' := by
  have q : nOf n₀ 90 = n₀ := by simp [nOf]
  have hK : 16 ≤ kOf k 90 := Nat.le_trans hk (kOf_ge k 90)
  have := h.bnd hk
  have e64 := subk_toNat (D := sp) (k := 64) (by omega)
  have e80 := subk_toNat (D := sp) (k := 80) (by omega)
  have h1 : Gn F Wl fb hi (nOf n₀ 90) (kOf k 90) V₁ := Gn.kept h (by omega) hK fun a ha => by
    rw [hv a (by unfold GRd at ha; omega)]
    exact ob90_out W a (by unfold GRd at ha; omega)
  have h2 := h1.reg (by omega) hK (by rw [e80]; omega) hR₁
  have h3 := h2.kept (by omega) hK fun a ha => hmo a (by unfold GRd at ha; omega) (by unfold GRd at ha; omega)
  have h4 := h3.reg (by omega) hK (by rw [e64]; omega) hR₂
  exact Gs.of ⟨by simp [nOf] <;> omega, by simp [kOf]⟩ h4

theorem g94 {sp : Addr} {f₁ a₁ d₁ : BitVec 64} {W V₁ V₂ : Addr → Byte}
    (hsp : hi + 1024 ≤ sp.toNat) (h : Gs F Wl fb hi n₀ k 94 W)
    (hv : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7990368 ≤ a.toNat ∧ a.toNat < 7990408) → V₁ a = W a)
    (hR₁ : Cxa.Reg V₁ V₂ (sp - 80#64) xl (xl + BitVec.ofNat 64 (16 + 32 * nOf n₀ 94)) (nOf n₀ 94) f₁ a₁ d₁) :
    Gs F Wl fb hi n₀ k 95 (Vst V₂ 7990336#64 (toBytesLE (BitVec.ofNat 8 1) 1)) := by
  have q : nOf n₀ 94 = n₀ + 2 := by simp [nOf]
  have hK : 16 ≤ kOf k 94 := Nat.le_trans hk (kOf_ge k 94)
  have := h.bnd hk
  have e80 := subk_toNat (D := sp) (k := 80) (by omega)
  have h1 : Gn F Wl fb hi (nOf n₀ 94) (kOf k 94) V₁ := Gn.kept h (by omega) hK fun a ha =>
    hv a (by unfold GRd at ha; omega) (by unfold GRd at ha; omega)
  have h2 := h1.reg (by omega) hK (by rw [e80]; omega) hR₁
  have h3 := h2.kept (W' := Vst V₂ 7990336#64 (toBytesLE (BitVec.ofNat 8 1) 1)) (by omega) hK fun a ha =>
    Tun.Vst_out V₂ _ _ a (by rw [toBytesLE_length]; decide)
      (by rw [toBytesLE_length, show (7990336#64 : Addr).toNat = 7990336 from rfl]; unfold GRd at ha; omega)
  exact Gs.of ⟨by simp [nOf] <;> omega, by simp [kOf]⟩ h3

/-- Two calls of `__cxa_atexit` with an object's stores before each (95, 99). -/
theorem gCx2 {m : Nat} {sp : Addr} {lo₁ up₁ lo₂ up₂ : Nat} {f₁ a₁ d₁ f₂ a₂ d₂ : BitVec 64}
    {W V₁ V₂ V₃ V' : Addr → Byte} (hsp : hi + 1024 ≤ sp.toNat)
    (e : nOf n₀ (m + 1) = nOf n₀ m + 1 + 1 ∧ kOf k (m + 1) = kOf k m)
    (hd₁ : ∀ a, GRd hi a → a < lo₁ ∨ up₁ ≤ a) (hd₂ : ∀ a, GRd hi a → a < lo₂ ∨ up₂ ≤ a)
    (h : Gs F Wl fb hi n₀ k m W)
    (hv : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (lo₁ ≤ a.toNat ∧ a.toNat < up₁) → V₁ a = W a)
    (hR₁ : Cxa.Reg V₁ V₂ (sp - 80#64) xl (xl + BitVec.ofNat 64 (16 + 32 * nOf n₀ m)) (nOf n₀ m) f₁ a₁ d₁)
    (hmo : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (lo₂ ≤ a.toNat ∧ a.toNat < up₂) → V₃ a = V₂ a)
    (hR₂ : Cxa.Reg V₃ V' (sp - 64#64) xl (xl + BitVec.ofNat 64 (16 + 32 * (nOf n₀ m + 1))) (nOf n₀ m + 1)
      f₂ a₂ d₂) :
    Gs F Wl fb hi n₀ k (m + 1) V' := by
  have q := nOf_le n₀ (m + 1)
  have hK : 16 ≤ kOf k m := Nat.le_trans hk (kOf_ge k m)
  have := h.bnd hk
  have e64 := subk_toNat (D := sp) (k := 64) (by omega)
  have e80 := subk_toNat (D := sp) (k := 80) (by omega)
  have h1 : Gn F Wl fb hi (nOf n₀ m) (kOf k m) V₁ := Gn.kept h (by omega) hK fun a ha =>
    hv a (by unfold GRd at ha; omega) (by have := hd₁ _ ha; omega)
  have h2 := h1.reg (by omega) hK (by rw [e80]; omega) hR₁
  have h3 := h2.kept (by omega) hK fun a ha => hmo a (by unfold GRd at ha; omega) (by have := hd₂ _ ha; omega)
  have h4 := h3.reg (by omega) hK (by rw [e64]; omega) hR₂
  exact Gs.of ⟨e.1, e.2⟩ h4

theorem g95 {sp : Addr} {f₁ a₁ d₁ f₂ a₂ d₂ : BitVec 64} {W V₁ V₂ V₃ V' : Addr → Byte}
    (hsp : hi + 1024 ≤ sp.toNat) (h : Gs F Wl fb hi n₀ k 95 W)
    (hv : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7990568 ≤ a.toNat ∧ a.toNat < 7990608) → V₁ a = W a)
    (hR₁ : Cxa.Reg V₁ V₂ (sp - 80#64) xl (xl + BitVec.ofNat 64 (16 + 32 * nOf n₀ 95)) (nOf n₀ 95) f₁ a₁ d₁)
    (hmo : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7990432 ≤ a.toNat ∧ a.toNat < 7990472) → V₃ a = V₂ a)
    (hR₂ : Cxa.Reg V₃ V' (sp - 64#64) xl (xl + BitVec.ofNat 64 (16 + 32 * (nOf n₀ 95 + 1))) (nOf n₀ 95 + 1)
      f₂ a₂ d₂) :
    Gs F Wl fb hi n₀ k 96 V' :=
  gCx2 hn hk hsp ⟨by simp [nOf] <;> omega, by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega)
    (fun a ha => by unfold GRd at ha; omega) h hv hR₁ hmo hR₂

theorem g99 {sp : Addr} {f₁ a₁ d₁ f₂ a₂ d₂ : BitVec 64} {W V₁ V₂ V₃ V' : Addr → Byte}
    (hsp : hi + 1024 ≤ sp.toNat) (h : Gs F Wl fb hi n₀ k 99 W)
    (hv : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7991392 ≤ a.toNat ∧ a.toNat < 7991432) → V₁ a = W a)
    (hR₁ : Cxa.Reg V₁ V₂ (sp - 80#64) xl (xl + BitVec.ofNat 64 (16 + 32 * nOf n₀ 99)) (nOf n₀ 99) f₁ a₁ d₁)
    (hmo : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) →
      ¬ (7991328 ≤ a.toNat ∧ a.toNat < 7991368) → V₃ a = V₂ a)
    (hR₂ : Cxa.Reg V₃ V' (sp - 64#64) xl (xl + BitVec.ofNat 64 (16 + 32 * (nOf n₀ 99 + 1))) (nOf n₀ 99 + 1)
      f₂ a₂ d₂) :
    Gs F Wl fb hi n₀ k 100 V' :=
  gCx2 hn hk hsp ⟨by simp [nOf] <;> omega, by simp [kOf]⟩ (fun a ha => by unfold GRd at ha; omega)
    (fun a ha => by unfold GRd at ha; omega) h hv hR₁ hmo hR₂

/-- A mutex's initialization at `[M, M + 40)` and one call of `__cxa_atexit` (100, 101). -/
theorem gmc {m M : Nat} {sp : Addr} {f₁ a₁ d₁ : BitVec 64} {W V₁ V' : Addr → Byte} (hsp : hi + 1024 ≤ sp.toNat)
    (e : nOf n₀ (m + 1) = nOf n₀ m + 1 ∧ kOf k (m + 1) = kOf k m) (hd : ∀ a, GRd hi a → a < M ∨ M + 40 ≤ a)
    (h : Gs F Wl fb hi n₀ k m W)
    (hv : ∀ a : Addr, ¬ (sp.toNat - 136 ≤ a.toNat ∧ a.toNat < sp.toNat - 64) → ¬ (M ≤ a.toNat ∧ a.toNat < M + 40) →
      V₁ a = W a)
    (hR : Cxa.Reg V₁ V' (sp - 64#64) xl (xl + BitVec.ofNat 64 (16 + 32 * nOf n₀ m)) (nOf n₀ m) f₁ a₁ d₁) :
    Gs F Wl fb hi n₀ k (m + 1) V' := by
  have q := nOf_le n₀ (m + 1)
  have hK : 16 ≤ kOf k m := Nat.le_trans hk (kOf_ge k m)
  have := h.bnd hk
  have e64 := subk_toNat (D := sp) (k := 64) (by omega)
  have h1 : Gn F Wl fb hi (nOf n₀ m) (kOf k m) V₁ := Gn.kept h (by omega) hK fun a ha =>
    hv a (by unfold GRd at ha; omega) (by have := hd _ ha; omega)
  exact Gs.of ⟨e.1, e.2⟩ (h1.reg (by omega) hK (by rw [e64]; omega) hR)

/-! ## `malloc` -/

theorem g98 {sp p : Addr} {f₁ a₁ d₁ : BitVec 64} {W V₂ V' : Addr → Byte} (hsp : hi + 1024 ≤ sp.toNat)
    (h : Gs F Wl fb hi n₀ k 98 W)
    (hv : ∀ a : Addr, ¬ (7990672 ≤ a.toNat ∧ a.toNat < 7990688) →
      (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → V₂ a = W a)
    (hp : fb.toNat + 64 ≤ p.toNat)
    (hH : ∀ U : Addr → Byte, (∀ a : Addr, GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 4 ≤ a.toNat) → U a = V₂ a) →
      Hp F Wl fb hi (k + 72752) U)
    (hR : Cxa.Reg V₂ V' (sp - 64#64) xl (xl + BitVec.ofNat 64 (16 + 32 * nOf n₀ 98)) (nOf n₀ 98) f₁ a₁ d₁) :
    Gs F Wl fb hi n₀ k 99 V' := by
  have q : nOf n₀ 98 = n₀ + 5 := by simp [nOf]
  have := h.bnd hk
  have e64 := subk_toNat (D := sp) (k := 64) (by omega)
  have el : xl.toNat = 8010400 := rfl
  have h1 : Gn F Wl fb hi (nOf n₀ 98) (k + 72752) V₂ :=
    ⟨h.1.kept fun a h1 h2 => hv a (by omega) (.inl (by omega)),
      h.2.1.kept (by omega) (by omega) (by decide) fun a ha => hv a (by unfold CxR at ha; rw [el] at ha; omega)
        (by unfold CxR at ha; rw [el] at ha; omega),
      hH V₂ fun _ _ _ => rfl⟩
  exact Gs.of ⟨by simp [nOf] <;> omega, by simp [kOf]⟩ (h1.reg (by omega) (by omega) (by rw [e64]; omega) hR)

theorem g102 {sp p : Addr} {W V' : Addr → Byte} (hsp : hi + 1024 ≤ sp.toNat)
    (h : Gs F Wl fb hi n₀ k 102 W)
    (hv : ∀ a : Addr, ¬ (8008064 ≤ a.toNat ∧ a.toNat < 8008128) →
      (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨
        hi ≤ a.toNat ∧ (a.toNat + 320 < sp.toNat ∨ sp.toNat - 72 ≤ a.toNat)) → V' a = W a)
    (hp : fb.toNat + 64 ≤ p.toNat)
    (hH : ∀ U : Addr → Byte, (∀ a : Addr, GlR hi a → (a.toNat < p.toNat ∨ p.toNat + 72704 ≤ a.toNat) →
      U a = V' a) → Hp F Wl fb hi k U) :
    Gs F Wl fb hi n₀ k 103 V' := by
  have q : nOf n₀ 102 = n₀ + 10 := by simp [nOf]
  have := h.bnd hk
  have el : xl.toNat = 8010400 := rfl
  exact Gs.of ⟨by simp [nOf] <;> omega, by simp [kOf]⟩
    (⟨h.1.kept fun a h1 h2 => hv a (by omega) (.inl (by omega)),
      h.2.1.kept (by omega) (by omega) (by decide) fun a ha => hv a (by unfold CxR at ha; rw [el] at ha; omega)
        (by unfold CxR at ha; rw [el] at ha; omega),
      hH V' fun _ _ _ => rfl⟩ : Gn F Wl fb hi (nOf n₀ 102) k V')

end cx

end FV7z.Ctor
