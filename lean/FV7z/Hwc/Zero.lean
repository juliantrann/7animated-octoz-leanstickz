import FV7z.Hwc.Vc3
import FV7z.Hwc.Tab
/-!
# `_dl_important_hwcaps`: the lengths of the result zeroed, 1392 → 1448 (PLAN.md G3, startup)

From 1392 with `rax = i`, `rcx = E` (8 or 16) and the result `P = r14` (`E` entries of 16 bytes, below the frame):
`result[j].len = 0` for every `j < E` (`Tab … σ (fun _ => 0)`, the pointers `σ` as they were), the bytes below `P`
and from `P + 16 E` on as they were (`Same`), to 1448 (`vc_1392e`). By induction on the entries left.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

/-- `rbp - 0x88` is `rbp - 0x98 + 16` (no wrap). -/
theorem off88 {r : Addr} (h : (r + 18446744073709551464#64).toNat + 24 ≤ 2 ^ 64) :
    (r + 18446744073709551480#64).toNat = (r + 18446744073709551464#64).toNat + 16 := by
  bv_omega

/-- A load of 8 bytes inside `lo`, `hi`. -/
theorem Same.rdq {V W : Addr → Byte} {lo hi : Nat} (hS : Same V W lo hi) {x : Addr} (h1 : lo ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ hi) (hx : x.toNat + 8 ≤ 2 ^ 64) : rdq(W, x) = rdq(V, x) := by
  rw [hS.rd h1 h2 hx]

/-- `upd ℓ i 0` is 0 below `i + 1` if `ℓ` is below `i`. -/
theorem upd_zero {ℓ : Nat → Addr} {i : Nat} (hz : ∀ j < i, ℓ j = 0#64) : ∀ j < i + 1, upd ℓ i 0#64 j = 0#64 := by
  intro j hj
  unfold upd
  by_cases h : j = i
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact hz j (by omega)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}

/-- The loop from 1392 (`rax = i`, `rdx = d`, the rest `g₀`) to 1448: the lengths zeroed. -/
theorem zero (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    {g₀ : Gprs} {E D : Nat} {σ : Nat → Addr} {V₀ : Addr → Byte} (hE : E = 8 ∧ D = 48 ∨ E = 16 ∧ D = 64)
    (hc : g₀.rcx = BitVec.ofNat 64 E)
    (hP : g₀.r14.toNat + 16 * E ≤ (g₀.rbp + 18446744073709551464#64).toNat)
    (hfr : (g₀.rbp + 18446744073709551464#64).toNat + 24 ≤ 2 ^ 64)
    (hR : rdq(V₀, g₀.rbp + 18446744073709551480#64) = BitVec.ofNat 64 E)
    (hD : rdq(V₀, g₀.rbp + 18446744073709551464#64) = BitVec.ofNat 64 D)
    (hW : ∀ a : Addr, g₀.r14.toNat ≤ a.toNat → a.toNat < g₀.r14.toNat + 16 * E → Foot Wl a)
    (hf1 : ∀ k < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551480#64) k))
    (hf2 : ∀ k < 8, Foot F.data (Addr.add (g₀.rbp + 18446744073709551464#64) k))
    (k : ∀ Y t' (V' : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = hwc_at.add 1448 →
      Y.cpu.gpr = { g₀ with
        rax := BitVec.ofNat 64 E, rcx := g₀.r12, rdx := BitVec.ofNat 64 (16 * (E - 1)),
        rbx := g₀.rbx + BitVec.ofNat 64 D, rdi := 1#64, r10 := BitVec.ofNat 64 E } →
      Tab V' g₀.r14 E σ (fun _ => 0#64) → Same V₀ V' (g₀.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V' 0 g₀.r14.toNat → GoG prof L o gev gP gE Y t') :
    ∀ (n i : Nat), i + n + 1 = E → ∀ (X : State) (t : Nat) (V : Addr → Byte) (ℓ : Nat → Addr) (d : Addr),
      KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1392 →
      X.cpu.gpr = { g₀ with rax := BitVec.ofNat 64 i, rdx := d } →
      Tab V g₀.r14 E σ ℓ → (∀ j < i, ℓ j = 0#64) → Same V₀ V (g₀.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V 0 g₀.r14.toNat → GoG prof L o gev gP gE X t := by
  have hlt := (g₀.rbp + 18446744073709551464#64).isLt
  have hE8 : 8 ≤ E := by omega
  have hPE : g₀.r14.toNat + 16 * E ≤ 2 ^ 64 := by omega
  have e88 := off88 hfr
  intro n
  induction n with
  | zero =>
    intro i hi X t V ℓ d hK hA hrip hgx hT hz hS1 hS0
    obtain rfl : i = E - 1 := by omega
    have hr14 : X.cpu.gpr.r14 = g₀.r14 := by rw [hgx]
    have hrbp : X.cpu.gpr.rbp = g₀.rbp := by rw [hgx]
    have ea : (g₀.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)).toNat = g₀.r14.toNat + (16 * (E - 1) + 8) :=
      toNat_off (by omega)
    have l8 : (toBytesLE 0#64 8).length = 8 := toBytesLE_length _ _
    have hS1' := hS1.st (a := g₀.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) (bs := toBytesLE 0#64 8)
      (by rw [l8, ea]; omega) (Or.inl (by rw [l8, ea]; omega))
    have hS0' := hS0.st (a := g₀.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) (bs := toBytesLE 0#64 8)
      (by rw [l8, ea]; omega) (Or.inr (by rw [ea]; omega))
    have hR' : rdq(Vst V (X.cpu.gpr.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) (toBytesLE 0#64 8),
        X.cpu.gpr.rbp + 18446744073709551480#64) = BitVec.ofNat 64 E := by
      rw [hr14, hrbp, hS1'.rdq (by omega) (by omega) (by omega)]
      exact hR
    have hD' : rdq(Vst V (X.cpu.gpr.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) (toBytesLE 0#64 8),
        X.cpu.gpr.rbp + 18446744073709551464#64) = BitVec.ofNat 64 D := by
      rw [hr14, hrbp, hS1'.rdq (by omega) (by omega) (by omega)]
      exact hD
    have hs : ∀ k < 8, Foot Wl (Addr.add (X.cpu.gpr.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) k) := by
      intro j hj
      rw [hr14]
      have e := toNat_add_of_fits (a := g₀.r14 + BitVec.ofNat 64 (16 * (E - 1) + 8)) hj (by rw [ea]; omega)
      exact hW _ (by rw [e, ea]; omega) (by rw [e, ea]; omega)
    refine (c_1392 prof fb).run c hfs hin _ hK hA hrip
      (vc_1392e (E := E) (D := D) hE (by rw [hgx]) (by rw [hgx]; exact hc) hR' hD' hs
        (fun j hj => by rw [hrbp]; exact hf1 j hj) (fun j hj => by rw [hrbp]; exact hf2 j hj)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
    rw [hr14] at hAY
    have hz' := upd_zero (ℓ := ℓ) (i := E - 1) hz
    exact k Y t' _ hKY hAY hrY (by rw [hgY, hgx]; try rfl)
      ((hT.stL hPE (j := E - 1) (by omega) 0#64).congr (fun _ _ => rfl) fun j hj => hz' j (by omega)) hS1' hS0'
  | succ n ih =>
    intro i hi X t V ℓ d hK hA hrip hgx hT hz hS1 hS0
    have hr14 : X.cpu.gpr.r14 = g₀.r14 := by rw [hgx]
    have ea : (g₀.r14 + BitVec.ofNat 64 (16 * i + 8)).toNat = g₀.r14.toNat + (16 * i + 8) :=
      toNat_off (by omega)
    have l8 : (toBytesLE 0#64 8).length = 8 := toBytesLE_length _ _
    have hs : ∀ k < 8, Foot Wl (Addr.add (X.cpu.gpr.r14 + BitVec.ofNat 64 (16 * i + 8)) k) := by
      intro j hj
      rw [hr14]
      have e := toNat_add_of_fits (a := g₀.r14 + BitVec.ofNat 64 (16 * i + 8)) hj (by rw [ea]; omega)
      exact hW _ (by rw [e, ea]; omega) (by rw [e, ea]; omega)
    refine (c_1392 prof fb).run c hfs hin _ hK hA hrip
      (vc_1392l (i := i) (E := E) (by omega) (by rw [hgx]) (by rw [hgx]; exact hc) hs) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
    rw [hr14] at hAY
    exact ih (i + 1) (by omega) Y t' _ (upd ℓ i 0#64) (BitVec.ofNat 64 (16 * i)) hKY hAY hrY
      (by rw [hgY, hgx]; try rfl) (hT.stL hPE (by omega) 0#64) (upd_zero hz)
      (hS1.st (by rw [l8, ea]; omega) (Or.inl (by rw [l8, ea]; omega)))
      (hS0.st (by rw [l8, ea]; omega) (Or.inr (by rw [ea]; omega)))

end FV7z.Hwc
