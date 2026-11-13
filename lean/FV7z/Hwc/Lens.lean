import FV7z.Hwc.Zero
/-!
# `_dl_important_hwcaps`: one capability added to the lengths, 1465 → 1448 / 1522 (PLAN.md G3, startup)

For the capability with the mask `s = 2^(c-1)` (`rsi`) and `temp[c-1].len = T` (at `rbx - 8`): entry `j` of the
result (`m = E - 1 - j`) gets `T + 1` added if `s &&& m ≠ 0` (`addc`). The code walks the entries with three
places: 1465 (`rax = E - j`, `rdx = P + 16 j`), 1478 (the bit of `m` set, `rax = m`, `rdx = P + 16 (j + 1)`) and
1508 (clear). `Done`: the entries below `j` done, the rest as they were. By induction on the entries left:
`lens78_08` (1478 and 1508 at `j`), `at1465`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

theorem sub1 {x y : Nat} (h : x = y + 1) : BitVec.ofNat 64 x - 1#64 = BitVec.ofNat 64 y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem a16 (P : Addr) (j : Nat) :
    P + BitVec.ofNat 64 (16 * j) + 16#64 = P + BitVec.ofNat 64 (16 * (j + 1)) := by
  rw [BitVec.add_assoc]
  refine congrArg (P + ·) ?_
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

theorem a8m (P : Addr) (j : Nat) :
    P + BitVec.ofNat 64 (16 * (j + 1)) + 18446744073709551608#64 = P + BitVec.ofNat 64 (16 * j + 8) := by
  -- not `omega` on `toNat`: with `2^64 - 8` it ran out of kernel memory (a114)
  rw [show 16 * (j + 1) = 16 * j + 8 + 8 by omega, BitVec.ofNat_add]
  simp only [BitVec.add_assoc, BitVec.reduceOfNat, BitVec.reduceAdd, BitVec.add_zero]

/-- Entry `j` after the capability with the mask `s`, `temp.len = T`. -/
def addc (ℓ : Nat → Addr) (s T : Addr) (E j : Nat) : Addr :=
  if s &&& BitVec.ofNat 64 (E - 1 - j) = 0#64 then ℓ j else ℓ j + T + 1#64

/-- The entries below `j` done, the rest as they were. -/
def Done (ℓ₀ : Nat → Addr) (s T : Addr) (E j : Nat) (ℓ : Nat → Addr) : Prop :=
  (∀ i < j, ℓ i = addc ℓ₀ s T E i) ∧ ∀ i, j ≤ i → ℓ i = ℓ₀ i

variable {ℓ₀ ℓ : Nat → Addr} {s T : Addr} {E j : Nat}

theorem Done.set (hD : Done ℓ₀ s T E j ℓ) (hz : ¬s &&& BitVec.ofNat 64 (E - 1 - j) = 0#64) :
    Done ℓ₀ s T E (j + 1) (upd ℓ j (ℓ j + T + 1#64)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · unfold upd
    by_cases h : i = j
    · rw [ite_eq_left h, h, hD.2 j (Nat.le_refl _)]
      unfold addc
      rw [ite_eq_right hz]
    · rw [ite_eq_right h]
      exact hD.1 i (by omega)
  · unfold upd
    rw [ite_eq_right (by omega)]
    exact hD.2 i (by omega)

theorem Done.clr (hD : Done ℓ₀ s T E j ℓ) (hz : s &&& BitVec.ofNat 64 (E - 1 - j) = 0#64) :
    Done ℓ₀ s T E (j + 1) ℓ := by
  refine ⟨fun i hi => ?_, fun i hi => hD.2 i (by omega)⟩
  by_cases h : i = j
  · rw [h, hD.2 j (Nat.le_refl _)]
    unfold addc
    rw [ite_eq_left hz]
  · exact hD.1 i (by omega)

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {g₁ : Gprs} {σ : Nat → Addr} {V₀ : Addr → Byte}

/-- At 1478 (`set`) or 1508 (clear) for entry `j`: the registers. -/
abbrev G78 (g₁ : Gprs) (E j : Nat) (a8 a9 : Addr) : Gprs :=
  { g₁ with rax := BitVec.ofNat 64 (E - 1 - j), rdx := g₁.r14 + BitVec.ofNat 64 (16 * (j + 1)), r8 := a8, r9 := a9 }

/-- The state at 1478 for entry `j` leads on. -/
def S78 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (g₁ : Gprs)
    (σ ℓ₀ : Nat → Addr) (V₀ : Addr → Byte) (s T : Addr) (E j : Nat) : Prop :=
  ∀ (X : State) (t : Nat) (V : Addr → Byte) (ℓ : Nat → Addr) (a8 a9 : Addr), KeptW Wl s₀ X →
    Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1478 → X.cpu.gpr = G78 g₁ E j a8 a9 →
    ¬s &&& BitVec.ofNat 64 (E - 1 - j) = 0#64 → Tab V g₁.r14 E σ ℓ → Done ℓ₀ s T E j ℓ →
    Same V₀ V (g₁.r14.toNat + 16 * E) (2 ^ 64) → Same V₀ V 0 g₁.r14.toNat → GoG prof L o gev gP gE X t

/-- The state at 1508 for entry `j` (its bit clear: done) leads on. -/
def S08 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (g₁ : Gprs)
    (σ ℓ₀ : Nat → Addr) (V₀ : Addr → Byte) (s T : Addr) (E j : Nat) : Prop :=
  ∀ (X : State) (t : Nat) (V : Addr → Byte) (ℓ : Nat → Addr) (a8 a9 : Addr), KeptW Wl s₀ X →
    Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1508 → X.cpu.gpr = G78 g₁ E j a8 a9 →
    s &&& BitVec.ofNat 64 (E - 1 - j) = 0#64 → Tab V g₁.r14 E σ ℓ → Done ℓ₀ s T E (j + 1) ℓ →
    Same V₀ V (g₁.r14.toNat + 16 * E) (2 ^ 64) → Same V₀ V 0 g₁.r14.toNat → GoG prof L o gev gP gE X t

/-- 1465 for entry `j` (`rax = E - j`, `rdx = P + 16 j`): on to 1478 or 1508 for `j`. -/
theorem at1465 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hsi : g₁.rsi = s) (hE : E < 2 ^ 32) (hj : j < E)
    (h78 : S78 prof F Wl L s₀ o gev gP gE g₁ σ ℓ₀ V₀ s T E j)
    (h08 : S08 prof F Wl L s₀ o gev gP gE g₁ σ ℓ₀ V₀ s T E j) :
    ∀ (X : State) (t : Nat) (V : Addr → Byte) (ℓ : Nat → Addr) (a8 a9 : Addr), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1465 →
      X.cpu.gpr = { g₁ with
        rax := BitVec.ofNat 64 (E - j), rdx := g₁.r14 + BitVec.ofNat 64 (16 * j), r8 := a8, r9 := a9 } →
      Tab V g₁.r14 E σ ℓ → Done ℓ₀ s T E j ℓ → Same V₀ V (g₁.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V 0 g₁.r14.toNat → GoG prof L o gev gP gE X t := by
  intro X t V ℓ a8 a9 hK hA hrip hgx hT hD hS1 hS0
  refine (c_1465 prof fb).run c hfs hin _ hK hA hrip vc_1465 ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  have hra : X.cpu.gpr.rax - 1#64 = BitVec.ofNat 64 (E - 1 - j) := by
    rw [hgx]
    exact sub1 (x := E - j) (y := E - 1 - j) (by omega)
  have hrd : X.cpu.gpr.rdx + 16#64 = g₁.r14 + BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [hgx]
    exact a16 _ _
  have hrs : X.cpu.gpr.rsi = s := by
    rw [hgx]
    exact hsi
  rw [hra, hrd] at hgY
  rw [hrs, hra] at hrY
  rw [hgx] at hgY
  by_cases hz : s &&& BitVec.ofNat 64 (E - 1 - j) = 0#64
  · rw [ite_eq_left hz] at hrY
    exact h08 Y t' _ ℓ a8 a9 hKY hAY hrY (hgY.trans rfl) hz hT (hD.clr hz) hS1 hS0
  · rw [ite_eq_right hz] at hrY
    exact h78 Y t' _ ℓ a8 a9 hKY hAY hrY (hgY.trans rfl) hz hT hD hS1 hS0

/-- 1478 and 1508 for entry `j`, `j + n + 1 = E`: to 1448 (`rcx ≠ 0`) or 1522 with `rbx - 16` and the lengths
`addc`. -/
theorem lens78_08 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hsi : g₁.rsi = s) (hE : E < 2 ^ 32) (hPE : g₁.r14.toNat + 16 * E ≤ 2 ^ 64)
    (hB : g₁.r14.toNat + 16 * E ≤ (g₁.rbx + 18446744073709551608#64).toNat)
    (hB' : (g₁.rbx + 18446744073709551608#64).toNat + 8 ≤ 2 ^ 64)
    (hT0 : rdq(V₀, g₁.rbx + 18446744073709551608#64) = T)
    (hW : ∀ a : Addr, g₁.r14.toNat ≤ a.toNat → a.toNat < g₁.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a)
    (hfT : ∀ k < 8, Foot F.data (Addr.add (g₁.rbx + 18446744073709551608#64) k))
    (k : ∀ Y t' (V' : Addr → Byte) (a8 a9 : Addr), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = hwc_at.add (if g₁.rcx = 0#64 then 1522 else 1448) →
      Y.cpu.gpr = { g₁ with
        rax := 0#64, rdx := g₁.r14 + BitVec.ofNat 64 (16 * E), r8 := a8, r9 := a9, rbx := g₁.rbx - 16#64 } →
      Tab V' g₁.r14 E σ (addc ℓ₀ s T E) → Same V₀ V' (g₁.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V' 0 g₁.r14.toNat → GoG prof L o gev gP gE Y t') :
    ∀ (n j : Nat), j + n + 1 = E →
      S78 prof F Wl L s₀ o gev gP gE g₁ σ ℓ₀ V₀ s T E j ∧ S08 prof F Wl L s₀ o gev gP gE g₁ σ ℓ₀ V₀ s T E j := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain rfl : j = E - 1 := by omega
    refine ⟨?_, ?_⟩
    · intro X t V ℓ a8 a9 _ _ _ _ hz
      exact (hz (by rw [Nat.sub_self]; first | exact BitVec.and_zero | simp)).elim
    · intro X t V ℓ a8 a9 hK hA hrip hgx hz hT hD hS1 hS0
      have hgx' : X.cpu.gpr = { g₁ with
          rax := 0#64, rdx := g₁.r14 + BitVec.ofNat 64 (16 * E), r8 := a8, r9 := a9 } := by
        rw [hgx, G78, Nat.sub_self, show E - 1 + 1 = E by omega]
      refine (c_1508 prof fb).run c hfs hin _ hK hA hrip (vc_1508e (by rw [hgx'])) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      have hrc : X.cpu.gpr.rcx = g₁.rcx := by rw [hgx']
      rw [hrc] at hrY
      rw [hgx'] at hgY
      exact k Y t' _ a8 a9 hKY hAY hrY (hgY.trans rfl)
        (hT.congr (fun _ _ => rfl) fun i hi => hD.1 i (by omega)) hS1 hS0
  | succ n ih =>
    intro j hj
    obtain ⟨ih78, ih08⟩ := ih (j + 1) (by omega)
    refine ⟨?_, ?_⟩
    · -- 1478: entry `j` gets `T + 1`
      intro X t V ℓ a8 a9 hK hA hrip hgx hz hT hD hS1 hS0
      have hrd : X.cpu.gpr.rdx + 18446744073709551608#64 = g₁.r14 + BitVec.ofNat 64 (16 * j + 8) := by
        rw [hgx]
        exact a8m _ _
      have hrb : X.cpu.gpr.rbx = g₁.rbx := by rw [hgx]
      have ea : (g₁.r14 + BitVec.ofNat 64 (16 * j + 8)).toNat = g₁.r14.toNat + (16 * j + 8) :=
        toNat_off (by omega)
      have hL : rdq(V, X.cpu.gpr.rdx + 18446744073709551608#64) = ℓ j := by
        rw [hrd]
        exact (hT j (by omega)).2
      have hT' : rdq(V, X.cpu.gpr.rbx + 18446744073709551608#64) = T := by
        rw [hrb, hS1.rdq hB hB' hB']
        exact hT0
      have hfd : ∀ k < 8, Foot Wl (Addr.add (X.cpu.gpr.rdx + 18446744073709551608#64) k) ∧
          Foot F.data (Addr.add (X.cpu.gpr.rdx + 18446744073709551608#64) k) := by
        intro i hi
        rw [hrd]
        have e := toNat_add_of_fits (a := g₁.r14 + BitVec.ofNat 64 (16 * j + 8)) hi (by rw [ea]; omega)
        exact hW _ (by rw [e, ea]; omega) (by rw [e, ea]; omega)
      refine (c_1478 prof fb).run c hfs hin _ hK hA hrip
        (vc_1478 hL hT' (fun i hi => (hfd i hi).2) (fun i hi => by rw [hrb]; exact hfT i hi)
          (fun i hi => (hfd i hi).1)) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      have hra : X.cpu.gpr.rax - 1#64 = BitVec.ofNat 64 (E - 1 - (j + 1)) := by
        rw [hgx]
        exact sub1 (x := E - 1 - j) (y := E - 1 - (j + 1)) (by omega)
      have hrd2 : X.cpu.gpr.rdx + 16#64 = g₁.r14 + BitVec.ofNat 64 (16 * (j + 1 + 1)) := by
        rw [hgx]
        exact a16 _ _
      have hrs : X.cpu.gpr.rsi = s := by
        rw [hgx]
        exact hsi
      rw [hra, hrd2] at hgY
      rw [hrs, hra] at hrY
      rw [hrd] at hAY
      rw [hgx] at hgY
      have l8 : (toBytesLE (ℓ j + T + 1#64) 8).length = 8 := toBytesLE_length _ _
      have hT2 := hT.stL hPE (j := j) (by omega) (ℓ j + T + 1#64)
      have hD2 := hD.set hz
      have hS1' := hS1.st (a := g₁.r14 + BitVec.ofNat 64 (16 * j + 8)) (bs := toBytesLE (ℓ j + T + 1#64) 8)
        (by rw [l8, ea]; omega) (Or.inl (by rw [l8, ea]; omega))
      have hS0' := hS0.st (a := g₁.r14 + BitVec.ofNat 64 (16 * j + 8)) (bs := toBytesLE (ℓ j + T + 1#64) 8)
        (by rw [l8, ea]; omega) (Or.inr (by rw [ea]; omega))
      by_cases hz2 : s &&& BitVec.ofNat 64 (E - 1 - (j + 1)) = 0#64
      · rw [ite_eq_left hz2] at hrY
        exact ih08 Y t' _ _ (ℓ j + T + 1#64) (ℓ j) hKY hAY hrY (hgY.trans rfl) hz2 hT2 (hD2.clr hz2) hS1' hS0'
      · rw [ite_eq_right hz2] at hrY
        exact ih78 Y t' _ _ (ℓ j + T + 1#64) (ℓ j) hKY hAY hrY (hgY.trans rfl) hz2 hT2 hD2 hS1' hS0'
    · -- 1508: entries remain, to 1465 for `j + 1`
      intro X t V ℓ a8 a9 hK hA hrip hgx hz hT hD hS1 hS0
      have hra : X.cpu.gpr.rax ≠ 0#64 := by
        rw [hgx]
        intro h
        have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.reducePow] at this
        omega
      refine (c_1508 prof fb).run c hfs hin _ hK hA hrip (vc_1508l hra) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      refine at1465 c hfs hin hsi hE (j := j + 1) (by omega) ih78 ih08 Y t' _ ℓ a8 a9 hKY hAY hrY ?_ hT hD hS1 hS0
      rw [hgY, hgx, G78, show E - 1 - j = E - (j + 1) by omega]

end FV7z.Hwc
