import FV7z.Hwc.Caps
/-!
# `_dl_important_hwcaps`: the pointers of the result, 1568 → 1681 (PLAN.md G3, startup)

With `H = 2^(cnt-1)` and `E = 2 H` entries at `P = r14` (`str[0]`, `str[1]` set before): the first half (1568,
`rax = P + 16 i`, `rdx = E - i`, `2 ≤ i < H`): `str[i] = len[i-2] + str[i-2]` (`i` even) or `str[i-1]` (odd)
(`pt1`); then 1602, 1612 (`rsi = P + 16 H`, `rdx = -16 H`, `rdi = T + 1`); the second half (1632, `rcx = k`,
`rsi = P + 16 (E - k)`): `str[i] = str[i - H] + T + 1` (`pt`); after the last, `*Q = len[0]`, the frame popped, to
the `ret` (1681). `PD`: the entries below `i` done, the rest as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Hwc

theorem a16m (P : Addr) (j : Nat) :
    P + BitVec.ofNat 64 (16 * (j + 1)) + 18446744073709551600#64 = P + BitVec.ofNat 64 (16 * j) := by
  rw [show 16 * (j + 1) = 16 * j + 16 by omega, BitVec.ofNat_add]
  simp only [BitVec.add_assoc, BitVec.reduceOfNat, BitVec.reduceAdd, BitVec.add_zero]

theorem a24m (P : Addr) (j : Nat) :
    P + BitVec.ofNat 64 (16 * (j + 2)) + 18446744073709551592#64 = P + BitVec.ofNat 64 (16 * j + 8) := by
  rw [show 16 * (j + 2) = 16 * j + 8 + 24 by omega, BitVec.ofNat_add]
  simp only [BitVec.add_assoc, BitVec.reduceOfNat, BitVec.reduceAdd, BitVec.add_zero]

theorem a32m (P : Addr) (j : Nat) :
    P + BitVec.ofNat 64 (16 * (j + 2)) + 18446744073709551584#64 = P + BitVec.ofNat 64 (16 * j) := by
  rw [show 16 * (j + 2) = 16 * j + 32 by omega, BitVec.ofNat_add]
  simp only [BitVec.add_assoc, BitVec.reduceOfNat, BitVec.reduceAdd, BitVec.add_zero]

/-- `rsi + rdx` in the second half. -/
theorem aH (P : Addr) (i H : Nat) :
    P + BitVec.ofNat 64 (16 * (i + H)) + (0#64 - BitVec.ofNat 64 (16 * H)) = P + BitVec.ofNat 64 (16 * i) := by
  rw [BitVec.zero_sub, ← BitVec.sub_eq_add_neg, show 16 * (i + H) = 16 * i + 16 * H by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- `rsi` after 1602. -/
theorem a1602 (P : Addr) {H E : Nat} (h : H = 4 ∧ E = 8 ∨ H = 8 ∧ E = 16) :
    P + 32#64 + BitVec.ofNat 64 (16 * (E - 2 - H)) = P + BitVec.ofNat 64 (16 * H) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [Nat.reduceSub, Nat.reduceMul, BitVec.add_assoc, BitVec.reduceOfNat, BitVec.reduceAdd]

/-- The frame slots below `rbp`, from `rbp - 0x98`. -/
theorem off68 {r : Addr} (h : (r + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64) :
    (r + 18446744073709551512#64).toNat = (r + 18446744073709551464#64).toNat + 48 := by
  bv_omega

theorem off50 {r : Addr} (h : (r + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64) :
    (r + 18446744073709551536#64).toNat = (r + 18446744073709551464#64).toNat + 72 := by
  bv_omega

theorem off70 {r : Addr} (h : (r + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64) :
    (r + 18446744073709551504#64).toNat = (r + 18446744073709551464#64).toNat + 40 := by
  bv_omega

/-- 8 bytes at `P + m` inside the table. -/
theorem foot8 {P : Addr} {E m : Nat} {p : Addr → Prop} (hPE : P.toNat + 16 * E ≤ 2 ^ 64) (hm : m + 8 ≤ 16 * E)
    (hW : ∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + 16 * E → p a) :
    ∀ k < 8, p (Addr.add (P + BitVec.ofNat 64 m) k) := by
  intro k hk
  have ea : (P + BitVec.ofNat 64 m).toNat = P.toNat + m := toNat_off (by omega)
  have e := toNat_add_of_fits (a := P + BitVec.ofNat 64 m) hk (by rw [ea]; omega)
  exact hW _ (by rw [e, ea]; omega) (by rw [e, ea]; omega)

/-- A store of 8 bytes into the table keeps the bytes outside. -/
theorem Same.tab {V₀ V : Addr → Byte} {P : Addr} {E m : Nat} (hPE : P.toNat + 16 * E ≤ 2 ^ 64)
    (hm : m + 8 ≤ 16 * E) (h1 : Same V₀ V (P.toNat + 16 * E) (2 ^ 64)) (h0 : Same V₀ V 0 P.toNat) (v : Addr) :
    Same V₀ (Vst V (P + BitVec.ofNat 64 m) (toBytesLE v 8)) (P.toNat + 16 * E) (2 ^ 64) ∧
      Same V₀ (Vst V (P + BitVec.ofNat 64 m) (toBytesLE v 8)) 0 P.toNat := by
  have l8 : (toBytesLE v 8).length = 8 := toBytesLE_length _ _
  have ea : (P + BitVec.ofNat 64 m).toNat = P.toNat + m := toNat_off (by omega)
  exact ⟨h1.st (by rw [l8, ea]; omega) (Or.inl (by rw [l8, ea]; omega)),
    h0.st (by rw [l8, ea]; omega) (Or.inr (by rw [ea]; omega))⟩

/-- The pointers of the first half (`str[0]`, `str[1]` as they were). -/
def pt1 (σ ℓ : Nat → Addr) : Nat → Addr
  | 0 => σ 0
  | 1 => σ 1
  | i + 2 => if i % 2 = 1 then pt1 σ ℓ (i + 1) else ℓ i + pt1 σ ℓ i

theorem pt1_ss (σ ℓ : Nat → Addr) (i : Nat) :
    pt1 σ ℓ (i + 2) = if i % 2 = 1 then pt1 σ ℓ (i + 1) else ℓ i + pt1 σ ℓ i := rfl

/-- All the pointers: the second half `str[i - H] + T + 1`. -/
def pt (σ ℓ : Nat → Addr) (H : Nat) (T : Addr) (i : Nat) : Addr :=
  if i < H then pt1 σ ℓ i else pt1 σ ℓ (i - H) + (T + 1#64)

/-- The pointers below `i` as `f`, the rest as `σ`. -/
def PD (σ f : Nat → Addr) (i : Nat) (σ' : Nat → Addr) : Prop :=
  (∀ j < i, σ' j = f j) ∧ ∀ j, i ≤ j → σ' j = σ j

theorem PD.st {σ f σ' : Nat → Addr} {i : Nat} (h : PD σ f i σ') {v : Addr} (hv : v = f i) :
    PD σ f (i + 1) (upd σ' i v) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · unfold upd
    by_cases e : j = i
    · rw [ite_eq_left e, hv, e]
    · rw [ite_eq_right e]
      exact h.1 j (by omega)
  · unfold upd
    rw [ite_eq_right (by omega)]
    exact h.2 j (by omega)

theorem PD.two (σ ℓ : Nat → Addr) : PD σ (pt1 σ ℓ) 2 σ :=
  ⟨fun j hj => by
    rcases j with _ | _ | j
    · rfl
    · rfl
    · omega, fun _ _ => rfl⟩

theorem PD.half {σ ℓ σ' : Nat → Addr} {H : Nat} {T : Addr} (h : PD σ (pt1 σ ℓ) H σ') :
    PD σ (pt σ ℓ H T) H σ' :=
  ⟨fun j hj => by
    rw [h.1 j hj]
    unfold pt
    rw [ite_eq_left hj], h.2⟩

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}
  {g₃ : Gprs} {E H : Nat} {σ ℓ : Nat → Addr} {V₀ : Addr → Byte}

/-- The first half: 1568 at `i` to 1602 with the pointers below `H` (`pt1`). -/
theorem half1 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    (hHE : H = 4 ∧ E = 8 ∨ H = 8 ∧ E = 16) (hrcx : g₃.rcx = BitVec.ofNat 64 H)
    (hPE : g₃.r14.toNat + 16 * E ≤ 2 ^ 64)
    (hW : ∀ a : Addr, g₃.r14.toNat ≤ a.toNat → a.toNat < g₃.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a)
    (k : ∀ Y t' (V' : Addr → Byte) (w : Addr) (σ' : Nat → Addr), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' →
      Y.cpu.rip = hwc_at.add 1602 →
      Y.cpu.gpr = { g₃ with
        rax := g₃.r14 + BitVec.ofNat 64 (16 * H), rdx := BitVec.ofNat 64 H, rdi := w } →
      Tab V' g₃.r14 E σ' ℓ → PD σ (pt1 σ ℓ) H σ' → Same V₀ V' (g₃.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V' 0 g₃.r14.toNat → GoG prof L o gev gP gE Y t') :
    ∀ (m i : Nat), i + m + 1 = H → 2 ≤ i → ∀ (X : State) (t : Nat) (V : Addr → Byte) (w : Addr)
      (σ' : Nat → Addr), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1568 →
      X.cpu.gpr = { g₃ with
        rax := g₃.r14 + BitVec.ofNat 64 (16 * i), rdx := BitVec.ofNat 64 (E - i), rdi := w } →
      Tab V g₃.r14 E σ' ℓ → PD σ (pt1 σ ℓ) i σ' → Same V₀ V (g₃.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V 0 g₃.r14.toNat → GoG prof L o gev gP gE X t := by
  have hWl := fun a h1 h2 => (hW a h1 h2).1
  have hWd := fun a h1 h2 => (hW a h1 h2).2
  intro m
  induction m with
  | zero =>
    intro i hi hi2 X t V w σ' hK hA hrip hgx hT hD hS1 hS0
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 2 := ⟨i - 2, by omega⟩
    have hra : X.cpu.gpr.rax = g₃.r14 + BitVec.ofNat 64 (16 * (l + 2)) := by rw [hgx]
    have hS : rdq(V, X.cpu.gpr.rax + 18446744073709551600#64) = σ' (l + 1) := by
      rw [hra, a16m]
      exact (hT (l + 1) (by omega)).1
    refine (c_1568 prof fb).run c hfs hin _ hK hA hrip
      (vc_1568e (c := H) (d := E - (l + 2)) (by omega) (by rw [hgx]) (by rw [hgx]; exact hrcx) hS
        (by rw [hra, a16m]; exact foot8 hPE (by omega) hWd)
        (by rw [hra]; exact foot8 hPE (by omega) hWl)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
    have hr16 : X.cpu.gpr.rax + 16#64 = g₃.r14 + BitVec.ofNat 64 (16 * H) := by
      have e := a16 g₃.r14 (l + 2)
      rw [show l + 2 + 1 = H by omega] at e
      rw [hra]
      exact e
    rw [ite_eq_left (show E - (l + 2) = H + 1 by omega)] at hrY
    rw [hr16, show E - (l + 2) - 1 = H by omega] at hgY
    rw [hgx] at hgY
    rw [hra] at hAY
    have hv : σ' (l + 1) = pt1 σ ℓ (l + 2) := by
      rw [hD.1 (l + 1) (by omega), pt1_ss, ite_eq_left (show l % 2 = 1 by omega)]
    obtain ⟨hS1', hS0'⟩ := Same.tab hPE (m := 16 * (l + 2)) (by omega) hS1 hS0 (σ' (l + 1))
    have hD' := hD.st hv
    rw [show l + 2 + 1 = H by omega] at hD'
    exact k Y t' _ _ _ hKY hAY hrY (hgY.trans rfl) (hT.stS hPE (by omega) _) hD' hS1' hS0'
  | succ m ih =>
    intro i hi hi2 X t V w σ' hK hA hrip hgx hT hD hS1 hS0
    obtain ⟨l, rfl⟩ : ∃ l, i = l + 2 := ⟨i - 2, by omega⟩
    have hra : X.cpu.gpr.rax = g₃.r14 + BitVec.ofNat 64 (16 * (l + 2)) := by rw [hgx]
    have hr16 : X.cpu.gpr.rax + 16#64 = g₃.r14 + BitVec.ofNat 64 (16 * (l + 2 + 1)) := by
      rw [hra]
      exact a16 _ _
    have hSt := fun v => Same.tab hPE (m := 16 * (l + 2)) (by omega) hS1 hS0 v
    by_cases hl : l % 2 = 1
    · -- `i` odd: `str[i] = str[i-1]`
      have hS : rdq(V, X.cpu.gpr.rax + 18446744073709551600#64) = σ' (l + 1) := by
        rw [hra, a16m]
        exact (hT (l + 1) (by omega)).1
      refine (c_1568 prof fb).run c hfs hin _ hK hA hrip
        (vc_1568e (c := H) (d := E - (l + 2)) (by omega) (by rw [hgx]) (by rw [hgx]; exact hrcx) hS
          (by rw [hra, a16m]; exact foot8 hPE (by omega) hWd)
          (by rw [hra]; exact foot8 hPE (by omega) hWl)) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      rw [ite_eq_right (show ¬E - (l + 2) = H + 1 by omega)] at hrY
      rw [hr16, show E - (l + 2) - 1 = E - (l + 2 + 1) by omega] at hgY
      rw [hgx] at hgY
      rw [hra] at hAY
      have hv : σ' (l + 1) = pt1 σ ℓ (l + 2) := by
        rw [hD.1 (l + 1) (by omega), pt1_ss, ite_eq_left hl]
      exact ih (l + 2 + 1) (by omega) (by omega) Y t' _ _ _ hKY hAY hrY (hgY.trans rfl)
        (hT.stS hPE (by omega) _) (hD.st hv) (hSt _).1 (hSt _).2
    · -- `i` even: `str[i] = len[i-2] + str[i-2]`
      have hL : rdq(V, X.cpu.gpr.rax + 18446744073709551592#64) = ℓ l := by
        rw [hra, a24m]
        exact (hT l (by omega)).2
      have hS : rdq(V, X.cpu.gpr.rax + 18446744073709551584#64) = σ' l := by
        rw [hra, a32m]
        exact (hT l (by omega)).1
      refine (c_1568 prof fb).run c hfs hin _ hK hA hrip
        (vc_1568o (c := H) (d := E - (l + 2)) (by omega) (by rw [hgx]) (by rw [hgx]; exact hrcx) hL hS
          (by rw [hra, a24m]; exact foot8 hPE (by omega) hWd)
          (by rw [hra, a32m]; exact foot8 hPE (by omega) hWd)
          (by rw [hra]; exact foot8 hPE (by omega) hWl)) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      rw [hr16, show E - (l + 2) - 1 = E - (l + 2 + 1) by omega] at hgY
      rw [hgx] at hgY
      rw [hra] at hAY
      have hv : ℓ l + σ' l = pt1 σ ℓ (l + 2) := by
        rw [hD.1 l (by omega), pt1_ss, ite_eq_right hl]
      exact ih (l + 2 + 1) (by omega) (by omega) Y t' _ _ _ hKY hAY hrY (hgY.trans rfl)
        (hT.stS hPE (by omega) _) (hD.st hv) (hSt _).1 (hSt _).2

end FV7z.Hwc
