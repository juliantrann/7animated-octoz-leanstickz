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

/-- The second half: 1632 with `rcx = k` (`str[i]`, `i = E - k`) to the `ret` (1681), `*Q = len[0]`. -/
theorem half2 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    {T Q r8v : Addr} (hHE : H = 4 ∧ E = 8 ∨ H = 8 ∧ E = 16) (hPE : g₃.r14.toNat + 16 * E ≤ 2 ^ 64)
    (hW : ∀ a : Addr, g₃.r14.toNat ≤ a.toNat → a.toNat < g₃.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a)
    (hfr : g₃.r14.toNat + 16 * E ≤ (g₃.rbp + 18446744073709551464#64).toNat)
    (hfr' : (g₃.rbp + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64)
    (hQ₀ : rdq(V₀, g₃.rbp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hfQ : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551504#64) i))
    (hf0 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551576#64) i))
    (hf1 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551584#64) i))
    (hf2 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551592#64) i))
    (hf3 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551600#64) i))
    (hf4 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551608#64) i))
    (hf5 : ∀ i < 8, Foot F.data (Addr.add g₃.rbp i))
    (k : ∀ Y t' (W : Addr → Byte) (σF : Nat → Addr), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (ℓ 0) 8)) → Y.cpu.rip = hwc_at.add 1681 →
      Y.cpu.gpr = { g₃ with
        rax := g₃.r14, rcx := 0#64, rdx := 0#64 - BitVec.ofNat 64 (16 * H),
        rsi := g₃.r14 + BitVec.ofNat 64 (16 * E), rdi := T + 1#64, r8 := r8v,
        rbx := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551576#64),
        r12 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551584#64),
        r13 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551592#64),
        r14 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551600#64),
        r15 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551608#64),
        rbp := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp), rsp := g₃.rbp + 8#64 } →
      Tab W g₃.r14 E σF ℓ → (∀ j < E, σF j = pt σ ℓ H T j) → Same V₀ W (g₃.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ W 0 g₃.r14.toNat → GoG prof L o gev gP gE Y t') :
    ∀ (kk : Nat), 1 ≤ kk → kk ≤ H → ∀ (X : State) (t : Nat) (V : Addr → Byte) (a : Addr) (σ' : Nat → Addr),
      KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1632 →
      X.cpu.gpr = { g₃ with
        rax := a, rcx := BitVec.ofNat 64 kk, rdx := 0#64 - BitVec.ofNat 64 (16 * H),
        rsi := g₃.r14 + BitVec.ofNat 64 (16 * (E - kk)), rdi := T + 1#64, r8 := r8v } →
      Tab V g₃.r14 E σ' ℓ → PD σ (pt σ ℓ H T) (E - kk) σ' → Same V₀ V (g₃.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V 0 g₃.r14.toNat → GoG prof L o gev gP gE X t := by
  have hWl := fun a h1 h2 => (hW a h1 h2).1
  have hWd := fun a h1 h2 => (hW a h1 h2).2
  intro kk
  induction kk with
  | zero => intro h1; exact absurd h1 (by omega)
  | succ kk ih =>
    intro h1 h2 X t V a σ' hK hA hrip hgx hT hD hS1 hS0
    have hrsi0 : X.cpu.gpr.rsi = g₃.r14 + BitVec.ofNat 64 (16 * (E - (kk + 1))) := by rw [hgx]
    have hrdi0 : X.cpu.gpr.rdi = T + 1#64 := by rw [hgx]
    have hrd : X.cpu.gpr.rsi + X.cpu.gpr.rdx = g₃.r14 + BitVec.ofNat 64 (16 * (E - (kk + 1) - H)) := by
      have e := aH g₃.r14 (E - (kk + 1) - H) H
      rw [show E - (kk + 1) - H + H = E - (kk + 1) by omega] at e
      rw [hgx]
      exact e
    have hr16 : X.cpu.gpr.rsi + 16#64 = g₃.r14 + BitVec.ofNat 64 (16 * (E - kk)) := by
      have e := a16 g₃.r14 (E - (kk + 1))
      rw [show E - (kk + 1) + 1 = E - kk by omega] at e
      rw [hrsi0]
      exact e
    have hX : rdq(V, X.cpu.gpr.rsi + X.cpu.gpr.rdx) = σ' (E - (kk + 1) - H) := by
      rw [hrd]
      exact (hT _ (by omega)).1
    have hf : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rdx) i) := by
      rw [hrd]
      exact foot8 hPE (by omega) hWd
    have hs : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsi i) := by
      rw [hrsi0]
      exact foot8 hPE (by omega) hWl
    have hv : σ' (E - (kk + 1) - H) + (T + 1#64) = pt σ ℓ H T (E - (kk + 1)) := by
      rw [hD.1 _ (by omega)]
      unfold pt
      rw [ite_eq_left (show E - (kk + 1) - H < H by omega), ite_eq_right (show ¬E - (kk + 1) < H by omega)]
    have hSt := Same.tab hPE (m := 16 * (E - (kk + 1))) (by omega) hS1 hS0 (σ' (E - (kk + 1) - H) + (T + 1#64))
    have hD' := hD.st hv
    rw [show E - (kk + 1) + 1 = E - kk by omega] at hD'
    by_cases h0 : kk = 0
    · -- the last: `*Q = len[0]`, the frame popped
      subst h0
      have hrbp0 : X.cpu.gpr.rbp = g₃.rbp := by rw [hgx]
      have hr140 : X.cpu.gpr.r14 = g₃.r14 := by rw [hgx]
      have hT2 := hT.stS hPE (j := E - (0 + 1)) (by omega) (σ' (E - (0 + 1) - H) + (T + 1#64))
      refine (c_1632 prof fb).run c hfs hin _ hK hA hrip
        (vc_1632e (X := σ' (E - (0 + 1) - H)) (M := ℓ 0) (Q := Q) (by rw [hgx]; try rfl) hX
          (by rw [hrsi0, hrdi0, hr140]; exact (hT2 0 (by omega)).2)
          (by
            rw [hrsi0, hrdi0, hrbp0, hSt.1.rdq (by rw [off70 hfr']; omega) (by rw [off70 hfr']; omega)
              (by rw [off70 hfr']; omega)]
            exact hQ₀)
          rfl rfl rfl rfl rfl rfl hf hs
          (by rw [hr140]; exact foot8 (m := 8) hPE (by omega) hWd)
          (by rw [hrbp0]; exact hfQ) hsQ (by rw [hrbp0]; exact hf0) (by rw [hrbp0]; exact hf1)
          (by rw [hrbp0]; exact hf2) (by rw [hrbp0]; exact hf3) (by rw [hrbp0]; exact hf4)
          (by rw [hrbp0]; exact hf5)) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      rw [hr16] at hgY
      rw [hrsi0, hrdi0, hrbp0, hr140] at hgY
      rw [hgx] at hgY
      rw [hrsi0, hrdi0] at hAY
      exact k Y t' _ _ hKY hAY hrY (hgY.trans rfl) hT2 (fun j hj => hD'.1 j (by omega)) hSt.1 hSt.2
    · -- the next entry
      refine (c_1632 prof fb).run c hfs hin _ hK hA hrip
        (vc_1632l (k := kk + 1) (by omega) (by omega) (by rw [hgx]) hX hf hs) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
      rw [hr16, Nat.add_sub_cancel] at hgY
      rw [hgx] at hgY
      rw [hrsi0, hrdi0] at hAY
      exact ih (by omega) (by omega) Y t' _ _ _ hKY hAY hrY (hgY.trans rfl) (hT.stS hPE (by omega) _) hD'
        hSt.1 hSt.2

/-- 1602 and 1612 (`rsi = P + 16 H`, `rdx = -16 H`, `rdi = T + 1`), then the second half to 1681. -/
theorem mid (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L hwc_at hwc)
    {T Q : Addr} (hHE : H = 4 ∧ E = 8 ∨ H = 8 ∧ E = 16) (hrcx : g₃.rcx = BitVec.ofNat 64 H)
    (hr8 : g₃.r8 = BitVec.ofNat 64 (E - 2)) (hrsi : g₃.rsi = g₃.r14 + 32#64)
    (hPE : g₃.r14.toNat + 16 * E ≤ 2 ^ 64)
    (hW : ∀ a : Addr, g₃.r14.toNat ≤ a.toNat → a.toNat < g₃.r14.toNat + 16 * E → Foot Wl a ∧ Foot F.data a)
    (hfr : g₃.r14.toNat + 16 * E ≤ (g₃.rbp + 18446744073709551464#64).toNat)
    (hfr' : (g₃.rbp + 18446744073709551464#64).toNat + 160 ≤ 2 ^ 64)
    (hq₀ : rdd(V₀, g₃.rbp + 18446744073709551512#64) = BitVec.ofNat 32 H)
    (hT₀ : rdq(V₀, g₃.rbp + 18446744073709551536#64) = T)
    (hfq : ∀ i < 4, Foot F.data (Addr.add (g₃.rbp + 18446744073709551512#64) i))
    (hfT : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551536#64) i))
    (hQ₀ : rdq(V₀, g₃.rbp + 18446744073709551504#64) = Q) (hsQ : ∀ i < 8, Foot Wl (Addr.add Q i))
    (hfQ : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551504#64) i))
    (hf0 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551576#64) i))
    (hf1 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551584#64) i))
    (hf2 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551592#64) i))
    (hf3 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551600#64) i))
    (hf4 : ∀ i < 8, Foot F.data (Addr.add (g₃.rbp + 18446744073709551608#64) i))
    (hf5 : ∀ i < 8, Foot F.data (Addr.add g₃.rbp i))
    (k : ∀ Y t' (W : Addr → Byte) (σF : Nat → Addr), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst W Q (toBytesLE (ℓ 0) 8)) → Y.cpu.rip = hwc_at.add 1681 →
      Y.cpu.gpr = { g₃ with
        rax := g₃.r14, rcx := 0#64, rdx := 0#64 - BitVec.ofNat 64 (16 * H),
        rsi := g₃.r14 + BitVec.ofNat 64 (16 * E), rdi := T + 1#64, r8 := BitVec.ofNat 64 (16 * (E - 2 - H)),
        rbx := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551576#64),
        r12 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551584#64),
        r13 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551592#64),
        r14 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551600#64),
        r15 := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp + 18446744073709551608#64),
        rbp := rdq(Vst W Q (toBytesLE (ℓ 0) 8), g₃.rbp), rsp := g₃.rbp + 8#64 } →
      Tab W g₃.r14 E σF ℓ → (∀ j < E, σF j = pt σ ℓ H T j) → Same V₀ W (g₃.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ W 0 g₃.r14.toNat → GoG prof L o gev gP gE Y t') :
    ∀ (X : State) (t : Nat) (V : Addr → Byte) (w : Addr) (σ' : Nat → Addr), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = hwc_at.add 1602 →
      X.cpu.gpr = { g₃ with
        rax := g₃.r14 + BitVec.ofNat 64 (16 * H), rdx := BitVec.ofNat 64 H, rdi := w } →
      Tab V g₃.r14 E σ' ℓ → PD σ (pt1 σ ℓ) H σ' → Same V₀ V (g₃.r14.toNat + 16 * E) (2 ^ 64) →
      Same V₀ V 0 g₃.r14.toNat → GoG prof L o gev gP gE X t := by
  intro X t V w σ' hK hA hrip hgx hT hD hS1 hS0
  have hrs : X.cpu.gpr.rsi + BitVec.ofNat 64 (16 * (E - 2 - H)) = g₃.r14 + BitVec.ofNat 64 (16 * (E - H)) := by
    have e : X.cpu.gpr.rsi = g₃.r14 + 32#64 := by rw [hgx]; exact hrsi
    rw [e, show E - H = H by omega]
    exact a1602 _ hHE
  refine (c_1602 prof fb).run c hfs hin _ hK hA hrip
    (vc_1602 (c := H) (E := E) hHE (by rw [hgx]; exact hr8) (by rw [hgx]; exact hrcx)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t' hKY hAY hrY hgY -
  rw [hrs] at hgY
  have hrbp : Y.cpu.gpr.rbp = g₃.rbp := by rw [hgY, hgx]
  have hq : rdd(V, Y.cpu.gpr.rbp + 18446744073709551512#64) = BitVec.ofNat 32 H := by
    rw [hrbp, hS1.rd (by rw [off68 hfr']; omega) (by rw [off68 hfr']; omega) (by rw [off68 hfr']; omega)]
    exact hq₀
  have hT' : rdq(V, Y.cpu.gpr.rbp + 18446744073709551536#64) = T := by
    rw [hrbp, hS1.rdq (by rw [off50 hfr']; omega) (by rw [off50 hfr']; omega) (by rw [off50 hfr']; omega)]
    exact hT₀
  refine (c_1612 prof fb).run c hfs hin _ hKY hAY hrY
    (vc_1612 (c := H) (T := T) (by omega) hq hT' (by rw [hrbp]; exact hfq) (by rw [hrbp]; exact hfT)) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t'' hKZ hAZ hrZ hgZ -
  rw [hgY, hgx] at hgZ
  refine half2 c hfs hin hHE hPE hW hfr hfr' hQ₀ hsQ hfQ hf0 hf1 hf2 hf3 hf4 hf5 k H (by omega) (Nat.le_refl _)
    Z t'' _ _ σ' hKZ hAZ hrZ (hgZ.trans (by rw [← hrcx]; try rfl)) hT hD.half hS1 hS0

end FV7z.Hwc
