import FV7z.Startup.StrAt
/-!
# What `strncmp` returns (PLAN.md G3, `strncmp`)

`Str.NcmpAt` asks of the `eax` a call of `strncmp` returns, for every `m ≤ rdx` with the first `m` bytes of the two
strings equal and not 0: 0 if `m = rdx` or the next bytes are both 0, not 0 if they differ (`NRes`). The
implementation finds the first place `p` where the bytes differ or are 0 (the stop) and returns 0 if `p ≥ rdx`
(`nres_zero`), else the difference of the two bytes at `p` (`nres_at`); the two strings play the same part
(`nres_comm`).
-/
namespace FV7z.Strncmp
open ZellicX86

/-- The bytes at `a` and `b` up to `k` (excluded): equal and not 0. -/
def Same (V : Addr → Byte) (a b : Addr) (k : Nat) : Prop :=
  ∀ i < k, V (Addr.add a i) = V (Addr.add b i) ∧ V (Addr.add a i) ≠ 0

/-- `r` is what `strncmp` of the bytes at `a` and `b`, at most `n`, may return. -/
def NRes (V : Addr → Byte) (a b : Addr) (n : Nat) (r : BitVec 32) : Prop :=
  ∀ m ≤ n, Same V a b m →
    (m = n → r = 0) ∧ (m < n → V (Addr.add a m) = V (Addr.add b m) → V (Addr.add a m) = 0 → r = 0) ∧
    (m < n → V (Addr.add a m) ≠ V (Addr.add b m) → r ≠ 0)

theorem Same.mono {V : Addr → Byte} {a b : Addr} {k k' : Nat} (h : Same V a b k) (hk : k' ≤ k) : Same V a b k' :=
  fun i hi => h i (by omega)

theorem Same.comm {V : Addr → Byte} {a b : Addr} {k : Nat} (h : Same V a b k) : Same V b a k :=
  fun i hi => ⟨(h i hi).1.symm, (h i hi).1 ▸ (h i hi).2⟩

/-- No stop before `n`: 0. -/
theorem nres_zero {V : Addr → Byte} {a b : Addr} {n k : Nat} (h : Same V a b k) (hk : n ≤ k) : NRes V a b n 0 :=
  fun m hm _ => ⟨fun _ => rfl, fun _ _ _ => rfl, fun hmn hne => absurd (h m (by omega)).1 hne⟩

/-- The stop at `p < n`: `r` is 0 just when the bytes at `p` are the same. -/
theorem nres_at {V : Addr → Byte} {a b : Addr} {n p : Nat} {r : BitVec 32} (hp : p < n) (hpre : Same V a b p)
    (hstop : ¬ (V (Addr.add a p) = V (Addr.add b p) ∧ V (Addr.add a p) ≠ 0))
    (hr : r = 0 ↔ V (Addr.add a p) = V (Addr.add b p)) : NRes V a b n r := by
  intro m hm hs
  have hmp : m ≤ p := by
    refine Nat.le_of_not_lt fun h => hstop (hs p h)
  rcases Nat.lt_or_eq_of_le hmp with h | rfl
  · exact ⟨fun h' => absurd h' (by omega), fun _ _ h0 => absurd h0 (hpre m h).2,
      fun _ hne => absurd (hpre m h).1 hne⟩
  · exact ⟨fun h' => absurd h' (by omega), fun _ he _ => hr.2 he, fun _ hne h0 => hne (hr.1 h0)⟩

theorem nres_comm {V : Addr → Byte} {a b : Addr} {n : Nat} {r : BitVec 32} (h : NRes V a b n r) :
    NRes V b a n r := by
  intro m hm hs
  obtain ⟨h1, h2, h3⟩ := h m hm hs.comm
  exact ⟨h1, fun hmn he h0 => h2 hmn he.symm (he ▸ h0), fun hmn hne => h3 hmn (Ne.symm hne)⟩

end FV7z.Strncmp
