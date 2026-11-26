/-!
# `largebin_index_64` and the flag facts of `Im7` (PLAN.md G3, `malloc`)

- `lix m`: glibc 2.31's `largebin_index_64 (m)` for `m > 1023`, the way `_int_malloc` computes it (`cmp $0xbffff`,
  `cmovb` at 2192 for `m >> 15 < 5`).
- `dlt`, `dlt'`, `deq`: the flags of a comparison of a register with a constant in the form `simp` leaves them, from
  bounds on `toNat`; `shr_nat`: a shift as a division.
-/
namespace FV7z.Im7

/-- `largebin_index_64 m` for `1024 ≤ m`. -/
def lix (m : Nat) : Nat :=
  if m / 64 ≤ 48 then 48 + m / 64 else if m / 512 ≤ 20 then 91 + m / 512 else if m / 4096 ≤ 10 then 110 + m / 4096
  else if m / 32768 < 5 then 119 + m / 32768 else if m ≤ 786431 then 124 + m / 262144 else 126

theorem lix_ge {m : Nat} (h : 4112 < m) : 97 ≤ lix m := by
  unfold lix; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem lix_le (m : Nat) : lix m ≤ 126 ∨ m / 64 ≤ 48 := by
  unfold lix; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem shr_nat (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem dlt {x : BitVec 64} {c : Nat} (h : c ≤ x.toNat) : decide (x.toNat < c) = false :=
  decide_eq_false (by omega)

theorem dlt' {x : BitVec 64} {c : Nat} (h : x.toNat < c) : decide (x.toNat < c) = true := decide_eq_true h

theorem deq {x : BitVec 64} {c : Nat} (h : x.toNat ≠ c) (hc : c < 2 ^ 64 := by decide) :
    decide (x = BitVec.ofNat 64 c) = false :=
  decide_eq_false (fun e => h (by rw [e, BitVec.toNat_ofNat]; omega))

theorem deq' {x : BitVec 64} {c : Nat} (h : x.toNat = c) : decide (x = BitVec.ofNat 64 c) = true :=
  decide_eq_true (by apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat]; omega)

/-- The flags of `cmp x, c; jbe` taken: `x ≤ c`. -/
theorem dle {x : BitVec 64} {c : Nat} (h : x.toNat ≤ c) :
    (decide (x.toNat < c) || decide (x = BitVec.ofNat 64 c)) = true := by
  by_cases e : x.toNat = c
  · rw [deq' e, Bool.or_true]
  · rw [dlt' (by omega), Bool.true_or]

end FV7z.Im7
