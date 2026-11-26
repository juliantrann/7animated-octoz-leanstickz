import FV7z.Mga.Vc
import FV7z.Strlen.Entry
/-!
# `_int_memalign`: the arithmetic of the aligned chunk (PLAN.md §M, M1)

`alignment` a power of two `2 ^ k` (`4 ≤ k < 64`), `m` the memory of the chunk `_int_malloc` gave (16-aligned, not
aligned to `alignment`), `p = m - 16`:

- `bS`: the stack pointer of the body (`S - 56`); `bS_toNat`.
- `neg_pow`, `and_negp`: `x & -alignment` rounds down.
- `np m al`: `newp`, the first aligned spot `brk` from `m` (as a chunk), one `alignment` on when `brk - p` is below
  `MINSIZE`; `brk_ok`: with `A` the first multiple of `alignment` above `m`, `brk = A - 16` and `A - m` between 16
  and `alignment - 16`, a multiple of 16; `np_ok`: `leadsize = newp - p` between 32 and `alignment + 16`, a
  multiple of 16, and `newp + 16` aligned.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mga

/-- The stack pointer of the body: six pushes and `sub rsp, 8` under `S`. -/
abbrev bS (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 8#64

theorem bS_toNat {S : Addr} (hS : 80 ≤ S.toNat) : (bS S).toNat = S.toNat - 56 := by
  obtain ⟨-, -, -, -, -, e6⟩ := Mcn.fr_e6 hS
  have e7 := Prepare.toNat_sub8 (a := S - 8 - 8 - 8 - 8 - 8 - 8) (by rw [e6]; omega)
  show (S - 8 - 8 - 8 - 8 - 8 - 8 - 8).toNat = _
  rw [e7, e6]; omega

theorem neg_pow {al : Addr} {k : Nat} (hk : k < 64) (ha : al.toNat = 2 ^ k) :
    (0 - al).toNat = (2 ^ (64 - k) - 1) <<< k := by
  have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
  have h2 : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have h3 : 2 ^ (64 - k) * 2 ^ k = 2 ^ 64 := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  rw [BitVec.toNat_sub, ha, Nat.shiftLeft_eq, Nat.sub_mul, h3, Nat.one_mul, show (0 : Addr).toNat = 0 from rfl, Nat.add_zero,
    Nat.mod_eq_of_lt (by omega)]

/-- `x & -alignment` rounds down. -/
theorem and_negp {al : Addr} {k : Nat} (hk : k < 64) (ha : al.toNat = 2 ^ k) (x : Addr) :
    (x &&& (0 - al)).toNat = x.toNat / 2 ^ k * 2 ^ k := by
  rw [BitVec.toNat_and, neg_pow hk ha]
  exact Strlen.nat_and_hi _ k (by omega) x.isLt

/-- `brk` from `m`: with `A` the first multiple of `alignment` above `m`, `brk = A - 16`, `A - m` a multiple of 16
from 16 to `alignment - 16`. -/
theorem brk_ok {m al : Addr} {k : Nat} (hk : k < 64) (h4 : 4 ≤ k) (ha : al.toNat = 2 ^ k) (h16 : 16 ≤ m.toNat)
    (hm : m.toNat % 16 = 0) (hn : m.toNat % 2 ^ k ≠ 0) (hfit : m.toNat + 2 ^ k < 2 ^ 64) :
    ∃ A : Nat, (brk m al).toNat = A - 16 ∧ A % 2 ^ k = 0 ∧ A % 16 = 0 ∧ m.toNat + 16 ≤ A ∧
      A + 16 ≤ m.toNat + 2 ^ k := by
  have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
  have hd : 16 ∣ 2 ^ k := by
    have := Nat.pow_dvd_pow 2 h4
    simpa using this
  have hs : (m + al + 18446744073709551615#64).toNat = m.toNat + 2 ^ k - 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, ha, show (18446744073709551615#64).toNat = 2 ^ 64 - 1 from rfl]
    omega
  have hq := Nat.div_add_mod (m.toNat + 2 ^ k - 1) (2 ^ k)
  have hr := Nat.mod_lt (m.toNat + 2 ^ k - 1) h1
  have hA : (m.toNat + 2 ^ k - 1) / 2 ^ k * 2 ^ k % 2 ^ k = 0 := Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left _ _)
  have hA16 : (m.toNat + 2 ^ k - 1) / 2 ^ k * 2 ^ k % 16 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd (Nat.dvd_mul_left _ _))
  have hk16 : 2 ^ k % 16 = 0 := Nat.mod_eq_zero_of_dvd hd
  have hb : (m + al + 18446744073709551615#64 &&& 0 - al).toNat = (m.toNat + 2 ^ k - 1) / 2 ^ k * 2 ^ k := by
    rw [and_negp hk ha, hs]
  rw [Nat.mul_comm] at hq
  generalize (m.toNat + 2 ^ k - 1) / 2 ^ k * 2 ^ k = A at hq hA hA16 hb
  generalize (m.toNat + 2 ^ k - 1) % 2 ^ k = R at hq hr
  have hne : A ≠ m.toNat := fun e => hn (by rw [← e]; exact hA)
  refine ⟨A, ?_, hA, hA16, ?_, ?_⟩
  · show ((m + al + 18446744073709551615#64 &&& 0 - al) - 16#64).toNat = _
    rw [BitVec.toNat_sub, hb, show (16#64).toNat = 16 from rfl]
    omega
  · omega
  · omega

/-- `newp`: `brk`, or `brk + alignment` when `brk - p` (`p = m - 16`) is below `MINSIZE`. -/
def np (m al : Addr) : Addr :=
  if (brk m al - (m + 18446744073709551600#64)).toNat ≤ 31 then brk m al + al else brk m al

/-- `newp`: `leadsize = newp - p` from 32 to `alignment + 16`, a multiple of 16, `newp + 16` aligned. -/
theorem np_ok {m al : Addr} {k : Nat} (hk : k < 64) (h4 : 4 ≤ k) (ha : al.toNat = 2 ^ k) (h16 : 16 ≤ m.toNat)
    (hm : m.toNat % 16 = 0) (hn : m.toNat % 2 ^ k ≠ 0) (hfit : m.toNat + 2 ^ k + 2 ^ k < 2 ^ 64) :
    ∃ L : Nat, (np m al).toNat = m.toNat - 16 + L ∧ (np m al - (m + 18446744073709551600#64)).toNat = L ∧
      32 ≤ L ∧ L ≤ 2 ^ k + 16 ∧ L % 16 = 0 ∧ ((np m al).toNat + 16) % 2 ^ k = 0 := by
  obtain ⟨A, hb, hA, hA16, h1, h2⟩ := brk_ok hk h4 ha h16 hm hn (by omega)
  have hk16 : 2 ^ k % 16 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using Nat.pow_dvd_pow 2 h4)
  have hp : (m + 18446744073709551600#64).toNat = m.toNat - 16 := by
    rw [BitVec.toNat_add, show (18446744073709551600#64).toNat = 2 ^ 64 - 16 from rfl]
    omega
  have hd : (brk m al - (m + 18446744073709551600#64)).toNat = A - m.toNat := by
    rw [BitVec.toNat_sub, hb, hp]
    omega
  unfold np
  by_cases hc : (brk m al - (m + 18446744073709551600#64)).toNat ≤ 31
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    have e : (brk m al + al).toNat = A - 16 + 2 ^ k := by
      rw [BitVec.toNat_add, hb, ha]
      omega
    refine ⟨A - m.toNat + 2 ^ k, by rw [e]; omega, ?_, by omega, by omega, by omega, ?_⟩
    · rw [BitVec.toNat_sub, e, hp]
      omega
    · rw [e, show A - 16 + 2 ^ k + 16 = A + 2 ^ k by omega, Nat.add_mod_right, hA]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    refine ⟨A - m.toNat, by rw [hb]; omega, hd, by omega, by omega, by omega, ?_⟩
    rw [hb, show A - 16 + 16 = A by omega, hA]

end FV7z.Mga
