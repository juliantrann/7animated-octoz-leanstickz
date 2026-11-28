import FV7z.Cpd.Defs
/-!
# The items of `NCommandLineParser::CParser::~CParser`'s `_switches` (PLAN.md §M, M1)

`_switches` = `b` an array of `CSwitchResult`s of 24 bytes: `ip b i` the item `i`; `ip0`, `ip_s`, `ip_m24`, `ip_m8`,
`ip1_m32`, `ip_ne`: its addresses (by `BitVec.ofNat_add` and constant folds, not `bv_omega`).
-/
open ZellicX86 Decode FV7z
namespace FV7z.Cpd

/-- The item `i` of the array at `b` (24 bytes each). -/
abbrev ip (b : Addr) (i : Nat) : Addr := b + BitVec.ofNat 64 (24 * i)

theorem ip0 (b : Addr) : ip b 0 = b := by
  show b + BitVec.ofNat 64 (24 * 0) = b
  rw [Nat.mul_zero]
  exact BitVec.add_zero b

theorem ip_s (b : Addr) (i : Nat) : ip b (i + 1) = ip b i + 24#64 := by
  show b + BitVec.ofNat 64 (24 * (i + 1)) = b + BitVec.ofNat 64 (24 * i) + 24#64
  rw [Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.add_assoc]

theorem ip_m24 (b : Addr) (i : Nat) : ip b (i + 1) - 24#64 = ip b i := by
  rw [ip_s]
  exact BitVec.add_sub_cancel _ _

theorem ip_m8 (b : Addr) (i : Nat) : ip b (i + 1) + 18446744073709551608#64 = ip b i + 16#64 := by
  have h : (24#64 : BitVec 64) + 18446744073709551608#64 = 16#64 := by decide
  rw [ip_s, BitVec.add_assoc, h]

theorem ip1_m32 (b : Addr) : ip b 1 + 18446744073709551584#64 = b + 18446744073709551608#64 := by
  have h : BitVec.ofNat 64 (24 * 1) + 18446744073709551584#64 = 18446744073709551608#64 := by decide
  show b + BitVec.ofNat 64 (24 * 1) + 18446744073709551584#64 = b + 18446744073709551608#64
  rw [BitVec.add_assoc, h]

theorem ip_ne (b : Addr) {i : Nat} (h0 : 0 < i) (h : 24 * i < 18446744073709551616) : b ≠ ip b i := by
  intro he
  have h1 : BitVec.ofNat 64 (24 * i) = 0#64 := BitVec.add_right_eq_self.1 he.symm
  have h2 : 24 * i % 2 ^ 64 = 0 :=
    (BitVec.toNat_ofNat (24 * i) 64).symm.trans ((congrArg BitVec.toNat h1).trans rfl)
  have h3 : 24 * i < 2 ^ 64 := h
  rw [Nat.mod_eq_of_lt h3] at h2
  omega

end FV7z.Cpd
