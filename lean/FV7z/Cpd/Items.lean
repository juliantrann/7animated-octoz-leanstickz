import FV7z.Cpd.Defs
/-!
# The items of `NCommandLineParser::CParser::~CParser`'s `_switches` (PLAN.md §M, M1)

`_switches` = `b` an array of `CSwitchResult`s of 24 bytes: `ip b i` the item `i`; `ip0`, `ip_m24`, `ip_m8`,
`ip1_m32`, `ip_ne`: its addresses.
-/
open ZellicX86 Decode FV7z
namespace FV7z.Cpd

/-- The item `i` of the array at `b` (24 bytes each). -/
abbrev ip (b : Addr) (i : Nat) : Addr := b + BitVec.ofNat 64 (24 * i)

theorem ip0 (b : Addr) : ip b 0 = b := by
  show b + BitVec.ofNat 64 (24 * 0) = b
  rw [Nat.mul_zero]
  exact BitVec.add_zero b

theorem ip_m24 (b : Addr) (i : Nat) : ip b (i + 1) - 24#64 = ip b i := by
  bv_omega

theorem ip_m8 (b : Addr) (i : Nat) : ip b (i + 1) + 18446744073709551608#64 = ip b i + 16#64 := by
  bv_omega

theorem ip1_m32 (b : Addr) : ip b 1 + 18446744073709551584#64 = b + 18446744073709551608#64 := by
  bv_omega

theorem ip_ne (b : Addr) {i : Nat} (h0 : 0 < i) (h : 24 * i < 18446744073709551616) : b ≠ ip b i := by
  bv_omega

end FV7z.Cpd
