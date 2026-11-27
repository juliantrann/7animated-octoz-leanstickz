import FV7z.Lemmas.Wp
/-!
# The 24-byte frame of `push r12; push rbx; sub rsp, 8` (PLAN.md §M, M1)

Functions that save `r12` and `rbx` and keep `rsp` 16-aligned with `sub rsp, 8` (`CPropVariant::operator=(UInt32)`
at `0x457430`, `FV7z/Pvu`; `ExtractFileNameFromPath` at `0x4528f0`, `FV7z/Efn`): `s` the entry's `rsp`, the saved
`r12` at `s - 8`, `rbx` at `s - 16`, a `call`'s return address at `s - 32`. The address facts, one small `bv_omega`
lemma each, to `rw` before `omega` (never `bv_omega` in a big context).
-/
namespace FV7z.Fr24

theorem pe16 (s : BitVec 64) : s - 8 - 8 = s - 16 := by bv_omega
theorem pe32 (s : BitVec 64) : s - 8 - 8 - 8#64 - 8 = s - 32 := by bv_omega
theorem peD (s : BitVec 64) : s - 24 - 8 = s - 32 := by bv_omega
theorem peA (s : BitVec 64) : s - 8 - 8 - 8#64 + 8#64 = s - 16 := by bv_omega
theorem peA' (s : BitVec 64) : s - 24 + 8#64 = s - 16 := by bv_omega
theorem peB (s : BitVec 64) : s - 16 + 8 = s - 8 := by bv_omega
theorem peC (s : BitVec 64) : s - 8 + 8 = s := by bv_omega
theorem pt8 (s : BitVec 64) (h : 32 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem pt16 (s : BitVec 64) (h : 32 ≤ s.toNat) : (s - 16).toNat = s.toNat - 16 := by bv_omega

end FV7z.Fr24
