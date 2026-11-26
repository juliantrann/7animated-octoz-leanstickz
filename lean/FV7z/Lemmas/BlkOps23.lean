import FV7z.Lemmas.BlkOps2
/-!
# `or r8, x`, `not r64` (PLAN.md §M, M1)

7-Zip's `DoesNameContainWildcard` joins two `sete` results with `or al, cl`: `Op.or8`, as `Op.xor8`
(`FV7z/Lemmas/SpFs.lean`) with `|||`, the low byte written and the flags of the result. `ConvertStringToUInt64`
checks for overflow with `not rdx`: `Op.not64`, as `Op.not32` (`FV7z/Lemmas/BlkOps20.lean`) at 64 bits.
-/
namespace FV7z
open ZellicX86 Decode

/-- `or r8, x`. -/
def Op.or8 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wrLo g r (gv g 8 r ||| x.val 8 g)) fun g f fl => LogF f (gv g 8 r ||| x.val 8 g) fl

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpI.or8 {r len : Nat} (x : Src) :
    OpI prof (mk .or 8 [gr 8 r, x.opd 8] len) (Op.or8 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, ⟨_, rfl⟩, rfl, rfl, rfl⟩

/-- `not r64`: no flags change. -/
def Op.not64 (r : Nat) : Op := .reg (fun g _ => wr g r (~~~ gv g 64 r)) fun _ f fl => fl = rfz f

theorem OpI.not64 {r len : Nat} : OpI prof (mk .not 64 [gr 64 r] len) (Op.not64 r) := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end

end FV7z
