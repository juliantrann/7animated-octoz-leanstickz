import FV7z.Lemmas.BlkOps14
/-!
# `movsxd r64, r32` (PLAN.md G3, startup)

The form `_dl_get_origin` has beside those of the earlier `BlkOps` files:

- `Op.sxr`: `movsxd r64, r32` (`OpI.sxr`): the length of the directory part, an `int`, as `malloc`'s and `mempcpy`'s
  argument.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `movsxd r64, r32`. -/
def sxr (r q : Nat) : Op := .reg (fun g _ => wr g r ((gv g 32 q).signExtend 64)) fun _ f fl => fl = rfz f

end Op

section
variable {prof : Profile}

theorem OpI.sxr {r q len : Nat} : OpI prof (mk .movsxd 64 [gr 64 r, gr 32 q] len) (Op.sxr r q) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end

end FV7z
