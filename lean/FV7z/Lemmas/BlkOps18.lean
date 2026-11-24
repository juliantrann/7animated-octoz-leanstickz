import FV7z.Lemmas.BlkOps17
/-!
# `movzx r32, r16` (PLAN.md §M, constructors)

The form the static constructor `csuTg 70` (the CRC-16 table) has beside those of the earlier `BlkOps` files:

- `Op.zxr16`: `movzx r32, r16` (`OpI.zxr16`): the table's next word kept to 16 bits.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `movzx r32, r16`. -/
def zxr16 (r q : Nat) : Op := .reg (fun g _ => wr g r ((gv g 16 q).setWidth 32)) fun _ f fl => fl = rfz f

end Op

variable {prof : Profile}

theorem OpI.zxr16 {r q len : Nat} : OpI prof (mk .movzx 32 [gr 32 r, gr 16 q] len) (Op.zxr16 r q) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end FV7z
