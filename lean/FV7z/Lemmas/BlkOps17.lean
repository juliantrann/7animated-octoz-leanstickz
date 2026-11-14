import FV7z.Lemmas.BlkOps16
/-!
# `mul r64` (PLAN.md G3, startup)

The form `_dl_init_paths` has beside those of the earlier `BlkOps` files:

- `Op.mul64`: `mul r64` (`OpI.mul64`): the 128-bit product of `rax` and `r`, its low half to `rax`, its high half to
  `rdx` (the division by 80 of `round_size`, by a multiply with `0xcccccccccccccccd`). The flags: what the model
  leaves (`CF`, `OF` whether the high half is not 0, the others undefined); nothing is said of them here.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- The 128-bit product `mul r64` takes: `rax` times `r`. -/
abbrev mulp (g : Gprs) (q : Nat) : BitVec 128 := (gv g 64 0).setWidth 128 * (gv g 64 q).setWidth 128

/-- `mul r64`. -/
def mul64 (q : Nat) : Op :=
  .reg (fun g _ => wr (wr g 0 ((mulp g q).setWidth 64)) 2 ((mulp g q).extractLsb' 64 64)) fun _ _ _ => True

end Op

section
variable {prof : Profile}

theorem OpI.mul64 {q len : Nat} : OpI prof (mk .mul 64 [gr 64 q] len) (Op.mul64 q) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, trivial, rfl, rfl, rfl⟩

end

end FV7z
