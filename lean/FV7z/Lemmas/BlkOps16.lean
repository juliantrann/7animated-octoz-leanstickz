import FV7z.Lemmas.BlkOps15
/-!
# `bt r64, r64` (PLAN.md G3, startup)

The form `_dl_important_hwcaps` has beside those of the earlier `BlkOps` files:

- `Op.bt64`: `bt r64, r64` (`OpI.bt64`): `CF` is the bit of `r` that `q` names (modulo 64), the registers kept; the
  other flags are what the model leaves (`OF`, `SF`, `AF`, `PF` undefined, `ZF` by vendor).
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `bt r64, r64`. -/
def bt64 (r q : Nat) : Op :=
  .reg (fun g _ => g) fun g _ fl => fl.cf = (gv g 64 r).getLsbD ((gv g 64 q).toNat % 64)

end Op

section
variable {prof : Profile}

theorem OpI.bt64 {r q len : Nat} : OpI prof (mk (.bit .bt) 64 [gr 64 r, gr 64 q] len) (Op.bt64 r q) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end

end FV7z
