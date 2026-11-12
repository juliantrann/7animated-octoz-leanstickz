import FV7z.Lemmas.BlkOps13
/-!
# `movzx r32, r8` (PLAN.md G3, `malloc`)

The form `_int_malloc` has on its second call beside those of the earlier `BlkOps` files:

- `Op.zxr`: `movzx r32, r8` of a low byte (`OpI.zxr`), after a `setcc`: the bit of `NON_MAIN_ARENA` in the size of
  the chunk cut from the top.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `movzx r32, r8`: the low byte of `q`, zero-extended. -/
def zxr (r q : Nat) : Op := .reg (fun g _ => wr g r ((gv g 8 q).setWidth 32)) fun _ f fl => fl = rfz f

end Op

variable {prof : Profile}

theorem OpI.zxr {r q len : Nat} : OpI prof (mk .movzx 32 [gr 32 r, gr 8 q] len) (Op.zxr r q) :=
  fun _ _ _ htf hdec => ⟨_, _, movzx_rr8 htf hdec, rfl, rfl, rfl, rfl⟩

end FV7z
