import FV7z.Lemmas.BlkOps14
/-!
# `cmp r16, x` (PLAN.md §M, M1)

7-Zip's `CPropVariant::~CPropVariant` tests the 16-bit type tag in `ax` with `cmp ax, 7` and `cmp ax, 0x36`.

- `OpI.cmp16`: `cmp r16, x` (`Op.cmp 16`), as `OpI.test16` (`FV7z/Lemmas/BlkOps14.lean`) for `cmp`.
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile}

theorem OpI.cmp16 {r len : Nat} (x : Src) :
    OpI prof (mk .cmp 16 [gr 16 r, x.opd 16] len) (Op.cmp 16 r x) := fun s o t htf hdec => by
  cases x <;> exact ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end

end FV7z
