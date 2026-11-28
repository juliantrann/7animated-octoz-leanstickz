import FV7z.Lemmas.BlkOps2
/-!
# `movsx r32, r8` (PLAN.md §M, M1)

An instruction of 7-Zip's `CParser::ParseString` (measured with `tools/blk_gen.py`: `movsx esi, al`, the post char
as the argument of `FindCharPosInString`).

- `Op.sxb32`, `OpI.sxb32`: `movsx r32, r8` as an `Op` of `Blk.lean`, as `Op.sxb16` (`BlkOps24.lean`) of 32 bits: the
  register zero-extended from bit 32 up; no flags change.
-/
namespace FV7z
open ZellicX86 Decode

/-- `movsx r32, r8`: no flags change. -/
def Op.sxb32 (r q : Nat) : Op :=
  .reg (fun g _ => wr g r ((gv g 8 q).signExtend 32)) fun _ f fl => fl = rfz f

variable {prof : Profile}

theorem OpI.sxb32 {r q len : Nat} : OpI prof (mk .movsx 32 [gr 32 r, gr 8 q] len) (Op.sxb32 r q) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end FV7z
