import FV7z.Lemmas.BlkOps5
/-!
# `movsx r64, word [m]` (PLAN.md §M, M1)

An instruction of 7-Zip's `ConvertPropVariantToShortString` (measured with `tools/blk_gen.py`: `movswq 0x8(%rdi),
%rdi`, a `VT_I2` value as the argument of `ConvertInt64ToString`).

- `Op.ldsxw`, `OpI.ldsxw`: `movsx r64, word [m]` as an `Op` of `Blk.lean`, as `Op.ldsxq` (`BlkOps26.lean`) of 16 bits.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile}

/-- `movsx r64, word [m]`. -/
def Op.ldsxw (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load 2 (fun g => eaG g b i sc d) (fun g _ bs => wr g r ((ofBytesLE 16 bs).signExtend 64)) fun _ f _ fl => fl = rfz f

theorem OpI.ldsxw {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .movsx 64 [gr 64 r, .mem (mg b i sc d 16)] len) (Op.ldsxw r b i sc d) := by
  dsimp only [Op.ldsxw, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.movsx, movSigned, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Opd.width, Nat.reduceDiv]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end FV7z
