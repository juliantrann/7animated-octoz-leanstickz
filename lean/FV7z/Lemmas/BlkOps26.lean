import FV7z.Lemmas.BlkOps5
/-!
# `movsx r64, byte [m]` (PLAN.md §M, M1)

An instruction of glibc's `____strtoul_l_internal` (measured with `tools/blk_gen.py`: `movsbq (%r13), %rax`, a
character as the index of a table of the locale).

- `Op.ldsxq`, `OpI.ldsxq`: `movsx r64, byte [m]` as an `Op` of `Blk.lean`, as `Op.ldsxb` (`BlkOps5.lean`) at 64 bits.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile}

/-- `movsx r64, byte [m]`. -/
def Op.ldsxq (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load 1 (fun g => eaG g b i sc d) (fun g _ bs => wr g r ((ofBytesLE 8 bs).signExtend 64)) fun _ f _ fl => fl = rfz f

theorem OpI.ldsxq {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .movsx 64 [gr 64 r, .mem (mg b i sc d 8)] len) (Op.ldsxq r b i sc d) := by
  dsimp only [Op.ldsxq, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.movsx, movSigned, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Opd.width, Nat.reduceDiv]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end FV7z
