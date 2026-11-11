import FV7z.Lemmas.BlkOps4
/-!
# `movsx r32, byte [m]` (PLAN.md G3, startup)

An instruction of `_dl_discover_osversion` (measured with `tools/blk_gen.py`: `movsbl (%rdi), %ecx`, the characters
of the kernel's release).

- `Op.ldsxb`, `OpI.ldsxb`: `movsx r32, byte [m]` as an `Op` of `Blk.lean`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile}

/-- `movsx r32, byte [m]`. -/
def Op.ldsxb (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load 1 (fun g => eaG g b i sc d) (fun g _ bs => wr g r ((ofBytesLE 8 bs).signExtend 32)) fun _ f _ fl => fl = rfz f

theorem OpI.ldsxb {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .movsx 32 [gr 32 r, .mem (mg b i sc d 8)] len) (Op.ldsxb r b i sc d) := by
  dsimp only [Op.ldsxb, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.movsx, movSigned, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Opd.width, Nat.reduceDiv]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end FV7z
