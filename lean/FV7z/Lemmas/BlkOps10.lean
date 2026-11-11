import FV7z.Lemmas.BlkOps9
/-!
# `cmp r16, [m]` (PLAN.md G3, startup)

The form `getenv` has beside those of `BlkOps.lean` to `BlkOps9.lean`:

- `OpI.cmpm16`: `cmp r, [m]` of 16 bits is `Op.cmpm 16` (`OpI.cmpm` is of 32 and 64 bits).
-/
namespace FV7z
open ZellicX86 Decode

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `cmp r16, [m]`. -/
theorem OpI.cmpm16 {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .cmp 16 [gr 16 r, .mem (mg b i sc d 16)] len) (Op.cmpm 16 r b i sc d) := by
  dsimp only [Op.cmpm, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
