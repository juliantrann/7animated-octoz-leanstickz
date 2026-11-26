import FV7z.Lemmas.BlkOps12
/-!
# `test dword [m], imm` (PLAN.md §M, M1)

glibc's `__fileno` tests a bit of the `FILE`'s flags with `test dword [rdi], 0x2000`: `Op.testmi` at 32 bits, as
`OpI.testmi8` at 8.
-/
namespace FV7z
open ZellicX86 Decode

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `test dword [m], imm`. -/
theorem OpI.testmi32 {v len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .test 32 [.mem (mg b i sc d 32), .imm 32 v] len) (Op.testmi 32 b i sc d v) := by
  dsimp only [Op.testmi, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, ?t', instruction_next htf hdec ?h, ⟨?af, rfl⟩, rfl, rfl, rfl⟩
  case h =>
    cases b <;> cases i <;>
    · simp only [exec, Sem.test, alu, logicOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

end

end FV7z
