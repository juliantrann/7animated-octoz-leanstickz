import FV7z.Lemmas.BlkOps12
/-!
# `cmp byte [m], r8` (PLAN.md §M, M1)

`Op.cmpmr 8` (`FV7z/Lemmas/BlkOps12.lean`) for the byte form, as the GUID compare loops of the `QueryInterface`s
have it (`cmp byte [rsi + rax], r8b`): `OpI.cmpmr8`.
-/
namespace FV7z
open ZellicX86 Decode

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `cmp byte [m], r8`. -/
theorem OpI.cmpmr8 {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .cmp 8 [.mem (mg b i sc d 8), gr 8 r] len) (Op.cmpmr 8 b i sc d r) := by
  dsimp only [Op.cmpmr, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
