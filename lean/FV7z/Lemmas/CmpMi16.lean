import FV7z.Lemmas.BlkOps2
/-!
# `cmp word [m], imm` (PLAN.md §M, M1)

7-Zip's `VariantClear` tests a `PROPVARIANT`'s 16-bit type tag: `cmp word [rdi], 8` (`VT_BSTR`). `Op.cmpmi` at
16 bits, as `OpI.cmpmi` (`FV7z/Lemmas/BlkOps2.lean`) proves it at 8 and 32.
-/
namespace FV7z
open ZellicX86 Decode

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpI.cmpmi16 {v len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .cmp 16 [.mem (mg b i sc d 16), .imm 16 v] len) (Op.cmpmi 16 b i sc d v) := by
  dsimp only [Op.cmpmi, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
