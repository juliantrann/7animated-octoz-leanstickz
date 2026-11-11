import FV7z.Lemmas.BlkOps8
/-!
# `cmp r, [A]` (PLAN.md G3, startup)

The form `__libc_init_first` has beside those of `BlkOps2.lean`, `BlkOps7.lean` and `BlkOps8.lean`, with an operand
`[rip + d]` (`OpIA` of `Blk.lean`):

- `Op.cmpma`: `cmp r, [A]` of 16, 32 or 64 bits (`OpIA.cmpm_rip`).
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `cmp r, [A]`, the address fixed. -/
def cmpma (w r A : Nat) : Op :=
  .load (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ _ => g)
    fun g f bs fl => fl = subF (rfz f) (gv g w r) (ofBytesLE w bs)

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `cmp r, [rip + d]`, at `x`. -/
theorem OpIA.cmpm_rip {w r len d A : Nat} {x : Addr} (hw : w = 16 ∨ w = 32 ∨ w = 64)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .cmp w [gr w r, .mem (mrip d w)] len) (Op.cmpma w r A) := by
  dsimp only [Op.cmpma, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl | rfl <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one,
      Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
