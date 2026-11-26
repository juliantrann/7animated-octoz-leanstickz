import FV7z.Lemmas.BlkOps12
/-!
# `test [rip + d], r64` (PLAN.md §M, M1, `__bsd_signal`)

- `Op.testmra`: `test [A], r` of `w` bits, the address fixed; `AF` is undefined (`LogF`).
- `OpIA.testmr_rip`: the 64-bit form at `x`, the address `A` = `x + len + d`.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `test [A], r`, the address fixed. -/
def testmra (w A r : Nat) : Op :=
  .load (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ _ => g)
    fun g f bs fl => LogF f (ofBytesLE w bs &&& gv g w r) fl

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `test qword [rip + d], r64`, at `x`. -/
theorem OpIA.testmr_rip {r len d A : Nat} {x : Addr} (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .test 64 [.mem (mrip d 64), gr 64 r] len) (Op.testmra 64 A r) := by
  dsimp only [Op.testmra, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, ?t', instruction_next htf hdec ?h, ⟨?af, rfl⟩, rfl, rfl, rfl⟩
  case h =>
    simp only [exec, Sem.test, alu, logicOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one,
      Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
