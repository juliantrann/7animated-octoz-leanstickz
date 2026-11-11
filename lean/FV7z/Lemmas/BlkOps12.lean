import FV7z.Lemmas.BlkOps11
/-!
# `cmp [m], r` and `test byte [m], imm` (PLAN.md G3, `malloc`)

The forms `sysmalloc` has beside those of the earlier `BlkOps` files:

- `Op.cmpmr`, `Op.cmpmra`: `cmp [m], r` of 32 or 64 bits, the operand `[b + i·sc + d]` (`OpI.cmpmr`) or `[rip + d]`
  (`OpIA.cmpmr_rip`, the address `A` in the `Op`).
- `Op.testmi`, `Op.testmia`: `test byte [m], imm` likewise (`OpI.testmi8`, `OpIA.testmi8_rip`); `AF` is undefined
  (`LogF`).
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `cmp [m], r`. -/
def cmpmr (w : Nat) (b i : Option Nat) (sc d r : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ _ => g)
    fun g f bs fl => fl = subF (rfz f) (ofBytesLE w bs) (gv g w r)

/-- `cmp [A], r`, the address fixed. -/
def cmpmra (w A r : Nat) : Op :=
  .load (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ _ => g)
    fun g f bs fl => fl = subF (rfz f) (ofBytesLE w bs) (gv g w r)

/-- `test [m], imm`. -/
def testmi (w : Nat) (b i : Option Nat) (sc d v : Nat) : Op :=
  .load (w / 8) (fun g => eaG g b i sc d) (fun g _ _ => g)
    fun _ f bs fl => LogF f (ofBytesLE w bs &&& BitVec.ofNat w v) fl

/-- `test [A], imm`, the address fixed. -/
def testmia (w A v : Nat) : Op :=
  .load (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ _ => g)
    fun _ f bs fl => LogF f (ofBytesLE w bs &&& BitVec.ofNat w v) fl

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `cmp [m], r`. -/
theorem OpI.cmpmr {w r len sc d : Nat} {b i : Option Nat} (hw : w = 32 ∨ w = 64) :
    OpI prof (mk .cmp w [.mem (mg b i sc d w), gr w r] len) (Op.cmpmr w b i sc d r) := by
  dsimp only [Op.cmpmr, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;> cases b <;> cases i <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `cmp [rip + d], r`, at `x`. -/
theorem OpIA.cmpmr_rip {w r len d A : Nat} {x : Addr} (hw : w = 32 ∨ w = 64)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .cmp w [.mem (mrip d w), gr w r] len) (Op.cmpmra w A r) := by
  dsimp only [Op.cmpmra, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;>
  · simp only [exec, Sem.cmp, alu, subOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one,
      Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `test byte [m], imm`. -/
theorem OpI.testmi8 {v len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk .test 8 [.mem (mg b i sc d 8), .imm 8 v] len) (Op.testmi 8 b i sc d v) := by
  dsimp only [Op.testmi, OpI]
  intro s o t htf hac hdec hld
  refine ⟨_, ?t', instruction_next htf hdec ?h, ⟨?af, rfl⟩, rfl, rfl, rfl⟩
  case h =>
    cases b <;> cases i <;>
    · simp only [exec, Sem.test, alu, logicOp, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

/-- `test byte [rip + d], imm`, at `x`. -/
theorem OpIA.testmi8_rip {v len d A : Nat} {x : Addr} (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .test 8 [.mem (mrip d 8), .imm 8 v] len) (Op.testmia 8 A v) := by
  dsimp only [Op.testmia, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, ?t', instruction_next htf hdec ?h, ⟨?af, rfl⟩, rfl, rfl, rfl⟩
  case h =>
    simp only [exec, Sem.test, alu, logicOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one, Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

end

end FV7z
