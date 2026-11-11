import FV7z.Lemmas.BlkOps7
/-!
# Bytes and `xmm` registers at fixed addresses (PLAN.md G3, startup)

The forms `__register_atfork` has beside those of `BlkOps2.lean` and `BlkOps7.lean`, with an operand `[rip + d]`
(`OpIA` of `Blk.lean`: at `x`, an instruction of `len` bytes addresses `x + len + d`, the address `A` in the `Op`):

- `Op.cmpmia 8`, `Op.stia 8`: `cmp byte [A], imm` and `mov byte [A], imm` (`OpIA.cmpmi8_rip`, `OpIA.sti8_rip`).
- `Op.addma`: `add r, [A]` (`OpIA.addm_rip`).
- `Op.vla`, `Op.vsa`: `movdqa`/`movaps` of an `xmm` register from and to `[A]`, a multiple of 16, the register's value
  not followed (`Op.vld`, `Op.vst`; `OpIA.vl_movdqa_rip`, `vl_movaps_rip`, `vs_movdqa_rip`, `vs_movaps_rip`).
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `add r, [A]`, the address fixed. -/
def addma (w r A : Nat) : Op :=
  .load (w / 8) (fun _ => BitVec.ofNat 64 A) (fun g _ bs => wr g r (addR (gv g w r) (ofBytesLE w bs)))
    fun g f bs fl => fl = addF (rfz f) (gv g w r) (ofBytesLE w bs)

/-- A load of `n` bytes at `A` into a vector register. -/
def vla (n A : Nat) : Op := .vld n fun _ => BitVec.ofNat 64 A

/-- A store of `n` bytes of a vector register at `A`. -/
def vsa (n A : Nat) : Op := .vst n fun _ => BitVec.ofNat 64 A

end Op

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

/-- `cmp byte [rip + d], imm`, at `x`. -/
theorem OpIA.cmpmi8_rip {v len d A : Nat} {x : Addr} (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .cmp 8 [.mem (mrip d 8), .imm 8 v] len) (Op.cmpmia 8 A v) := by
  dsimp only [Op.cmpmia, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  simp only [exec, Sem.cmp, alu, subOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one, Prog.readFlags]
  rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `mov byte [rip + d], imm`, at `x`. -/
theorem OpIA.sti8_rip {v len d A : Nat} {x : Addr} (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .mov 8 [.mem (mrip d 8), .imm 8 v] len) (Op.stia 8 A v) := by
  dsimp only [Op.stia, OpIA]
  intro s o t hrip htf hac hdec _ hwr
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨t, instruction_next htf hdec ?_⟩
  simp only [exec, Sem.mov, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.readRip, Prog.write, Prog.run, Opd.width, writeOp, BitVec.mul_one]
  rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- `add r, [rip + d]`, at `x`. -/
theorem OpIA.addm_rip {w r len d A : Nat} {x : Addr} (hw : w = 32 ∨ w = 64)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk .add w [gr w r, .mem (mrip d w)] len) (Op.addma w r A) := by
  dsimp only [Op.addma, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  rcases hw with rfl | rfl <;>
  · simp only [exec, Sem.add, alu, addOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.readRip, Prog.read, Prog.run, Opd.width, writeOp, BitVec.mul_one,
      Prog.readFlags]
    rw [eaR_adv, he, checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `movdqa xmm, [rip + d]`, at `x`, the address a multiple of 16. -/
theorem OpIA.vl_movdqa_rip {w k len d A : Nat} {x : Addr} (hal : (BitVec.ofNat 64 A).toNat % 16 = 0)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk (.sse .movdqa) w [.xmm k, .mem (mrip d 128)] len) (Op.vla 16 A) := by
  dsimp only [Op.vla, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨?_, t, instruction_next htf hdec ?_⟩
  rotate_left
  · simp only [exec, execSse, Sem.movdqa, moveAligned, aligned16, Prog.alignedTo, mk, mrip, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, writeOp,
      Prog.readZmm, BitVec.mul_one, eaR_adv, he, hal, true_or]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `movaps xmm, [rip + d]`, at `x`, the address a multiple of 16. -/
theorem OpIA.vl_movaps_rip {w k len d A : Nat} {x : Addr} (hal : (BitVec.ofNat 64 A).toNat % 16 = 0)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk (.sse .movaps) w [.xmm k, .mem (mrip d 128)] len) (Op.vla 16 A) := by
  dsimp only [Op.vla, OpIA]
  intro s o t hrip htf hac hdec hld
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨?_, t, instruction_next htf hdec ?_⟩
  rotate_left
  · simp only [exec, execSse, Sem.movaps, moveAligned, aligned16, Prog.alignedTo, mk, mrip, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.run, writeOp,
      Prog.readZmm, BitVec.mul_one, eaR_adv, he, hal, true_or]
    rw [checkAccess_ok (s := advance s len) hac hld]
    rfl

/-- `movdqa [rip + d], xmm`, at `x`, the address a multiple of 16. -/
theorem OpIA.vs_movdqa_rip {w k len d A : Nat} {x : Addr} (hal : (BitVec.ofNat 64 A).toNat % 16 = 0)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk (.sse .movdqa) w [.mem (mrip d 128), .xmm k] len) (Op.vsa 16 A) := by
  dsimp only [Op.vsa, OpIA]
  intro s o t hrip htf hac hdec hwr
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨toBytesLE ((s.cpu.vec.zmm (xmmOf k)).setWidth 128) 16, t, toBytesLE_length _ _,
    instruction_next htf hdec ?h⟩
  case h =>
    simp only [exec, execSse, Sem.movdqa, moveAligned, aligned16, Prog.alignedTo, mk, mrip, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.write, Prog.run, writeOp,
      Prog.readZmm, BitVec.mul_one, eaR_adv, he, hal, true_or]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    rfl

/-- `movaps [rip + d], xmm`, at `x`, the address a multiple of 16. -/
theorem OpIA.vs_movaps_rip {w k len d A : Nat} {x : Addr} (hal : (BitVec.ofNat 64 A).toNat % 16 = 0)
    (hA : x.add len + BitVec.ofNat 64 d = BitVec.ofNat 64 A) :
    OpIA prof x (mk (.sse .movaps) w [.mem (mrip d 128), .xmm k] len) (Op.vsa 16 A) := by
  dsimp only [Op.vsa, OpIA]
  intro s o t hrip htf hac hdec hwr
  have he : eaR s len d = BitVec.ofNat 64 A := by rw [← hA, ← hrip]
  refine ⟨toBytesLE ((s.cpu.vec.zmm (xmmOf k)).setWidth 128) 16, t, toBytesLE_length _ _,
    instruction_next htf hdec ?h⟩
  case h =>
    simp only [exec, execSse, Sem.movaps, moveAligned, aligned16, Prog.alignedTo, mk, mrip, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.write, Prog.run, writeOp,
      Prog.readZmm, BitVec.mul_one, eaR_adv, he, hal, true_or]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    rfl

end

end FV7z
