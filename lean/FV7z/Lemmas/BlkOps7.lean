import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps4
/-!
# `cdqe`, and moves of an `xmm` register whose value is not followed (PLAN.md G3, startup)

A function that copies a structure through `xmm` registers (`__libc_sigaction`, the signal mask of its argument)
loads 16 bytes into a register and stores them elsewhere. Where the proof does not need what the bytes are, the two
are `Op`s of a stretch (`Blk.lean`): `Op.vld`, a load that leaves the vector registers any, and `Op.vst`, a store of
bytes that are any. (Where it does, they are steps of their own: `BlkOps4.lean`, `Xmm2.lean`.)

- `Op.cdqe`, `OpI.cdqe`.
- `Op.vl`, `Op.vs`: `Op.vld` and `Op.vst` at `[b + i * sc + d]`; `OpI.vl_movdqu`, `OpI.vl_movups`, `OpI.vl_movq`,
  `OpI.vl_movhps`, `OpI.vs_movdqu`, `OpI.vs_movups`.
-/
namespace FV7z
open ZellicX86 Decode

namespace Op

/-- `cdqe`: `rax` is `eax`, sign-extended. -/
def cdqe : Op := .reg (fun g _ => g.set 0 ((g.rax.setWidth 32).signExtend 64)) fun _ f fl => fl = rfz f
/-- A load of `n` bytes at `[b + i * sc + d]` into a vector register. -/
def vl (n : Nat) (b i : Option Nat) (sc d : Nat) : Op := .vld n fun g => eaG g b i sc d
/-- A store of `n` bytes of a vector register at `[b + i * sc + d]`. -/
def vs (n : Nat) (b i : Option Nat) (sc d : Nat) : Op := .vst n fun g => eaG g b i sc d

end Op

variable {prof : Profile}

theorem OpI.cdqe {len : Nat} : OpI prof (mk .cbw 64 [] len) Op.cdqe := by
  dsimp only [Op.cdqe, OpI]
  intro s o t htf hdec
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  simp only [exec, Sem.cbw, mk, accOf, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, pure,
    Prog.readReg, Prog.run, writeOp, Nat.reduceDiv]
  rfl

theorem OpI.vl_movdqu {w k len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.sse .movdqu) w [.xmm k, .mem (mg b i sc d 128)] len) (Op.vl 16 b i sc d) := by
  dsimp only [Op.vl, OpI]
  intro s o t htf hac hdec hld
  cases b <;> cases i <;>
  · refine ⟨?_, t, instruction_next htf hdec ?_⟩
    rotate_left
    · simp only [exec, execSse, Sem.movdqu, moveBits, mg, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readZmm]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

theorem OpI.vl_movups {w k len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.sse .movups) w [.xmm k, .mem (mg b i sc d 128)] len) (Op.vl 16 b i sc d) := by
  dsimp only [Op.vl, OpI]
  intro s o t htf hac hdec hld
  cases b <;> cases i <;>
  · refine ⟨?_, t, instruction_next htf hdec ?_⟩
    rotate_left
    · simp only [exec, execSse, Sem.movups, moveBits, mg, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readZmm]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

theorem OpI.vl_movq {w k len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.sse .movq) w [.xmm k, .mem (mg b i sc d 64)] len) (Op.vl 8 b i sc d) := by
  dsimp only [Op.vl, OpI]
  intro s o t htf hac hdec hld
  cases b <;> cases i <;>
  · refine ⟨?_, t, instruction_next htf hdec ?_⟩
    rotate_left
    · simp only [exec, execSse, Sem.movq, moveBits, mg, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readZmm]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

theorem OpI.vl_movhps {w k len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.sse .movhps) w [.xmm k, .mem (mg b i sc d 64)] len) (Op.vl 8 b i sc d) := by
  dsimp only [Op.vl, OpI]
  intro s o t htf hac hdec hld
  cases b <;> cases i <;>
  · refine ⟨?_, t, instruction_next htf hdec ?_⟩
    rotate_left
    · simp only [exec, execSse, Sem.movhps, mg, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readZmm]
      rw [checkAccess_ok (s := advance s len) hac hld]
      rfl

theorem OpI.vs_movdqu {w k len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.sse .movdqu) w [.mem (mg b i sc d 128), .xmm k] len) (Op.vs 16 b i sc d) := by
  dsimp only [Op.vs, OpI]
  intro s o t htf hac hdec hwr
  cases b <;> cases i <;>
  · refine ⟨toBytesLE ((s.cpu.vec.zmm (xmmOf k)).setWidth 128) 16, t, toBytesLE_length _ _,
      instruction_next htf hdec ?h⟩
    case h =>
      simp only [exec, execSse, Sem.movdqu, moveBits, mg, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp, Prog.readZmm]
      rw [checkAccess_ok (s := advance s len) hac hwr]
      rfl

theorem OpI.vs_movups {w k len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.sse .movups) w [.mem (mg b i sc d 128), .xmm k] len) (Op.vs 16 b i sc d) := by
  dsimp only [Op.vs, OpI]
  intro s o t htf hac hdec hwr
  cases b <;> cases i <;>
  · refine ⟨toBytesLE ((s.cpu.vec.zmm (xmmOf k)).setWidth 128) 16, t, toBytesLE_length _ _,
      instruction_next htf hdec ?h⟩
    case h =>
      simp only [exec, execSse, Sem.movups, moveBits, mg, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
        memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, writeOp, Prog.readZmm]
      rw [checkAccess_ok (s := advance s len) hac hwr]
      rfl

end FV7z
