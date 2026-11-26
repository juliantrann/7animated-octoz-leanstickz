import FV7z.Lemmas.BlkOps2
/-!
# `cmovcc r32, [m]`, `cmovcc r64, [m]` (PLAN.md §M, M1)

glibc's `__getdtablesize` takes `RLIMIT_NOFILE`'s soft limit from the stack with `cmovns eax, [rsp]`. The source is
read whatever the condition, and a 32-bit destination is written (zero-extended) even when the condition is false
(Zellic's `Sem.cmovcc`): a load (`Op.load`) of 4 bytes, `Op.cmovld32`. glibc's `__opendir` bounds the buffer by the
directory's block size with `cmovae rbx, [rsp + 56]`: `Op.cmovld64`, the register kept when the condition is false.
-/
namespace FV7z
open ZellicX86 Decode

/-- `cmovcc r32, [b + i * sc + d]`. -/
def Op.cmovld32 (cc : Cond) (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load 4 (fun g => eaG g b i sc d) (fun g f bs => wr g r (if f.cond cc then ofBytesLE 32 bs else gv g 32 r))
    fun _ f _ fl => fl = rfz f

/-- `cmovcc r64, [b + i * sc + d]`. -/
def Op.cmovld64 (cc : Cond) (r : Nat) (b i : Option Nat) (sc d : Nat) : Op :=
  .load 8 (fun g => eaG g b i sc d) (fun g f bs => if f.cond cc then wr g r (ofBytesLE 64 bs) else g)
    fun _ f _ fl => fl = rfz f

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpI.cmovld32 {cc : Cond} {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.cmovcc cc) 32 [gr 32 r, .mem (mg b i sc d 32)] len) (Op.cmovld32 cc r b i sc d) := by
  dsimp only [Op.cmovld32, OpI]
  intro s o t htf hac hdec hld
  have hc' : (advance s len).cpu.rflags.cond cc = s.cpu.rflags.cond cc := rfz_cond _ cc
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases hc : s.cpu.rflags.cond cc <;> rw [hc] at hc' <;> cases b <;> cases i <;>
  · simp only [exec, Sem.cmovcc, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags, Prog.writeReg, done, hc']
    rw [checkAccess_ok (s := advance s len) hac hld]
    try simp only [hc', Bool.false_eq_true, ↓reduceIte]
    rfl

theorem OpI.cmovld64 {cc : Cond} {r len sc d : Nat} {b i : Option Nat} :
    OpI prof (mk (.cmovcc cc) 64 [gr 64 r, .mem (mg b i sc d 64)] len) (Op.cmovld64 cc r b i sc d) := by
  dsimp only [Op.cmovld64, OpI]
  intro s o t htf hac hdec hld
  have hc' : (advance s len).cpu.rflags.cond cc = s.cpu.rflags.cond cc := rfz_cond _ cc
  refine ⟨_, t, instruction_next htf hdec ?_, rfl, rfl, rfl, rfl⟩
  cases hc : s.cpu.rflags.cond cc <;> rw [hc] at hc' <;> cases b <;> cases i <;>
  · simp only [exec, Sem.cmovcc, mk, mg, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef,
      effOffset, pure, Prog.readReg, Prog.read, Prog.run, writeOp, Prog.readFlags, Prog.writeReg, done, hc, hc']
    rw [checkAccess_ok (s := advance s len) hac hld]
    try simp only [hc, hc', Bool.false_eq_true, ↓reduceIte]
    rfl

end

end FV7z
