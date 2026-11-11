import FV7z.Lemmas.BlkOps2
/-!
# More instructions of compiled code: the 64-bit shifts (PLAN.md G3, startup)

`shl r64, x` (measured with `decshow` on `_dl_debug_initialize`: `shl rax, 4`), beside the 32-bit one of `BlkOps.lean`;
`shr r64, x` and `sar r64, x` (`register_tm_clones`: `shr rsi, 63`, `sar rax, 3`, `sar rsi, 1`), of which `ZF` is known
when the count is not 0: a `je` follows the last one.
-/
namespace FV7z
open ZellicX86 Decode

/-- `shl r64, x`: the count taken modulo 64. -/
def Op.shl64 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g 64 r <<< ((x.val 8 g).toNat % 64))) fun _ _ _ => True

variable {prof : Profile}

theorem OpI.shl64 {r len : Nat} (x : Src) : OpI prof (mk .shl 64 [gr 64 r, x.opd 8] len) (Op.shl64 r x) := by
  dsimp only [Op.shl64, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .shl 64 [gr 64 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        (gv s.cpu.gpr 64 r <<< ((x.val 8 s.cpu.gpr).toNat % 64))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, trivial, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.shl, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, BitVec.shiftLeft_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.shl, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, writeOp, Prog.readFlags, Nat.reduceEqDiff]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, BitVec.shiftLeft_zero]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · have hlt : (BitVec.ofNat 8 v).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.ofNat 8 v).toNat % 64 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- `shr r64, x`: the count taken modulo 64; `ZF` says whether the result is 0 when the count is not 0. -/
def Op.shr64 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g 64 r >>> ((x.val 8 g).toNat % 64))) fun g _ fl =>
    (x.val 8 g).toNat % 64 ≠ 0 → fl.zf = (gv g 64 r >>> ((x.val 8 g).toNat % 64) == 0)

theorem OpI.shr64 {r len : Nat} (x : Src) : OpI prof (mk .shr 64 [gr 64 r, x.opd 8] len) (Op.shr64 r x) := by
  dsimp only [Op.shr64, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .shr 64 [gr 64 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        (gv s.cpu.gpr 64 r >>> ((x.val 8 s.cpu.gpr).toNat % 64))) fl), t') ∧
      ((x.val 8 s.cpu.gpr).toNat % 64 ≠ 0 → fl.zf = (gv s.cpu.gpr 64 r >>> ((x.val 8 s.cpu.gpr).toNat % 64) == 0)) ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, hP, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, hP, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.shr, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, BitVec.ushiftRight_zero]
      exact ⟨_, _, rfl, fun h => absurd rfl h, rfl, rfl, rfl⟩
    · have hlt : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, fun _ => rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.shr, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, writeOp, Prog.readFlags, Nat.reduceEqDiff]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, BitVec.ushiftRight_zero]
      exact ⟨_, _, rfl, fun h => absurd rfl h, rfl, rfl, rfl⟩
    · have hlt : (BitVec.ofNat 8 v).toNat % 64 < 64 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.ofNat 8 v).toNat % 64 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, fun _ => rfl, rfl, rfl, rfl⟩

/-- `sar r64, x`: the count taken modulo 64; `ZF` says whether the result is 0 when the count is not 0. -/
def Op.sar64 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r ((gv g 64 r).sshiftRight ((x.val 8 g).toNat % 64))) fun g _ fl =>
    (x.val 8 g).toNat % 64 ≠ 0 → fl.zf = ((gv g 64 r).sshiftRight ((x.val 8 g).toNat % 64) == 0)

theorem OpI.sar64 {r len : Nat} (x : Src) : OpI prof (mk .sar 64 [gr 64 r, x.opd 8] len) (Op.sar64 r x) := by
  dsimp only [Op.sar64, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .sar 64 [gr 64 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        ((gv s.cpu.gpr 64 r).sshiftRight ((x.val 8 s.cpu.gpr).toNat % 64))) fl), t') ∧
      ((x.val 8 s.cpu.gpr).toNat % 64 ≠ 0 → fl.zf = ((gv s.cpu.gpr 64 r).sshiftRight ((x.val 8 s.cpu.gpr).toNat % 64) == 0)) ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, hP, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, hP, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.sar, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, BitVec.sshiftRight_zero]
      exact ⟨_, _, rfl, fun h => absurd rfl h, rfl, rfl, rfl⟩
    · by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 1 <;> simp only [h0, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, fun _ => rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.sar, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, writeOp, Prog.readFlags, Nat.reduceEqDiff]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, BitVec.sshiftRight_zero]
      exact ⟨_, _, rfl, fun h => absurd rfl h, rfl, rfl, rfl⟩
    · by_cases h1 : (BitVec.ofNat 8 v).toNat % 64 = 1 <;> simp only [h0, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, fun _ => rfl, rfl, rfl, rfl⟩

end FV7z
