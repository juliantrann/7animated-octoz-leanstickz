import FV7z.Lemmas.BlkOps10
/-!
# More instructions of compiled code: the 64-bit rotations (PLAN.md G3, startup)

`rol r64, x` and `ror r64, x` (measured with `decshow` on `__cxa_atexit`: `rol rdi, 0x11`, glibc's `PTR_MANGLE` of a
function pointer after the `xor` with the pointer guard; `ror` undoes it where the pointer is called).
-/
namespace FV7z
open ZellicX86 Decode

theorem rotl0 (x : BitVec 64) : x.rotateLeft 0 = x := by
  have h : x >>> 64 = 0#64 := by
    ext i hi
    simp
  simp [BitVec.rotateLeft, BitVec.rotateLeftAux, h]

theorem rotr0 (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

/-- `rol r64, x`: the count taken modulo 64. -/
def Op.rol64 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r ((gv g 64 r).rotateLeft ((x.val 8 g).toNat % 64))) fun _ _ _ => True

/-- `ror r64, x`: the count taken modulo 64. -/
def Op.ror64 (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r ((gv g 64 r).rotateRight ((x.val 8 g).toNat % 64))) fun _ _ _ => True

variable {prof : Profile}

theorem OpI.rol64 {r len : Nat} (x : Src) : OpI prof (mk .rol 64 [gr 64 r, x.opd 8] len) (Op.rol64 r x) := by
  dsimp only [Op.rol64, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .rol 64 [gr 64 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        ((gv s.cpu.gpr 64 r).rotateLeft ((x.val 8 s.cpu.gpr).toNat % 64))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, trivial, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.rol, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, rotl0]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 1 <;>
        simp only [h0, h1, ↓reduceIte, Nat.mod_mod] <;> exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.rol, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, writeOp, Prog.readFlags, Nat.reduceEqDiff]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, rotl0]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · by_cases h1 : (BitVec.ofNat 8 v).toNat % 64 = 1 <;> simp only [h0, h1, ↓reduceIte, Nat.mod_mod] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩

theorem OpI.ror64 {r len : Nat} (x : Src) : OpI prof (mk .ror 64 [gr 64 r, x.opd 8] len) (Op.ror64 r x) := by
  dsimp only [Op.ror64, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .ror 64 [gr 64 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        ((gv s.cpu.gpr 64 r).rotateRight ((x.val 8 s.cpu.gpr).toNat % 64))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, trivial, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.ror, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, rotr0]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 64 = 1 <;>
        simp only [h0, h1, ↓reduceIte, Nat.mod_mod] <;> exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.ror, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, writeOp, Prog.readFlags, Nat.reduceEqDiff]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 64 = 0
    · simp only [h0, ↓reduceIte, rotr0]
      exact ⟨_, _, rfl, rfl, rfl, rfl⟩
    · by_cases h1 : (BitVec.ofNat 8 v).toNat % 64 = 1 <;> simp only [h0, h1, ↓reduceIte, Nat.mod_mod] <;>
        exact ⟨_, _, rfl, rfl, rfl, rfl⟩

end FV7z
