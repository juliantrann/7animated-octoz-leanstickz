import FV7z.Lemmas.BlkOps20
/-!
# `shr r32, imm8` with `ZF` (PLAN.md M, ctor 103)

glibc's `intel_check_word` walks the bytes of a `cpuid(2)` register with `shr esi, 8; jne`: the loop ends because
`ZF` says whether the shifted value is 0. `Op.shr` leaves the flags to an oracle; `Op.shr32z` says `ZF` when the count
(modulo 32) is not 0, as `Op.shr64` does at 64 bits.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile}

/-- `shr r32, x`: the count taken modulo 32; `ZF` says whether the result is 0 when the count is not 0. -/
def Op.shr32z (r : Nat) (x : Src) : Op :=
  .reg (fun g _ => wr g r (gv g 32 r >>> ((x.val 8 g).toNat % 32))) fun g _ fl =>
    (x.val 8 g).toNat % 32 ≠ 0 → fl.zf = (gv g 32 r >>> ((x.val 8 g).toNat % 32) == 0)

theorem OpI.shr32z {r len : Nat} (x : Src) : OpI prof (mk .shr 32 [gr 32 r, x.opd 8] len) (Op.shr32z r x) := by
  dsimp only [Op.shr32z, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .shr 32 [gr 32 r, x.opd 8] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wr s.cpu.gpr r
        (gv s.cpu.gpr 32 r >>> ((x.val 8 s.cpu.gpr).toNat % 32))) fl), t') ∧
      ((x.val 8 s.cpu.gpr).toNat % 32 ≠ 0 →
        fl.zf = (gv s.cpu.gpr 32 r >>> ((x.val 8 s.cpu.gpr).toNat % 32) == 0)) ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, hP, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, hP, h1, h2, h3⟩
  cases x with
  | r q =>
    simp only [exec, Sem.shr, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.ushiftRight_zero]
      exact ⟨_, _, rfl, fun h => absurd rfl h, rfl, rfl, rfl⟩
    · have hlt : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.setWidth 8 (s.cpu.gpr.get (regOf q))).toNat % 32 = 1 <;>
        simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, fun _ => rfl, rfl, rfl, rfl⟩
  | i v =>
    simp only [exec, Sem.shr, shiftInst, shiftRot, mk, gr, Src.opd, Src.val, gv, bind, Prog.bind, readOp,
      Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
      Nat.reduceEqDiff, or_true, false_or]
    by_cases h0 : (BitVec.ofNat 8 v).toNat % 32 = 0
    · simp only [h0, ↓reduceIte, BitVec.ushiftRight_zero]
      exact ⟨_, _, rfl, fun h => absurd rfl h, rfl, rfl, rfl⟩
    · have hlt : (BitVec.ofNat 8 v).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      by_cases h1 : (BitVec.ofNat 8 v).toNat % 32 = 1 <;> simp only [h0, hlt, h1, ↓reduceIte] <;>
        exact ⟨_, _, rfl, fun _ => rfl, rfl, rfl, rfl⟩

end FV7z
