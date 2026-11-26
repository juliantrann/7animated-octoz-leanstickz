import FV7z.Lemmas.BlkOps2
/-!
# `shr r16, imm`, `movsx r16, r8`, `imul r32, r32, imm` (PLAN.md §M, M1)

7-Zip's `LzmaProps_Decode` splits the properties byte `d` into `lc`, `lp`, `pb` by dividing by 9 and 5 with
multiplications: `shr ax, 9`, `movsx dx, al`, `imul edx, edx, 0x67`, `shr dx, 9`.

- `Op.shr16`: `shr r16, imm`, the low 16 bits written (`wrLo`), the count taken modulo 32 as the model does for
  widths under 64; the flags unconstrained, as `Op.shr` (`FV7z/Lemmas/BlkOps.lean`).
- `Op.sxb16`: `movsx r16, r8`, the low 16 bits written; no flags change.
- `Op.imul3d`: `imul r32, r32, imm`, as `Op.imul3` (`FV7z/Lemmas/BlkOps20.lean`) at 32 bits.
-/
namespace FV7z
open ZellicX86 Decode

/-- `shr r16, imm`. -/
def Op.shr16 (r v : Nat) : Op :=
  .reg (fun g _ => wrLo g r (gv g 16 r >>> ((BitVec.ofNat 8 v).toNat % 32))) fun _ _ _ => True

/-- `movsx r16, r8`: no flags change. -/
def Op.sxb16 (r q : Nat) : Op :=
  .reg (fun g _ => wrLo g r ((gv g 8 q).signExtend 16)) fun _ f fl => fl = rfz f

/-- `imul r32, q32, imm`: the flags unconstrained. -/
def Op.imul3d (r q v : Nat) : Op :=
  .reg (fun g _ => wr g r (((gv g 32 q).signExtend (2 * 32) * (BitVec.ofNat 32 v).signExtend (2 * 32)).setWidth 32))
    fun _ _ _ => True

section
set_option linter.unusedSimpArgs false
variable {prof : Profile}

theorem OpI.shr16 {r v len : Nat} : OpI prof (mk .shr 16 [gr 16 r, .imm 8 v] len) (Op.shr16 r v) := by
  dsimp only [Op.shr16, OpI]
  intro s o t htf hdec
  suffices h : ∃ fl t', ((exec prof (mk .shr 16 [gr 16 r, .imm 8 v] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len (wrLo s.cpu.gpr r
        (gv s.cpu.gpr 16 r >>> ((BitVec.ofNat 8 v).toNat % 32))) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, trivial, h1, h2, h3⟩
  simp only [exec, Sem.shr, shiftInst, shiftRot, mk, gr, gv, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, advance_gpr,
    Nat.reduceEqDiff, or_true, false_or]
  by_cases h0 : (BitVec.ofNat 8 v).toNat % 32 = 0
  · simp only [h0, ↓reduceIte, BitVec.ushiftRight_zero]
    exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  · by_cases h1 : (BitVec.ofNat 8 v).toNat % 32 = 1 <;> by_cases h2 : (BitVec.ofNat 8 v).toNat % 32 < 16 <;>
      simp only [h0, h1, h2, ↓reduceIte, Nat.reduceLT] <;>
      first
      | exact ⟨_, _, rfl, rfl, rfl, rfl⟩
      | omega

theorem OpI.sxb16 {r q len : Nat} : OpI prof (mk .movsx 16 [gr 16 r, gr 8 q] len) (Op.sxb16 r q) :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

theorem OpI.imul3d {r q v len : Nat} :
    OpI prof (mk .imul 32 [gr 32 r, gr 32 q, .imm 32 v] len) (Op.imul3d r q v) := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, trivial, rfl, rfl, rfl⟩

end

end FV7z
