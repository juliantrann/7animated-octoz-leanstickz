import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CInFile::read_part` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Irp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0xb8, 0x00, 0x00, 0x40, 0x00, 0x48, 0x81, 0xfa,
  0x00, 0x00, 0x40, 0x00, 0x8b, 0x3f, 0x48, 0x0f, 0x47, 0xd0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4194304)] 5) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 4194304)] 7) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk (.cmovcc 7) 64 [gr 64 2, gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8),
  Op.mov 32 0 (.i 4194304),
  Op.cmp 64 2 (.i 4194304),
  Op.ld 32 7 (some 7) none 1 0,
  Op.cmov64 7 2 0]

theorem b0 (prof : Profile) : Blk prof p0 0 26 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.i 4194304) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.cmp (.i 4194304) (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.cmov64) (by decide) <|
  .nil 26

/-- The stretch at `31`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Irp
