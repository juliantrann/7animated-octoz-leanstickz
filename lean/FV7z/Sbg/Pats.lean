import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NIO::CFileBase::seekToBegin() const` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sbg
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x31, 0xd2, 0x31, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8),
  Op.xor 32 2 (.r 2),
  Op.xor 32 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 12 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Sbg
