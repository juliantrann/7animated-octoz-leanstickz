import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NIO::COutFile::OpenBinary_forWrite_oflag(char const*, int)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Obw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x89, 0xd5, 0x41, 0x54, 0x49, 0x89, 0xf4, 0x55, 0x48,
  0x89, 0xfd, 0x48, 0x8d, 0x7f, 0x48]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 7) none 1 72 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 32 13 (.r 2),
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.lea 64 7 (some 7) none 1 72]

theorem b0 (prof : Profile) : Blk prof p0 0 22 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 22

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x8b, 0x4d, 0x58, 0x44, 0x89, 0xea, 0x4c, 0x89, 0xe6, 0x48, 0x89, 0xef, 0x5d, 0x41, 0x5c, 0x41,
  0x5d]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 5) none 1 88 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 1 (some 5) none 1 88,
  Op.mov 32 2 (.r 13),
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 5),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b1 (prof : Profile) : Blk prof p1 0 17 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.pop) (by decide) <|
  .cons (p1_13 _) (OpI.pop) (by decide) <|
  .cons (p1_15 _) (OpI.pop) (by decide) <|
  .nil 17

end FV7z.Obw
