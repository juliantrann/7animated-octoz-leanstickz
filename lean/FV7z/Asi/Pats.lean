import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::InsertSpace` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Asi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xf4, 0x89, 0xd6, 0x55, 0x89, 0xd5, 0x53, 0x48,
  0x89, 0xfb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.mov 32 6 (.r 2),
  Op.push 5,
  Op.mov 32 5 (.r 2),
  Op.push 3,
  Op.mov 64 3 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 18

/-- The stretch at `23`. -/
def p1 : List Byte := [
  0x41, 0x8b, 0x34, 0x24, 0x48, 0x8b, 0x3b, 0xba, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xf0, 0x29,
  0xf2, 0x48, 0x01, 0xfe, 0x03, 0x53, 0x08, 0x01, 0xe8, 0x5b, 0x5d, 0x48, 0x01, 0xc7, 0x41, 0x5c]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 12) none 1 0 32)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk .add 32 [gr 32 2, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p1_25 : ∀ feat, Dec feat p1 25 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p1_26 : ∀ feat, Dec feat p1 26 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p1_27 : ∀ feat, Dec feat p1 27 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p1_30 : ∀ feat, Dec feat p1 30 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 6 (some 12) none 1 0,
  Op.ld 64 7 (some 3) none 1 0,
  Op.mov 32 2 (.i 1),
  Op.mov 64 0 (.r 6),
  Op.sub 32 2 (.r 6),
  Op.add 64 6 (.r 7),
  Op.addm 32 2 (some 3) none 1 8,
  Op.add 32 0 (.r 5),
  Op.pop 3,
  Op.pop 5,
  Op.add 64 7 (.r 0),
  Op.pop 12]

theorem b1 (prof : Profile) : Blk prof p1 0 32 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.sub (.r 6) (.inl rfl)) (by decide) <|
  .cons (p1_17 _) (OpI.add (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_20 _) (OpI.addm (.inl rfl)) (by decide) <|
  .cons (p1_23 _) (OpI.add (.r 5) (.inl rfl)) (by decide) <|
  .cons (p1_25 _) (OpI.pop) (by decide) <|
  .cons (p1_26 _) (OpI.pop) (by decide) <|
  .cons (p1_27 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p1_30 _) (OpI.pop) (by decide) <|
  .nil 32

end FV7z.Asi
