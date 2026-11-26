import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `InStream_AtBegin_GetSize` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Iag
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x48, 0x89, 0xf1, 0xba, 0x02, 0x00, 0x00, 0x00, 0x31, 0xf6,
  0x55, 0x48, 0x89, 0xfd, 0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x07]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 1 (.r 6),
  Op.mov 32 2 (.i 2),
  Op.xor 32 6 (.r 6),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.sub 64 4 (.i 8),
  Op.ld 64 0 (some 7) none 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 27 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.push) (by decide) <|
  .cons (p0_17 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_24 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 27

/-- The stretch at `30`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xef, 0x41, 0x89, 0xc4]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 7 (.r 5),
  Op.mov 32 12 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `41`. -/
def p2 : List Byte := [
  0x45, 0x85, 0xe4, 0x44, 0x0f, 0x44, 0xe0, 0x48, 0x83, 0xc4, 0x08, 0x5d, 0x44, 0x89, 0xe0, 0x41,
  0x5c]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk (.cmovcc 4) 32 [gr 32 12, gr 32 0] 4) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p2_15 : ∀ feat, Dec feat p2 15 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 32 12 (.r 12),
  Op.cmov32 4 12 0,
  Op.add 64 4 (.i 8),
  Op.pop 5,
  Op.mov 32 0 (.r 12),
  Op.pop 12]

theorem b2 (prof : Profile) : Blk prof p2 0 17 o2 :=
  .cons (p2_0 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.cmov32) (by decide) <|
  .cons (p2_7 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.pop) (by decide) <|
  .cons (p2_12 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p2_15 _) (OpI.pop) (by decide) <|
  .nil 17

end FV7z.Iag
