import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::UString(const wchar_t*, unsigned, const wchar_t*, unsigned)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Uc4
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x49, 0x89, 0xf6, 0x41, 0x55, 0x49, 0x89, 0xcd, 0x41, 0x54,
  0x49, 0x89, 0xfc, 0x55, 0x44, 0x89, 0xc5, 0x53, 0x89, 0xd3, 0x42, 0x8d, 0x34, 0x03]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 3) (some 8) 1 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.mov 64 14 (.r 6),
  Op.push 13,
  Op.mov 64 13 (.r 1),
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.mov 32 5 (.r 8),
  Op.push 3,
  Op.mov 32 3 (.r 2),
  Op.lea 32 6 (some 3) (some 8) 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 30 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.push) (by decide) <|
  .cons (p0_20 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.push) (by decide) <|
  .cons (p0_24 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 30

/-- The stretch at `35`. -/
def p1 : List Byte := [
  0x4d, 0x8b, 0x24, 0x24, 0x48, 0x89, 0xda, 0x4c, 0x89, 0xf6, 0x4c, 0x89, 0xe7]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 12 (some 12) none 1 0,
  Op.mov 64 2 (.r 3),
  Op.mov 64 6 (.r 14),
  Op.mov 64 7 (.r 12)]

theorem b1 (prof : Profile) : Blk prof p1 0 13 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `53`. -/
def p2 : List Byte := [
  0x49, 0x8d, 0x3c, 0x9c, 0x8d, 0x55, 0x01, 0x5b, 0x4c, 0x89, 0xee, 0x5d, 0x41, 0x5c, 0x41, 0x5d,
  0x41, 0x5e]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 12) (some 3) 4 0 0)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 5) none 1 1 0)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 64 7 (some 12) (some 3) 4 0,
  Op.lea 32 2 (some 5) none 1 1,
  Op.pop 3,
  Op.mov 64 6 (.r 13),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b2 (prof : Profile) : Blk prof p2 0 18 o2 :=
  .cons (p2_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.pop) (by decide) <|
  .cons (p2_8 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.pop) (by decide) <|
  .cons (p2_12 _) (OpI.pop) (by decide) <|
  .cons (p2_14 _) (OpI.pop) (by decide) <|
  .cons (p2_16 _) (OpI.pop) (by decide) <|
  .nil 18

end FV7z.Uc4
