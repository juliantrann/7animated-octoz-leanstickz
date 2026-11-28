import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::Delete` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Adl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x53, 0x89, 0xd3, 0x8d, 0x0c, 0x1e, 0x48, 0x83, 0xec, 0x08, 0x8b,
  0x57, 0x08, 0x89, 0xd0, 0x29, 0xf0, 0x39, 0xd1, 0x0f, 0x47, 0xd8, 0x85, 0xdb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 6) (some 3) 1 0 0)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk (.cmovcc 7) 32 [gr 32 3, gr 32 0] 3) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .test 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.push 3,
  Op.mov 32 3 (.r 2),
  Op.lea 32 1 (some 6) (some 3) 1 0,
  Op.sub 64 4 (.i 8),
  Op.ld 32 2 (some 7) none 1 8,
  Op.mov 32 0 (.r 2),
  Op.sub 32 0 (.r 6),
  Op.cmp 32 1 (.r 2),
  Op.cmov32 7 3 0,
  Op.test 32 3 (.r 3)]

theorem b0 (prof : Profile) : Blk prof p0 0 29 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.sub (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_24 _) (OpI.cmov32) (by decide) <|
  .cons (p0_27 _) (OpI.test (.r 3) (.inl rfl)) (by decide) <|
  .nil 29

def j0 : List Byte := [0x75, 0x11]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `31`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.pop) (by decide) <|
  .cons (p1_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xfd, 0x48, 0x8b, 0x3f, 0x8d, 0x04, 0x33, 0x83, 0xc2, 0x01, 0x89, 0xf6, 0x29, 0xc2,
  0x4c, 0x8d, 0x04, 0x07, 0x48, 0x01, 0xf7, 0x4c, 0x89, 0xc6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 3) (some 6) 1 0 0)] 3) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 7) (some 0) 1 0 0)] 4) := by dec_rfl
theorem p2_20 : ∀ feat, Dec feat p2 20 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p2_23 : ∀ feat, Dec feat p2 23 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 5 (.r 7),
  Op.ld 64 7 (some 7) none 1 0,
  Op.lea 32 0 (some 3) (some 6) 1 0,
  Op.add 32 2 (.i 1),
  Op.mov 32 6 (.r 6),
  Op.sub 32 2 (.r 0),
  Op.lea 64 8 (some 7) (some 0) 1 0,
  Op.add 64 7 (.r 6),
  Op.mov 64 6 (.r 8)]

theorem b2 (prof : Profile) : Blk prof p2 0 26 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_16 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_20 _) (OpI.add (.r 6) (.inr rfl)) (by decide) <|
  .cons (p2_23 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 26

end FV7z.Adl
