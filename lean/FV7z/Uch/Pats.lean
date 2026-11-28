import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::UString(const UString&, wchar_t)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Uch
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x89, 0xd5, 0x41, 0x54, 0x55, 0x48, 0x89, 0xfd, 0x53,
  0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08, 0x8b, 0x46, 0x08, 0x8d, 0x70, 0x01]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 32 13 (.r 2),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.ld 32 0 (some 6) none 1 8,
  Op.lea 32 6 (some 0) none 1 1]

theorem b0 (prof : Profile) : Blk prof p0 0 29 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 29

/-- The stretch at `34`. -/
def p1 : List Byte := [
  0x44, 0x8b, 0x63, 0x08, 0x48, 0x8b, 0x6d, 0x00, 0x48, 0x8b, 0x33, 0x4c, 0x89, 0xe2, 0x48, 0x89,
  0xef]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 3) none 1 8 32)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 12 (some 3) none 1 8,
  Op.ld 64 5 (some 5) none 1 0,
  Op.ld 64 6 (some 3) none 1 0,
  Op.mov 64 2 (.r 12),
  Op.mov 64 7 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 17 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_11 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p1_14 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 17

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x46, 0x89, 0x6c, 0xa5, 0x00, 0x42, 0xc7, 0x44, 0xa5, 0x04, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83,
  0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 5) (some 12) 4 0 32), gr 32 13] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 32 [.mem (mg (some 5) (some 12) 4 4 32), .imm 32 0] 9) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_18 : ∀ feat, Dec feat p2 18 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_19 : ∀ feat, Dec feat p2 19 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p2_20 : ∀ feat, Dec feat p2 20 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p2_22 : ∀ feat, Dec feat p2 22 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.st 32 (some 5) (some 12) 4 0 13,
  Op.sti 32 (some 5) (some 12) 4 4 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b2 (prof : Profile) : Blk prof p2 0 24 o2 :=
  .cons (p2_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_5 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_14 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_18 _) (OpI.pop) (by decide) <|
  .cons (p2_19 _) (OpI.pop) (by decide) <|
  .cons (p2_20 _) (OpI.pop) (by decide) <|
  .cons (p2_22 _) (OpI.pop) (by decide) <|
  .nil 24

end FV7z.Uch
