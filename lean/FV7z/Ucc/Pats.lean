import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::UString(const UString&)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ucc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08,
  0x8b, 0x76, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.ld 32 6 (some 6) none 1 8]

theorem b0 (prof : Profile) : Blk prof p0 0 19 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 19

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x8b, 0x43, 0x08, 0x48, 0x8b, 0x33, 0x48, 0x8b, 0x7d, 0x00, 0x48, 0x83, 0xc4, 0x08, 0x5b, 0x8d,
  0x50, 0x01, 0x5d]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 0 (some 3) none 1 8,
  Op.ld 64 6 (some 3) none 1 0,
  Op.ld 64 7 (some 5) none 1 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.lea 32 2 (some 0) none 1 1,
  Op.pop 5]

theorem b1 (prof : Profile) : Blk prof p1 0 19 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_14 _) (OpI.pop) (by decide) <|
  .cons (p1_15 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.pop) (by decide) <|
  .nil 19

end FV7z.Ucc
