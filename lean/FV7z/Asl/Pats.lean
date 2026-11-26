import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::SetStartLen` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Asl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x53, 0x48, 0x89, 0xfb, 0x89, 0xf7, 0x48, 0x89, 0xfd, 0x48, 0x83,
  0xc7, 0x01, 0x48, 0x83, 0xec, 0x08, 0x48, 0xc7, 0x03, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), .imm 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.mov 32 7 (.r 6),
  Op.mov 64 5 (.r 7),
  Op.add 64 7 (.i 1),
  Op.sub 64 4 (.i 8),
  Op.sti 64 (some 3) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 29 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 29

/-- The stretch at `34`. -/
def p1 : List Byte := [
  0x89, 0x6b, 0x08, 0x89, 0x6b, 0x0c, 0x48, 0x89, 0x03, 0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 8 32), gr 32 5] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 12 32), gr 32 5] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.st 32 (some 3) none 1 8 5,
  Op.st 32 (some 3) none 1 12 5,
  Op.st 64 (some 3) none 1 0 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b1 (prof : Profile) : Blk prof p1 0 15 o1 :=
  .cons (p1_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_9 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.pop) (by decide) <|
  .cons (p1_14 _) (OpI.pop) (by decide) <|
  .nil 15

end FV7z.Asl
