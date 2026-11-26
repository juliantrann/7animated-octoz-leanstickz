import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `MY_lstat` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mls
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x49, 0x89, 0xf9, 0x31, 0xc0, 0x48, 0x89, 0xf7, 0xb9, 0x12, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 18)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.mov 64 9 (.r 7),
  Op.xor 32 0 (.r 0),
  Op.mov 64 7 (.r 6),
  Op.mov 32 1 (.i 18)]

theorem b0 (prof : Profile) : Blk prof p0 0 13 o0 :=
  .cons (p0_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.i 18) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x84, 0xd2, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0xf2, 0x4c, 0x89, 0xce]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 8 2 (.r 2),
  Op.mov 32 7 (.i 1),
  Op.mov 64 2 (.r 6),
  Op.mov 64 6 (.r 9)]

theorem b1 (prof : Profile) : Blk prof p1 0 13 o1 :=
  .cons (p1_0 _) (OpI.test8 (.r 2)) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .nil 13

def j0 : List Byte := [0x75, 0x09]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 9] 2) := by dec_rfl

end FV7z.Mls
