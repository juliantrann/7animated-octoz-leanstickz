import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaDec_Free` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ldf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 16

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x73, 0x18, 0x48, 0x89, 0xef]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) none 1 24 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 6 (some 3) none 1 24,
  Op.mov 64 7 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `31`. -/
def p2 : List Byte := [
  0x48, 0xc7, 0x43, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 24 64), .imm 64 0] 8) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 64 (some 3) none 1 24 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_8 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.pop) (by decide) <|
  .cons (p2_13 _) (OpI.pop) (by decide) <|
  .nil 14

end FV7z.Ldf
