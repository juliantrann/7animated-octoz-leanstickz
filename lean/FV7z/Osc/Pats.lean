import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CStdOutStream::operator<< (const char *)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Osc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x48, 0x89, 0xf7, 0x49, 0x8b, 0x34, 0x24]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.mov 64 7 (.r 6),
  Op.ld 64 6 (some 12) none 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 16

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x4c, 0x89, 0xe0, 0x41, 0x5c]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 0 (.r 12),
  Op.pop 12]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.pop) (by decide) <|
  .nil 5

end FV7z.Osc
