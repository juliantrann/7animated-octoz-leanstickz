import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `ConvertUTF8ToUnicode_Flags` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.U8f
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x49, 0x89, 0xf0, 0x8b, 0x77, 0x08, 0x48, 0x8b, 0x3f, 0x89, 0xd1, 0x4c,
  0x89, 0xc2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 8 (.r 6),
  Op.ld 32 6 (some 7) none 1 8,
  Op.ld 64 7 (some 7) none 1 0,
  Op.mov 32 1 (.r 2),
  Op.mov 64 2 (.r 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 18

end FV7z.U8f
