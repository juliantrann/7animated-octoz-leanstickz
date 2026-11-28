import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CompareStrings` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cst
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x8b, 0x02, 0x8b, 0x0f, 0x8b, 0x16, 0x48, 0x8b, 0x14, 0xd0, 0x48, 0x8b, 0x04, 0xc8, 0x48,
  0x8b, 0x32, 0x48, 0x8b, 0x38]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 6) none 1 0 32)] 2) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) (some 2) 8 0 64)] 4) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) (some 1) 8 0 64)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.ld 64 0 (some 2) none 1 0,
  Op.ld 32 1 (some 7) none 1 0,
  Op.ld 32 2 (some 6) none 1 0,
  Op.ld 64 2 (some 0) (some 2) 8 0,
  Op.ld 64 0 (some 0) (some 1) 8 0,
  Op.ld 64 6 (some 2) none 1 0,
  Op.ld 64 7 (some 0) none 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 21 o0 :=
  .cons (p0_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 21

end FV7z.Cst
