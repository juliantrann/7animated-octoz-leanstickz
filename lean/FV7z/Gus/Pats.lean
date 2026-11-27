import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArchiveExtractCallback::GetUnpackSize` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gus
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0xb7, 0xa8, 0x01, 0x00, 0x00, 0x48, 0x8d, 0x4f, 0x6a, 0x48, 0x8d,
  0x97, 0x98, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x7f, 0x40]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 7) none 1 424 32)] 6) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 7) none 1 106 0)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 7) none 1 408 0)] 7) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 64 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 6 (some 7) none 1 424,
  Op.lea 64 1 (some 7) none 1 106,
  Op.lea 64 2 (some 7) none 1 408,
  Op.ld 64 7 (some 7) none 1 64]

theorem b0 (prof : Profile) : Blk prof p0 0 25 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_21 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 25

end FV7z.Gus
