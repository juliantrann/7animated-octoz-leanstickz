import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `InStream_SeekToBegin` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Isb
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x07, 0x31, 0xc9, 0x31, 0xd2, 0x31, 0xf6, 0x48, 0x8b, 0x40,
  0x20]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 32 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 64 0 (some 7) none 1 0,
  Op.xor 32 1 (.r 1),
  Op.xor 32 2 (.r 2),
  Op.xor 32 6 (.r 6),
  Op.ld 64 0 (some 0) none 1 32]

theorem b0 (prof : Profile) : Blk prof p0 0 17 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 17

end FV7z.Isb
