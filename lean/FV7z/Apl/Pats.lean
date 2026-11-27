import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `operator+(const AString &, const AString &)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Apl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x44, 0x8b, 0x4e, 0x08, 0x49, 0x89, 0xfc, 0x44, 0x8b, 0x42,
  0x08, 0x48, 0x8b, 0x0a, 0x48, 0x8b, 0x36, 0x44, 0x89, 0xca]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 9, .mem (mg (some 6) none 1 8 32)] 4) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 32 [gr 32 8, .mem (mg (some 2) none 1 8 32)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.ld 32 9 (some 6) none 1 8,
  Op.mov 64 12 (.r 7),
  Op.ld 32 8 (some 2) none 1 8,
  Op.ld 64 1 (some 2) none 1 0,
  Op.ld 64 6 (some 6) none 1 0,
  Op.mov 32 2 (.r 9)]

theorem b0 (prof : Profile) : Blk prof p0 0 26 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .nil 26

/-- The stretch at `31`. -/
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

end FV7z.Apl
