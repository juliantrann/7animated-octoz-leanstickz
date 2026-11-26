import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CDirItems::ScanProgress` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dsp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x4c, 0x8b, 0x87, 0xc0, 0x00, 0x00, 0x00, 0x48, 0x89, 0xf2, 0x4d, 0x85,
  0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 7) none 1 192 64)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 64 8 (some 7) none 1 192,
  Op.mov 64 2 (.r 6),
  Op.test 64 8 (.r 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 17 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 17

def j0 : List Byte := [0x74, 0x1d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `19`. -/
def p1 : List Byte := [
  0x49, 0x8b, 0x00, 0x48, 0x8d, 0x77, 0x48, 0xb9, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xc7, 0x48,
  0x8b, 0x40, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 8) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 7) none 1 72 0)] 4) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 8) none 1 0,
  Op.lea 64 6 (some 7) none 1 72,
  Op.mov 32 1 (.i 1),
  Op.mov 64 7 (.r 8),
  Op.ld 64 0 (some 0) none 1 8]

theorem b1 (prof : Profile) : Blk prof p1 0 19 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 19

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x31, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Dsp
