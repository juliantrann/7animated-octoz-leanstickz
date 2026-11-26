import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_Exit` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Exit
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x49, 0xc7, 0xc1, 0xb8, 0xff, 0xff, 0xff, 0x89, 0xfa, 0x41, 0xb8, 0xe7,
  0x00, 0x00, 0x00, 0xbe, 0x3c, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 9, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 231)] 6) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 60)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 9 (.i 18446744073709551544),
  Op.mov 32 2 (.r 7),
  Op.mov 32 8 (.i 231),
  Op.mov 32 6 (.i 60)]

theorem b0 (prof : Profile) : Blk prof p0 0 24 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 18446744073709551544) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.i 231) (.inl rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.mov (.i 60) (.inl rfl)) (by decide) <|
  .nil 24

def j0 : List Byte := [0xeb, 0x15]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk .jmp 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `47`. -/
def p1 : List Byte := [
  0x89, 0xd7, 0x44, 0x89, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 7 (.r 2),
  Op.mov 32 0 (.r 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Exit
