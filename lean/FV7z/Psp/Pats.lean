import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `PrintSpaces` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Psp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x89, 0xf8, 0xbf, 0x20, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x05, 0x81, 0xe4, 0x0f, 0x00, 0x48,
  0x83, 0xec, 0x08, 0x44, 0x29, 0xc7, 0x48, 0x01, 0xc7, 0x48, 0xc7, 0xc0, 0x70, 0xed, 0x79, 0x00,
  0x48, 0x8b, 0x30]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 32)] 5) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1041537 0)] 7) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7990640)] 7) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.mov 32 8 (.r 7),
  Op.mov 32 7 (.i 32),
  Op.mov 64 0 (.i 7250528),
  Op.sub 64 4 (.i 8),
  Op.sub 32 7 (.r 8),
  Op.add 64 7 (.r 0),
  Op.mov 64 0 (.i 7990640),
  Op.ld 64 6 (some 0) none 1 0]

theorem b0 (prof : Profile) : BlkA prof p0 (0x5ebdd0 : Addr) 0 35 o0 :=
  .cons (p0_0 _) ((OpI.mov (.r 7) (.inl rfl)).at _) (by decide) <|
  .cons (p0_3 _) ((OpI.mov (.i 32) (.inl rfl)).at _) (by decide) <|
  .cons (p0_8 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_15 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_19 _) ((OpI.sub (.r 8) (.inl rfl)).at _) (by decide) <|
  .cons (p0_22 _) ((OpI.add (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p0_25 _) ((OpI.mov (.i 7990640) (.inr rfl)).at _) (by decide) <|
  .cons (p0_32 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .nil 35

/-- The stretch at `40`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Psp
