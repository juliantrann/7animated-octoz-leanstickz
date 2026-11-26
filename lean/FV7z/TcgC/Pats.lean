import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__tcgetattr` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.TcgC
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `86`. -/
def p0 : List Byte := [
  0x41, 0xc6, 0x40, 0x30, 0x00, 0x41, 0x88, 0x40, 0x10, 0x8b, 0x44, 0x24, 0x08, 0x66, 0x41, 0x89,
  0x50, 0x21, 0x0f, 0xb6, 0x54, 0x24, 0x23, 0x25, 0x0f, 0x10, 0x00, 0x00, 0x41, 0xc7, 0x40, 0x2c,
  0x00, 0x00, 0x00, 0x00, 0x41, 0x89, 0x40, 0x34, 0x41, 0x89, 0x40, 0x38, 0x41, 0x88, 0x50, 0x23]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 8 [.mem (mg (some 8) none 1 48 8), .imm 8 0] 5) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 8 [.mem (mg (some 8) none 1 16 8), gr 8 0] 4) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 8 32)] 4) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 16 [.mem (mg (some 8) none 1 33 16), gr 16 2] 5) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 4) none 1 35 8)] 5) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4111)] 5) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 32 [.mem (mg (some 8) none 1 44 32), .imm 32 0] 8) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 32 [.mem (mg (some 8) none 1 52 32), gr 32 0] 4) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .mov 32 [.mem (mg (some 8) none 1 56 32), gr 32 0] 4) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 8 [.mem (mg (some 8) none 1 35 8), gr 8 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.sti 8 (some 8) none 1 48 0,
  Op.st 8 (some 8) none 1 16 0,
  Op.ld 32 0 (some 4) none 1 8,
  Op.st 16 (some 8) none 1 33 2,
  Op.ldzx 8 2 (some 4) none 1 35,
  Op.and 32 0 (.i 4111),
  Op.sti 32 (some 8) none 1 44 0,
  Op.st 32 (some 8) none 1 52 0,
  Op.st 32 (some 8) none 1 56 0,
  Op.st 8 (some 8) none 1 35 2]

theorem b0 (prof : Profile) : Blk prof p0 0 48 o0 :=
  .cons (p0_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p0_18 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.and (.i 4111) (.inl rfl)) (by decide) <|
  .cons (p0_28 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_36 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_40 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_44 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 48

end FV7z.TcgC
