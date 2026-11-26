import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CLocalProgress::CLocalProgress` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lpc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0xd0, 0x3b, 0x78, 0x00, 0xc7, 0x47, 0x08, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x47, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc0, 0x10, 0x48, 0xc7,
  0x47, 0x18, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x07, 0xb8, 0x01, 0x01, 0x00, 0x00, 0x66, 0x89,
  0x47, 0x0c, 0x48, 0xc7, 0x47, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x28, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x47, 0x30, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7879632)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), .imm 64 0] 8) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), .imm 64 0] 8) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p0_41 : ∀ feat, Dec feat p0 41 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 257)] 5) := by dec_rfl
theorem p0_46 : ∀ feat, Dec feat p0 46 (FV7z.mk .mov 16 [.mem (mg (some 7) none 1 12 16), gr 16 0] 4) := by dec_rfl
theorem p0_50 : ∀ feat, Dec feat p0 50 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), .imm 64 0] 8) := by dec_rfl
theorem p0_58 : ∀ feat, Dec feat p0 58 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 40 64), .imm 64 0] 8) := by dec_rfl
theorem p0_66 : ∀ feat, Dec feat p0 66 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 48 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 7879632),
  Op.sti 32 (some 7) none 1 8 0,
  Op.sti 64 (some 7) none 1 16 0,
  Op.add 64 0 (.i 16),
  Op.sti 64 (some 7) none 1 24 0,
  Op.st 64 (some 7) none 1 0 0,
  Op.mov 32 0 (.i 257),
  Op.st 16 (some 7) none 1 12 0,
  Op.sti 64 (some 7) none 1 32 0,
  Op.sti 64 (some 7) none 1 40 0,
  Op.sti 64 (some 7) none 1 48 0]

theorem b0 (prof : Profile) : Blk prof p0 0 74 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7879632) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_18 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_26 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p0_30 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_38 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_41 _) (OpI.mov (.i 257) (.inl rfl)) (by decide) <|
  .cons (p0_46 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p0_50 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_58 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_66 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 74

end FV7z.Lpc
