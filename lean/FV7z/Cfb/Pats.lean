import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CFileInfoBase::ClearBase` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cfb
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0x07, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x08, 0x00,
  0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x10, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x18, 0x00,
  0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x20, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x28, 0x00,
  0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x30, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x38, 0x00,
  0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x40, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x47, 0x48, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x47, 0x50, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x58, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x47, 0x60, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 8 64), .imm 64 0] 8) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), .imm 64 0] 8) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), .imm 64 0] 8) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), .imm 64 0] 8) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 40 64), .imm 64 0] 8) := by dec_rfl
theorem p0_51 : ∀ feat, Dec feat p0 51 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 48 64), .imm 64 0] 8) := by dec_rfl
theorem p0_59 : ∀ feat, Dec feat p0 59 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 56 64), .imm 64 0] 8) := by dec_rfl
theorem p0_67 : ∀ feat, Dec feat p0 67 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 64 64), .imm 64 0] 8) := by dec_rfl
theorem p0_75 : ∀ feat, Dec feat p0 75 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 72 32), .imm 32 0] 7) := by dec_rfl
theorem p0_82 : ∀ feat, Dec feat p0 82 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 80 64), .imm 64 0] 8) := by dec_rfl
theorem p0_90 : ∀ feat, Dec feat p0 90 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 88 64), .imm 64 0] 8) := by dec_rfl
theorem p0_98 : ∀ feat, Dec feat p0 98 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 96 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sti 64 (some 7) none 1 0 0,
  Op.sti 64 (some 7) none 1 8 0,
  Op.sti 64 (some 7) none 1 16 0,
  Op.sti 64 (some 7) none 1 24 0,
  Op.sti 64 (some 7) none 1 32 0,
  Op.sti 64 (some 7) none 1 40 0,
  Op.sti 64 (some 7) none 1 48 0,
  Op.sti 64 (some 7) none 1 56 0,
  Op.sti 64 (some 7) none 1 64 0,
  Op.sti 32 (some 7) none 1 72 0,
  Op.sti 64 (some 7) none 1 80 0,
  Op.sti 64 (some 7) none 1 88 0,
  Op.sti 64 (some 7) none 1 96 0]

theorem b0 (prof : Profile) : Blk prof p0 0 106 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_11 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_19 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_27 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_35 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_43 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_51 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_59 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_67 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_75 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_82 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_90 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_98 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 106

end FV7z.Cfb
