import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArcErrorInfo::ClearErrors` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cle
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x47, 0x18, 0x48, 0xc7, 0x07, 0x00, 0x00, 0x00, 0x00, 0xc7,
  0x47, 0x08, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x10, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x47,
  0x20, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x47, 0x28, 0xc7,
  0x47, 0x30, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 24 64)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), .imm 64 0] 8) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 32 32), .imm 32 0] 7) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 0] 6) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 48 32), .imm 32 0] 7) := by dec_rfl
theorem p0_54 : ∀ feat, Dec feat p0 54 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 64 0 (some 7) none 1 24,
  Op.sti 64 (some 7) none 1 0 0,
  Op.sti 32 (some 7) none 1 8 0,
  Op.sti 64 (some 7) none 1 16 0,
  Op.sti 32 (some 7) none 1 32 0,
  Op.sti 32 (some 0) none 1 0 0,
  Op.ld 64 0 (some 7) none 1 40,
  Op.sti 32 (some 7) none 1 48 0,
  Op.sti 32 (some 0) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 60 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_15 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_22 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_30 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_37 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_43 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_47 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_54 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 60

end FV7z.Cle
