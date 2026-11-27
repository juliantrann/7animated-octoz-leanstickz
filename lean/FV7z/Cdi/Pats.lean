import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CDirItems::CDirItems` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cdi
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
  0x00, 0x00, 0x00, 0xc7, 0x47, 0x40, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x47, 0x44, 0x00, 0x48, 0xc7,
  0x47, 0x48, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x50, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7,
  0x47, 0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x60, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7,
  0x47, 0x68, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x70, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7,
  0x47, 0x78, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x87, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x48, 0xc7, 0x87, 0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x87, 0x90,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x87, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x87, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x87,
  0xa8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x87, 0xb0, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0xc6, 0x87, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x87, 0xc0, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 8 64), .imm 64 0] 8) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), .imm 64 0] 8) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), .imm 64 0] 8) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), .imm 64 0] 8) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 40 64), .imm 64 0] 8) := by dec_rfl
theorem p0_51 : ∀ feat, Dec feat p0 51 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 48 64), .imm 64 0] 8) := by dec_rfl
theorem p0_59 : ∀ feat, Dec feat p0 59 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 56 64), .imm 64 0] 8) := by dec_rfl
theorem p0_67 : ∀ feat, Dec feat p0 67 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 64 32), .imm 32 0] 7) := by dec_rfl
theorem p0_74 : ∀ feat, Dec feat p0 74 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 68 8), .imm 8 0] 4) := by dec_rfl
theorem p0_78 : ∀ feat, Dec feat p0 78 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 72 64), .imm 64 0] 8) := by dec_rfl
theorem p0_86 : ∀ feat, Dec feat p0 86 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 80 64), .imm 64 0] 8) := by dec_rfl
theorem p0_94 : ∀ feat, Dec feat p0 94 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 88 64), .imm 64 0] 8) := by dec_rfl
theorem p0_102 : ∀ feat, Dec feat p0 102 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 96 64), .imm 64 0] 8) := by dec_rfl
theorem p0_110 : ∀ feat, Dec feat p0 110 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 104 64), .imm 64 0] 8) := by dec_rfl
theorem p0_118 : ∀ feat, Dec feat p0 118 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 112 64), .imm 64 0] 8) := by dec_rfl
theorem p0_126 : ∀ feat, Dec feat p0 126 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 120 64), .imm 64 0] 8) := by dec_rfl
theorem p0_134 : ∀ feat, Dec feat p0 134 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 128 64), .imm 64 0] 11) := by dec_rfl
theorem p0_145 : ∀ feat, Dec feat p0 145 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 136 64), .imm 64 0] 11) := by dec_rfl
theorem p0_156 : ∀ feat, Dec feat p0 156 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 144 64), .imm 64 0] 11) := by dec_rfl
theorem p0_167 : ∀ feat, Dec feat p0 167 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 152 64), .imm 64 0] 11) := by dec_rfl
theorem p0_178 : ∀ feat, Dec feat p0 178 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 160 64), .imm 64 0] 11) := by dec_rfl
theorem p0_189 : ∀ feat, Dec feat p0 189 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 168 64), .imm 64 0] 11) := by dec_rfl
theorem p0_200 : ∀ feat, Dec feat p0 200 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 176 64), .imm 64 0] 11) := by dec_rfl
theorem p0_211 : ∀ feat, Dec feat p0 211 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 184 8), .imm 8 0] 7) := by dec_rfl
theorem p0_218 : ∀ feat, Dec feat p0 218 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 192 64), .imm 64 0] 11) := by dec_rfl

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
  Op.sti 32 (some 7) none 1 64 0,
  Op.sti 8 (some 7) none 1 68 0,
  Op.sti 64 (some 7) none 1 72 0,
  Op.sti 64 (some 7) none 1 80 0,
  Op.sti 64 (some 7) none 1 88 0,
  Op.sti 64 (some 7) none 1 96 0,
  Op.sti 64 (some 7) none 1 104 0,
  Op.sti 64 (some 7) none 1 112 0,
  Op.sti 64 (some 7) none 1 120 0,
  Op.sti 64 (some 7) none 1 128 0,
  Op.sti 64 (some 7) none 1 136 0,
  Op.sti 64 (some 7) none 1 144 0,
  Op.sti 64 (some 7) none 1 152 0,
  Op.sti 64 (some 7) none 1 160 0,
  Op.sti 64 (some 7) none 1 168 0,
  Op.sti 64 (some 7) none 1 176 0,
  Op.sti 8 (some 7) none 1 184 0,
  Op.sti 64 (some 7) none 1 192 0]

theorem b0 (prof : Profile) : Blk prof p0 0 229 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_11 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_19 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_27 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_35 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_43 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_51 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_59 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_67 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_74 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_78 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_86 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_94 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_102 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_110 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_118 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_126 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_134 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_145 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_156 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_167 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_178 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_189 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_200 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_211 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_218 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 229

end FV7z.Cdi
