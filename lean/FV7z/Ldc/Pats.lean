import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCompress::NLzma::CDecoder::CDecoder` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ldc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0x98, 0xc4, 0x78, 0x00, 0xc6, 0x47, 0x46, 0x00, 0xc7,
  0x47, 0x40, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x50, 0x10, 0x48, 0xc7, 0x47, 0x70, 0x00, 0x00,
  0x00, 0x00, 0x48, 0x89, 0x17, 0x48, 0x8d, 0x90, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x57, 0x08,
  0x48, 0x8d, 0x90, 0xb8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x57, 0x10, 0x48, 0x8d, 0x90, 0xe8, 0x00,
  0x00, 0x00, 0x48, 0x89, 0x57, 0x18, 0x48, 0x8d, 0x90, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57,
  0x20, 0x48, 0x8d, 0x90, 0x50, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57, 0x28, 0x48, 0x8d, 0x90, 0x88,
  0x01, 0x00, 0x00, 0x48, 0x05, 0xb8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x47, 0x38, 0x31, 0xc0, 0x48,
  0x89, 0x57, 0x30, 0x66, 0x89, 0x47, 0x44, 0x48, 0xc7, 0x87, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x47, 0x48, 0x00, 0x00, 0x10, 0x00, 0x48, 0xc7, 0x47, 0x50, 0x00, 0x00,
  0x10, 0x00, 0x48, 0xc7, 0x47, 0x58, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0x60, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x87, 0x98, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x87,
  0x88, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7914648)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 70 8), .imm 8 0] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 64 32), .imm 32 0] 7) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 16 0)] 4) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 112 64), .imm 64 0] 8) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 2] 3) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 136 0)] 7) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 8 64), gr 64 2] 4) := by dec_rfl
theorem p0_48 : ∀ feat, Dec feat p0 48 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 184 0)] 7) := by dec_rfl
theorem p0_55 : ∀ feat, Dec feat p0 55 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), gr 64 2] 4) := by dec_rfl
theorem p0_59 : ∀ feat, Dec feat p0 59 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 232 0)] 7) := by dec_rfl
theorem p0_66 : ∀ feat, Dec feat p0 66 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), gr 64 2] 4) := by dec_rfl
theorem p0_70 : ∀ feat, Dec feat p0 70 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 280 0)] 7) := by dec_rfl
theorem p0_77 : ∀ feat, Dec feat p0 77 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), gr 64 2] 4) := by dec_rfl
theorem p0_81 : ∀ feat, Dec feat p0 81 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 336 0)] 7) := by dec_rfl
theorem p0_88 : ∀ feat, Dec feat p0 88 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 40 64), gr 64 2] 4) := by dec_rfl
theorem p0_92 : ∀ feat, Dec feat p0 92 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 392 0)] 7) := by dec_rfl
theorem p0_99 : ∀ feat, Dec feat p0 99 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 440)] 6) := by dec_rfl
theorem p0_105 : ∀ feat, Dec feat p0 105 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 56 64), gr 64 0] 4) := by dec_rfl
theorem p0_109 : ∀ feat, Dec feat p0 109 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_111 : ∀ feat, Dec feat p0 111 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 48 64), gr 64 2] 4) := by dec_rfl
theorem p0_115 : ∀ feat, Dec feat p0 115 (FV7z.mk .mov 16 [.mem (mg (some 7) none 1 68 16), gr 16 0] 4) := by dec_rfl
theorem p0_119 : ∀ feat, Dec feat p0 119 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 256 64), .imm 64 0] 11) := by dec_rfl
theorem p0_130 : ∀ feat, Dec feat p0 130 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 72 64), .imm 64 1048576] 8) := by dec_rfl
theorem p0_138 : ∀ feat, Dec feat p0 138 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 80 64), .imm 64 1048576] 8) := by dec_rfl
theorem p0_146 : ∀ feat, Dec feat p0 146 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 88 64), .imm 64 0] 8) := by dec_rfl
theorem p0_154 : ∀ feat, Dec feat p0 154 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 96 64), .imm 64 0] 8) := by dec_rfl
theorem p0_162 : ∀ feat, Dec feat p0 162 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 152 64), .imm 64 0] 11) := by dec_rfl
theorem p0_173 : ∀ feat, Dec feat p0 173 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 136 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 7914648),
  Op.sti 8 (some 7) none 1 70 0,
  Op.sti 32 (some 7) none 1 64 0,
  Op.lea 64 2 (some 0) none 1 16,
  Op.sti 64 (some 7) none 1 112 0,
  Op.st 64 (some 7) none 1 0 2,
  Op.lea 64 2 (some 0) none 1 136,
  Op.st 64 (some 7) none 1 8 2,
  Op.lea 64 2 (some 0) none 1 184,
  Op.st 64 (some 7) none 1 16 2,
  Op.lea 64 2 (some 0) none 1 232,
  Op.st 64 (some 7) none 1 24 2,
  Op.lea 64 2 (some 0) none 1 280,
  Op.st 64 (some 7) none 1 32 2,
  Op.lea 64 2 (some 0) none 1 336,
  Op.st 64 (some 7) none 1 40 2,
  Op.lea 64 2 (some 0) none 1 392,
  Op.add 64 0 (.i 440),
  Op.st 64 (some 7) none 1 56 0,
  Op.xor 32 0 (.r 0),
  Op.st 64 (some 7) none 1 48 2,
  Op.st 16 (some 7) none 1 68 0,
  Op.sti 64 (some 7) none 1 256 0,
  Op.sti 64 (some 7) none 1 72 1048576,
  Op.sti 64 (some 7) none 1 80 1048576,
  Op.sti 64 (some 7) none 1 88 0,
  Op.sti 64 (some 7) none 1 96 0,
  Op.sti 64 (some 7) none 1 152 0,
  Op.sti 64 (some 7) none 1 136 0]

theorem b0 (prof : Profile) : Blk prof p0 0 184 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7914648) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_22 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_34 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_37 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_44 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_48 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_55 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_59 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_66 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_70 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_77 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_81 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_88 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_92 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_99 _) (OpI.add (.i 440) (.inr rfl)) (by decide) <|
  .cons (p0_105 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_109 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_111 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_115 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p0_119 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_130 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_138 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_146 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_154 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_162 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_173 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 184

end FV7z.Ldc
