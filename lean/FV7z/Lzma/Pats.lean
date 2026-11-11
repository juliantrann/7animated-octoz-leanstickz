import FV7z.Lemmas.Sp
/-!
# The stretches of straight-line code of `LzmaDec_DecodeReal_3` (PLAN.md G2, pilot)

Each distinct stretch between labels and jumps (`p*`, 82 of them) and each distinct jump (`j*`, 50) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lzma
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x53, 0x55, 0x41, 0x54, 0x41, 0x55, 0x41, 0x56, 0x41, 0x57, 0x48, 0x8d, 0x44, 0x24, 0x80, 0x48,
  0x83, 0xe0, 0x80, 0x48, 0x8b, 0xec, 0x48, 0x8b, 0xe0, 0x48, 0x89, 0x28, 0x48, 0x89, 0x78, 0x08,
  0xc7, 0x40, 0x64, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x50, 0x48, 0x48, 0x8b, 0xdf, 0x4c, 0x8b,
  0x63, 0x18, 0x49, 0x03, 0xf4, 0x48, 0x89, 0x70, 0x40, 0x8b, 0x7b, 0x48, 0x89, 0x78, 0x70, 0x8b,
  0x7b, 0x4c, 0x89, 0x78, 0x74, 0x8b, 0x7b, 0x50, 0x89, 0x78, 0x78, 0x8b, 0x7b, 0x54, 0x89, 0x78,
  0x7c, 0x4c, 0x8b, 0x73, 0x28, 0x4d, 0x03, 0xf4, 0x4c, 0x89, 0x70, 0x68, 0x4c, 0x89, 0x60, 0x38,
  0x8a, 0x4b, 0x02, 0xbf, 0x01, 0x00, 0x00, 0x00, 0xd3, 0xe7, 0xff, 0xcf, 0x89, 0x78, 0x58, 0x8a,
  0x0b, 0xba, 0x00, 0x01, 0x00, 0x00, 0x8b, 0xfa, 0xd3, 0xea, 0x80, 0xc1, 0x01, 0x89, 0x48, 0x50,
  0x8a, 0x4b, 0x01, 0xd3, 0xe7, 0x2b, 0xfa, 0x89, 0x78, 0x54, 0x44, 0x8b, 0xcf, 0x4c, 0x8b, 0x5b,
  0x10, 0x4c, 0x89, 0x58, 0x30, 0x48, 0x8b, 0x7b, 0x20, 0x48, 0x89, 0x78, 0x28, 0x8b, 0x4b, 0x44,
  0x89, 0x48, 0x5c, 0x44, 0x8b, 0x6b, 0x40, 0x44, 0x8b, 0x43, 0x58, 0x41, 0xd1, 0xe0, 0x4c, 0x8b,
  0x7b, 0x30, 0x8b, 0x43, 0x38, 0x8b, 0x6b, 0x3c, 0x41, 0xba, 0x00, 0x08, 0x00, 0x00, 0x33, 0xdb,
  0x41, 0x0b, 0xcd]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_1 : ∀ feat, Dec feat p0 1 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 4) none 1 18446744073709551488 0)] 5) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551488)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 64 [gr 64 4, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 5] 3) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), gr 64 7] 4) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 100 32), .imm 32 0] 7) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 72 64), gr 64 2] 4) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_46 : ∀ feat, Dec feat p0 46 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 3) none 1 24 64)] 4) := by dec_rfl
theorem p0_50 : ∀ feat, Dec feat p0 50 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p0_53 : ∀ feat, Dec feat p0 53 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 64 64), gr 64 6] 4) := by dec_rfl
theorem p0_57 : ∀ feat, Dec feat p0 57 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 72 32)] 3) := by dec_rfl
theorem p0_60 : ∀ feat, Dec feat p0 60 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 112 32), gr 32 7] 3) := by dec_rfl
theorem p0_63 : ∀ feat, Dec feat p0 63 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 76 32)] 3) := by dec_rfl
theorem p0_66 : ∀ feat, Dec feat p0 66 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 116 32), gr 32 7] 3) := by dec_rfl
theorem p0_69 : ∀ feat, Dec feat p0 69 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 80 32)] 3) := by dec_rfl
theorem p0_72 : ∀ feat, Dec feat p0 72 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 120 32), gr 32 7] 3) := by dec_rfl
theorem p0_75 : ∀ feat, Dec feat p0 75 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 3) none 1 84 32)] 3) := by dec_rfl
theorem p0_78 : ∀ feat, Dec feat p0 78 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 124 32), gr 32 7] 3) := by dec_rfl
theorem p0_81 : ∀ feat, Dec feat p0 81 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 3) none 1 40 64)] 4) := by dec_rfl
theorem p0_85 : ∀ feat, Dec feat p0 85 (FV7z.mk .add 64 [gr 64 14, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p0_88 : ∀ feat, Dec feat p0 88 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 104 64), gr 64 14] 4) := by dec_rfl
theorem p0_92 : ∀ feat, Dec feat p0 92 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 56 64), gr 64 12] 4) := by dec_rfl
theorem p0_96 : ∀ feat, Dec feat p0 96 (FV7z.mk .mov 8 [gr 8 1, .mem (mg (some 3) none 1 2 8)] 3) := by dec_rfl
theorem p0_99 : ∀ feat, Dec feat p0 99 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p0_104 : ∀ feat, Dec feat p0 104 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p0_106 : ∀ feat, Dec feat p0 106 (FV7z.mk .dec 32 [gr 32 7] 2) := by dec_rfl
theorem p0_108 : ∀ feat, Dec feat p0 108 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 88 32), gr 32 7] 3) := by dec_rfl
theorem p0_111 : ∀ feat, Dec feat p0 111 (FV7z.mk .mov 8 [gr 8 1, .mem (mg (some 3) none 1 0 8)] 2) := by dec_rfl
theorem p0_113 : ∀ feat, Dec feat p0 113 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 256)] 5) := by dec_rfl
theorem p0_118 : ∀ feat, Dec feat p0 118 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_120 : ∀ feat, Dec feat p0 120 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p0_122 : ∀ feat, Dec feat p0 122 (FV7z.mk .add 8 [gr 8 1, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p0_125 : ∀ feat, Dec feat p0 125 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 80 32), gr 32 1] 3) := by dec_rfl
theorem p0_128 : ∀ feat, Dec feat p0 128 (FV7z.mk .mov 8 [gr 8 1, .mem (mg (some 3) none 1 1 8)] 3) := by dec_rfl
theorem p0_131 : ∀ feat, Dec feat p0 131 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p0_133 : ∀ feat, Dec feat p0 133 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_135 : ∀ feat, Dec feat p0 135 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 84 32), gr 32 7] 3) := by dec_rfl
theorem p0_138 : ∀ feat, Dec feat p0 138 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p0_141 : ∀ feat, Dec feat p0 141 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 3) none 1 16 64)] 4) := by dec_rfl
theorem p0_145 : ∀ feat, Dec feat p0 145 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 48 64), gr 64 11] 4) := by dec_rfl
theorem p0_149 : ∀ feat, Dec feat p0 149 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 32 64)] 4) := by dec_rfl
theorem p0_153 : ∀ feat, Dec feat p0 153 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 40 64), gr 64 7] 4) := by dec_rfl
theorem p0_157 : ∀ feat, Dec feat p0 157 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 3) none 1 68 32)] 3) := by dec_rfl
theorem p0_160 : ∀ feat, Dec feat p0 160 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 92 32), gr 32 1] 3) := by dec_rfl
theorem p0_163 : ∀ feat, Dec feat p0 163 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 3) none 1 64 32)] 4) := by dec_rfl
theorem p0_167 : ∀ feat, Dec feat p0 167 (FV7z.mk .mov 32 [gr 32 8, .mem (mg (some 3) none 1 88 32)] 4) := by dec_rfl
theorem p0_171 : ∀ feat, Dec feat p0 171 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p0_174 : ∀ feat, Dec feat p0 174 (FV7z.mk .mov 64 [gr 64 15, .mem (mg (some 3) none 1 48 64)] 4) := by dec_rfl
theorem p0_178 : ∀ feat, Dec feat p0 178 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 56 32)] 3) := by dec_rfl
theorem p0_181 : ∀ feat, Dec feat p0 181 (FV7z.mk .mov 32 [gr 32 5, .mem (mg (some 3) none 1 60 32)] 3) := by dec_rfl
theorem p0_184 : ∀ feat, Dec feat p0 184 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 2048)] 6) := by dec_rfl
theorem p0_190 : ∀ feat, Dec feat p0 190 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p0_192 : ∀ feat, Dec feat p0 192 (FV7z.mk .or 32 [gr 32 1, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 3,
  Op.push 5,
  Op.push 12,
  Op.push 13,
  Op.push 14,
  Op.push 15,
  Op.lea 64 0 (some 4) none 1 18446744073709551488,
  Op.and 64 0 (.i 18446744073709551488),
  Op.mov 64 5 (.r 4),
  Op.mov 64 4 (.r 0),
  Op.st 64 (some 0) none 1 0 5,
  Op.st 64 (some 0) none 1 8 7,
  Op.sti 32 (some 0) none 1 100 0,
  Op.st 64 (some 0) none 1 72 2,
  Op.mov 64 3 (.r 7),
  Op.ld 64 12 (some 3) none 1 24,
  Op.add 64 6 (.r 12),
  Op.st 64 (some 0) none 1 64 6,
  Op.ld 32 7 (some 3) none 1 72,
  Op.st 32 (some 0) none 1 112 7,
  Op.ld 32 7 (some 3) none 1 76,
  Op.st 32 (some 0) none 1 116 7,
  Op.ld 32 7 (some 3) none 1 80,
  Op.st 32 (some 0) none 1 120 7,
  Op.ld 32 7 (some 3) none 1 84,
  Op.st 32 (some 0) none 1 124 7,
  Op.ld 64 14 (some 3) none 1 40,
  Op.add 64 14 (.r 12),
  Op.st 64 (some 0) none 1 104 14,
  Op.st 64 (some 0) none 1 56 12,
  Op.ld8 1 (some 3) none 1 2,
  Op.mov 32 7 (.i 1),
  Op.shl 7 (.r 1),
  Op.dec 32 7,
  Op.st 32 (some 0) none 1 88 7,
  Op.ld8 1 (some 3) none 1 0,
  Op.mov 32 2 (.i 256),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.r 1),
  Op.add8 1 (.i 1),
  Op.st 32 (some 0) none 1 80 1,
  Op.ld8 1 (some 3) none 1 1,
  Op.shl 7 (.r 1),
  Op.sub 32 7 (.r 2),
  Op.st 32 (some 0) none 1 84 7,
  Op.mov 32 9 (.r 7),
  Op.ld 64 11 (some 3) none 1 16,
  Op.st 64 (some 0) none 1 48 11,
  Op.ld 64 7 (some 3) none 1 32,
  Op.st 64 (some 0) none 1 40 7,
  Op.ld 32 1 (some 3) none 1 68,
  Op.st 32 (some 0) none 1 92 1,
  Op.ld 32 13 (some 3) none 1 64,
  Op.ld 32 8 (some 3) none 1 88,
  Op.shl 8 (.i 1),
  Op.ld 64 15 (some 3) none 1 48,
  Op.ld 32 0 (some 3) none 1 56,
  Op.ld 32 5 (some 3) none 1 60,
  Op.mov 32 10 (.i 2048),
  Op.xor 32 3 (.r 3),
  Op.or 32 1 (.r 13)]

theorem b0 (prof : Profile) : Blk prof p0 0 195 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_1 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.push) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.and (.i 18446744073709551488) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_28 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_32 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_39 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_43 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_46 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_50 _) (OpI.add (.r 12) (.inr rfl)) (by decide) <|
  .cons (p0_53 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_57 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_60 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_63 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_66 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_69 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_72 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_75 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_78 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_81 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_85 _) (OpI.add (.r 12) (.inr rfl)) (by decide) <|
  .cons (p0_88 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_92 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_96 _) (OpI.ld8) (by decide) <|
  .cons (p0_99 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p0_104 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p0_106 _) (OpI.dec (.inl rfl)) (by decide) <|
  .cons (p0_108 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_111 _) (OpI.ld8) (by decide) <|
  .cons (p0_113 _) (OpI.mov (.i 256) (.inl rfl)) (by decide) <|
  .cons (p0_118 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_120 _) (OpI.shr (.r 1)) (by decide) <|
  .cons (p0_122 _) (OpI.add8 (.i 1)) (by decide) <|
  .cons (p0_125 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_128 _) (OpI.ld8) (by decide) <|
  .cons (p0_131 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p0_133 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_135 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_138 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_141 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_145 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_149 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_153 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_157 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_160 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_163 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_167 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_171 _) (OpI.shl (.i 1)) (by decide) <|
  .cons (p0_174 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_178 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_181 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_184 _) (OpI.mov (.i 2048) (.inl rfl)) (by decide) <|
  .cons (p0_190 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p0_192 _) (OpI.or (.r 13) (.inl rfl)) (by decide) <|
  .nil 195

def j0 : List Byte := [0x74, 0x0e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `197`. -/
def p1 : List Byte := [
  0x49, 0x03, 0xfc, 0x4d, 0x3b, 0xf4, 0x49, 0x0f, 0x45, 0xfe, 0x0f, 0xb6, 0x5f, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 64 [gr 64 14, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk (.cmovcc 5) 64 [gr 64 7, gr 64 14] 4) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 7) none 1 18446744073709551615 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 7 (.r 12),
  Op.cmp 64 14 (.r 12),
  Op.cmov64 5 7 14,
  Op.ldzx 8 3 (some 7) none 1 18446744073709551615]

theorem b1 (prof : Profile) : Blk prof p1 0 14 o1 :=
  .cons (p1_0 _) (OpI.add (.r 12) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.cmp (.r 12) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.cmov64) (by decide) <|
  .cons (p1_10 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 14

/-- The stretch at `211`. -/
def p2 : List Byte := [
  0x8b, 0x4c, 0x24, 0x58, 0x41, 0x23, 0xcd, 0xc1, 0xe1, 0x05, 0x4b, 0x8d, 0x34, 0x03, 0x41, 0x83,
  0xf8, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 88 32)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 11) (some 8) 1 0 0)] 4) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 1 (some 4) none 1 88,
  Op.and 32 1 (.r 13),
  Op.shl 1 (.i 5),
  Op.lea 64 6 (some 11) (some 8) 1 0,
  Op.cmp 32 8 (.i 8)]

theorem b2 (prof : Profile) : Blk prof p2 0 18 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.and (.r 13) (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.shl (.i 5)) (by decide) <|
  .cons (p2_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.cmp (.i 8) (.inl rfl)) (by decide) <|
  .nil 18

def j1 : List Byte := [0x0f, 0x82, 0xfe, 0x02, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 2) 64 [.rel 766] 6) := by dec_rfl

/-- The stretch at `235`. -/
def p3 : List Byte := [
  0x41, 0x83, 0xf8, 0x0e]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 14)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 8 (.i 14)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 14) (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x0f, 0x82, 0xc5, 0x0d, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 2) 64 [.rel 3525] 6) := by dec_rfl

def j3 : List Byte := [0xe9, 0x0f, 0x0a, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 2575] 5) := by dec_rfl

/-- The stretch at `256`. -/
def p4 : List Byte := [
  0x45, 0x33, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 8 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `259`. -/
def p5 : List Byte := [
  0x41, 0x8b, 0xfd, 0xc1, 0xe7, 0x08, 0x03, 0xdf, 0x41, 0x23, 0xd9, 0x48, 0x03, 0xf1, 0x8b, 0x4c,
  0x24, 0x50, 0x8d, 0x1c, 0x5b, 0x49, 0x81, 0xc3, 0x80, 0x02, 0x00, 0x00, 0xd3, 0xe3, 0x4c, 0x03,
  0xdb, 0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x89, 0x96, 0x00, 0xfe,
  0xff, 0xff, 0x41, 0xff, 0xc5, 0x41, 0x0f, 0xb7, 0x4b, 0x02, 0x41, 0x0f, 0xb7, 0x53, 0x04]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .and 32 [gr 32 3, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 80 32)] 4) := by dec_rfl
theorem p5_18 : ∀ feat, Dec feat p5 18 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 3) (some 3) 2 0 0)] 3) := by dec_rfl
theorem p5_21 : ∀ feat, Dec feat p5 21 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 640)] 7) := by dec_rfl
theorem p5_28 : ∀ feat, Dec feat p5 28 (FV7z.mk .shl 32 [gr 32 3, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p5_30 : ∀ feat, Dec feat p5 30 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p5_33 : ∀ feat, Dec feat p5 33 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p5_36 : ∀ feat, Dec feat p5 36 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_38 : ∀ feat, Dec feat p5 38 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p5_41 : ∀ feat, Dec feat p5 41 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p5_43 : ∀ feat, Dec feat p5 43 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 18446744073709551104 16), gr 16 2] 7) := by dec_rfl
theorem p5_50 : ∀ feat, Dec feat p5 50 (FV7z.mk .inc 32 [gr 32 13] 3) := by dec_rfl
theorem p5_53 : ∀ feat, Dec feat p5 53 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 11) none 1 2 16)] 5) := by dec_rfl
theorem p5_58 : ∀ feat, Dec feat p5 58 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) none 1 4 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 7 (.r 13),
  Op.shl 7 (.i 8),
  Op.add 32 3 (.r 7),
  Op.and 32 3 (.r 9),
  Op.add 64 6 (.r 1),
  Op.ld 32 1 (some 4) none 1 80,
  Op.lea 32 3 (some 3) (some 3) 2 0,
  Op.add 64 11 (.i 640),
  Op.shl 3 (.r 1),
  Op.add 64 11 (.r 3),
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 6) none 1 18446744073709551104 2,
  Op.inc 32 13,
  Op.ldzx 16 1 (some 11) none 1 2,
  Op.ldzx 16 2 (some 11) none 1 4]

theorem b5 (prof : Profile) : Blk prof p5 0 63 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p5_6 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.and (.r 9) (.inl rfl)) (by decide) <|
  .cons (p5_11 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p5_14 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_18 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p5_21 _) (OpI.add (.i 640) (.inr rfl)) (by decide) <|
  .cons (p5_28 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p5_30 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .cons (p5_33 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p5_36 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_38 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p5_41 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p5_43 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p5_50 _) (OpI.inc (.inl rfl)) (by decide) <|
  .cons (p5_53 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p5_58 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 63

/-- The stretch at `322`. -/
def p6 : List Byte := [
  0x3d, 0x00, 0x00, 0x00, 0x01]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16777216)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 0 (.i 16777216)]

theorem b6 (prof : Profile) : Blk prof p6 0 5 o6 :=
  .cons (p6_0 _) (OpI.cmp (.i 16777216) (.inl rfl)) (by decide) <|
  .nil 5

def j4 : List Byte := [0x73, 0x0c]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 3) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `329`. -/
def p7 : List Byte := [
  0xc1, 0xe5, 0x08, 0x41, 0x8a, 0x2f, 0xc1, 0xe0, 0x08, 0x49, 0xff, 0xc7]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .shl 32 [gr 32 5, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 8 [gr 8 5, .mem (mg (some 15) none 1 0 8)] 3) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .inc 64 [gr 64 15] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.shl 5 (.i 8),
  Op.ld8 5 (some 15) none 1 0,
  Op.shl 0 (.i 8),
  Op.inc 64 15]

theorem b7 (prof : Profile) : Blk prof p7 0 12 o7 :=
  .cons (p7_0 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p7_3 _) (OpI.ld8) (by decide) <|
  .cons (p7_6 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p7_9 _) (OpI.inc (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `341`. -/
def p8 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7b, 0x06, 0x0f, 0x43, 0xd7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42,
  0xee, 0x41, 0x0f, 0x42, 0xfa, 0xbb, 0x02, 0x00, 0x00, 0x00, 0x83, 0xdb, 0xff, 0x2b, 0xf9, 0xc1,
  0xff, 0x05, 0x03, 0xf9, 0x66, 0x41, 0x89, 0x7b, 0x02, 0x41, 0x0f, 0xb7, 0x0c, 0x9b, 0x03, 0xdb]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_2 : ∀ feat, Dec feat p8 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_14 : ∀ feat, Dec feat p8 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p8_17 : ∀ feat, Dec feat p8 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) none 1 6 16)] 5) := by dec_rfl
theorem p8_22 : ∀ feat, Dec feat p8 22 (FV7z.mk (.cmovcc 3) 32 [gr 32 2, gr 32 7] 3) := by dec_rfl
theorem p8_25 : ∀ feat, Dec feat p8 25 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p8_30 : ∀ feat, Dec feat p8 30 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p8_33 : ∀ feat, Dec feat p8 33 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p8_37 : ∀ feat, Dec feat p8 37 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p8_42 : ∀ feat, Dec feat p8 42 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p8_45 : ∀ feat, Dec feat p8 45 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p8_47 : ∀ feat, Dec feat p8 47 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p8_50 : ∀ feat, Dec feat p8 50 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p8_52 : ∀ feat, Dec feat p8 52 (FV7z.mk .mov 16 [.mem (mg (some 11) none 1 2 16), gr 16 7] 5) := by dec_rfl
theorem p8_57 : ∀ feat, Dec feat p8 57 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 11) (some 3) 4 0 16)] 5) := by dec_rfl
theorem p8_62 : ∀ feat, Dec feat p8 62 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) none 1 6,
  Op.cmov32 3 2 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.cmov32 2 7 10,
  Op.mov 32 3 (.i 2),
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 11) none 1 2 7,
  Op.ldzx 16 1 (some 11) (some 3) 4 0,
  Op.add 32 3 (.r 3)]

theorem b8 (prof : Profile) : Blk prof p8 0 64 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p8_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p8_5 _) (OpI.imul) (by decide) <|
  .cons (p8_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p8_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p8_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p8_14 _) (OpI.cmov32) (by decide) <|
  .cons (p8_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p8_22 _) (OpI.cmov32) (by decide) <|
  .cons (p8_25 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p8_30 _) (OpI.cmov32) (by decide) <|
  .cons (p8_33 _) (OpI.cmov32) (by decide) <|
  .cons (p8_37 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p8_42 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p8_45 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p8_47 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p8_50 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p8_52 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p8_57 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p8_62 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 64

/-- The stretch at `424`. -/
def p9 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7c, 0x5b, 0x02, 0x0f, 0x43, 0xcf, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f,
  0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83, 0xdb, 0xff, 0x2b, 0xfa, 0xc1, 0xff, 0x05,
  0x03, 0xfa, 0x66, 0x41, 0x89, 0x3c, 0x33, 0x41, 0x0f, 0xb7, 0x14, 0x9b, 0x03, 0xdb]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p9_12 : ∀ feat, Dec feat p9 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_14 : ∀ feat, Dec feat p9 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p9_17 : ∀ feat, Dec feat p9 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) (some 3) 2 2 16)] 6) := by dec_rfl
theorem p9_23 : ∀ feat, Dec feat p9 23 (FV7z.mk (.cmovcc 3) 32 [gr 32 1, gr 32 7] 3) := by dec_rfl
theorem p9_26 : ∀ feat, Dec feat p9 26 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p9_31 : ∀ feat, Dec feat p9 31 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p9_34 : ∀ feat, Dec feat p9 34 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p9_36 : ∀ feat, Dec feat p9 36 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p9_40 : ∀ feat, Dec feat p9 40 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p9_43 : ∀ feat, Dec feat p9 43 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p9_45 : ∀ feat, Dec feat p9 45 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p9_48 : ∀ feat, Dec feat p9 48 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p9_50 : ∀ feat, Dec feat p9 50 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p9_55 : ∀ feat, Dec feat p9 55 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) (some 3) 4 0 16)] 5) := by dec_rfl
theorem p9_60 : ∀ feat, Dec feat p9 60 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) (some 3) 2 2,
  Op.cmov32 3 1 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.ldzx 16 2 (some 11) (some 3) 4 0,
  Op.add 32 3 (.r 3)]

theorem b9 (prof : Profile) : Blk prof p9 0 62 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p9_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p9_5 _) (OpI.imul) (by decide) <|
  .cons (p9_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p9_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p9_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p9_14 _) (OpI.cmov32) (by decide) <|
  .cons (p9_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p9_23 _) (OpI.cmov32) (by decide) <|
  .cons (p9_26 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p9_31 _) (OpI.cmov32) (by decide) <|
  .cons (p9_34 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p9_36 _) (OpI.cmov32) (by decide) <|
  .cons (p9_40 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p9_43 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p9_45 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p9_48 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p9_50 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p9_55 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p9_60 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 62

/-- The stretch at `505`. -/
def p10 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7c, 0x5b, 0x02, 0x0f, 0x43, 0xd7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f,
  0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83, 0xdb, 0xff, 0x2b, 0xf9, 0xc1, 0xff, 0x05,
  0x03, 0xf9, 0x66, 0x41, 0x89, 0x3c, 0x33, 0x41, 0x0f, 0xb7, 0x0c, 0x9b, 0x03, 0xdb]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p10_12 : ∀ feat, Dec feat p10 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p10_14 : ∀ feat, Dec feat p10 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p10_17 : ∀ feat, Dec feat p10 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) (some 3) 2 2 16)] 6) := by dec_rfl
theorem p10_23 : ∀ feat, Dec feat p10 23 (FV7z.mk (.cmovcc 3) 32 [gr 32 2, gr 32 7] 3) := by dec_rfl
theorem p10_26 : ∀ feat, Dec feat p10 26 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p10_31 : ∀ feat, Dec feat p10 31 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p10_34 : ∀ feat, Dec feat p10 34 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p10_36 : ∀ feat, Dec feat p10 36 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p10_40 : ∀ feat, Dec feat p10 40 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p10_43 : ∀ feat, Dec feat p10 43 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p10_45 : ∀ feat, Dec feat p10 45 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p10_48 : ∀ feat, Dec feat p10 48 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p10_50 : ∀ feat, Dec feat p10 50 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p10_55 : ∀ feat, Dec feat p10 55 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 11) (some 3) 4 0 16)] 5) := by dec_rfl
theorem p10_60 : ∀ feat, Dec feat p10 60 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) (some 3) 2 2,
  Op.cmov32 3 2 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.ldzx 16 1 (some 11) (some 3) 4 0,
  Op.add 32 3 (.r 3)]

theorem b10 (prof : Profile) : Blk prof p10 0 62 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p10_5 _) (OpI.imul) (by decide) <|
  .cons (p10_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p10_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p10_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p10_14 _) (OpI.cmov32) (by decide) <|
  .cons (p10_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p10_23 _) (OpI.cmov32) (by decide) <|
  .cons (p10_26 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p10_31 _) (OpI.cmov32) (by decide) <|
  .cons (p10_34 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p10_36 _) (OpI.cmov32) (by decide) <|
  .cons (p10_40 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p10_43 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p10_45 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p10_48 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p10_50 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p10_55 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p10_60 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 62

/-- The stretch at `829`. -/
def p11 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7c, 0x5b, 0x02, 0x0f, 0x43, 0xd7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f,
  0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83, 0xdb, 0xff, 0x2b, 0xf9, 0xc1, 0xff, 0x05,
  0x03, 0xf9, 0x66, 0x41, 0x89, 0x3c, 0x33, 0x03, 0xdb]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p11_2 : ∀ feat, Dec feat p11 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p11_12 : ∀ feat, Dec feat p11 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p11_14 : ∀ feat, Dec feat p11 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p11_17 : ∀ feat, Dec feat p11 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) (some 3) 2 2 16)] 6) := by dec_rfl
theorem p11_23 : ∀ feat, Dec feat p11 23 (FV7z.mk (.cmovcc 3) 32 [gr 32 2, gr 32 7] 3) := by dec_rfl
theorem p11_26 : ∀ feat, Dec feat p11 26 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p11_31 : ∀ feat, Dec feat p11 31 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p11_34 : ∀ feat, Dec feat p11 34 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p11_36 : ∀ feat, Dec feat p11 36 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p11_40 : ∀ feat, Dec feat p11 40 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p11_43 : ∀ feat, Dec feat p11 43 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p11_45 : ∀ feat, Dec feat p11 45 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p11_48 : ∀ feat, Dec feat p11 48 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p11_50 : ∀ feat, Dec feat p11 50 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p11_55 : ∀ feat, Dec feat p11 55 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) (some 3) 2 2,
  Op.cmov32 3 2 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.add 32 3 (.r 3)]

theorem b11 (prof : Profile) : Blk prof p11 0 57 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p11_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p11_5 _) (OpI.imul) (by decide) <|
  .cons (p11_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p11_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p11_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p11_14 _) (OpI.cmov32) (by decide) <|
  .cons (p11_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p11_23 _) (OpI.cmov32) (by decide) <|
  .cons (p11_26 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p11_31 _) (OpI.cmov32) (by decide) <|
  .cons (p11_34 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p11_36 _) (OpI.cmov32) (by decide) <|
  .cons (p11_40 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p11_43 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p11_45 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p11_48 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p11_50 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p11_55 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 57

/-- The stretch at `905`. -/
def p12 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x81,
  0xdb, 0xff, 0x00, 0x00, 0x00, 0x2b, 0xfa, 0xc1, 0xff, 0x05, 0x03, 0xfa, 0x66, 0x41, 0x89, 0x3c,
  0x33, 0x4c, 0x8b, 0x5c, 0x24, 0x30, 0x8b, 0x4c, 0x24, 0x58, 0x41, 0x23, 0xcd, 0xc1, 0xe1, 0x05,
  0x4b, 0x8d, 0x34, 0x03, 0x41, 0x88, 0x1e, 0x49, 0xff, 0xc6, 0x4c, 0x3b, 0x7c, 0x24, 0x48]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p12_2 : ∀ feat, Dec feat p12 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p12_10 : ∀ feat, Dec feat p12 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p12_12 : ∀ feat, Dec feat p12 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p12_14 : ∀ feat, Dec feat p12 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p12_17 : ∀ feat, Dec feat p12 17 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p12_22 : ∀ feat, Dec feat p12 22 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p12_25 : ∀ feat, Dec feat p12 25 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p12_27 : ∀ feat, Dec feat p12 27 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p12_31 : ∀ feat, Dec feat p12 31 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 255)] 6) := by dec_rfl
theorem p12_37 : ∀ feat, Dec feat p12 37 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p12_39 : ∀ feat, Dec feat p12 39 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p12_42 : ∀ feat, Dec feat p12 42 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p12_44 : ∀ feat, Dec feat p12 44 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p12_49 : ∀ feat, Dec feat p12 49 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 4) none 1 48 64)] 5) := by dec_rfl
theorem p12_54 : ∀ feat, Dec feat p12 54 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 88 32)] 4) := by dec_rfl
theorem p12_58 : ∀ feat, Dec feat p12 58 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p12_61 : ∀ feat, Dec feat p12 61 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p12_64 : ∀ feat, Dec feat p12 64 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 11) (some 8) 1 0 0)] 4) := by dec_rfl
theorem p12_68 : ∀ feat, Dec feat p12 68 (FV7z.mk .mov 8 [.mem (mg (some 14) none 1 0 8), gr 8 3] 3) := by dec_rfl
theorem p12_71 : ∀ feat, Dec feat p12 71 (FV7z.mk .inc 64 [gr 64 14] 3) := by dec_rfl
theorem p12_74 : ∀ feat, Dec feat p12 74 (FV7z.mk .cmp 64 [gr 64 15, .mem (mg (some 4) none 1 72 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 255),
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.ld 64 11 (some 4) none 1 48,
  Op.ld 32 1 (some 4) none 1 88,
  Op.and 32 1 (.r 13),
  Op.shl 1 (.i 5),
  Op.lea 64 6 (some 11) (some 8) 1 0,
  Op.st 8 (some 14) none 1 0 3,
  Op.inc 64 14,
  Op.cmpm 64 15 (some 4) none 1 72]

theorem b12 (prof : Profile) : Blk prof p12 0 79 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p12_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p12_5 _) (OpI.imul) (by decide) <|
  .cons (p12_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p12_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p12_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p12_14 _) (OpI.cmov32) (by decide) <|
  .cons (p12_17 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p12_22 _) (OpI.cmov32) (by decide) <|
  .cons (p12_25 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p12_27 _) (OpI.cmov32) (by decide) <|
  .cons (p12_31 _) (OpI.sbb (.i 255) (.inl rfl)) (by decide) <|
  .cons (p12_37 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p12_39 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p12_42 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p12_44 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p12_49 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_54 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p12_58 _) (OpI.and (.r 13) (.inl rfl)) (by decide) <|
  .cons (p12_61 _) (OpI.shl (.i 5)) (by decide) <|
  .cons (p12_64 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_68 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p12_71 _) (OpI.inc (.inr rfl)) (by decide) <|
  .cons (p12_74 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 79

def j5 : List Byte := [0x0f, 0x83, 0x25, 0x0e, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 3) 64 [.rel 3621] 6) := by dec_rfl

/-- The stretch at `990`. -/
def p13 : List Byte := [
  0x4c, 0x3b, 0x74, 0x24, 0x40]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 64 [gr 64 14, .mem (mg (some 4) none 1 64 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmpm 64 14 (some 4) none 1 64]

theorem b13 (prof : Profile) : Blk prof p13 0 5 o13 :=
  .cons (p13_0 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 5

def j6 : List Byte := [0x0f, 0x83, 0x1a, 0x0e, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 3) 64 [.rel 3610] 6) := by dec_rfl

/-- The stretch at `1001`. -/
def p14 : List Byte := [
  0x0f, 0xb7, 0x94, 0x0e, 0x00, 0xfe, 0xff, 0xff]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) (some 1) 1 18446744073709551104 16)] 8) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ldzx 16 2 (some 6) (some 1) 1 18446744073709551104]

theorem b14 (prof : Profile) : Blk prof p14 0 8 o14 :=
  .cons (p14_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `1028`. -/
def p15 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x3b, 0xe8]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p15_2 : ∀ feat, Dec feat p15 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.cmp 32 5 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 10 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p15_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p15_5 _) (OpI.imul) (by decide) <|
  .cons (p15_8 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 10

def j7 : List Byte := [0x0f, 0x82, 0xec, 0xfc, 0xff, 0xff]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709550828] 6) := by dec_rfl

/-- The stretch at `1044`. -/
def p16 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x89, 0xbc,
  0x0e, 0x00, 0xfe, 0xff, 0xff, 0x0f, 0xb7, 0x56, 0x20]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_2 : ∀ feat, Dec feat p16 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p16_6 : ∀ feat, Dec feat p16 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p16_8 : ∀ feat, Dec feat p16 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p16_11 : ∀ feat, Dec feat p16 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p16_13 : ∀ feat, Dec feat p16 13 (FV7z.mk .mov 16 [.mem (mg (some 6) (some 1) 1 18446744073709551104 16), gr 16 7] 8) := by dec_rfl
theorem p16_21 : ∀ feat, Dec feat p16 21 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) none 1 32 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 6) (some 1) 1 18446744073709551104 7,
  Op.ldzx 16 2 (some 6) none 1 32]

theorem b16 (prof : Profile) : Blk prof p16 0 25 o16 :=
  .cons (p16_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p16_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p16_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p16_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p16_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p16_21 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 25

def j8 : List Byte := [0x0f, 0x83, 0x10, 0x0b, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 3) 64 [.rel 2832] 6) := by dec_rfl

/-- The stretch at `1104`. -/
def p17 : List Byte := [
  0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x89, 0x56, 0x20, 0x49, 0x81,
  0xc3, 0x00, 0xfa, 0xff, 0xff, 0x41, 0x83, 0xc0, 0x18]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p17_5 : ∀ feat, Dec feat p17 5 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p17_8 : ∀ feat, Dec feat p17 8 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p17_10 : ∀ feat, Dec feat p17 10 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 32 16), gr 16 2] 4) := by dec_rfl
theorem p17_14 : ∀ feat, Dec feat p17 14 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 18446744073709550080)] 7) := by dec_rfl
theorem p17_21 : ∀ feat, Dec feat p17 21 (FV7z.mk .add 32 [gr 32 8, Src.opd 32 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 6) none 1 32 2,
  Op.add 64 11 (.i 18446744073709550080),
  Op.add 32 8 (.i 24)]

theorem b17 (prof : Profile) : Blk prof p17 0 25 o17 :=
  .cons (p17_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p17_5 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p17_8 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p17_10 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p17_14 _) (OpI.add (.i 18446744073709550080) (.inr rfl)) (by decide) <|
  .cons (p17_21 _) (OpI.add (.i 24) (.inl rfl)) (by decide) <|
  .nil 25

/-- The stretch at `1129`. -/
def p18 : List Byte := [
  0x41, 0xbc, 0x05, 0x00, 0x00, 0x00, 0x41, 0x0f, 0xb7, 0x13]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 5)] 6) := by dec_rfl
theorem p18_6 : ∀ feat, Dec feat p18 6 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) none 1 0 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.mov 32 12 (.i 5),
  Op.ldzx 16 2 (some 11) none 1 0]

theorem b18 (prof : Profile) : Blk prof p18 0 10 o18 :=
  .cons (p18_0 _) (OpI.mov (.i 5) (.inl rfl)) (by decide) <|
  .cons (p18_6 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 10

def j9 : List Byte := [0x0f, 0x82, 0xca, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 2) 64 [.rel 202] 6) := by dec_rfl

/-- The stretch at `1174`. -/
def p19 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x41, 0x89,
  0x3b, 0x49, 0x83, 0xc3, 0x10, 0x41, 0xbc, 0xfd, 0xff, 0xff, 0xff, 0x41, 0x0f, 0xb7, 0x13]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p19_2 : ∀ feat, Dec feat p19 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p19_6 : ∀ feat, Dec feat p19 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p19_8 : ∀ feat, Dec feat p19 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p19_11 : ∀ feat, Dec feat p19 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p19_13 : ∀ feat, Dec feat p19 13 (FV7z.mk .mov 16 [.mem (mg (some 11) none 1 0 16), gr 16 7] 4) := by dec_rfl
theorem p19_17 : ∀ feat, Dec feat p19 17 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p19_21 : ∀ feat, Dec feat p19 21 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 4294967293)] 6) := by dec_rfl
theorem p19_27 : ∀ feat, Dec feat p19 27 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) none 1 0 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 11) none 1 0 7,
  Op.add 64 11 (.i 16),
  Op.mov 32 12 (.i 4294967293),
  Op.ldzx 16 2 (some 11) none 1 0]

theorem b19 (prof : Profile) : Blk prof p19 0 31 o19 :=
  .cons (p19_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p19_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p19_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p19_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p19_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p19_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p19_17 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p19_21 _) (OpI.mov (.i 4294967293) (.inl rfl)) (by decide) <|
  .cons (p19_27 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 31

def j10 : List Byte := [0x0f, 0x82, 0x88, 0x00, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 2) 64 [.rel 136] 6) := by dec_rfl

/-- The stretch at `1240`. -/
def p20 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x41, 0x89,
  0x3b, 0x49, 0x81, 0xc3, 0xf0, 0x01, 0x00, 0x00, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x41, 0x0f, 0xb7,
  0x4b, 0x02, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p20_2 : ∀ feat, Dec feat p20 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p20_6 : ∀ feat, Dec feat p20 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p20_8 : ∀ feat, Dec feat p20 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p20_11 : ∀ feat, Dec feat p20 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p20_13 : ∀ feat, Dec feat p20 13 (FV7z.mk .mov 16 [.mem (mg (some 11) none 1 0 16), gr 16 7] 4) := by dec_rfl
theorem p20_17 : ∀ feat, Dec feat p20 17 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 496)] 7) := by dec_rfl
theorem p20_24 : ∀ feat, Dec feat p20 24 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p20_29 : ∀ feat, Dec feat p20 29 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 11) none 1 2 16)] 5) := by dec_rfl
theorem p20_34 : ∀ feat, Dec feat p20 34 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 11) none 1 0 7,
  Op.add 64 11 (.i 496),
  Op.mov 32 3 (.i 1),
  Op.ldzx 16 1 (some 11) none 1 2,
  Op.nop]

theorem b20 (prof : Profile) : Blk prof p20 0 40 o20 :=
  .cons (p20_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p20_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p20_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p20_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p20_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p20_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p20_17 _) (OpI.add (.i 496) (.inr rfl)) (by decide) <|
  .cons (p20_24 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p20_29 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p20_34 _) (OpI.nop) (by decide) <|
  .nil 40

/-- The stretch at `1280`. -/
def p21 : List Byte := [
  0x41, 0x0f, 0xb7, 0x14, 0x9b, 0x03, 0xdb]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) (some 3) 4 0 16)] 5) := by dec_rfl
theorem p21_5 : ∀ feat, Dec feat p21 5 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.ldzx 16 2 (some 11) (some 3) 4 0,
  Op.add 32 3 (.r 3)]

theorem b21 (prof : Profile) : Blk prof p21 0 7 o21 :=
  .cons (p21_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p21_5 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `1306`. -/
def p22 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7c, 0x5b, 0x02, 0x0f, 0x43, 0xd7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f,
  0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83, 0xdb, 0xff, 0x2b, 0xf9, 0xc1, 0xff, 0x05,
  0x03, 0xf9, 0x66, 0x41, 0x89, 0x3c, 0x33, 0x8b, 0xca, 0x83, 0xfb, 0x40]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p22_2 : ∀ feat, Dec feat p22 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p22_5 : ∀ feat, Dec feat p22 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p22_8 : ∀ feat, Dec feat p22 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p22_10 : ∀ feat, Dec feat p22 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p22_12 : ∀ feat, Dec feat p22 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p22_14 : ∀ feat, Dec feat p22 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p22_17 : ∀ feat, Dec feat p22 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) (some 3) 2 2 16)] 6) := by dec_rfl
theorem p22_23 : ∀ feat, Dec feat p22 23 (FV7z.mk (.cmovcc 3) 32 [gr 32 2, gr 32 7] 3) := by dec_rfl
theorem p22_26 : ∀ feat, Dec feat p22 26 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p22_31 : ∀ feat, Dec feat p22 31 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p22_34 : ∀ feat, Dec feat p22 34 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p22_36 : ∀ feat, Dec feat p22 36 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p22_40 : ∀ feat, Dec feat p22 40 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p22_43 : ∀ feat, Dec feat p22 43 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p22_45 : ∀ feat, Dec feat p22 45 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p22_48 : ∀ feat, Dec feat p22 48 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p22_50 : ∀ feat, Dec feat p22 50 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p22_55 : ∀ feat, Dec feat p22 55 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p22_57 : ∀ feat, Dec feat p22 57 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.i 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) (some 3) 2 2,
  Op.cmov32 3 2 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.mov 32 1 (.r 2),
  Op.cmp 32 3 (.i 64)]

theorem b22 (prof : Profile) : Blk prof p22 0 60 o22 :=
  .cons (p22_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p22_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p22_5 _) (OpI.imul) (by decide) <|
  .cons (p22_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p22_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p22_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p22_14 _) (OpI.cmov32) (by decide) <|
  .cons (p22_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p22_23 _) (OpI.cmov32) (by decide) <|
  .cons (p22_26 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p22_31 _) (OpI.cmov32) (by decide) <|
  .cons (p22_34 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p22_36 _) (OpI.cmov32) (by decide) <|
  .cons (p22_40 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p22_43 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p22_45 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p22_48 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p22_50 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p22_55 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p22_57 _) (OpI.cmp (.i 64) (.inl rfl)) (by decide) <|
  .nil 60

def j11 : List Byte := [0x72, 0xa8]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551528] 2) := by dec_rfl

/-- The stretch at `1368`. -/
def p23 : List Byte := [
  0x41, 0xbc, 0xed, 0x00, 0x00, 0x00]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 237)] 6) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 32 12 (.i 237)]

theorem b23 (prof : Profile) : Blk prof p23 0 6 o23 :=
  .cons (p23_0 _) (OpI.mov (.i 237) (.inl rfl)) (by decide) <|
  .nil 6

def j12 : List Byte := [0xeb, 0x67]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk .jmp 64 [.rel 103] 2) := by dec_rfl

/-- The stretch at `1376`. -/
def p24 : List Byte := [
  0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x41, 0x89, 0x13, 0x4c, 0x03,
  0xd9, 0x41, 0x0f, 0xb7, 0x53, 0x02, 0x41, 0x0f, 0xb7, 0x4b, 0x04]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p24_3 : ∀ feat, Dec feat p24 3 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p24_5 : ∀ feat, Dec feat p24 5 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p24_8 : ∀ feat, Dec feat p24 8 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p24_10 : ∀ feat, Dec feat p24 10 (FV7z.mk .mov 16 [.mem (mg (some 11) none 1 0 16), gr 16 2] 4) := by dec_rfl
theorem p24_14 : ∀ feat, Dec feat p24 14 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p24_17 : ∀ feat, Dec feat p24 17 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) none 1 2 16)] 5) := by dec_rfl
theorem p24_22 : ∀ feat, Dec feat p24 22 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 11) none 1 4 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 11) none 1 0 2,
  Op.add 64 11 (.r 1),
  Op.ldzx 16 2 (some 11) none 1 2,
  Op.ldzx 16 1 (some 11) none 1 4]

theorem b24 (prof : Profile) : Blk prof p24 0 27 o24 :=
  .cons (p24_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p24_3 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p24_5 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p24_8 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p24_10 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p24_14 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p24_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p24_22 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 27

/-- The stretch at `1422`. -/
def p25 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7b, 0x06, 0x0f, 0x43, 0xcf, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42,
  0xee, 0x41, 0x0f, 0x42, 0xfa, 0xbb, 0x02, 0x00, 0x00, 0x00, 0x83, 0xdb, 0xff, 0x2b, 0xfa, 0xc1,
  0xff, 0x05, 0x03, 0xfa, 0x66, 0x41, 0x89, 0x7b, 0x02]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p25_2 : ∀ feat, Dec feat p25 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p25_5 : ∀ feat, Dec feat p25 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p25_8 : ∀ feat, Dec feat p25 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p25_10 : ∀ feat, Dec feat p25 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p25_12 : ∀ feat, Dec feat p25 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p25_14 : ∀ feat, Dec feat p25 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p25_17 : ∀ feat, Dec feat p25 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) none 1 6 16)] 5) := by dec_rfl
theorem p25_22 : ∀ feat, Dec feat p25 22 (FV7z.mk (.cmovcc 3) 32 [gr 32 1, gr 32 7] 3) := by dec_rfl
theorem p25_25 : ∀ feat, Dec feat p25 25 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p25_30 : ∀ feat, Dec feat p25 30 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p25_33 : ∀ feat, Dec feat p25 33 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p25_37 : ∀ feat, Dec feat p25 37 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p25_42 : ∀ feat, Dec feat p25 42 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p25_45 : ∀ feat, Dec feat p25 45 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p25_47 : ∀ feat, Dec feat p25 47 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p25_50 : ∀ feat, Dec feat p25 50 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p25_52 : ∀ feat, Dec feat p25 52 (FV7z.mk .mov 16 [.mem (mg (some 11) none 1 2 16), gr 16 7] 5) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) none 1 6,
  Op.cmov32 3 1 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.cmov32 2 7 10,
  Op.mov 32 3 (.i 2),
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 11) none 1 2 7]

theorem b25 (prof : Profile) : Blk prof p25 0 57 o25 :=
  .cons (p25_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p25_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p25_5 _) (OpI.imul) (by decide) <|
  .cons (p25_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p25_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p25_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p25_14 _) (OpI.cmov32) (by decide) <|
  .cons (p25_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p25_22 _) (OpI.cmov32) (by decide) <|
  .cons (p25_25 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p25_30 _) (OpI.cmov32) (by decide) <|
  .cons (p25_33 _) (OpI.cmov32) (by decide) <|
  .cons (p25_37 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p25_42 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p25_45 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p25_47 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p25_50 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p25_52 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 57

/-- The stretch at `1581`. -/
def p26 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x41,
  0x1b, 0xdc, 0x2b, 0xfa, 0xc1, 0xff, 0x05, 0x03, 0xfa, 0x66, 0x41, 0x89, 0x3c, 0x33, 0x4c, 0x8b,
  0x5c, 0x24, 0x30, 0x41, 0x83, 0xf8, 0x18]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p26_2 : ∀ feat, Dec feat p26 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p26_5 : ∀ feat, Dec feat p26 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p26_8 : ∀ feat, Dec feat p26 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p26_10 : ∀ feat, Dec feat p26 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p26_12 : ∀ feat, Dec feat p26 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p26_14 : ∀ feat, Dec feat p26 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p26_17 : ∀ feat, Dec feat p26 17 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p26_22 : ∀ feat, Dec feat p26 22 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p26_25 : ∀ feat, Dec feat p26 25 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p26_27 : ∀ feat, Dec feat p26 27 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p26_31 : ∀ feat, Dec feat p26 31 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p26_34 : ∀ feat, Dec feat p26 34 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p26_36 : ∀ feat, Dec feat p26 36 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p26_39 : ∀ feat, Dec feat p26 39 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p26_41 : ∀ feat, Dec feat p26 41 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p26_46 : ∀ feat, Dec feat p26 46 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 4) none 1 48 64)] 5) := by dec_rfl
theorem p26_51 : ∀ feat, Dec feat p26 51 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.r 12),
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.ld 64 11 (some 4) none 1 48,
  Op.cmp 32 8 (.i 24)]

theorem b26 (prof : Profile) : Blk prof p26 0 55 o26 :=
  .cons (p26_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p26_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p26_5 _) (OpI.imul) (by decide) <|
  .cons (p26_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p26_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p26_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p26_14 _) (OpI.cmov32) (by decide) <|
  .cons (p26_17 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p26_22 _) (OpI.cmov32) (by decide) <|
  .cons (p26_25 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p26_27 _) (OpI.cmov32) (by decide) <|
  .cons (p26_31 _) (OpI.sbb (.r 12) (.inl rfl)) (by decide) <|
  .cons (p26_34 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p26_36 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p26_39 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p26_41 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p26_46 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p26_51 _) (OpI.cmp (.i 24) (.inl rfl)) (by decide) <|
  .nil 55

def j13 : List Byte := [0x0f, 0x82, 0xfe, 0x03, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 2) 64 [.rel 1022] 6) := by dec_rfl

/-- The stretch at `1642`. -/
def p27 : List Byte := [
  0xbf, 0x05, 0x00, 0x00, 0x00, 0x83, 0xfb, 0x05, 0x0f, 0x42, 0xfb, 0x49, 0x83, 0xc3, 0x80, 0xc1,
  0xe7, 0x07, 0x4c, 0x03, 0xdf, 0x44, 0x8b, 0xe3, 0x41, 0x0f, 0xb7, 0x4b, 0x02, 0x41, 0x0f, 0xb7,
  0x53, 0x04]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 5)] 5) := by dec_rfl
theorem p27_5 : ∀ feat, Dec feat p27 5 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.i 5)] 3) := by dec_rfl
theorem p27_8 : ∀ feat, Dec feat p27 8 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 3] 3) := by dec_rfl
theorem p27_11 : ∀ feat, Dec feat p27 11 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 18446744073709551488)] 4) := by dec_rfl
theorem p27_15 : ∀ feat, Dec feat p27 15 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.i 7)] 3) := by dec_rfl
theorem p27_18 : ∀ feat, Dec feat p27 18 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p27_21 : ∀ feat, Dec feat p27 21 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p27_24 : ∀ feat, Dec feat p27 24 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 11) none 1 2 16)] 5) := by dec_rfl
theorem p27_29 : ∀ feat, Dec feat p27 29 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) none 1 4 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.mov 32 7 (.i 5),
  Op.cmp 32 3 (.i 5),
  Op.cmov32 2 7 3,
  Op.add 64 11 (.i 18446744073709551488),
  Op.shl 7 (.i 7),
  Op.add 64 11 (.r 7),
  Op.mov 32 12 (.r 3),
  Op.ldzx 16 1 (some 11) none 1 2,
  Op.ldzx 16 2 (some 11) none 1 4]

theorem b27 (prof : Profile) : Blk prof p27 0 34 o27 :=
  .cons (p27_0 _) (OpI.mov (.i 5) (.inl rfl)) (by decide) <|
  .cons (p27_5 _) (OpI.cmp (.i 5) (.inl rfl)) (by decide) <|
  .cons (p27_8 _) (OpI.cmov32) (by decide) <|
  .cons (p27_11 _) (OpI.add (.i 18446744073709551488) (.inr rfl)) (by decide) <|
  .cons (p27_15 _) (OpI.shl (.i 7)) (by decide) <|
  .cons (p27_18 _) (OpI.add (.r 7) (.inr rfl)) (by decide) <|
  .cons (p27_21 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p27_24 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p27_29 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 34

/-- The stretch at `2021`. -/
def p28 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7c, 0x5b, 0x02, 0x0f, 0x43, 0xd7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f,
  0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83, 0xdb, 0xff, 0x2b, 0xf9, 0xc1, 0xff, 0x05,
  0x03, 0xf9, 0x66, 0x41, 0x89, 0x3c, 0x33, 0x8b, 0xcb, 0x03, 0xdb]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p28_2 : ∀ feat, Dec feat p28 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p28_5 : ∀ feat, Dec feat p28 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p28_8 : ∀ feat, Dec feat p28 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p28_10 : ∀ feat, Dec feat p28 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p28_12 : ∀ feat, Dec feat p28 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p28_14 : ∀ feat, Dec feat p28 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p28_17 : ∀ feat, Dec feat p28 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) (some 3) 2 2 16)] 6) := by dec_rfl
theorem p28_23 : ∀ feat, Dec feat p28 23 (FV7z.mk (.cmovcc 3) 32 [gr 32 2, gr 32 7] 3) := by dec_rfl
theorem p28_26 : ∀ feat, Dec feat p28 26 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p28_31 : ∀ feat, Dec feat p28 31 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p28_34 : ∀ feat, Dec feat p28 34 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p28_36 : ∀ feat, Dec feat p28 36 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p28_40 : ∀ feat, Dec feat p28 40 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p28_43 : ∀ feat, Dec feat p28 43 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p28_45 : ∀ feat, Dec feat p28 45 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p28_48 : ∀ feat, Dec feat p28 48 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p28_50 : ∀ feat, Dec feat p28 50 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p28_55 : ∀ feat, Dec feat p28 55 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p28_57 : ∀ feat, Dec feat p28 57 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) (some 3) 2 2,
  Op.cmov32 3 2 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.mov 32 1 (.r 3),
  Op.add 32 3 (.r 3)]

theorem b28 (prof : Profile) : Blk prof p28 0 59 o28 :=
  .cons (p28_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p28_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p28_5 _) (OpI.imul) (by decide) <|
  .cons (p28_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p28_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p28_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p28_14 _) (OpI.cmov32) (by decide) <|
  .cons (p28_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p28_23 _) (OpI.cmov32) (by decide) <|
  .cons (p28_26 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p28_31 _) (OpI.cmov32) (by decide) <|
  .cons (p28_34 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p28_36 _) (OpI.cmov32) (by decide) <|
  .cons (p28_40 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p28_43 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p28_45 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p28_48 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p28_50 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p28_55 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p28_57 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 59

/-- The stretch at `2099`. -/
def p29 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83,
  0xdb, 0x3f, 0x2b, 0xfa, 0xc1, 0xff, 0x05, 0x03, 0xfa, 0x66, 0x41, 0x89, 0x3c, 0x33, 0x83, 0xe3,
  0x03, 0x4c, 0x8b, 0x5c, 0x24, 0x30, 0x83, 0xf9, 0x27]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p29_2 : ∀ feat, Dec feat p29 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p29_5 : ∀ feat, Dec feat p29 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p29_8 : ∀ feat, Dec feat p29 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p29_10 : ∀ feat, Dec feat p29 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p29_12 : ∀ feat, Dec feat p29 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p29_14 : ∀ feat, Dec feat p29 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p29_17 : ∀ feat, Dec feat p29 17 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p29_22 : ∀ feat, Dec feat p29 22 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p29_25 : ∀ feat, Dec feat p29 25 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p29_27 : ∀ feat, Dec feat p29 27 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p29_31 : ∀ feat, Dec feat p29 31 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p29_34 : ∀ feat, Dec feat p29 34 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p29_36 : ∀ feat, Dec feat p29 36 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p29_39 : ∀ feat, Dec feat p29 39 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p29_41 : ∀ feat, Dec feat p29 41 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 6) 1 0 16), gr 16 7] 5) := by dec_rfl
theorem p29_46 : ∀ feat, Dec feat p29 46 (FV7z.mk .and 32 [gr 32 3, Src.opd 32 (.i 3)] 3) := by dec_rfl
theorem p29_49 : ∀ feat, Dec feat p29 49 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 4) none 1 48 64)] 5) := by dec_rfl
theorem p29_54 : ∀ feat, Dec feat p29 54 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 39)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 63),
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 11) (some 6) 1 0 7,
  Op.and 32 3 (.i 3),
  Op.ld 64 11 (some 4) none 1 48,
  Op.cmp 32 1 (.i 39)]

theorem b29 (prof : Profile) : Blk prof p29 0 57 o29 :=
  .cons (p29_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p29_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p29_5 _) (OpI.imul) (by decide) <|
  .cons (p29_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p29_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p29_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p29_14 _) (OpI.cmov32) (by decide) <|
  .cons (p29_17 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p29_22 _) (OpI.cmov32) (by decide) <|
  .cons (p29_25 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p29_27 _) (OpI.cmov32) (by decide) <|
  .cons (p29_31 _) (OpI.sbb (.i 63) (.inl rfl)) (by decide) <|
  .cons (p29_34 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p29_36 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p29_39 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p29_41 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p29_46 _) (OpI.and (.i 3) (.inl rfl)) (by decide) <|
  .cons (p29_49 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p29_54 _) (OpI.cmp (.i 39) (.inl rfl)) (by decide) <|
  .nil 57

def j14 : List Byte := [0x0f, 0x82, 0x8e, 0x08, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 2) 64 [.rel 2190] 6) := by dec_rfl

/-- The stretch at `2162`. -/
def p30 : List Byte := [
  0x83, 0xe9, 0x25, 0x83, 0xcb, 0x02, 0x41, 0x0f, 0xb7, 0x53, 0x02, 0xc1, 0xe3, 0x05, 0x4d, 0x8d,
  0x4b, 0x04]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 37)] 3) := by dec_rfl
theorem p30_3 : ∀ feat, Dec feat p30 3 (FV7z.mk .or 32 [gr 32 3, Src.opd 32 (.i 2)] 3) := by dec_rfl
theorem p30_6 : ∀ feat, Dec feat p30 6 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 11) none 1 2 16)] 5) := by dec_rfl
theorem p30_11 : ∀ feat, Dec feat p30 11 (FV7z.mk .shl 32 [gr 32 3, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p30_14 : ∀ feat, Dec feat p30 14 (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 11) none 1 4 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.sub 32 1 (.i 37),
  Op.or 32 3 (.i 2),
  Op.ldzx 16 2 (some 11) none 1 2,
  Op.shl 3 (.i 5),
  Op.lea 64 9 (some 11) none 1 4]

theorem b30 (prof : Profile) : Blk prof p30 0 18 o30 :=
  .cons (p30_0 _) (OpI.sub (.i 37) (.inl rfl)) (by decide) <|
  .cons (p30_3 _) (OpI.or (.i 2) (.inl rfl)) (by decide) <|
  .cons (p30_6 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p30_11 _) (OpI.shl (.i 5)) (by decide) <|
  .cons (p30_14 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 18

def j15 : List Byte := [0xeb, 0x2c]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 44] 2) := by dec_rfl

/-- The stretch at `2208`. -/
def p31 : List Byte := [
  0xd1, 0xe8, 0x8b, 0xfd, 0x2b, 0xe8, 0x0f, 0x48, 0xef, 0x0f, 0x49, 0xde, 0xff, 0xc9]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p31_2 : ∀ feat, Dec feat p31 2 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p31_4 : ∀ feat, Dec feat p31 4 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p31_6 : ∀ feat, Dec feat p31 6 (FV7z.mk (.cmovcc 8) 32 [gr 32 5, gr 32 7] 3) := by dec_rfl
theorem p31_9 : ∀ feat, Dec feat p31 9 (FV7z.mk (.cmovcc 9) 32 [gr 32 3, gr 32 6] 3) := by dec_rfl
theorem p31_12 : ∀ feat, Dec feat p31 12 (FV7z.mk .dec 32 [gr 32 1] 2) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.shr 0 (.i 1),
  Op.mov 32 7 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 8 5 7,
  Op.cmov32 9 3 6,
  Op.dec 32 1]

theorem b31 (prof : Profile) : Blk prof p31 0 14 o31 :=
  .cons (p31_0 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p31_2 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p31_4 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p31_6 _) (OpI.cmov32) (by decide) <|
  .cons (p31_9 _) (OpI.cmov32) (by decide) <|
  .cons (p31_12 _) (OpI.dec (.inl rfl)) (by decide) <|
  .nil 14

def j16 : List Byte := [0x74, 0x30]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 4) 64 [.rel 48] 2) := by dec_rfl

/-- The stretch at `2224`. -/
def p32 : List Byte := [
  0x03, 0xdb]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.add 32 3 (.r 3)]

theorem b32 (prof : Profile) : Blk prof p32 0 2 o32 :=
  .cons (p32_0 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `2226`. -/
def p33 : List Byte := [
  0x8d, 0x73, 0x10]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 3) none 1 16 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.lea 32 6 (some 3) none 1 16]

theorem b33 (prof : Profile) : Blk prof p33 0 3 o33 :=
  .cons (p33_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 3

def j17 : List Byte := [0x0f, 0x83, 0xe0, 0xff, 0xff, 0xff]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551584] 6) := by dec_rfl

def j18 : List Byte := [0xeb, 0xd2]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk .jmp 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `2272`. -/
def p34 : List Byte := [
  0x41, 0x0f, 0xb7, 0x09]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 9) none 1 0 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.ldzx 16 1 (some 9) none 1 0]

theorem b34 (prof : Profile) : Blk prof p34 0 4 o34 :=
  .cons (p34_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `2295`. -/
def p35 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x7b, 0x06, 0x0f, 0x43, 0xcf, 0x0f, 0x42, 0xee, 0xbf, 0x1f, 0x00, 0x00,
  0x00, 0x41, 0x0f, 0x42, 0xfa, 0x49, 0x8d, 0x73, 0x06, 0x4c, 0x0f, 0x43, 0xce, 0x2b, 0xfa, 0xc1,
  0xff, 0x05, 0x03, 0xfa, 0x66, 0x41, 0x89, 0x7b, 0x02, 0x49, 0x83, 0xc1, 0x04, 0x41, 0x0f, 0xb7,
  0x11]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p35_2 : ∀ feat, Dec feat p35 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p35_5 : ∀ feat, Dec feat p35 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p35_8 : ∀ feat, Dec feat p35 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p35_10 : ∀ feat, Dec feat p35 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p35_12 : ∀ feat, Dec feat p35 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p35_14 : ∀ feat, Dec feat p35 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p35_17 : ∀ feat, Dec feat p35 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 11) none 1 6 16)] 5) := by dec_rfl
theorem p35_22 : ∀ feat, Dec feat p35 22 (FV7z.mk (.cmovcc 3) 32 [gr 32 1, gr 32 7] 3) := by dec_rfl
theorem p35_25 : ∀ feat, Dec feat p35 25 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p35_28 : ∀ feat, Dec feat p35 28 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p35_33 : ∀ feat, Dec feat p35 33 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p35_37 : ∀ feat, Dec feat p35 37 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 11) none 1 6 0)] 4) := by dec_rfl
theorem p35_41 : ∀ feat, Dec feat p35 41 (FV7z.mk (.cmovcc 3) 64 [gr 64 9, gr 64 6] 4) := by dec_rfl
theorem p35_45 : ∀ feat, Dec feat p35 45 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p35_47 : ∀ feat, Dec feat p35 47 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p35_50 : ∀ feat, Dec feat p35 50 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p35_52 : ∀ feat, Dec feat p35 52 (FV7z.mk .mov 16 [.mem (mg (some 11) none 1 2 16), gr 16 7] 5) := by dec_rfl
theorem p35_57 : ∀ feat, Dec feat p35 57 (FV7z.mk .add 64 [gr 64 9, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p35_61 : ∀ feat, Dec feat p35 61 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 9) none 1 0 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 11) none 1 6,
  Op.cmov32 3 1 7,
  Op.cmov32 2 5 6,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 7 10,
  Op.lea 64 6 (some 11) none 1 6,
  Op.cmov64 3 9 6,
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 11) none 1 2 7,
  Op.add 64 9 (.i 4),
  Op.ldzx 16 2 (some 9) none 1 0]

theorem b35 (prof : Profile) : Blk prof p35 0 65 o35 :=
  .cons (p35_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p35_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p35_5 _) (OpI.imul) (by decide) <|
  .cons (p35_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p35_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p35_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p35_14 _) (OpI.cmov32) (by decide) <|
  .cons (p35_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p35_22 _) (OpI.cmov32) (by decide) <|
  .cons (p35_25 _) (OpI.cmov32) (by decide) <|
  .cons (p35_28 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p35_33 _) (OpI.cmov32) (by decide) <|
  .cons (p35_37 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p35_41 _) (OpI.cmov64) (by decide) <|
  .cons (p35_45 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p35_47 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p35_50 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p35_52 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p35_57 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p35_61 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 65

/-- The stretch at `2379`. -/
def p36 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x79, 0x04, 0x0f, 0x43, 0xd7, 0x0f, 0x42, 0xee, 0xbf, 0x1f, 0x00, 0x00,
  0x00, 0x41, 0x0f, 0x42, 0xfa, 0x49, 0x8d, 0x71, 0x04, 0x4c, 0x0f, 0x43, 0xce, 0x2b, 0xf9, 0xc1,
  0xff, 0x05, 0x03, 0xf9, 0x66, 0x89, 0x7e, 0xf8, 0x49, 0x83, 0xc1, 0x08, 0x41, 0x0f, 0xb7, 0x09]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p36_2 : ∀ feat, Dec feat p36 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p36_5 : ∀ feat, Dec feat p36 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p36_8 : ∀ feat, Dec feat p36 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p36_10 : ∀ feat, Dec feat p36 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p36_12 : ∀ feat, Dec feat p36 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p36_14 : ∀ feat, Dec feat p36 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p36_17 : ∀ feat, Dec feat p36 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 9) none 1 4 16)] 5) := by dec_rfl
theorem p36_22 : ∀ feat, Dec feat p36 22 (FV7z.mk (.cmovcc 3) 32 [gr 32 2, gr 32 7] 3) := by dec_rfl
theorem p36_25 : ∀ feat, Dec feat p36 25 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p36_28 : ∀ feat, Dec feat p36 28 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p36_33 : ∀ feat, Dec feat p36 33 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p36_37 : ∀ feat, Dec feat p36 37 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 9) none 1 4 0)] 4) := by dec_rfl
theorem p36_41 : ∀ feat, Dec feat p36 41 (FV7z.mk (.cmovcc 3) 64 [gr 64 9, gr 64 6] 4) := by dec_rfl
theorem p36_45 : ∀ feat, Dec feat p36 45 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p36_47 : ∀ feat, Dec feat p36 47 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p36_50 : ∀ feat, Dec feat p36 50 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p36_52 : ∀ feat, Dec feat p36 52 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 18446744073709551608 16), gr 16 7] 4) := by dec_rfl
theorem p36_56 : ∀ feat, Dec feat p36 56 (FV7z.mk .add 64 [gr 64 9, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p36_60 : ∀ feat, Dec feat p36 60 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 9) none 1 0 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 9) none 1 4,
  Op.cmov32 3 2 7,
  Op.cmov32 2 5 6,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 7 10,
  Op.lea 64 6 (some 9) none 1 4,
  Op.cmov64 3 9 6,
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 6) none 1 18446744073709551608 7,
  Op.add 64 9 (.i 8),
  Op.ldzx 16 1 (some 9) none 1 0]

theorem b36 (prof : Profile) : Blk prof p36 0 64 o36 :=
  .cons (p36_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p36_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p36_5 _) (OpI.imul) (by decide) <|
  .cons (p36_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p36_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p36_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p36_14 _) (OpI.cmov32) (by decide) <|
  .cons (p36_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p36_22 _) (OpI.cmov32) (by decide) <|
  .cons (p36_25 _) (OpI.cmov32) (by decide) <|
  .cons (p36_28 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p36_33 _) (OpI.cmov32) (by decide) <|
  .cons (p36_37 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p36_41 _) (OpI.cmov64) (by decide) <|
  .cons (p36_45 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p36_47 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p36_50 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p36_52 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p36_56 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p36_60 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 64

/-- The stretch at `2462`. -/
def p37 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x41, 0x0f, 0xb7, 0x79, 0x08, 0x0f, 0x43, 0xcf, 0x0f, 0x42, 0xee, 0xbf, 0x1f, 0x00, 0x00,
  0x00, 0x41, 0x0f, 0x42, 0xfa, 0x49, 0x8d, 0x71, 0x08, 0x4c, 0x0f, 0x43, 0xce, 0x2b, 0xfa, 0xc1,
  0xff, 0x05, 0x03, 0xfa, 0x66, 0x89, 0x7e, 0xf0, 0x4d, 0x2b, 0xcb, 0x41, 0xd1, 0xe9, 0x41, 0x0b,
  0xd9]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p37_2 : ∀ feat, Dec feat p37 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p37_5 : ∀ feat, Dec feat p37 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p37_8 : ∀ feat, Dec feat p37 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p37_10 : ∀ feat, Dec feat p37 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p37_12 : ∀ feat, Dec feat p37 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p37_14 : ∀ feat, Dec feat p37 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p37_17 : ∀ feat, Dec feat p37 17 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 9) none 1 8 16)] 5) := by dec_rfl
theorem p37_22 : ∀ feat, Dec feat p37 22 (FV7z.mk (.cmovcc 3) 32 [gr 32 1, gr 32 7] 3) := by dec_rfl
theorem p37_25 : ∀ feat, Dec feat p37 25 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p37_28 : ∀ feat, Dec feat p37 28 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p37_33 : ∀ feat, Dec feat p37 33 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p37_37 : ∀ feat, Dec feat p37 37 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 9) none 1 8 0)] 4) := by dec_rfl
theorem p37_41 : ∀ feat, Dec feat p37 41 (FV7z.mk (.cmovcc 3) 64 [gr 64 9, gr 64 6] 4) := by dec_rfl
theorem p37_45 : ∀ feat, Dec feat p37 45 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p37_47 : ∀ feat, Dec feat p37 47 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p37_50 : ∀ feat, Dec feat p37 50 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p37_52 : ∀ feat, Dec feat p37 52 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 18446744073709551600 16), gr 16 7] 4) := by dec_rfl
theorem p37_56 : ∀ feat, Dec feat p37 56 (FV7z.mk .sub 64 [gr 64 9, Src.opd 64 (.r 11)] 3) := by dec_rfl
theorem p37_59 : ∀ feat, Dec feat p37 59 (FV7z.mk .shr 32 [gr 32 9, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p37_62 : ∀ feat, Dec feat p37 62 (FV7z.mk .or 32 [gr 32 3, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.ldzx 16 7 (some 9) none 1 8,
  Op.cmov32 3 1 7,
  Op.cmov32 2 5 6,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 7 10,
  Op.lea 64 6 (some 9) none 1 8,
  Op.cmov64 3 9 6,
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 6) none 1 18446744073709551600 7,
  Op.sub 64 9 (.r 11),
  Op.shr 9 (.i 1),
  Op.or 32 3 (.r 9)]

theorem b37 (prof : Profile) : Blk prof p37 0 65 o37 :=
  .cons (p37_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p37_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p37_5 _) (OpI.imul) (by decide) <|
  .cons (p37_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p37_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p37_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p37_14 _) (OpI.cmov32) (by decide) <|
  .cons (p37_17 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p37_22 _) (OpI.cmov32) (by decide) <|
  .cons (p37_25 _) (OpI.cmov32) (by decide) <|
  .cons (p37_28 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p37_33 _) (OpI.cmov32) (by decide) <|
  .cons (p37_37 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p37_41 _) (OpI.cmov64) (by decide) <|
  .cons (p37_45 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p37_47 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p37_50 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p37_52 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p37_56 _) (OpI.sub (.r 11) (.inr rfl)) (by decide) <|
  .cons (p37_59 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p37_62 _) (OpI.or (.r 9) (.inl rfl)) (by decide) <|
  .nil 65

/-- The stretch at `2546`. -/
def p38 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x67, 0x8d, 0x7b, 0xf8, 0x0f, 0x42, 0xdf, 0x0f, 0x42, 0xee, 0xbf, 0x1f, 0x00, 0x00, 0x00,
  0x41, 0x0f, 0x42, 0xfa, 0x2b, 0xf9, 0xc1, 0xff, 0x05, 0x03, 0xf9, 0x66, 0x43, 0x89, 0x3c, 0x4b]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p38_2 : ∀ feat, Dec feat p38 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p38_5 : ∀ feat, Dec feat p38 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p38_8 : ∀ feat, Dec feat p38 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p38_10 : ∀ feat, Dec feat p38 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p38_12 : ∀ feat, Dec feat p38 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p38_14 : ∀ feat, Dec feat p38 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p38_17 : ∀ feat, Dec feat p38 17 (FV7z.mk .lea 32 [gr 32 7, .mem (mga (some 3) none 1 18446744073709551608 0)] 4) := by dec_rfl
theorem p38_21 : ∀ feat, Dec feat p38 21 (FV7z.mk (.cmovcc 2) 32 [gr 32 3, gr 32 7] 3) := by dec_rfl
theorem p38_24 : ∀ feat, Dec feat p38 24 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p38_27 : ∀ feat, Dec feat p38 27 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p38_32 : ∀ feat, Dec feat p38 32 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p38_36 : ∀ feat, Dec feat p38 36 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p38_38 : ∀ feat, Dec feat p38 38 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p38_41 : ∀ feat, Dec feat p38 41 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p38_43 : ∀ feat, Dec feat p38 43 (FV7z.mk .mov 16 [.mem (mg (some 11) (some 9) 2 0 16), gr 16 7] 5) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.lea32a 7 (some 3) none 1 18446744073709551608,
  Op.cmov32 2 3 7,
  Op.cmov32 2 5 6,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 7 10,
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 11) (some 9) 2 0 7]

theorem b38 (prof : Profile) : Blk prof p38 0 48 o38 :=
  .cons (p38_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p38_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p38_5 _) (OpI.imul) (by decide) <|
  .cons (p38_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p38_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p38_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p38_14 _) (OpI.cmov32) (by decide) <|
  .cons (p38_17 _) (OpI.lea32a) (by decide) <|
  .cons (p38_21 _) (OpI.cmov32) (by decide) <|
  .cons (p38_24 _) (OpI.cmov32) (by decide) <|
  .cons (p38_27 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p38_32 _) (OpI.cmov32) (by decide) <|
  .cons (p38_36 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p38_38 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p38_41 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p38_43 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 48

/-- The stretch at `2594`. -/
def p39 : List Byte := [
  0x8b, 0x74, 0x24, 0x70, 0x8b, 0x4c, 0x24, 0x74, 0x8b, 0x54, 0x24, 0x78, 0x8b, 0x7c, 0x24, 0x5c,
  0x85, 0xff, 0x41, 0x0f, 0x44, 0xfd, 0x3b, 0xdf]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 4) none 1 112 32)] 4) := by dec_rfl
theorem p39_4 : ∀ feat, Dec feat p39 4 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 116 32)] 4) := by dec_rfl
theorem p39_8 : ∀ feat, Dec feat p39 8 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 120 32)] 4) := by dec_rfl
theorem p39_12 : ∀ feat, Dec feat p39 12 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 92 32)] 4) := by dec_rfl
theorem p39_16 : ∀ feat, Dec feat p39 16 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p39_18 : ∀ feat, Dec feat p39 18 (FV7z.mk (.cmovcc 4) 32 [gr 32 7, gr 32 13] 4) := by dec_rfl
theorem p39_22 : ∀ feat, Dec feat p39 22 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.ld 32 6 (some 4) none 1 112,
  Op.ld 32 1 (some 4) none 1 116,
  Op.ld 32 2 (some 4) none 1 120,
  Op.ld 32 7 (some 4) none 1 92,
  Op.test 32 7 (.r 7),
  Op.cmov32 4 7 13,
  Op.cmp 32 3 (.r 7)]

theorem b39 (prof : Profile) : Blk prof p39 0 24 o39 :=
  .cons (p39_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p39_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p39_8 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p39_12 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p39_16 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .cons (p39_18 _) (OpI.cmov32) (by decide) <|
  .cons (p39_22 _) (OpI.cmp (.r 7) (.inl rfl)) (by decide) <|
  .nil 24

def j19 : List Byte := [0x0f, 0x83, 0xb3, 0x07, 0x00, 0x00]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 3) 64 [.rel 1971] 6) := by dec_rfl

/-- The stretch at `2624`. -/
def p40 : List Byte := [
  0xff, 0xc3, 0x89, 0x5c, 0x24, 0x70, 0x41, 0x8b, 0xdc, 0x89, 0x74, 0x24, 0x74, 0x89, 0x4c, 0x24,
  0x78, 0x89, 0x54, 0x24, 0x7c, 0x41, 0x83, 0xf8, 0x26, 0x41, 0xb8, 0x0e, 0x00, 0x00, 0x00, 0xbf,
  0x14, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x43, 0xc7]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .inc 32 [gr 32 3] 2) := by dec_rfl
theorem p40_2 : ∀ feat, Dec feat p40 2 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 112 32), gr 32 3] 4) := by dec_rfl
theorem p40_6 : ∀ feat, Dec feat p40 6 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p40_9 : ∀ feat, Dec feat p40 9 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 116 32), gr 32 6] 4) := by dec_rfl
theorem p40_13 : ∀ feat, Dec feat p40 13 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 120 32), gr 32 1] 4) := by dec_rfl
theorem p40_17 : ∀ feat, Dec feat p40 17 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 124 32), gr 32 2] 4) := by dec_rfl
theorem p40_21 : ∀ feat, Dec feat p40 21 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 38)] 4) := by dec_rfl
theorem p40_25 : ∀ feat, Dec feat p40 25 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 14)] 6) := by dec_rfl
theorem p40_31 : ∀ feat, Dec feat p40 31 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 20)] 5) := by dec_rfl
theorem p40_36 : ∀ feat, Dec feat p40 36 (FV7z.mk (.cmovcc 3) 32 [gr 32 8, gr 32 7] 4) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.inc 32 3,
  Op.st 32 (some 4) none 1 112 3,
  Op.mov 32 3 (.r 12),
  Op.st 32 (some 4) none 1 116 6,
  Op.st 32 (some 4) none 1 120 1,
  Op.st 32 (some 4) none 1 124 2,
  Op.cmp 32 8 (.i 38),
  Op.mov 32 8 (.i 14),
  Op.mov 32 7 (.i 20),
  Op.cmov32 3 8 7]

theorem b40 (prof : Profile) : Blk prof p40 0 40 o40 :=
  .cons (p40_0 _) (OpI.inc (.inl rfl)) (by decide) <|
  .cons (p40_2 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p40_6 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p40_9 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p40_13 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p40_17 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p40_21 _) (OpI.cmp (.i 38) (.inl rfl)) (by decide) <|
  .cons (p40_25 _) (OpI.mov (.i 14) (.inl rfl)) (by decide) <|
  .cons (p40_31 _) (OpI.mov (.i 20) (.inl rfl)) (by decide) <|
  .cons (p40_36 _) (OpI.cmov32) (by decide) <|
  .nil 40

/-- The stretch at `2664`. -/
def p41 : List Byte := [
  0x48, 0x8b, 0x54, 0x24, 0x40, 0x49, 0x2b, 0xd6]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 64 64)] 5) := by dec_rfl
theorem p41_5 : ∀ feat, Dec feat p41 5 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.ld 64 2 (some 4) none 1 64,
  Op.sub 64 2 (.r 14)]

theorem b41 (prof : Profile) : Blk prof p41 0 8 o41 :=
  .cons (p41_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p41_5 _) (OpI.sub (.r 14) (.inr rfl)) (by decide) <|
  .nil 8

def j20 : List Byte := [0x0f, 0x84, 0x41, 0x07, 0x00, 0x00]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 4) 64 [.rel 1857] 6) := by dec_rfl

/-- The stretch at `2678`. -/
def p42 : List Byte := [
  0x48, 0x3b, 0xd3, 0x0f, 0x43, 0xd3, 0x4c, 0x8b, 0x64, 0x24, 0x38, 0x8b, 0x4c, 0x24, 0x70, 0x49,
  0x8b, 0xfe, 0x4c, 0x03, 0xf2, 0x44, 0x03, 0xea, 0x2b, 0xda, 0x89, 0x5c, 0x24, 0x64, 0x49, 0x2b,
  0xfc, 0x48, 0x2b, 0xf9]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p42_3 : ∀ feat, Dec feat p42 3 (FV7z.mk (.cmovcc 3) 32 [gr 32 2, gr 32 3] 3) := by dec_rfl
theorem p42_6 : ∀ feat, Dec feat p42 6 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p42_11 : ∀ feat, Dec feat p42 11 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 112 32)] 4) := by dec_rfl
theorem p42_15 : ∀ feat, Dec feat p42 15 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p42_18 : ∀ feat, Dec feat p42 18 (FV7z.mk .add 64 [gr 64 14, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p42_21 : ∀ feat, Dec feat p42 21 (FV7z.mk .add 32 [gr 32 13, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p42_24 : ∀ feat, Dec feat p42 24 (FV7z.mk .sub 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p42_26 : ∀ feat, Dec feat p42 26 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 100 32), gr 32 3] 4) := by dec_rfl
theorem p42_30 : ∀ feat, Dec feat p42 30 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p42_33 : ∀ feat, Dec feat p42 33 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.cmp 64 2 (.r 3),
  Op.cmov32 3 2 3,
  Op.ld 64 12 (some 4) none 1 56,
  Op.ld 32 1 (some 4) none 1 112,
  Op.mov 64 7 (.r 14),
  Op.add 64 14 (.r 2),
  Op.add 32 13 (.r 2),
  Op.sub 32 3 (.r 2),
  Op.st 32 (some 4) none 1 100 3,
  Op.sub 64 7 (.r 12),
  Op.sub 64 7 (.r 1)]

theorem b42 (prof : Profile) : Blk prof p42 0 36 o42 :=
  .cons (p42_0 _) (OpI.cmp (.r 3) (.inr rfl)) (by decide) <|
  .cons (p42_3 _) (OpI.cmov32) (by decide) <|
  .cons (p42_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p42_11 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p42_15 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p42_18 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p42_21 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p42_24 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p42_26 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p42_30 _) (OpI.sub (.r 12) (.inr rfl)) (by decide) <|
  .cons (p42_33 _) (OpI.sub (.r 1) (.inr rfl)) (by decide) <|
  .nil 36

def j21 : List Byte := [0x73, 0x14]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 3) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `2716`. -/
def p43 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x28, 0x48, 0x03, 0xf9, 0x48, 0x2b, 0xcf, 0x48, 0x3b, 0xd1]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p43_5 : ∀ feat, Dec feat p43 5 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p43_8 : ∀ feat, Dec feat p43 8 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p43_11 : ∀ feat, Dec feat p43 11 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.ld 64 1 (some 4) none 1 40,
  Op.add 64 7 (.r 1),
  Op.sub 64 1 (.r 7),
  Op.cmp 64 2 (.r 1)]

theorem b43 (prof : Profile) : Blk prof p43 0 14 o43 :=
  .cons (p43_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p43_5 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p43_8 _) (OpI.sub (.r 7) (.inr rfl)) (by decide) <|
  .cons (p43_11 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 14

def j22 : List Byte := [0x0f, 0x87, 0xdb, 0x06, 0x00, 0x00]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 7) 64 [.rel 1755] 6) := by dec_rfl

/-- The stretch at `2736`. -/
def p44 : List Byte := [
  0x49, 0x03, 0xfc, 0x0f, 0xb6, 0x1f, 0x48, 0x03, 0xfa, 0x48, 0xf7, 0xda]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p44_3 : ∀ feat, Dec feat p44 3 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 7) none 1 0 8)] 3) := by dec_rfl
theorem p44_6 : ∀ feat, Dec feat p44 6 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p44_9 : ∀ feat, Dec feat p44 9 (FV7z.mk .neg 64 [gr 64 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.add 64 7 (.r 12),
  Op.ldzx 8 3 (some 7) none 1 0,
  Op.add 64 7 (.r 2),
  Op.neg 64 2]

theorem b44 (prof : Profile) : Blk prof p44 0 12 o44 :=
  .cons (p44_0 _) (OpI.add (.r 12) (.inr rfl)) (by decide) <|
  .cons (p44_3 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p44_6 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p44_9 _) (OpI.neg (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `2748`. -/
def p45 : List Byte := [
  0x49, 0xff, 0xce, 0x8b, 0x4c, 0x24, 0x58, 0x41, 0x23, 0xcd, 0xc1, 0xe1, 0x05, 0x4b, 0x8d, 0x34,
  0x03, 0x48, 0xff, 0xc2]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .dec 64 [gr 64 14] 3) := by dec_rfl
theorem p45_3 : ∀ feat, Dec feat p45 3 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 88 32)] 4) := by dec_rfl
theorem p45_7 : ∀ feat, Dec feat p45 7 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p45_10 : ∀ feat, Dec feat p45 10 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p45_13 : ∀ feat, Dec feat p45 13 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 11) (some 8) 1 0 0)] 4) := by dec_rfl
theorem p45_17 : ∀ feat, Dec feat p45 17 (FV7z.mk .inc 64 [gr 64 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.dec 64 14,
  Op.ld 32 1 (some 4) none 1 88,
  Op.and 32 1 (.r 13),
  Op.shl 1 (.i 5),
  Op.lea 64 6 (some 11) (some 8) 1 0,
  Op.inc 64 2]

theorem b45 (prof : Profile) : Blk prof p45 0 20 o45 :=
  .cons (p45_0 _) (OpI.dec (.inr rfl)) (by decide) <|
  .cons (p45_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p45_7 _) (OpI.and (.r 13) (.inl rfl)) (by decide) <|
  .cons (p45_10 _) (OpI.shl (.i 5)) (by decide) <|
  .cons (p45_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p45_17 _) (OpI.inc (.inr rfl)) (by decide) <|
  .nil 20

def j23 : List Byte := [0x74, 0x1b]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `2770`. -/
def p46 : List Byte := [
  0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl
theorem p46_7 : ∀ feat, Dec feat p46 7 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.nop,
  Op.nop]

theorem b46 (prof : Profile) : Blk prof p46 0 14 o46 :=
  .cons (p46_0 _) (OpI.nop) (by decide) <|
  .cons (p46_7 _) (OpI.nop) (by decide) <|
  .nil 14

/-- The stretch at `2784`. -/
def p47 : List Byte := [
  0x41, 0x88, 0x1c, 0x16, 0x0f, 0xb6, 0x1c, 0x17, 0x48, 0xff, 0xc2]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .mov 8 [.mem (mg (some 14) (some 2) 1 0 8), gr 8 3] 4) := by dec_rfl
theorem p47_4 : ∀ feat, Dec feat p47 4 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 7) (some 2) 1 0 8)] 4) := by dec_rfl
theorem p47_8 : ∀ feat, Dec feat p47 8 (FV7z.mk .inc 64 [gr 64 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.st 8 (some 14) (some 2) 1 0 3,
  Op.ldzx 8 3 (some 7) (some 2) 1 0,
  Op.inc 64 2]

theorem b47 (prof : Profile) : Blk prof p47 0 11 o47 :=
  .cons (p47_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p47_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p47_8 _) (OpI.inc (.inr rfl)) (by decide) <|
  .nil 11

def j24 : List Byte := [0x75, 0xf3]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551603] 2) := by dec_rfl

/-- The stretch at `2797`. -/
def p48 : List Byte := [
  0x41, 0x88, 0x1e, 0x49, 0xff, 0xc6, 0x4c, 0x3b, 0x7c, 0x24, 0x48]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .mov 8 [.mem (mg (some 14) none 1 0 8), gr 8 3] 3) := by dec_rfl
theorem p48_3 : ∀ feat, Dec feat p48 3 (FV7z.mk .inc 64 [gr 64 14] 3) := by dec_rfl
theorem p48_6 : ∀ feat, Dec feat p48 6 (FV7z.mk .cmp 64 [gr 64 15, .mem (mg (some 4) none 1 72 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.st 8 (some 14) none 1 0 3,
  Op.inc 64 14,
  Op.cmpm 64 15 (some 4) none 1 72]

theorem b48 (prof : Profile) : Blk prof p48 0 11 o48 :=
  .cons (p48_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p48_3 _) (OpI.inc (.inr rfl)) (by decide) <|
  .cons (p48_6 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 11

def j25 : List Byte := [0x0f, 0x83, 0x05, 0x07, 0x00, 0x00]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 3) 64 [.rel 1797] 6) := by dec_rfl

def j26 : List Byte := [0x0f, 0x83, 0xfa, 0x06, 0x00, 0x00]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 3) 64 [.rel 1786] 6) := by dec_rfl

def j27 : List Byte := [0x0f, 0x83, 0xe0, 0xf8, 0xff, 0xff]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709549792] 6) := by dec_rfl

/-- The stretch at `2868`. -/
def p49 : List Byte := [
  0x41, 0x8b, 0xfd, 0xc1, 0xe7, 0x08, 0x03, 0xdf, 0x23, 0x5c, 0x24, 0x54, 0x48, 0x03, 0xf1, 0x8b,
  0x4c, 0x24, 0x50, 0x8d, 0x1c, 0x5b, 0x49, 0x81, 0xc3, 0x80, 0x02, 0x00, 0x00, 0xd3, 0xe3, 0x4c,
  0x03, 0xdb, 0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x89, 0x96, 0x00,
  0xfe, 0xff, 0xff, 0x41, 0xff, 0xc5, 0x8b, 0x4c, 0x24, 0x70, 0x4c, 0x89, 0x74, 0x24, 0x68, 0x41,
  0x8d, 0x78, 0xf4, 0x41, 0x83, 0xe8, 0x06, 0x41, 0x83, 0xf8, 0x0e, 0x44, 0x0f, 0x43, 0xc7, 0x4d,
  0x2b, 0xf4, 0x4c, 0x2b, 0xf1]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p49_3 : ∀ feat, Dec feat p49 3 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p49_6 : ∀ feat, Dec feat p49 6 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p49_8 : ∀ feat, Dec feat p49 8 (FV7z.mk .and 32 [gr 32 3, .mem (mg (some 4) none 1 84 32)] 4) := by dec_rfl
theorem p49_12 : ∀ feat, Dec feat p49 12 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p49_15 : ∀ feat, Dec feat p49 15 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 80 32)] 4) := by dec_rfl
theorem p49_19 : ∀ feat, Dec feat p49 19 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 3) (some 3) 2 0 0)] 3) := by dec_rfl
theorem p49_22 : ∀ feat, Dec feat p49 22 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 640)] 7) := by dec_rfl
theorem p49_29 : ∀ feat, Dec feat p49 29 (FV7z.mk .shl 32 [gr 32 3, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p49_31 : ∀ feat, Dec feat p49 31 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p49_34 : ∀ feat, Dec feat p49 34 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p49_37 : ∀ feat, Dec feat p49 37 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p49_39 : ∀ feat, Dec feat p49 39 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p49_42 : ∀ feat, Dec feat p49 42 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p49_44 : ∀ feat, Dec feat p49 44 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 18446744073709551104 16), gr 16 2] 7) := by dec_rfl
theorem p49_51 : ∀ feat, Dec feat p49 51 (FV7z.mk .inc 32 [gr 32 13] 3) := by dec_rfl
theorem p49_54 : ∀ feat, Dec feat p49 54 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 112 32)] 4) := by dec_rfl
theorem p49_58 : ∀ feat, Dec feat p49 58 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 104 64), gr 64 14] 5) := by dec_rfl
theorem p49_63 : ∀ feat, Dec feat p49 63 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 8) none 1 18446744073709551604 0)] 4) := by dec_rfl
theorem p49_67 : ∀ feat, Dec feat p49 67 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.i 6)] 4) := by dec_rfl
theorem p49_71 : ∀ feat, Dec feat p49 71 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 14)] 4) := by dec_rfl
theorem p49_75 : ∀ feat, Dec feat p49 75 (FV7z.mk (.cmovcc 3) 32 [gr 32 8, gr 32 7] 4) := by dec_rfl
theorem p49_79 : ∀ feat, Dec feat p49 79 (FV7z.mk .sub 64 [gr 64 14, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p49_82 : ∀ feat, Dec feat p49 82 (FV7z.mk .sub 64 [gr 64 14, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.mov 32 7 (.r 13),
  Op.shl 7 (.i 8),
  Op.add 32 3 (.r 7),
  Op.andm 32 3 (some 4) none 1 84,
  Op.add 64 6 (.r 1),
  Op.ld 32 1 (some 4) none 1 80,
  Op.lea 32 3 (some 3) (some 3) 2 0,
  Op.add 64 11 (.i 640),
  Op.shl 3 (.r 1),
  Op.add 64 11 (.r 3),
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 6) none 1 18446744073709551104 2,
  Op.inc 32 13,
  Op.ld 32 1 (some 4) none 1 112,
  Op.st 64 (some 4) none 1 104 14,
  Op.lea 32 7 (some 8) none 1 18446744073709551604,
  Op.sub 32 8 (.i 6),
  Op.cmp 32 8 (.i 14),
  Op.cmov32 3 8 7,
  Op.sub 64 14 (.r 12),
  Op.sub 64 14 (.r 1)]

theorem b49 (prof : Profile) : Blk prof p49 0 85 o49 :=
  .cons (p49_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p49_3 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p49_6 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p49_8 _) (OpI.andm (.inl rfl)) (by decide) <|
  .cons (p49_12 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p49_15 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p49_19 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p49_22 _) (OpI.add (.i 640) (.inr rfl)) (by decide) <|
  .cons (p49_29 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p49_31 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .cons (p49_34 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p49_37 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p49_39 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p49_42 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p49_44 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p49_51 _) (OpI.inc (.inl rfl)) (by decide) <|
  .cons (p49_54 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p49_58 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p49_63 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p49_67 _) (OpI.sub (.i 6) (.inl rfl)) (by decide) <|
  .cons (p49_71 _) (OpI.cmp (.i 14) (.inl rfl)) (by decide) <|
  .cons (p49_75 _) (OpI.cmov32) (by decide) <|
  .cons (p49_79 _) (OpI.sub (.r 12) (.inr rfl)) (by decide) <|
  .cons (p49_82 _) (OpI.sub (.r 1) (.inr rfl)) (by decide) <|
  .nil 85

def j28 : List Byte := [0x73, 0x05]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 3) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `2955`. -/
def p50 : List Byte := [
  0x4c, 0x03, 0x74, 0x24, 0x28]

theorem p50_0 : ∀ feat, Dec feat p50 0 (FV7z.mk .add 64 [gr 64 14, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o50 : List Op := [
  Op.addm 64 14 (some 4) none 1 40]

theorem b50 (prof : Profile) : Blk prof p50 0 5 o50 :=
  .cons (p50_0 _) (OpI.addm (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `2960`. -/
def p51 : List Byte := [
  0x47, 0x0f, 0xb6, 0x0c, 0x34, 0x41, 0xbc, 0x00, 0x02, 0x00, 0x00, 0x41, 0xc1, 0xe1, 0x02, 0x45,
  0x8b, 0xf4, 0x45, 0x23, 0xf1, 0x43, 0x0f, 0xb7, 0x8c, 0x33, 0x02, 0x02, 0x00, 0x00, 0x4b, 0x8d,
  0x94, 0x33, 0x02, 0x02, 0x00, 0x00, 0x45, 0x33, 0xe6, 0x45, 0x03, 0xc9]

theorem p51_0 : ∀ feat, Dec feat p51 0 (FV7z.mk .movzx 32 [gr 32 9, .mem (mg (some 12) (some 14) 1 0 8)] 5) := by dec_rfl
theorem p51_5 : ∀ feat, Dec feat p51 5 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 512)] 6) := by dec_rfl
theorem p51_11 : ∀ feat, Dec feat p51 11 (FV7z.mk .shl 32 [gr 32 9, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p51_15 : ∀ feat, Dec feat p51 15 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p51_18 : ∀ feat, Dec feat p51 18 (FV7z.mk .and 32 [gr 32 14, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p51_21 : ∀ feat, Dec feat p51 21 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 11) (some 14) 1 514 16)] 9) := by dec_rfl
theorem p51_30 : ∀ feat, Dec feat p51 30 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 11) (some 14) 1 514 0)] 8) := by dec_rfl
theorem p51_38 : ∀ feat, Dec feat p51 38 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p51_41 : ∀ feat, Dec feat p51 41 (FV7z.mk .add 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o51 : List Op := [
  Op.ldzx 8 9 (some 12) (some 14) 1 0,
  Op.mov 32 12 (.i 512),
  Op.shl 9 (.i 2),
  Op.mov 32 14 (.r 12),
  Op.and 32 14 (.r 9),
  Op.ldzx 16 1 (some 11) (some 14) 1 514,
  Op.lea 64 2 (some 11) (some 14) 1 514,
  Op.xor 32 12 (.r 14),
  Op.add 32 9 (.r 9)]

theorem b51 (prof : Profile) : Blk prof p51 0 44 o51 :=
  .cons (p51_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p51_5 _) (OpI.mov (.i 512) (.inl rfl)) (by decide) <|
  .cons (p51_11 _) (OpI.shl (.i 2)) (by decide) <|
  .cons (p51_15 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p51_18 _) (OpI.and (.r 9) (.inl rfl)) (by decide) <|
  .cons (p51_21 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p51_30 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p51_38 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .cons (p51_41 _) (OpI.add (.r 9) (.inl rfl)) (by decide) <|
  .nil 44

/-- The stretch at `3023`. -/
def p52 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x45, 0x0f,
  0x43, 0xe6, 0x45, 0x8b, 0xf1, 0x0f, 0x43, 0xc7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42, 0xee,
  0x41, 0x0f, 0x42, 0xfa, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x83, 0xdb, 0xfd, 0x2b, 0xf9, 0xc1, 0xff,
  0x05, 0x03, 0xf9, 0x66, 0x89, 0x3a, 0x45, 0x23, 0xf4, 0x4b, 0x8d, 0x14, 0x23, 0x49, 0x03, 0xd6,
  0x0f, 0xb7, 0x0c, 0x5a, 0x45, 0x33, 0xe6, 0x03, 0xdb, 0x45, 0x03, 0xc9]

theorem p52_0 : ∀ feat, Dec feat p52 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p52_2 : ∀ feat, Dec feat p52 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p52_5 : ∀ feat, Dec feat p52 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p52_8 : ∀ feat, Dec feat p52 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p52_10 : ∀ feat, Dec feat p52 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p52_12 : ∀ feat, Dec feat p52 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p52_14 : ∀ feat, Dec feat p52 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 12, gr 32 14] 4) := by dec_rfl
theorem p52_18 : ∀ feat, Dec feat p52 18 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p52_21 : ∀ feat, Dec feat p52 21 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p52_24 : ∀ feat, Dec feat p52 24 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p52_29 : ∀ feat, Dec feat p52 29 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p52_32 : ∀ feat, Dec feat p52 32 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p52_36 : ∀ feat, Dec feat p52 36 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 0)] 5) := by dec_rfl
theorem p52_41 : ∀ feat, Dec feat p52 41 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967293)] 3) := by dec_rfl
theorem p52_44 : ∀ feat, Dec feat p52 44 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p52_46 : ∀ feat, Dec feat p52 46 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p52_49 : ∀ feat, Dec feat p52 49 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p52_51 : ∀ feat, Dec feat p52 51 (FV7z.mk .mov 16 [.mem (mg (some 2) none 1 0 16), gr 16 7] 3) := by dec_rfl
theorem p52_54 : ∀ feat, Dec feat p52 54 (FV7z.mk .and 32 [gr 32 14, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p52_57 : ∀ feat, Dec feat p52 57 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 11) (some 12) 1 0 0)] 4) := by dec_rfl
theorem p52_61 : ∀ feat, Dec feat p52 61 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p52_64 : ∀ feat, Dec feat p52 64 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 2) (some 3) 2 0 16)] 4) := by dec_rfl
theorem p52_68 : ∀ feat, Dec feat p52 68 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p52_71 : ∀ feat, Dec feat p52 71 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p52_73 : ∀ feat, Dec feat p52 73 (FV7z.mk .add 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o52 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 12 14,
  Op.mov 32 14 (.r 9),
  Op.cmov32 3 0 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.cmov32 2 7 10,
  Op.mov 32 3 (.i 0),
  Op.sbb 32 3 (.i 4294967293),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 2) none 1 0 7,
  Op.and 32 14 (.r 12),
  Op.lea 64 2 (some 11) (some 12) 1 0,
  Op.add 64 2 (.r 14),
  Op.ldzx 16 1 (some 2) (some 3) 2 0,
  Op.xor 32 12 (.r 14),
  Op.add 32 3 (.r 3),
  Op.add 32 9 (.r 9)]

theorem b52 (prof : Profile) : Blk prof p52 0 76 o52 :=
  .cons (p52_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p52_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p52_5 _) (OpI.imul) (by decide) <|
  .cons (p52_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p52_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p52_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p52_14 _) (OpI.cmov32) (by decide) <|
  .cons (p52_18 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p52_21 _) (OpI.cmov32) (by decide) <|
  .cons (p52_24 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p52_29 _) (OpI.cmov32) (by decide) <|
  .cons (p52_32 _) (OpI.cmov32) (by decide) <|
  .cons (p52_36 _) (OpI.mov (.i 0) (.inl rfl)) (by decide) <|
  .cons (p52_41 _) (OpI.sbb (.i 4294967293) (.inl rfl)) (by decide) <|
  .cons (p52_44 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p52_46 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p52_49 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p52_51 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p52_54 _) (OpI.and (.r 12) (.inl rfl)) (by decide) <|
  .cons (p52_57 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p52_61 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .cons (p52_64 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p52_68 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .cons (p52_71 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .cons (p52_73 _) (OpI.add (.r 9) (.inl rfl)) (by decide) <|
  .nil 76

/-- The stretch at `3118`. -/
def p53 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x45, 0x0f,
  0x43, 0xe6, 0x45, 0x8b, 0xf1, 0x0f, 0x43, 0xc7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42, 0xee,
  0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83, 0xdb, 0xff, 0x2b, 0xf9, 0xc1, 0xff, 0x05, 0x03, 0xf9,
  0x66, 0x89, 0x3c, 0x32, 0x45, 0x23, 0xf4, 0x4b, 0x8d, 0x14, 0x23, 0x49, 0x03, 0xd6, 0x0f, 0xb7,
  0x0c, 0x5a, 0x45, 0x33, 0xe6, 0x03, 0xdb, 0x45, 0x03, 0xc9]

theorem p53_0 : ∀ feat, Dec feat p53 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p53_2 : ∀ feat, Dec feat p53 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p53_5 : ∀ feat, Dec feat p53 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p53_8 : ∀ feat, Dec feat p53 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p53_10 : ∀ feat, Dec feat p53 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p53_12 : ∀ feat, Dec feat p53 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p53_14 : ∀ feat, Dec feat p53 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 12, gr 32 14] 4) := by dec_rfl
theorem p53_18 : ∀ feat, Dec feat p53 18 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p53_21 : ∀ feat, Dec feat p53 21 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p53_24 : ∀ feat, Dec feat p53 24 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p53_29 : ∀ feat, Dec feat p53 29 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p53_32 : ∀ feat, Dec feat p53 32 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p53_34 : ∀ feat, Dec feat p53 34 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p53_38 : ∀ feat, Dec feat p53 38 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p53_41 : ∀ feat, Dec feat p53 41 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p53_43 : ∀ feat, Dec feat p53 43 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p53_46 : ∀ feat, Dec feat p53 46 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p53_48 : ∀ feat, Dec feat p53 48 (FV7z.mk .mov 16 [.mem (mg (some 2) (some 6) 1 0 16), gr 16 7] 4) := by dec_rfl
theorem p53_52 : ∀ feat, Dec feat p53 52 (FV7z.mk .and 32 [gr 32 14, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p53_55 : ∀ feat, Dec feat p53 55 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 11) (some 12) 1 0 0)] 4) := by dec_rfl
theorem p53_59 : ∀ feat, Dec feat p53 59 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p53_62 : ∀ feat, Dec feat p53 62 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 2) (some 3) 2 0 16)] 4) := by dec_rfl
theorem p53_66 : ∀ feat, Dec feat p53 66 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p53_69 : ∀ feat, Dec feat p53 69 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p53_71 : ∀ feat, Dec feat p53 71 (FV7z.mk .add 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o53 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 12 14,
  Op.mov 32 14 (.r 9),
  Op.cmov32 3 0 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 2) (some 6) 1 0 7,
  Op.and 32 14 (.r 12),
  Op.lea 64 2 (some 11) (some 12) 1 0,
  Op.add 64 2 (.r 14),
  Op.ldzx 16 1 (some 2) (some 3) 2 0,
  Op.xor 32 12 (.r 14),
  Op.add 32 3 (.r 3),
  Op.add 32 9 (.r 9)]

theorem b53 (prof : Profile) : Blk prof p53 0 74 o53 :=
  .cons (p53_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p53_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p53_5 _) (OpI.imul) (by decide) <|
  .cons (p53_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p53_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p53_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p53_14 _) (OpI.cmov32) (by decide) <|
  .cons (p53_18 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p53_21 _) (OpI.cmov32) (by decide) <|
  .cons (p53_24 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p53_29 _) (OpI.cmov32) (by decide) <|
  .cons (p53_32 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p53_34 _) (OpI.cmov32) (by decide) <|
  .cons (p53_38 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p53_41 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p53_43 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p53_46 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p53_48 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p53_52 _) (OpI.and (.r 12) (.inl rfl)) (by decide) <|
  .cons (p53_55 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p53_59 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .cons (p53_62 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p53_66 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .cons (p53_69 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .cons (p53_71 _) (OpI.add (.r 9) (.inl rfl)) (by decide) <|
  .nil 74

/-- The stretch at `3583`. -/
def p54 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x45, 0x0f,
  0x43, 0xe6, 0x45, 0x8b, 0xf1, 0x0f, 0x43, 0xc7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42, 0xee,
  0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x83, 0xdb, 0xff, 0x2b, 0xf9, 0xc1, 0xff, 0x05, 0x03, 0xf9,
  0x66, 0x89, 0x3c, 0x32, 0x45, 0x23, 0xf4, 0x4b, 0x8d, 0x14, 0x23, 0x49, 0x03, 0xd6, 0x0f, 0xb7,
  0x0c, 0x5a, 0x03, 0xdb]

theorem p54_0 : ∀ feat, Dec feat p54 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p54_2 : ∀ feat, Dec feat p54 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p54_5 : ∀ feat, Dec feat p54 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p54_8 : ∀ feat, Dec feat p54 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p54_10 : ∀ feat, Dec feat p54 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p54_12 : ∀ feat, Dec feat p54 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p54_14 : ∀ feat, Dec feat p54 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 12, gr 32 14] 4) := by dec_rfl
theorem p54_18 : ∀ feat, Dec feat p54 18 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p54_21 : ∀ feat, Dec feat p54 21 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p54_24 : ∀ feat, Dec feat p54 24 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p54_29 : ∀ feat, Dec feat p54 29 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p54_32 : ∀ feat, Dec feat p54 32 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p54_34 : ∀ feat, Dec feat p54 34 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p54_38 : ∀ feat, Dec feat p54 38 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p54_41 : ∀ feat, Dec feat p54 41 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p54_43 : ∀ feat, Dec feat p54 43 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p54_46 : ∀ feat, Dec feat p54 46 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p54_48 : ∀ feat, Dec feat p54 48 (FV7z.mk .mov 16 [.mem (mg (some 2) (some 6) 1 0 16), gr 16 7] 4) := by dec_rfl
theorem p54_52 : ∀ feat, Dec feat p54 52 (FV7z.mk .and 32 [gr 32 14, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p54_55 : ∀ feat, Dec feat p54 55 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 11) (some 12) 1 0 0)] 4) := by dec_rfl
theorem p54_59 : ∀ feat, Dec feat p54 59 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p54_62 : ∀ feat, Dec feat p54 62 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 2) (some 3) 2 0 16)] 4) := by dec_rfl
theorem p54_66 : ∀ feat, Dec feat p54 66 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o54 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 12 14,
  Op.mov 32 14 (.r 9),
  Op.cmov32 3 0 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 4294967295),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 2) (some 6) 1 0 7,
  Op.and 32 14 (.r 12),
  Op.lea 64 2 (some 11) (some 12) 1 0,
  Op.add 64 2 (.r 14),
  Op.ldzx 16 1 (some 2) (some 3) 2 0,
  Op.add 32 3 (.r 3)]

theorem b54 (prof : Profile) : Blk prof p54 0 68 o54 :=
  .cons (p54_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p54_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p54_5 _) (OpI.imul) (by decide) <|
  .cons (p54_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p54_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p54_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p54_14 _) (OpI.cmov32) (by decide) <|
  .cons (p54_18 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p54_21 _) (OpI.cmov32) (by decide) <|
  .cons (p54_24 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p54_29 _) (OpI.cmov32) (by decide) <|
  .cons (p54_32 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p54_34 _) (OpI.cmov32) (by decide) <|
  .cons (p54_38 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p54_41 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p54_43 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p54_46 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p54_48 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p54_52 _) (OpI.and (.r 12) (.inl rfl)) (by decide) <|
  .cons (p54_55 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p54_59 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .cons (p54_62 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p54_66 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .nil 68

/-- The stretch at `3670`. -/
def p55 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc1, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42, 0xee, 0x8b, 0xf3, 0x41, 0x0f, 0x42, 0xfa, 0x81,
  0xdb, 0xff, 0x00, 0x00, 0x00, 0x2b, 0xf9, 0xc1, 0xff, 0x05, 0x03, 0xf9, 0x66, 0x89, 0x3c, 0x32,
  0x4c, 0x8b, 0x5c, 0x24, 0x30, 0x8b, 0x4c, 0x24, 0x58, 0x41, 0x23, 0xcd, 0xc1, 0xe1, 0x05, 0x4b,
  0x8d, 0x34, 0x03, 0x4c, 0x8b, 0x74, 0x24, 0x68, 0x41, 0x88, 0x1e, 0x49, 0xff, 0xc6, 0x4c, 0x3b,
  0x7c, 0x24, 0x48]

theorem p55_0 : ∀ feat, Dec feat p55 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p55_2 : ∀ feat, Dec feat p55 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p55_5 : ∀ feat, Dec feat p55 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 1] 3) := by dec_rfl
theorem p55_8 : ∀ feat, Dec feat p55 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p55_10 : ∀ feat, Dec feat p55 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p55_12 : ∀ feat, Dec feat p55 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p55_14 : ∀ feat, Dec feat p55 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p55_17 : ∀ feat, Dec feat p55 17 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p55_22 : ∀ feat, Dec feat p55 22 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p55_25 : ∀ feat, Dec feat p55 25 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p55_27 : ∀ feat, Dec feat p55 27 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p55_31 : ∀ feat, Dec feat p55 31 (FV7z.mk .sbb 32 [gr 32 3, Src.opd 32 (.i 255)] 6) := by dec_rfl
theorem p55_37 : ∀ feat, Dec feat p55 37 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p55_39 : ∀ feat, Dec feat p55 39 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p55_42 : ∀ feat, Dec feat p55 42 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p55_44 : ∀ feat, Dec feat p55 44 (FV7z.mk .mov 16 [.mem (mg (some 2) (some 6) 1 0 16), gr 16 7] 4) := by dec_rfl
theorem p55_48 : ∀ feat, Dec feat p55 48 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 4) none 1 48 64)] 5) := by dec_rfl
theorem p55_53 : ∀ feat, Dec feat p55 53 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 88 32)] 4) := by dec_rfl
theorem p55_57 : ∀ feat, Dec feat p55 57 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p55_60 : ∀ feat, Dec feat p55 60 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p55_63 : ∀ feat, Dec feat p55 63 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 11) (some 8) 1 0 0)] 4) := by dec_rfl
theorem p55_67 : ∀ feat, Dec feat p55 67 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 4) none 1 104 64)] 5) := by dec_rfl
theorem p55_72 : ∀ feat, Dec feat p55 72 (FV7z.mk .mov 8 [.mem (mg (some 14) none 1 0 8), gr 8 3] 3) := by dec_rfl
theorem p55_75 : ∀ feat, Dec feat p55 75 (FV7z.mk .inc 64 [gr 64 14] 3) := by dec_rfl
theorem p55_78 : ∀ feat, Dec feat p55 78 (FV7z.mk .cmp 64 [gr 64 15, .mem (mg (some 4) none 1 72 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o55 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 1,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.mov 32 6 (.r 3),
  Op.cmov32 2 7 10,
  Op.sbb 32 3 (.i 255),
  Op.sub 32 7 (.r 1),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 1),
  Op.st 16 (some 2) (some 6) 1 0 7,
  Op.ld 64 11 (some 4) none 1 48,
  Op.ld 32 1 (some 4) none 1 88,
  Op.and 32 1 (.r 13),
  Op.shl 1 (.i 5),
  Op.lea 64 6 (some 11) (some 8) 1 0,
  Op.ld 64 14 (some 4) none 1 104,
  Op.st 8 (some 14) none 1 0 3,
  Op.inc 64 14,
  Op.cmpm 64 15 (some 4) none 1 72]

theorem b55 (prof : Profile) : Blk prof p55 0 83 o55 :=
  .cons (p55_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p55_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p55_5 _) (OpI.imul) (by decide) <|
  .cons (p55_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p55_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p55_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p55_14 _) (OpI.cmov32) (by decide) <|
  .cons (p55_17 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p55_22 _) (OpI.cmov32) (by decide) <|
  .cons (p55_25 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p55_27 _) (OpI.cmov32) (by decide) <|
  .cons (p55_31 _) (OpI.sbb (.i 255) (.inl rfl)) (by decide) <|
  .cons (p55_37 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p55_39 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p55_42 _) (OpI.add (.r 1) (.inl rfl)) (by decide) <|
  .cons (p55_44 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p55_48 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p55_53 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p55_57 _) (OpI.and (.r 13) (.inl rfl)) (by decide) <|
  .cons (p55_60 _) (OpI.shl (.i 5)) (by decide) <|
  .cons (p55_63 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p55_67 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p55_72 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p55_75 _) (OpI.inc (.inr rfl)) (by decide) <|
  .cons (p55_78 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 83

def j29 : List Byte := [0x0f, 0x83, 0x54, 0x03, 0x00, 0x00]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 3) 64 [.rel 852] 6) := by dec_rfl

def j30 : List Byte := [0x0f, 0x83, 0x49, 0x03, 0x00, 0x00]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 3) 64 [.rel 841] 6) := by dec_rfl

def j31 : List Byte := [0x0f, 0x83, 0x2f, 0xf5, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709548847] 6) := by dec_rfl

/-- The stretch at `3813`. -/
def p56 : List Byte := [
  0x44, 0x8b, 0x4c, 0x24, 0x54, 0x41, 0x83, 0xe8, 0x06]

theorem p56_0 : ∀ feat, Dec feat p56 0 (FV7z.mk .mov 32 [gr 32 9, .mem (mg (some 4) none 1 84 32)] 5) := by dec_rfl
theorem p56_5 : ∀ feat, Dec feat p56 5 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.i 6)] 4) := by dec_rfl

/-- What the stretch does. -/
def o56 : List Op := [
  Op.ld 32 9 (some 4) none 1 84,
  Op.sub 32 8 (.i 6)]

theorem b56 (prof : Profile) : Blk prof p56 0 9 o56 :=
  .cons (p56_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p56_5 _) (OpI.sub (.i 6) (.inl rfl)) (by decide) <|
  .nil 9

def j32 : List Byte := [0xe9, 0x10, 0xf2, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk .jmp 64 [.rel 18446744073709548048] 5) := by dec_rfl

/-- The stretch at `3840`. -/
def p57 : List Byte := [
  0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x89, 0x94, 0x0e, 0x00, 0xf4,
  0xff, 0xff, 0x4c, 0x8b, 0x64, 0x24, 0x38, 0x49, 0x8b, 0xfe, 0x8b, 0x54, 0x24, 0x70, 0x49, 0x2b,
  0xfc, 0x49, 0x81, 0xeb, 0x00, 0xf6, 0xff, 0xff, 0x41, 0x83, 0xc8, 0x02, 0x41, 0xff, 0xc5, 0x8b,
  0x4c, 0x24, 0x58, 0x41, 0x23, 0xcd, 0xc1, 0xe1, 0x05, 0x4b, 0x8d, 0x34, 0x03, 0x48, 0x2b, 0xfa]

theorem p57_0 : ∀ feat, Dec feat p57 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p57_3 : ∀ feat, Dec feat p57 3 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p57_5 : ∀ feat, Dec feat p57 5 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p57_8 : ∀ feat, Dec feat p57 8 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p57_10 : ∀ feat, Dec feat p57 10 (FV7z.mk .mov 16 [.mem (mg (some 6) (some 1) 1 18446744073709548544 16), gr 16 2] 8) := by dec_rfl
theorem p57_18 : ∀ feat, Dec feat p57 18 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p57_23 : ∀ feat, Dec feat p57 23 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p57_26 : ∀ feat, Dec feat p57 26 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 112 32)] 4) := by dec_rfl
theorem p57_30 : ∀ feat, Dec feat p57 30 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p57_33 : ∀ feat, Dec feat p57 33 (FV7z.mk .sub 64 [gr 64 11, Src.opd 64 (.i 18446744073709549056)] 7) := by dec_rfl
theorem p57_40 : ∀ feat, Dec feat p57 40 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.i 2)] 4) := by dec_rfl
theorem p57_44 : ∀ feat, Dec feat p57 44 (FV7z.mk .inc 32 [gr 32 13] 3) := by dec_rfl
theorem p57_47 : ∀ feat, Dec feat p57 47 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 88 32)] 4) := by dec_rfl
theorem p57_51 : ∀ feat, Dec feat p57 51 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p57_54 : ∀ feat, Dec feat p57 54 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p57_57 : ∀ feat, Dec feat p57 57 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 11) (some 8) 1 0 0)] 4) := by dec_rfl
theorem p57_61 : ∀ feat, Dec feat p57 61 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o57 : List Op := [
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 6) (some 1) 1 18446744073709548544 2,
  Op.ld 64 12 (some 4) none 1 56,
  Op.mov 64 7 (.r 14),
  Op.ld 32 2 (some 4) none 1 112,
  Op.sub 64 7 (.r 12),
  Op.sub 64 11 (.i 18446744073709549056),
  Op.or 32 8 (.i 2),
  Op.inc 32 13,
  Op.ld 32 1 (some 4) none 1 88,
  Op.and 32 1 (.r 13),
  Op.shl 1 (.i 5),
  Op.lea 64 6 (some 11) (some 8) 1 0,
  Op.sub 64 7 (.r 2)]

theorem b57 (prof : Profile) : Blk prof p57 0 64 o57 :=
  .cons (p57_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p57_3 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p57_5 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p57_8 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p57_10 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p57_18 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p57_23 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p57_26 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p57_30 _) (OpI.sub (.r 12) (.inr rfl)) (by decide) <|
  .cons (p57_33 _) (OpI.sub (.i 18446744073709549056) (.inr rfl)) (by decide) <|
  .cons (p57_40 _) (OpI.or (.i 2) (.inl rfl)) (by decide) <|
  .cons (p57_44 _) (OpI.inc (.inl rfl)) (by decide) <|
  .cons (p57_47 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p57_51 _) (OpI.and (.r 13) (.inl rfl)) (by decide) <|
  .cons (p57_54 _) (OpI.shl (.i 5)) (by decide) <|
  .cons (p57_57 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p57_61 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .nil 64

/-- The stretch at `3906`. -/
def p58 : List Byte := [
  0x48, 0x03, 0x7c, 0x24, 0x28]

theorem p58_0 : ∀ feat, Dec feat p58 0 (FV7z.mk .add 64 [gr 64 7, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o58 : List Op := [
  Op.addm 64 7 (some 4) none 1 40]

theorem b58 (prof : Profile) : Blk prof p58 0 5 o58 :=
  .cons (p58_0 _) (OpI.addm (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `3911`. -/
def p59 : List Byte := [
  0x41, 0x0f, 0xb6, 0x1c, 0x3c]

theorem p59_0 : ∀ feat, Dec feat p59 0 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 12) (some 7) 1 0 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o59 : List Op := [
  Op.ldzx 8 3 (some 12) (some 7) 1 0]

theorem b59 (prof : Profile) : Blk prof p59 0 5 o59 :=
  .cons (p59_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 5

def j33 : List Byte := [0xe9, 0x9c, 0xfb, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk .jmp 64 [.rel 18446744073709550492] 5) := by dec_rfl

/-- The stretch at `3936`. -/
def p60 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x89, 0x7e,
  0x20, 0x41, 0x83, 0xf8, 0x0e, 0x41, 0xb8, 0x10, 0x00, 0x00, 0x00, 0xba, 0x16, 0x00, 0x00, 0x00,
  0x44, 0x0f, 0x43, 0xc2, 0x49, 0x81, 0xc3, 0x00, 0xf6, 0xff, 0xff, 0x0f, 0xb7, 0x56, 0x38]

theorem p60_0 : ∀ feat, Dec feat p60 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p60_2 : ∀ feat, Dec feat p60 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p60_4 : ∀ feat, Dec feat p60 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p60_6 : ∀ feat, Dec feat p60 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p60_8 : ∀ feat, Dec feat p60 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p60_11 : ∀ feat, Dec feat p60 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p60_13 : ∀ feat, Dec feat p60 13 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 32 16), gr 16 7] 4) := by dec_rfl
theorem p60_17 : ∀ feat, Dec feat p60 17 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 14)] 4) := by dec_rfl
theorem p60_21 : ∀ feat, Dec feat p60 21 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 16)] 6) := by dec_rfl
theorem p60_27 : ∀ feat, Dec feat p60 27 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 22)] 5) := by dec_rfl
theorem p60_32 : ∀ feat, Dec feat p60 32 (FV7z.mk (.cmovcc 3) 32 [gr 32 8, gr 32 2] 4) := by dec_rfl
theorem p60_36 : ∀ feat, Dec feat p60 36 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 18446744073709549056)] 7) := by dec_rfl
theorem p60_43 : ∀ feat, Dec feat p60 43 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) none 1 56 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o60 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 6) none 1 32 7,
  Op.cmp 32 8 (.i 14),
  Op.mov 32 8 (.i 16),
  Op.mov 32 2 (.i 22),
  Op.cmov32 3 8 2,
  Op.add 64 11 (.i 18446744073709549056),
  Op.ldzx 16 2 (some 6) none 1 56]

theorem b60 (prof : Profile) : Blk prof p60 0 47 o60 :=
  .cons (p60_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p60_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p60_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p60_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p60_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p60_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p60_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p60_17 _) (OpI.cmp (.i 14) (.inl rfl)) (by decide) <|
  .cons (p60_21 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p60_27 _) (OpI.mov (.i 22) (.inl rfl)) (by decide) <|
  .cons (p60_32 _) (OpI.cmov32) (by decide) <|
  .cons (p60_36 _) (OpI.add (.i 18446744073709549056) (.inr rfl)) (by decide) <|
  .cons (p60_43 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 47

def j34 : List Byte := [0x73, 0x72]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk (.jcc 3) 64 [.rel 114] 2) := by dec_rfl

/-- The stretch at `4014`. -/
def p61 : List Byte := [
  0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x89, 0x56, 0x38, 0x0f, 0xb7,
  0x94, 0x0e, 0x00, 0xf4, 0xff, 0xff]

theorem p61_0 : ∀ feat, Dec feat p61 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p61_3 : ∀ feat, Dec feat p61 3 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p61_5 : ∀ feat, Dec feat p61 5 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p61_8 : ∀ feat, Dec feat p61 8 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p61_10 : ∀ feat, Dec feat p61 10 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 56 16), gr 16 2] 4) := by dec_rfl
theorem p61_14 : ∀ feat, Dec feat p61 14 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) (some 1) 1 18446744073709548544 16)] 8) := by dec_rfl

/-- What the stretch does. -/
def o61 : List Op := [
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 6) none 1 56 2,
  Op.ldzx 16 2 (some 6) (some 1) 1 18446744073709548544]

theorem b61 (prof : Profile) : Blk prof p61 0 22 o61 :=
  .cons (p61_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p61_3 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p61_5 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p61_8 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p61_10 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p61_14 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 22

def j35 : List Byte := [0x0f, 0x82, 0x19, 0xff, 0xff, 0xff]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551385] 6) := by dec_rfl

/-- The stretch at `4071`. -/
def p62 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x89, 0xbc,
  0x0e, 0x00, 0xf4, 0xff, 0xff]

theorem p62_0 : ∀ feat, Dec feat p62 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p62_2 : ∀ feat, Dec feat p62 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p62_4 : ∀ feat, Dec feat p62 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p62_6 : ∀ feat, Dec feat p62 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p62_8 : ∀ feat, Dec feat p62 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p62_11 : ∀ feat, Dec feat p62 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p62_13 : ∀ feat, Dec feat p62 13 (FV7z.mk .mov 16 [.mem (mg (some 6) (some 1) 1 18446744073709548544 16), gr 16 7] 8) := by dec_rfl

/-- What the stretch does. -/
def o62 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 6) (some 1) 1 18446744073709548544 7]

theorem b62 (prof : Profile) : Blk prof p62 0 21 o62 :=
  .cons (p62_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p62_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p62_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p62_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p62_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p62_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p62_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 21

def j36 : List Byte := [0xe9, 0x68, 0xf4, 0xff, 0xff]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk .jmp 64 [.rel 18446744073709548648] 5) := by dec_rfl

/-- The stretch at `4128`. -/
def p63 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x89, 0x7e,
  0x38, 0x44, 0x8b, 0x4c, 0x24, 0x70, 0x8b, 0x5c, 0x24, 0x74, 0x44, 0x89, 0x4c, 0x24, 0x74, 0x0f,
  0xb7, 0x56, 0x50]

theorem p63_0 : ∀ feat, Dec feat p63 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p63_2 : ∀ feat, Dec feat p63 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p63_4 : ∀ feat, Dec feat p63 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p63_6 : ∀ feat, Dec feat p63 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p63_8 : ∀ feat, Dec feat p63 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p63_11 : ∀ feat, Dec feat p63 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p63_13 : ∀ feat, Dec feat p63 13 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 56 16), gr 16 7] 4) := by dec_rfl
theorem p63_17 : ∀ feat, Dec feat p63 17 (FV7z.mk .mov 32 [gr 32 9, .mem (mg (some 4) none 1 112 32)] 5) := by dec_rfl
theorem p63_22 : ∀ feat, Dec feat p63 22 (FV7z.mk .mov 32 [gr 32 3, .mem (mg (some 4) none 1 116 32)] 4) := by dec_rfl
theorem p63_26 : ∀ feat, Dec feat p63 26 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 116 32), gr 32 9] 5) := by dec_rfl
theorem p63_31 : ∀ feat, Dec feat p63 31 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) none 1 80 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o63 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 6) none 1 56 7,
  Op.ld 32 9 (some 4) none 1 112,
  Op.ld 32 3 (some 4) none 1 116,
  Op.st 32 (some 4) none 1 116 9,
  Op.ldzx 16 2 (some 6) none 1 80]

theorem b63 (prof : Profile) : Blk prof p63 0 35 o63 :=
  .cons (p63_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p63_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p63_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p63_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p63_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p63_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p63_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p63_17 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p63_22 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p63_26 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p63_31 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 35

def j37 : List Byte := [0x73, 0x17]
theorem j37_0 : ∀ feat, Dec feat j37 0 (FV7z.mk (.jcc 3) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `4194`. -/
def p64 : List Byte := [
  0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x89, 0x56, 0x50, 0x89, 0x5c,
  0x24, 0x70]

theorem p64_0 : ∀ feat, Dec feat p64 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p64_3 : ∀ feat, Dec feat p64 3 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p64_5 : ∀ feat, Dec feat p64 5 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p64_8 : ∀ feat, Dec feat p64 8 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p64_10 : ∀ feat, Dec feat p64 10 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 80 16), gr 16 2] 4) := by dec_rfl
theorem p64_14 : ∀ feat, Dec feat p64 14 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 112 32), gr 32 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o64 : List Op := [
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 6) none 1 80 2,
  Op.st 32 (some 4) none 1 112 3]

theorem b64 (prof : Profile) : Blk prof p64 0 18 o64 :=
  .cons (p64_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p64_3 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p64_5 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p64_8 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p64_10 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p64_14 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 18

def j38 : List Byte := [0xe9, 0xf0, 0xf3, 0xff, 0xff]
theorem j38_0 : ∀ feat, Dec feat j38 0 (FV7z.mk .jmp 64 [.rel 18446744073709548528] 5) := by dec_rfl

/-- The stretch at `4217`. -/
def p65 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x89, 0x7e,
  0x50, 0x44, 0x8b, 0x4c, 0x24, 0x78, 0x89, 0x5c, 0x24, 0x78, 0x0f, 0xb7, 0x56, 0x68]

theorem p65_0 : ∀ feat, Dec feat p65 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p65_2 : ∀ feat, Dec feat p65 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p65_4 : ∀ feat, Dec feat p65 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p65_6 : ∀ feat, Dec feat p65 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p65_8 : ∀ feat, Dec feat p65 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p65_11 : ∀ feat, Dec feat p65 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p65_13 : ∀ feat, Dec feat p65 13 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 80 16), gr 16 7] 4) := by dec_rfl
theorem p65_17 : ∀ feat, Dec feat p65 17 (FV7z.mk .mov 32 [gr 32 9, .mem (mg (some 4) none 1 120 32)] 5) := by dec_rfl
theorem p65_22 : ∀ feat, Dec feat p65 22 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 120 32), gr 32 3] 4) := by dec_rfl
theorem p65_26 : ∀ feat, Dec feat p65 26 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) none 1 104 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o65 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 6) none 1 80 7,
  Op.ld 32 9 (some 4) none 1 120,
  Op.st 32 (some 4) none 1 120 3,
  Op.ldzx 16 2 (some 6) none 1 104]

theorem b65 (prof : Profile) : Blk prof p65 0 30 o65 :=
  .cons (p65_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p65_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p65_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p65_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p65_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p65_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p65_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p65_17 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p65_22 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p65_26 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 30

def j39 : List Byte := [0x73, 0x18]
theorem j39_0 : ∀ feat, Dec feat j39 0 (FV7z.mk (.jcc 3) 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `4278`. -/
def p66 : List Byte := [
  0x41, 0x8b, 0xfa, 0x2b, 0xfa, 0xc1, 0xef, 0x05, 0x03, 0xd7, 0x66, 0x89, 0x56, 0x68, 0x44, 0x89,
  0x4c, 0x24, 0x70]

theorem p66_0 : ∀ feat, Dec feat p66 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p66_3 : ∀ feat, Dec feat p66 3 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p66_5 : ∀ feat, Dec feat p66 5 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p66_8 : ∀ feat, Dec feat p66 8 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p66_10 : ∀ feat, Dec feat p66 10 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 104 16), gr 16 2] 4) := by dec_rfl
theorem p66_14 : ∀ feat, Dec feat p66 14 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 112 32), gr 32 9] 5) := by dec_rfl

/-- What the stretch does. -/
def o66 : List Op := [
  Op.mov 32 7 (.r 10),
  Op.sub 32 7 (.r 2),
  Op.shr 7 (.i 5),
  Op.add 32 2 (.r 7),
  Op.st 16 (some 6) none 1 104 2,
  Op.st 32 (some 4) none 1 112 9]

theorem b66 (prof : Profile) : Blk prof p66 0 19 o66 :=
  .cons (p66_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p66_3 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p66_5 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p66_8 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p66_10 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p66_14 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 19

def j40 : List Byte := [0xe9, 0x9b, 0xf3, 0xff, 0xff]
theorem j40_0 : ∀ feat, Dec feat j40 0 (FV7z.mk .jmp 64 [.rel 18446744073709548443] 5) := by dec_rfl

/-- The stretch at `4302`. -/
def p67 : List Byte := [
  0x2b, 0xf8, 0x2b, 0xe8, 0x8b, 0xc7, 0x8b, 0xfa, 0xc1, 0xea, 0x05, 0x2b, 0xfa, 0x66, 0x89, 0x7e,
  0x68, 0x8b, 0x5c, 0x24, 0x7c, 0x44, 0x89, 0x4c, 0x24, 0x7c, 0x89, 0x5c, 0x24, 0x70]

theorem p67_0 : ∀ feat, Dec feat p67 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p67_2 : ∀ feat, Dec feat p67 2 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p67_4 : ∀ feat, Dec feat p67 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p67_6 : ∀ feat, Dec feat p67 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p67_8 : ∀ feat, Dec feat p67 8 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p67_11 : ∀ feat, Dec feat p67 11 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p67_13 : ∀ feat, Dec feat p67 13 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 104 16), gr 16 7] 4) := by dec_rfl
theorem p67_17 : ∀ feat, Dec feat p67 17 (FV7z.mk .mov 32 [gr 32 3, .mem (mg (some 4) none 1 124 32)] 4) := by dec_rfl
theorem p67_21 : ∀ feat, Dec feat p67 21 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 124 32), gr 32 9] 5) := by dec_rfl
theorem p67_26 : ∀ feat, Dec feat p67 26 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 112 32), gr 32 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o67 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 5 (.r 0),
  Op.mov 32 0 (.r 7),
  Op.mov 32 7 (.r 2),
  Op.shr 2 (.i 5),
  Op.sub 32 7 (.r 2),
  Op.st 16 (some 6) none 1 104 7,
  Op.ld 32 3 (some 4) none 1 124,
  Op.st 32 (some 4) none 1 124 9,
  Op.st 32 (some 4) none 1 112 3]

theorem b67 (prof : Profile) : Blk prof p67 0 30 o67 :=
  .cons (p67_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p67_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p67_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p67_6 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p67_8 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p67_11 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p67_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p67_17 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p67_21 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p67_26 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 30

def j41 : List Byte := [0xe9, 0x78, 0xf3, 0xff, 0xff]
theorem j41_0 : ∀ feat, Dec feat j41 0 (FV7z.mk .jmp 64 [.rel 18446744073709548408] 5) := by dec_rfl

/-- The stretch at `4352`. -/
def p68 : List Byte := [
  0x83, 0xe9, 0x21]

theorem p68_0 : ∀ feat, Dec feat p68 0 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 33)] 3) := by dec_rfl

/-- What the stretch does. -/
def o68 : List Op := [
  Op.sub 32 1 (.i 33)]

theorem b68 (prof : Profile) : Blk prof p68 0 3 o68 :=
  .cons (p68_0 _) (OpI.sub (.i 33) (.inl rfl)) (by decide) <|
  .nil 3

def j42 : List Byte := [0x0f, 0x86, 0x19, 0xf9, 0xff, 0xff]
theorem j42_0 : ∀ feat, Dec feat j42 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709549849] 6) := by dec_rfl

/-- The stretch at `4361`. -/
def p69 : List Byte := [
  0x83, 0xcb, 0x02, 0xd3, 0xe3, 0x49, 0x8d, 0x9c, 0x5b, 0x02, 0xf3, 0xff, 0xff, 0x41, 0xb9, 0x02,
  0x00, 0x00, 0x00, 0x0f, 0x1f, 0x40, 0x00]

theorem p69_0 : ∀ feat, Dec feat p69 0 (FV7z.mk .or 32 [gr 32 3, Src.opd 32 (.i 2)] 3) := by dec_rfl
theorem p69_3 : ∀ feat, Dec feat p69 3 (FV7z.mk .shl 32 [gr 32 3, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p69_5 : ∀ feat, Dec feat p69 5 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 11) (some 3) 2 18446744073709548290 0)] 8) := by dec_rfl
theorem p69_13 : ∀ feat, Dec feat p69 13 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 2)] 6) := by dec_rfl
theorem p69_19 : ∀ feat, Dec feat p69 19 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o69 : List Op := [
  Op.or 32 3 (.i 2),
  Op.shl 3 (.r 1),
  Op.lea 64 3 (some 11) (some 3) 2 18446744073709548290,
  Op.mov 32 9 (.i 2),
  Op.nop]

theorem b69 (prof : Profile) : Blk prof p69 0 23 o69 :=
  .cons (p69_0 _) (OpI.or (.i 2) (.inl rfl)) (by decide) <|
  .cons (p69_3 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p69_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p69_13 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p69_19 _) (OpI.nop) (by decide) <|
  .nil 23

/-- The stretch at `4384`. -/
def p70 : List Byte := [
  0x0f, 0xb7, 0x13, 0x4c, 0x8b, 0xdb, 0x49, 0x03, 0xd9]

theorem p70_0 : ∀ feat, Dec feat p70 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 3) none 1 0 16)] 3) := by dec_rfl
theorem p70_3 : ∀ feat, Dec feat p70 3 (FV7z.mk .mov 64 [gr 64 11, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p70_6 : ∀ feat, Dec feat p70 6 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o70 : List Op := [
  Op.ldzx 16 2 (some 3) none 1 0,
  Op.mov 64 11 (.r 3),
  Op.add 64 3 (.r 9)]

theorem b70 (prof : Profile) : Blk prof p70 0 9 o70 :=
  .cons (p70_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p70_3 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p70_6 _) (OpI.add (.r 9) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `4412`. -/
def p71 : List Byte := [
  0x8b, 0xf8, 0xc1, 0xe8, 0x0b, 0x0f, 0xaf, 0xc2, 0x2b, 0xf8, 0x8b, 0xf5, 0x2b, 0xe8, 0x0f, 0x43,
  0xc7, 0x4a, 0x8d, 0x3c, 0x0b, 0x48, 0x0f, 0x43, 0xdf, 0xbf, 0x1f, 0x00, 0x00, 0x00, 0x0f, 0x42,
  0xee, 0x41, 0x0f, 0x42, 0xfa, 0x45, 0x03, 0xc9, 0x2b, 0xfa, 0xc1, 0xff, 0x05, 0x03, 0xfa, 0x66,
  0x41, 0x89, 0x3b, 0xff, 0xc9]

theorem p71_0 : ∀ feat, Dec feat p71 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p71_2 : ∀ feat, Dec feat p71 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p71_5 : ∀ feat, Dec feat p71 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p71_8 : ∀ feat, Dec feat p71 8 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p71_10 : ∀ feat, Dec feat p71 10 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p71_12 : ∀ feat, Dec feat p71 12 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p71_14 : ∀ feat, Dec feat p71 14 (FV7z.mk (.cmovcc 3) 32 [gr 32 0, gr 32 7] 3) := by dec_rfl
theorem p71_17 : ∀ feat, Dec feat p71 17 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) (some 9) 1 0 0)] 4) := by dec_rfl
theorem p71_21 : ∀ feat, Dec feat p71 21 (FV7z.mk (.cmovcc 3) 64 [gr 64 3, gr 64 7] 4) := by dec_rfl
theorem p71_25 : ∀ feat, Dec feat p71 25 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p71_30 : ∀ feat, Dec feat p71 30 (FV7z.mk (.cmovcc 2) 32 [gr 32 5, gr 32 6] 3) := by dec_rfl
theorem p71_33 : ∀ feat, Dec feat p71 33 (FV7z.mk (.cmovcc 2) 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p71_37 : ∀ feat, Dec feat p71 37 (FV7z.mk .add 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p71_40 : ∀ feat, Dec feat p71 40 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p71_42 : ∀ feat, Dec feat p71 42 (FV7z.mk .sar 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p71_45 : ∀ feat, Dec feat p71 45 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p71_47 : ∀ feat, Dec feat p71 47 (FV7z.mk .mov 16 [.mem (mg (some 11) none 1 0 16), gr 16 7] 4) := by dec_rfl
theorem p71_51 : ∀ feat, Dec feat p71 51 (FV7z.mk .dec 32 [gr 32 1] 2) := by dec_rfl

/-- What the stretch does. -/
def o71 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 0 (.i 11),
  Op.imul 0 2,
  Op.sub 32 7 (.r 0),
  Op.mov 32 6 (.r 5),
  Op.sub 32 5 (.r 0),
  Op.cmov32 3 0 7,
  Op.lea 64 7 (some 3) (some 9) 1 0,
  Op.cmov64 3 3 7,
  Op.mov 32 7 (.i 31),
  Op.cmov32 2 5 6,
  Op.cmov32 2 7 10,
  Op.add 32 9 (.r 9),
  Op.sub 32 7 (.r 2),
  Op.sar 7 (.i 5),
  Op.add 32 7 (.r 2),
  Op.st 16 (some 11) none 1 0 7,
  Op.dec 32 1]

theorem b71 (prof : Profile) : Blk prof p71 0 53 o71 :=
  .cons (p71_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p71_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p71_5 _) (OpI.imul) (by decide) <|
  .cons (p71_8 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p71_10 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p71_12 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p71_14 _) (OpI.cmov32) (by decide) <|
  .cons (p71_17 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p71_21 _) (OpI.cmov64) (by decide) <|
  .cons (p71_25 _) (OpI.mov (.i 31) (.inl rfl)) (by decide) <|
  .cons (p71_30 _) (OpI.cmov32) (by decide) <|
  .cons (p71_33 _) (OpI.cmov32) (by decide) <|
  .cons (p71_37 _) (OpI.add (.r 9) (.inl rfl)) (by decide) <|
  .cons (p71_40 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p71_42 _) (OpI.sar (.i 5)) (by decide) <|
  .cons (p71_45 _) (OpI.add (.r 2) (.inl rfl)) (by decide) <|
  .cons (p71_47 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p71_51 _) (OpI.dec (.inl rfl)) (by decide) <|
  .nil 53

def j43 : List Byte := [0x75, 0xad]
theorem j43_0 : ∀ feat, Dec feat j43 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551533] 2) := by dec_rfl

/-- The stretch at `4467`. -/
def p72 : List Byte := [
  0x4c, 0x8b, 0x5c, 0x24, 0x30, 0x41, 0x2b, 0xd9, 0x81, 0xeb, 0x00, 0xf3, 0xff, 0xff, 0x49, 0x2b,
  0xdb, 0xd1, 0xeb]

theorem p72_0 : ∀ feat, Dec feat p72 0 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 4) none 1 48 64)] 5) := by dec_rfl
theorem p72_5 : ∀ feat, Dec feat p72 5 (FV7z.mk .sub 32 [gr 32 3, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p72_8 : ∀ feat, Dec feat p72 8 (FV7z.mk .sub 32 [gr 32 3, Src.opd 32 (.i 4294963968)] 6) := by dec_rfl
theorem p72_14 : ∀ feat, Dec feat p72 14 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 11)] 3) := by dec_rfl
theorem p72_17 : ∀ feat, Dec feat p72 17 (FV7z.mk .shr 32 [gr 32 3, Src.opd 8 (.i 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o72 : List Op := [
  Op.ld 64 11 (some 4) none 1 48,
  Op.sub 32 3 (.r 9),
  Op.sub 32 3 (.i 4294963968),
  Op.sub 64 3 (.r 11),
  Op.shr 3 (.i 1)]

theorem b72 (prof : Profile) : Blk prof p72 0 19 o72 :=
  .cons (p72_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p72_5 _) (OpI.sub (.r 9) (.inl rfl)) (by decide) <|
  .cons (p72_8 _) (OpI.sub (.i 4294963968) (.inl rfl)) (by decide) <|
  .cons (p72_14 _) (OpI.sub (.r 11) (.inr rfl)) (by decide) <|
  .cons (p72_17 _) (OpI.shr (.i 1)) (by decide) <|
  .nil 19

def j44 : List Byte := [0xe9, 0x97, 0xf8, 0xff, 0xff]
theorem j44_0 : ∀ feat, Dec feat j44 0 (FV7z.mk .jmp 64 [.rel 18446744073709549719] 5) := by dec_rfl

/-- The stretch at `4491`. -/
def p73 : List Byte := [
  0x48, 0x8b, 0xf7, 0x49, 0x8b, 0xfc, 0x48, 0x8b, 0x4c, 0x24, 0x28, 0x48, 0xf7, 0xda]

theorem p73_0 : ∀ feat, Dec feat p73 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p73_3 : ∀ feat, Dec feat p73 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p73_6 : ∀ feat, Dec feat p73 6 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p73_11 : ∀ feat, Dec feat p73 11 (FV7z.mk .neg 64 [gr 64 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o73 : List Op := [
  Op.mov 64 6 (.r 7),
  Op.mov 64 7 (.r 12),
  Op.ld 64 1 (some 4) none 1 40,
  Op.neg 64 2]

theorem b73 (prof : Profile) : Blk prof p73 0 14 o73 :=
  .cons (p73_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p73_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p73_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p73_11 _) (OpI.neg (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `4505`. -/
def p74 : List Byte := [
  0x0f, 0xb6, 0x1c, 0x37, 0x48, 0xff, 0xc6, 0x41, 0x88, 0x1c, 0x16, 0x48, 0xff, 0xc2, 0x48, 0x3b,
  0xf1]

theorem p74_0 : ∀ feat, Dec feat p74 0 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 7) (some 6) 1 0 8)] 4) := by dec_rfl
theorem p74_4 : ∀ feat, Dec feat p74 4 (FV7z.mk .inc 64 [gr 64 6] 3) := by dec_rfl
theorem p74_7 : ∀ feat, Dec feat p74 7 (FV7z.mk .mov 8 [.mem (mg (some 14) (some 2) 1 0 8), gr 8 3] 4) := by dec_rfl
theorem p74_11 : ∀ feat, Dec feat p74 11 (FV7z.mk .inc 64 [gr 64 2] 3) := by dec_rfl
theorem p74_14 : ∀ feat, Dec feat p74 14 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o74 : List Op := [
  Op.ldzx 8 3 (some 7) (some 6) 1 0,
  Op.inc 64 6,
  Op.st 8 (some 14) (some 2) 1 0 3,
  Op.inc 64 2,
  Op.cmp 64 6 (.r 1)]

theorem b74 (prof : Profile) : Blk prof p74 0 17 o74 :=
  .cons (p74_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p74_4 _) (OpI.inc (.inr rfl)) (by decide) <|
  .cons (p74_7 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p74_11 _) (OpI.inc (.inr rfl)) (by decide) <|
  .cons (p74_14 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 17

def j45 : List Byte := [0x75, 0xed]
theorem j45_0 : ∀ feat, Dec feat j45 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551597] 2) := by dec_rfl

/-- The stretch at `4524`. -/
def p75 : List Byte := [
  0x0f, 0xb6, 0x1f, 0x48, 0x2b, 0xfa]

theorem p75_0 : ∀ feat, Dec feat p75 0 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 7) none 1 0 8)] 3) := by dec_rfl
theorem p75_3 : ∀ feat, Dec feat p75 3 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o75 : List Op := [
  Op.ldzx 8 3 (some 7) none 1 0,
  Op.sub 64 7 (.r 2)]

theorem b75 (prof : Profile) : Blk prof p75 0 6 o75 :=
  .cons (p75_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p75_3 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .nil 6

def j46 : List Byte := [0xe9, 0x05, 0xf9, 0xff, 0xff]
theorem j46_0 : ∀ feat, Dec feat j46 0 (FV7z.mk .jmp 64 [.rel 18446744073709549829] 5) := by dec_rfl

/-- The stretch at `4535`. -/
def p76 : List Byte := [
  0x89, 0x5c, 0x24, 0x64]

theorem p76_0 : ∀ feat, Dec feat p76 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 100 32), gr 32 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o76 : List Op := [
  Op.st 32 (some 4) none 1 100 3]

theorem b76 (prof : Profile) : Blk prof p76 0 4 o76 :=
  .cons (p76_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 4

def j47 : List Byte := [0xeb, 0x46]
theorem j47_0 : ∀ feat, Dec feat j47 0 (FV7z.mk .jmp 64 [.rel 70] 2) := by dec_rfl

/-- The stretch at `4541`. -/
def p77 : List Byte := [
  0x41, 0x81, 0xc4, 0x00, 0x02, 0x00, 0x00, 0x44, 0x89, 0x64, 0x24, 0x64, 0x89, 0x5c, 0x24, 0x70,
  0x89, 0x74, 0x24, 0x74, 0x89, 0x4c, 0x24, 0x78, 0x89, 0x54, 0x24, 0x7c, 0x41, 0x83, 0xf8, 0x26,
  0x41, 0xb8, 0x0e, 0x00, 0x00, 0x00, 0xbf, 0x14, 0x00, 0x00, 0x00, 0x44, 0x0f, 0x43, 0xc7, 0xbb,
  0x01, 0x00, 0x00, 0x00]

theorem p77_0 : ∀ feat, Dec feat p77 0 (FV7z.mk .add 32 [gr 32 12, Src.opd 32 (.i 512)] 7) := by dec_rfl
theorem p77_7 : ∀ feat, Dec feat p77 7 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 100 32), gr 32 12] 5) := by dec_rfl
theorem p77_12 : ∀ feat, Dec feat p77 12 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 112 32), gr 32 3] 4) := by dec_rfl
theorem p77_16 : ∀ feat, Dec feat p77 16 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 116 32), gr 32 6] 4) := by dec_rfl
theorem p77_20 : ∀ feat, Dec feat p77 20 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 120 32), gr 32 1] 4) := by dec_rfl
theorem p77_24 : ∀ feat, Dec feat p77 24 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 124 32), gr 32 2] 4) := by dec_rfl
theorem p77_28 : ∀ feat, Dec feat p77 28 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 38)] 4) := by dec_rfl
theorem p77_32 : ∀ feat, Dec feat p77 32 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 14)] 6) := by dec_rfl
theorem p77_38 : ∀ feat, Dec feat p77 38 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 20)] 5) := by dec_rfl
theorem p77_43 : ∀ feat, Dec feat p77 43 (FV7z.mk (.cmovcc 3) 32 [gr 32 8, gr 32 7] 4) := by dec_rfl
theorem p77_47 : ∀ feat, Dec feat p77 47 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o77 : List Op := [
  Op.add 32 12 (.i 512),
  Op.st 32 (some 4) none 1 100 12,
  Op.st 32 (some 4) none 1 112 3,
  Op.st 32 (some 4) none 1 116 6,
  Op.st 32 (some 4) none 1 120 1,
  Op.st 32 (some 4) none 1 124 2,
  Op.cmp 32 8 (.i 38),
  Op.mov 32 8 (.i 14),
  Op.mov 32 7 (.i 20),
  Op.cmov32 3 8 7,
  Op.mov 32 3 (.i 1)]

theorem b77 (prof : Profile) : Blk prof p77 0 52 o77 :=
  .cons (p77_0 _) (OpI.add (.i 512) (.inl rfl)) (by decide) <|
  .cons (p77_7 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p77_12 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p77_16 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p77_20 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p77_24 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p77_28 _) (OpI.cmp (.i 38) (.inl rfl)) (by decide) <|
  .cons (p77_32 _) (OpI.mov (.i 14) (.inl rfl)) (by decide) <|
  .cons (p77_38 _) (OpI.mov (.i 20) (.inl rfl)) (by decide) <|
  .cons (p77_43 _) (OpI.cmov32) (by decide) <|
  .cons (p77_47 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 52

def j48 : List Byte := [0xeb, 0x12]
theorem j48_0 : ∀ feat, Dec feat j48 0 (FV7z.mk .jmp 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `4595`. -/
def p78 : List Byte := [
  0xff, 0xc3]

theorem p78_0 : ∀ feat, Dec feat p78 0 (FV7z.mk .inc 32 [gr 32 3] 2) := by dec_rfl

/-- What the stretch does. -/
def o78 : List Op := [
  Op.inc 32 3]

theorem b78 (prof : Profile) : Blk prof p78 0 2 o78 :=
  .cons (p78_0 _) (OpI.inc (.inl rfl)) (by decide) <|
  .nil 2

def j49 : List Byte := [0x75, 0xc6]
theorem j49_0 : ∀ feat, Dec feat j49 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551558] 2) := by dec_rfl

/-- The stretch at `4599`. -/
def p79 : List Byte := [
  0xc7, 0x44, 0x24, 0x64, 0x12, 0x01, 0x00, 0x00, 0x41, 0x83, 0xe8, 0x18]

theorem p79_0 : ∀ feat, Dec feat p79 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 100 32), .imm 32 274] 8) := by dec_rfl
theorem p79_8 : ∀ feat, Dec feat p79 8 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o79 : List Op := [
  Op.sti 32 (some 4) none 1 100 274,
  Op.sub 32 8 (.i 24)]

theorem b79 (prof : Profile) : Blk prof p79 0 12 o79 :=
  .cons (p79_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p79_8 _) (OpI.sub (.i 24) (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `4611`. -/
def p80 : List Byte := [
  0x33, 0xdb]

theorem p80_0 : ∀ feat, Dec feat p80 0 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o80 : List Op := [
  Op.xor 32 3 (.r 3)]

theorem b80 (prof : Profile) : Blk prof p80 0 2 o80 :=
  .cons (p80_0 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `4632`. -/
def p81 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x08, 0x4c, 0x2b, 0x74, 0x24, 0x38, 0x4c, 0x89, 0x71, 0x28, 0x4c, 0x89,
  0x79, 0x30, 0x89, 0x41, 0x38, 0x89, 0x69, 0x3c, 0x41, 0xd1, 0xe8, 0x44, 0x89, 0x41, 0x58, 0x44,
  0x89, 0x69, 0x40, 0x8b, 0x7c, 0x24, 0x64, 0x89, 0x79, 0x5c, 0x8b, 0x7c, 0x24, 0x70, 0x89, 0x79,
  0x48, 0x8b, 0x7c, 0x24, 0x74, 0x89, 0x79, 0x4c, 0x8b, 0x7c, 0x24, 0x78, 0x89, 0x79, 0x50, 0x8b,
  0x7c, 0x24, 0x7c, 0x89, 0x79, 0x54, 0x8b, 0xc3, 0x48, 0x8b, 0x24, 0x24, 0x41, 0x5f, 0x41, 0x5e,
  0x41, 0x5d, 0x41, 0x5c, 0x5d, 0x5b]

theorem p81_0 : ∀ feat, Dec feat p81 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p81_5 : ∀ feat, Dec feat p81 5 (FV7z.mk .sub 64 [gr 64 14, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p81_10 : ∀ feat, Dec feat p81 10 (FV7z.mk .mov 64 [.mem (mg (some 1) none 1 40 64), gr 64 14] 4) := by dec_rfl
theorem p81_14 : ∀ feat, Dec feat p81 14 (FV7z.mk .mov 64 [.mem (mg (some 1) none 1 48 64), gr 64 15] 4) := by dec_rfl
theorem p81_18 : ∀ feat, Dec feat p81 18 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 56 32), gr 32 0] 3) := by dec_rfl
theorem p81_21 : ∀ feat, Dec feat p81 21 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 60 32), gr 32 5] 3) := by dec_rfl
theorem p81_24 : ∀ feat, Dec feat p81 24 (FV7z.mk .shr 32 [gr 32 8, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p81_27 : ∀ feat, Dec feat p81 27 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 88 32), gr 32 8] 4) := by dec_rfl
theorem p81_31 : ∀ feat, Dec feat p81 31 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 64 32), gr 32 13] 4) := by dec_rfl
theorem p81_35 : ∀ feat, Dec feat p81 35 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 100 32)] 4) := by dec_rfl
theorem p81_39 : ∀ feat, Dec feat p81 39 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 92 32), gr 32 7] 3) := by dec_rfl
theorem p81_42 : ∀ feat, Dec feat p81 42 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 112 32)] 4) := by dec_rfl
theorem p81_46 : ∀ feat, Dec feat p81 46 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 72 32), gr 32 7] 3) := by dec_rfl
theorem p81_49 : ∀ feat, Dec feat p81 49 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 116 32)] 4) := by dec_rfl
theorem p81_53 : ∀ feat, Dec feat p81 53 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 76 32), gr 32 7] 3) := by dec_rfl
theorem p81_56 : ∀ feat, Dec feat p81 56 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 120 32)] 4) := by dec_rfl
theorem p81_60 : ∀ feat, Dec feat p81 60 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 80 32), gr 32 7] 3) := by dec_rfl
theorem p81_63 : ∀ feat, Dec feat p81 63 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 124 32)] 4) := by dec_rfl
theorem p81_67 : ∀ feat, Dec feat p81 67 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 84 32), gr 32 7] 3) := by dec_rfl
theorem p81_70 : ∀ feat, Dec feat p81 70 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p81_72 : ∀ feat, Dec feat p81 72 (FV7z.mk .mov 64 [gr 64 4, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p81_76 : ∀ feat, Dec feat p81 76 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl
theorem p81_78 : ∀ feat, Dec feat p81 78 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p81_80 : ∀ feat, Dec feat p81 80 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p81_82 : ∀ feat, Dec feat p81 82 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p81_84 : ∀ feat, Dec feat p81 84 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p81_85 : ∀ feat, Dec feat p81 85 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o81 : List Op := [
  Op.ld 64 1 (some 4) none 1 8,
  Op.subm 64 14 (some 4) none 1 56,
  Op.st 64 (some 1) none 1 40 14,
  Op.st 64 (some 1) none 1 48 15,
  Op.st 32 (some 1) none 1 56 0,
  Op.st 32 (some 1) none 1 60 5,
  Op.shr 8 (.i 1),
  Op.st 32 (some 1) none 1 88 8,
  Op.st 32 (some 1) none 1 64 13,
  Op.ld 32 7 (some 4) none 1 100,
  Op.st 32 (some 1) none 1 92 7,
  Op.ld 32 7 (some 4) none 1 112,
  Op.st 32 (some 1) none 1 72 7,
  Op.ld 32 7 (some 4) none 1 116,
  Op.st 32 (some 1) none 1 76 7,
  Op.ld 32 7 (some 4) none 1 120,
  Op.st 32 (some 1) none 1 80 7,
  Op.ld 32 7 (some 4) none 1 124,
  Op.st 32 (some 1) none 1 84 7,
  Op.mov 32 0 (.r 3),
  Op.ld 64 4 (some 4) none 1 0,
  Op.pop 15,
  Op.pop 14,
  Op.pop 13,
  Op.pop 12,
  Op.pop 5,
  Op.pop 3]

theorem b81 (prof : Profile) : Blk prof p81 0 86 o81 :=
  .cons (p81_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p81_5 _) (OpI.subm (.inr rfl)) (by decide) <|
  .cons (p81_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p81_14 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p81_18 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_21 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_24 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p81_27 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_31 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_35 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p81_39 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_42 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p81_46 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_49 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p81_53 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_56 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p81_60 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_63 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p81_67 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p81_70 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p81_72 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p81_76 _) (OpI.pop) (by decide) <|
  .cons (p81_78 _) (OpI.pop) (by decide) <|
  .cons (p81_80 _) (OpI.pop) (by decide) <|
  .cons (p81_82 _) (OpI.pop) (by decide) <|
  .cons (p81_84 _) (OpI.pop) (by decide) <|
  .cons (p81_85 _) (OpI.pop) (by decide) <|
  .nil 86

end FV7z.Lzma
