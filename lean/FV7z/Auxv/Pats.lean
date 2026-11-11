import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_dl_aux_init` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 46 of them) and each distinct jump (`j*`, 39) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Auxv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x07, 0x48, 0x89, 0x3d, 0x22, 0x91, 0x13, 0x00, 0x48, 0x85,
  0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [.mem (mrip 1282338 64), gr 64 7] 7) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 64 0 (some 7) none 1 0,
  Op.sta 64 8029504 7,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x66f410 : Addr) 0 17 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p0_7 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p0_14 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 17

def j0 : List Byte := [0x0f, 0x84, 0xf9, 0x03, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 1017] 6) := by dec_rfl

/-- The stretch at `23`. -/
def p1 : List Byte := [
  0x41, 0x57, 0x48, 0x8b, 0x35, 0x90, 0x56, 0x13, 0x00, 0x45, 0x31, 0xdb, 0x45, 0x31, 0xc9, 0x41,
  0x56, 0x8b, 0x0d, 0x86, 0x91, 0x13, 0x00, 0x45, 0x31, 0xf6, 0x45, 0x31, 0xc0, 0x41, 0x55, 0x4c,
  0x8b, 0x15, 0x8b, 0x3f, 0x12, 0x00, 0x48, 0x8d, 0x15, 0x0c, 0x42, 0x08, 0x00, 0x4c, 0x8b, 0x3d,
  0x3d, 0x91, 0x13, 0x00, 0x4c, 0x8b, 0x2d, 0x1e, 0x91, 0x13, 0x00, 0x41, 0x54, 0x45, 0x31, 0xe4,
  0x55, 0x8b, 0x2d, 0x52, 0x91, 0x13, 0x00, 0x53, 0x48, 0x8b, 0x1d, 0x92, 0x90, 0x13, 0x00, 0x48,
  0x89, 0x74, 0x24, 0xd8, 0x8b, 0x35, 0x5f, 0x28, 0x12, 0x00, 0x48, 0x89, 0x5c, 0x24, 0xe0, 0x48,
  0x8b, 0x1d, 0x13, 0x28, 0x12, 0x00, 0x89, 0x74, 0x24, 0xec, 0x48, 0x8b, 0x35, 0x30, 0x56, 0x13,
  0x00, 0x48, 0x89, 0x5c, 0x24, 0xf0, 0x0f, 0xb7, 0x1d, 0x28, 0x3f, 0x12, 0x00, 0x89, 0x4c, 0x24,
  0xf8, 0x48, 0x8b, 0x0d, 0x99, 0x90, 0x13, 0x00, 0xc6, 0x44, 0x24, 0xff, 0x00, 0xc6, 0x44, 0x24,
  0xfe, 0x00, 0xc6, 0x44, 0x24, 0xfd, 0x00, 0xc6, 0x44, 0x24, 0xeb, 0x00, 0xc6, 0x44, 0x24, 0xea,
  0x00, 0xc6, 0x44, 0x24, 0xfc, 0x00, 0x66, 0x89, 0x5c, 0x24, 0xe8, 0x31, 0xdb, 0x48, 0x89, 0x74,
  0x24, 0xd0, 0x31, 0xf6, 0x48, 0x89, 0x4c, 0x24, 0xc8, 0x31, 0xc9, 0x66, 0x0f, 0x1f, 0x44, 0x00,
  0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 6, .mem (mrip 1267344 64)] 7) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .xor 32 [gr 32 11, Src.opd 32 (.r 11)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .xor 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .mov 32 [gr 32 1, .mem (mrip 1282438 32)] 6) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p1_26 : ∀ feat, Dec feat p1 26 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p1_29 : ∀ feat, Dec feat p1 29 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p1_31 : ∀ feat, Dec feat p1 31 (FV7z.mk .mov 64 [gr 64 10, .mem (mrip 1195915 64)] 7) := by dec_rfl
theorem p1_38 : ∀ feat, Dec feat p1 38 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 541196 0)] 7) := by dec_rfl
theorem p1_45 : ∀ feat, Dec feat p1 45 (FV7z.mk .mov 64 [gr 64 15, .mem (mrip 1282365 64)] 7) := by dec_rfl
theorem p1_52 : ∀ feat, Dec feat p1 52 (FV7z.mk .mov 64 [gr 64 13, .mem (mrip 1282334 64)] 7) := by dec_rfl
theorem p1_59 : ∀ feat, Dec feat p1 59 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_61 : ∀ feat, Dec feat p1 61 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p1_64 : ∀ feat, Dec feat p1 64 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_65 : ∀ feat, Dec feat p1 65 (FV7z.mk .mov 32 [gr 32 5, .mem (mrip 1282386 32)] 6) := by dec_rfl
theorem p1_71 : ∀ feat, Dec feat p1 71 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_72 : ∀ feat, Dec feat p1 72 (FV7z.mk .mov 64 [gr 64 3, .mem (mrip 1282194 64)] 7) := by dec_rfl
theorem p1_79 : ∀ feat, Dec feat p1 79 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551576 64), gr 64 6] 5) := by dec_rfl
theorem p1_84 : ∀ feat, Dec feat p1 84 (FV7z.mk .mov 32 [gr 32 6, .mem (mrip 1189983 32)] 6) := by dec_rfl
theorem p1_90 : ∀ feat, Dec feat p1 90 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551584 64), gr 64 3] 5) := by dec_rfl
theorem p1_95 : ∀ feat, Dec feat p1 95 (FV7z.mk .mov 64 [gr 64 3, .mem (mrip 1189907 64)] 7) := by dec_rfl
theorem p1_102 : ∀ feat, Dec feat p1 102 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 18446744073709551596 32), gr 32 6] 4) := by dec_rfl
theorem p1_106 : ∀ feat, Dec feat p1 106 (FV7z.mk .mov 64 [gr 64 6, .mem (mrip 1267248 64)] 7) := by dec_rfl
theorem p1_113 : ∀ feat, Dec feat p1 113 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551600 64), gr 64 3] 5) := by dec_rfl
theorem p1_118 : ∀ feat, Dec feat p1 118 (FV7z.mk .movzx 32 [gr 32 3, .mem (mrip 1195816 16)] 7) := by dec_rfl
theorem p1_125 : ∀ feat, Dec feat p1 125 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 18446744073709551608 32), gr 32 1] 4) := by dec_rfl
theorem p1_129 : ∀ feat, Dec feat p1 129 (FV7z.mk .mov 64 [gr 64 1, .mem (mrip 1282201 64)] 7) := by dec_rfl
theorem p1_136 : ∀ feat, Dec feat p1 136 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551615 8), .imm 8 0] 5) := by dec_rfl
theorem p1_141 : ∀ feat, Dec feat p1 141 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551614 8), .imm 8 0] 5) := by dec_rfl
theorem p1_146 : ∀ feat, Dec feat p1 146 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551613 8), .imm 8 0] 5) := by dec_rfl
theorem p1_151 : ∀ feat, Dec feat p1 151 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551595 8), .imm 8 0] 5) := by dec_rfl
theorem p1_156 : ∀ feat, Dec feat p1 156 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551594 8), .imm 8 0] 5) := by dec_rfl
theorem p1_161 : ∀ feat, Dec feat p1 161 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551612 8), .imm 8 0] 5) := by dec_rfl
theorem p1_166 : ∀ feat, Dec feat p1 166 (FV7z.mk .mov 16 [.mem (mg (some 4) none 1 18446744073709551592 16), gr 16 3] 5) := by dec_rfl
theorem p1_171 : ∀ feat, Dec feat p1 171 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p1_173 : ∀ feat, Dec feat p1 173 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551568 64), gr 64 6] 5) := by dec_rfl
theorem p1_178 : ∀ feat, Dec feat p1 178 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_180 : ∀ feat, Dec feat p1 180 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551560 64), gr 64 1] 5) := by dec_rfl
theorem p1_185 : ∀ feat, Dec feat p1 185 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p1_187 : ∀ feat, Dec feat p1 187 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 15,
  Op.lda 64 6 8014528,
  Op.xor 32 11 (.r 11),
  Op.xor 32 9 (.r 9),
  Op.push 14,
  Op.lda 32 1 8029636,
  Op.xor 32 14 (.r 14),
  Op.xor 32 8 (.r 8),
  Op.push 13,
  Op.lda 64 10 7943128,
  Op.mov 64 2 (.i 7288416),
  Op.lda 64 15 8029592,
  Op.lda 64 13 8029568,
  Op.push 12,
  Op.xor 32 12 (.r 12),
  Op.push 5,
  Op.lda 32 5 8029632,
  Op.push 3,
  Op.lda 64 3 8029448,
  Op.st 64 (some 4) none 1 18446744073709551576 6,
  Op.lda 32 6 7937248,
  Op.st 64 (some 4) none 1 18446744073709551584 3,
  Op.lda 64 3 7937184,
  Op.st 32 (some 4) none 1 18446744073709551596 6,
  Op.lda 64 6 8014536,
  Op.st 64 (some 4) none 1 18446744073709551600 3,
  Op.ldzxa 16 3 7943116,
  Op.st 32 (some 4) none 1 18446744073709551608 1,
  Op.lda 64 1 8029512,
  Op.sti 8 (some 4) none 1 18446744073709551615 0,
  Op.sti 8 (some 4) none 1 18446744073709551614 0,
  Op.sti 8 (some 4) none 1 18446744073709551613 0,
  Op.sti 8 (some 4) none 1 18446744073709551595 0,
  Op.sti 8 (some 4) none 1 18446744073709551594 0,
  Op.sti 8 (some 4) none 1 18446744073709551612 0,
  Op.st 16 (some 4) none 1 18446744073709551592 3,
  Op.xor 32 3 (.r 3),
  Op.st 64 (some 4) none 1 18446744073709551568 6,
  Op.xor 32 6 (.r 6),
  Op.st 64 (some 4) none 1 18446744073709551560 1,
  Op.xor 32 1 (.r 1),
  Op.nop]

theorem b1 (prof : Profile) : BlkA prof p1 (0x66f427 : Addr) 0 193 o1 :=
  .cons (p1_0 _) ((OpI.push).at _) (by decide) <|
  .cons (p1_2 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_9 _) ((OpI.xor (.r 11) (.inl rfl)).at _) (by decide) <|
  .cons (p1_12 _) ((OpI.xor (.r 9) (.inl rfl)).at _) (by decide) <|
  .cons (p1_15 _) ((OpI.push).at _) (by decide) <|
  .cons (p1_17 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p1_23 _) ((OpI.xor (.r 14) (.inl rfl)).at _) (by decide) <|
  .cons (p1_26 _) ((OpI.xor (.r 8) (.inl rfl)).at _) (by decide) <|
  .cons (p1_29 _) ((OpI.push).at _) (by decide) <|
  .cons (p1_31 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_38 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_45 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_52 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_59 _) ((OpI.push).at _) (by decide) <|
  .cons (p1_61 _) ((OpI.xor (.r 12) (.inl rfl)).at _) (by decide) <|
  .cons (p1_64 _) ((OpI.push).at _) (by decide) <|
  .cons (p1_65 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p1_71 _) ((OpI.push).at _) (by decide) <|
  .cons (p1_72 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_79 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_84 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p1_90 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_95 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_102 _) ((OpI.st (.inr (.inr (.inl rfl)))).at _) (by decide) <|
  .cons (p1_106 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_113 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_118 _) (OpIA.ldzx_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_125 _) ((OpI.st (.inr (.inr (.inl rfl)))).at _) (by decide) <|
  .cons (p1_129 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_136 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (p1_141 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (p1_146 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (p1_151 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (p1_156 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (p1_161 _) ((OpI.sti (.inl rfl)).at _) (by decide) <|
  .cons (p1_166 _) ((OpI.st (.inr (.inl rfl))).at _) (by decide) <|
  .cons (p1_171 _) ((OpI.xor (.r 3) (.inl rfl)).at _) (by decide) <|
  .cons (p1_173 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_178 _) ((OpI.xor (.r 6) (.inl rfl)).at _) (by decide) <|
  .cons (p1_180 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_185 _) ((OpI.xor (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p1_187 _) ((OpI.nop).at _) (by decide) <|
  .nil 193

/-- The stretch at `216`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xe8, 0x03, 0x48, 0x83, 0xf8, 0x1e]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 3)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 30)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 64 0 (.i 3),
  Op.cmp 64 0 (.i 30)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.sub (.i 3) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmp (.i 30) (.inr rfl)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x77, 0x1e]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `226`. -/
def p3 : List Byte := [
  0x48, 0x63, 0x04, 0x82, 0x48, 0x01, 0xd0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 2) (some 0) 4 0 32)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldsx 0 (some 2) (some 0) 4 0,
  Op.add 64 0 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ldsx) (by decide) <|
  .cons (p3_4 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x3e, 0xff, 0xe0]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [gr 64 0] 3) := by dec_rfl

/-- The stretch at `240`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x47, 0x08, 0xc6, 0x44, 0x24, 0xff, 0x01, 0x48, 0x89, 0x44, 0x24, 0xf0, 0x66, 0x90]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551615 8), .imm 8 1] 5) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551600 64), gr 64 0] 5) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .nop 16 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 0 (some 7) none 1 8,
  Op.sti 8 (some 4) none 1 18446744073709551615 1,
  Op.st 64 (some 4) none 1 18446744073709551600 0,
  Op.nop]

theorem b4 (prof : Profile) : Blk prof p4 0 16 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_14 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `256`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x48, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.test 64 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 11 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 11

def j3 : List Byte := [0x75, 0xcb]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551563] 2) := by dec_rfl

/-- The stretch at `269`. -/
def p6 : List Byte := [
  0x0f, 0x1f, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.nop]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.nop) (by decide) <|
  .nil 3

/-- The stretch at `272`. -/
def p7 : List Byte := [
  0x45, 0x84, 0xc9]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 8 [gr 8 9, Src.opd 8 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 8 9 (.r 9)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.test8 (.r 9)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x0f, 0x85, 0xe7, 0x02, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 743] 6) := by dec_rfl

/-- The stretch at `281`. -/
def p8 : List Byte := [
  0x45, 0x84, 0xdb]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 8 [gr 8 11, Src.opd 8 (.r 11)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 8 11 (.r 11)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.test8 (.r 11)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x74, 0x06]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `286`. -/
def p9 : List Byte := [
  0x89, 0x2d, 0x8c, 0x90, 0x13, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [.mem (mrip 1282188 32), gr 32 5] 6) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.sta 32 8029632 5]

theorem b9 (prof : Profile) : BlkA prof p9 (0x66f52e : Addr) 0 6 o9 :=
  .cons (p9_0 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 6

/-- The stretch at `292`. -/
def p10 : List Byte := [
  0x84, 0xdb]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .test 8 [gr 8 3, Src.opd 8 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.test 8 3 (.r 3)]

theorem b10 (prof : Profile) : Blk prof p10 0 2 o10 :=
  .cons (p10_0 _) (OpI.test8 (.r 3)) (by decide) <|
  .nil 2

def j6 : List Byte := [0x74, 0x07]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `296`. -/
def p11 : List Byte := [
  0x4c, 0x89, 0x2d, 0x41, 0x90, 0x13, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [.mem (mrip 1282113 64), gr 64 13] 7) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.sta 64 8029568 13]

theorem b11 (prof : Profile) : BlkA prof p11 (0x66f538 : Addr) 0 7 o11 :=
  .cons (p11_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `303`. -/
def p12 : List Byte := [
  0x45, 0x84, 0xe4]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .test 8 [gr 8 12, Src.opd 8 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.test 8 12 (.r 12)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.test8 (.r 12)) (by decide) <|
  .nil 3

/-- The stretch at `308`. -/
def p13 : List Byte := [
  0x4c, 0x89, 0x3d, 0x4d, 0x90, 0x13, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mrip 1282125 64), gr 64 15] 7) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sta 64 8029592 15]

theorem b13 (prof : Profile) : BlkA prof p13 (0x66f544 : Addr) 0 7 o13 :=
  .cons (p13_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `315`. -/
def p14 : List Byte := [
  0x45, 0x84, 0xf6]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .test 8 [gr 8 14, Src.opd 8 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.test 8 14 (.r 14)]

theorem b14 (prof : Profile) : Blk prof p14 0 3 o14 :=
  .cons (p14_0 _) (OpI.test8 (.r 14)) (by decide) <|
  .nil 3

def j7 : List Byte := [0x74, 0x0c]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `320`. -/
def p15 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0xc8, 0x48, 0x89, 0x05, 0xec, 0x8f, 0x13, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 18446744073709551560 64)] 5) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .mov 64 [.mem (mrip 1282028 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 0 (some 4) none 1 18446744073709551560,
  Op.sta 64 8029512 0]

theorem b15 (prof : Profile) : BlkA prof p15 (0x66f550 : Addr) 0 12 o15 :=
  .cons (p15_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p15_5 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `332`. -/
def p16 : List Byte := [
  0x80, 0x7c, 0x24, 0xfc, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .cmp 8 [.mem (mg (some 4) none 1 18446744073709551612 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.cmpmi 8 (some 4) none 1 18446744073709551612 0]

theorem b16 (prof : Profile) : Blk prof p16 0 5 o16 :=
  .cons (p16_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `339`. -/
def p17 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0xd0, 0x48, 0x89, 0x05, 0x59, 0x55, 0x13, 0x00]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 18446744073709551568 64)] 5) := by dec_rfl
theorem p17_5 : ∀ feat, Dec feat p17 5 (FV7z.mk .mov 64 [.mem (mrip 1267033 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ld 64 0 (some 4) none 1 18446744073709551568,
  Op.sta 64 8014536 0]

theorem b17 (prof : Profile) : BlkA prof p17 (0x66f563 : Addr) 0 12 o17 :=
  .cons (p17_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p17_5 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `351`. -/
def p18 : List Byte := [
  0x80, 0x7c, 0x24, 0xea, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 8 [.mem (mg (some 4) none 1 18446744073709551594 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmpmi 8 (some 4) none 1 18446744073709551594 0]

theorem b18 (prof : Profile) : Blk prof p18 0 5 o18 :=
  .cons (p18_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `358`. -/
def p19 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0xd8, 0x48, 0x89, 0x05, 0x3e, 0x55, 0x13, 0x00]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 18446744073709551576 64)] 5) := by dec_rfl
theorem p19_5 : ∀ feat, Dec feat p19 5 (FV7z.mk .mov 64 [.mem (mrip 1267006 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 64 0 (some 4) none 1 18446744073709551576,
  Op.sta 64 8014528 0]

theorem b19 (prof : Profile) : BlkA prof p19 (0x66f576 : Addr) 0 12 o19 :=
  .cons (p19_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p19_5 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `370`. -/
def p20 : List Byte := [
  0x80, 0x7c, 0x24, 0xeb, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .cmp 8 [.mem (mg (some 4) none 1 18446744073709551595 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.cmpmi 8 (some 4) none 1 18446744073709551595 0]

theorem b20 (prof : Profile) : Blk prof p20 0 5 o20 :=
  .cons (p20_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `377`. -/
def p21 : List Byte := [
  0x0f, 0xb7, 0x44, 0x24, 0xe8, 0x66, 0x89, 0x05, 0x37, 0x3e, 0x12, 0x00]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 18446744073709551592 16)] 5) := by dec_rfl
theorem p21_5 : ∀ feat, Dec feat p21 5 (FV7z.mk .mov 16 [.mem (mrip 1195575 16), gr 16 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.ldzx 16 0 (some 4) none 1 18446744073709551592,
  Op.sta 16 7943116 0]

theorem b21 (prof : Profile) : BlkA prof p21 (0x66f589 : Addr) 0 12 o21 :=
  .cons (p21_0 _) ((OpI.ldzx (.inr rfl)).at _) (by decide) <|
  .cons (p21_5 _) (OpIA.st_rip (.inl rfl) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `389`. -/
def p22 : List Byte := [
  0x80, 0x7c, 0x24, 0xfd, 0x00]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .cmp 8 [.mem (mg (some 4) none 1 18446744073709551613 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.cmpmi 8 (some 4) none 1 18446744073709551613 0]

theorem b22 (prof : Profile) : Blk prof p22 0 5 o22 :=
  .cons (p22_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `396`. -/
def p23 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0xe0, 0x48, 0x89, 0x05, 0x60, 0x8f, 0x13, 0x00]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 18446744073709551584 64)] 5) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .mov 64 [.mem (mrip 1281888 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.ld 64 0 (some 4) none 1 18446744073709551584,
  Op.sta 64 8029448 0]

theorem b23 (prof : Profile) : BlkA prof p23 (0x66f59c : Addr) 0 12 o23 :=
  .cons (p23_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p23_5 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `408`. -/
def p24 : List Byte := [
  0x80, 0x7c, 0x24, 0xfe, 0x00]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .cmp 8 [.mem (mg (some 4) none 1 18446744073709551614 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.cmpmi 8 (some 4) none 1 18446744073709551614 0]

theorem b24 (prof : Profile) : Blk prof p24 0 5 o24 :=
  .cons (p24_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

def j8 : List Byte := [0x74, 0x14]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `415`. -/
def p25 : List Byte := [
  0x8b, 0x44, 0x24, 0xec, 0x89, 0x05, 0x27, 0x27, 0x12, 0x00, 0x8b, 0x44, 0x24, 0xf8, 0x89, 0x05,
  0x01, 0x90, 0x13, 0x00]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 18446744073709551596 32)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .mov 32 [.mem (mrip 1189671 32), gr 32 0] 6) := by dec_rfl
theorem p25_10 : ∀ feat, Dec feat p25 10 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 18446744073709551608 32)] 4) := by dec_rfl
theorem p25_14 : ∀ feat, Dec feat p25 14 (FV7z.mk .mov 32 [.mem (mrip 1282049 32), gr 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.ld 32 0 (some 4) none 1 18446744073709551596,
  Op.sta 32 7937248 0,
  Op.ld 32 0 (some 4) none 1 18446744073709551608,
  Op.sta 32 8029636 0]

theorem b25 (prof : Profile) : BlkA prof p25 (0x66f5af : Addr) 0 20 o25 :=
  .cons (p25_0 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .cons (p25_4 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p25_10 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .cons (p25_14 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 20

/-- The stretch at `435`. -/
def p26 : List Byte := [
  0x80, 0x7c, 0x24, 0xff, 0x00]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .cmp 8 [.mem (mg (some 4) none 1 18446744073709551615 8), .imm 8 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.cmpmi 8 (some 4) none 1 18446744073709551615 0]

theorem b26 (prof : Profile) : Blk prof p26 0 5 o26 :=
  .cons (p26_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `442`. -/
def p27 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0xf0, 0x48, 0x89, 0x05, 0xca, 0x26, 0x12, 0x00]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 18446744073709551600 64)] 5) := by dec_rfl
theorem p27_5 : ∀ feat, Dec feat p27 5 (FV7z.mk .mov 64 [.mem (mrip 1189578 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.ld 64 0 (some 4) none 1 18446744073709551600,
  Op.sta 64 7937184 0]

theorem b27 (prof : Profile) : BlkA prof p27 (0x66f5ca : Addr) 0 12 o27 :=
  .cons (p27_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p27_5 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `454`. -/
def p28 : List Byte := [
  0x83, 0xf9, 0x0f]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.cmp 32 1 (.i 15)]

theorem b28 (prof : Profile) : Blk prof p28 0 3 o28 :=
  .cons (p28_0 _) (OpI.cmp (.i 15) (.inl rfl)) (by decide) <|
  .nil 3

def j9 : List Byte := [0x75, 0x18]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `459`. -/
def p29 : List Byte := [
  0xc7, 0x05, 0xdf, 0x8f, 0x13, 0x00, 0x01, 0x00, 0x00, 0x00, 0x31, 0xc0, 0x41, 0x09, 0xf0, 0x0f,
  0x95, 0xc0, 0x89, 0x05, 0xed, 0x26, 0x12, 0x00]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [.mem (mrip 1282015 32), .imm 32 1] 10) := by dec_rfl
theorem p29_10 : ∀ feat, Dec feat p29 10 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p29_12 : ∀ feat, Dec feat p29 12 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 6)] 3) := by dec_rfl
theorem p29_15 : ∀ feat, Dec feat p29 15 (FV7z.mk (.setcc 5) 8 [gr 8 0] 3) := by dec_rfl
theorem p29_18 : ∀ feat, Dec feat p29 18 (FV7z.mk .mov 32 [.mem (mrip 1189613 32), gr 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.stia 32 8029636 1,
  Op.xor 32 0 (.r 0),
  Op.or 32 8 (.r 6),
  Op.setcc 5 0,
  Op.sta 32 7937248 0]

theorem b29 (prof : Profile) : BlkA prof p29 (0x66f5db : Addr) 0 24 o29 :=
  .cons (p29_0 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p29_10 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p29_12 _) ((OpI.or (.r 6) (.inl rfl)).at _) (by decide) <|
  .cons (p29_15 _) ((OpI.setcc).at _) (by decide) <|
  .cons (p29_18 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 24

/-- The stretch at `483`. -/
def p30 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p30_1 : ∀ feat, Dec feat p30 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p30_2 : ∀ feat, Dec feat p30 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p30_4 : ∀ feat, Dec feat p30 4 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p30_6 : ∀ feat, Dec feat p30 6 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p30_8 : ∀ feat, Dec feat p30 8 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b30 (prof : Profile) : Blk prof p30 0 10 o30 :=
  .cons (p30_0 _) (OpI.pop) (by decide) <|
  .cons (p30_1 _) (OpI.pop) (by decide) <|
  .cons (p30_2 _) (OpI.pop) (by decide) <|
  .cons (p30_4 _) (OpI.pop) (by decide) <|
  .cons (p30_6 _) (OpI.pop) (by decide) <|
  .cons (p30_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `496`. -/
def p31 : List Byte := [
  0x48, 0x8b, 0x47, 0x08, 0x48, 0x83, 0xc7, 0x10, 0xc6, 0x44, 0x24, 0xfd, 0x01, 0x48, 0x89, 0x44,
  0x24, 0xe0, 0x48, 0x8b, 0x07, 0x48, 0x85, 0xc0]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p31_4 : ∀ feat, Dec feat p31 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p31_8 : ∀ feat, Dec feat p31 8 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551613 8), .imm 8 1] 5) := by dec_rfl
theorem p31_13 : ∀ feat, Dec feat p31 13 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551584 64), gr 64 0] 5) := by dec_rfl
theorem p31_18 : ∀ feat, Dec feat p31 18 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p31_21 : ∀ feat, Dec feat p31 21 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.ld 64 0 (some 7) none 1 8,
  Op.add 64 7 (.i 16),
  Op.sti 8 (some 4) none 1 18446744073709551613 1,
  Op.st 64 (some 4) none 1 18446744073709551584 0,
  Op.ld 64 0 (some 7) none 1 0,
  Op.test 64 0 (.r 0)]

theorem b31 (prof : Profile) : Blk prof p31 0 24 o31 :=
  .cons (p31_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p31_8 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p31_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p31_18 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_21 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 24

def j10 : List Byte := [0x0f, 0x85, 0xca, 0xfe, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551306] 6) := by dec_rfl

def j11 : List Byte := [0xe9, 0xfd, 0xfe, 0xff, 0xff]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551357] 5) := by dec_rfl

/-- The stretch at `536`. -/
def p32 : List Byte := [
  0x48, 0x8b, 0x47, 0x08, 0x48, 0x83, 0xc7, 0x10, 0xc6, 0x44, 0x24, 0xea, 0x01, 0x48, 0x89, 0x44,
  0x24, 0xd8, 0x48, 0x8b, 0x07, 0x48, 0x85, 0xc0]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p32_4 : ∀ feat, Dec feat p32 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p32_8 : ∀ feat, Dec feat p32 8 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551594 8), .imm 8 1] 5) := by dec_rfl
theorem p32_13 : ∀ feat, Dec feat p32 13 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551576 64), gr 64 0] 5) := by dec_rfl
theorem p32_18 : ∀ feat, Dec feat p32 18 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p32_21 : ∀ feat, Dec feat p32 21 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.ld 64 0 (some 7) none 1 8,
  Op.add 64 7 (.i 16),
  Op.sti 8 (some 4) none 1 18446744073709551594 1,
  Op.st 64 (some 4) none 1 18446744073709551576 0,
  Op.ld 64 0 (some 7) none 1 0,
  Op.test 64 0 (.r 0)]

theorem b32 (prof : Profile) : Blk prof p32 0 24 o32 :=
  .cons (p32_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p32_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p32_8 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p32_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p32_18 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p32_21 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 24

def j12 : List Byte := [0x0f, 0x85, 0xa2, 0xfe, 0xff, 0xff]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551266] 6) := by dec_rfl

def j13 : List Byte := [0xe9, 0xd5, 0xfe, 0xff, 0xff]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk .jmp 64 [.rel 18446744073709551317] 5) := by dec_rfl

/-- The stretch at `576`. -/
def p33 : List Byte := [
  0x8b, 0x47, 0x08, 0x48, 0x83, 0xc7, 0x10, 0xc6, 0x44, 0x24, 0xfe, 0x01, 0xb9, 0xff, 0xff, 0xff,
  0xff, 0xc7, 0x44, 0x24, 0xf8, 0x01, 0x00, 0x00, 0x00, 0x89, 0x44, 0x24, 0xec, 0x48, 0x8b, 0x07,
  0x48, 0x85, 0xc0]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p33_3 : ∀ feat, Dec feat p33 3 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p33_7 : ∀ feat, Dec feat p33 7 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551614 8), .imm 8 1] 5) := by dec_rfl
theorem p33_12 : ∀ feat, Dec feat p33 12 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p33_17 : ∀ feat, Dec feat p33 17 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 18446744073709551608 32), .imm 32 1] 8) := by dec_rfl
theorem p33_25 : ∀ feat, Dec feat p33 25 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 18446744073709551596 32), gr 32 0] 4) := by dec_rfl
theorem p33_29 : ∀ feat, Dec feat p33 29 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p33_32 : ∀ feat, Dec feat p33 32 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.ld 32 0 (some 7) none 1 8,
  Op.add 64 7 (.i 16),
  Op.sti 8 (some 4) none 1 18446744073709551614 1,
  Op.mov 32 1 (.i 4294967295),
  Op.sti 32 (some 4) none 1 18446744073709551608 1,
  Op.st 32 (some 4) none 1 18446744073709551596 0,
  Op.ld 64 0 (some 7) none 1 0,
  Op.test 64 0 (.r 0)]

theorem b33 (prof : Profile) : Blk prof p33 0 35 o33 :=
  .cons (p33_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p33_3 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p33_7 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p33_12 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p33_17 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p33_25 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p33_29 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p33_32 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 35

def j14 : List Byte := [0x0f, 0x85, 0x6f, 0xfe, 0xff, 0xff]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551215] 6) := by dec_rfl

def j15 : List Byte := [0xe9, 0xa2, 0xfe, 0xff, 0xff]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 18446744073709551266] 5) := by dec_rfl

/-- The stretch at `624`. -/
def p34 : List Byte := [
  0x0f, 0xb7, 0x47, 0x08, 0x48, 0x83, 0xc7, 0x10, 0xc6, 0x44, 0x24, 0xeb, 0x01, 0x66, 0x89, 0x44,
  0x24, 0xe8, 0x48, 0x8b, 0x07, 0x48, 0x85, 0xc0]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 8 16)] 4) := by dec_rfl
theorem p34_4 : ∀ feat, Dec feat p34 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p34_8 : ∀ feat, Dec feat p34 8 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551595 8), .imm 8 1] 5) := by dec_rfl
theorem p34_13 : ∀ feat, Dec feat p34 13 (FV7z.mk .mov 16 [.mem (mg (some 4) none 1 18446744073709551592 16), gr 16 0] 5) := by dec_rfl
theorem p34_18 : ∀ feat, Dec feat p34 18 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p34_21 : ∀ feat, Dec feat p34 21 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.ldzx 16 0 (some 7) none 1 8,
  Op.add 64 7 (.i 16),
  Op.sti 8 (some 4) none 1 18446744073709551595 1,
  Op.st 16 (some 4) none 1 18446744073709551592 0,
  Op.ld 64 0 (some 7) none 1 0,
  Op.test 64 0 (.r 0)]

theorem b34 (prof : Profile) : Blk prof p34 0 24 o34 :=
  .cons (p34_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p34_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p34_8 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p34_13 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p34_18 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p34_21 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 24

def j16 : List Byte := [0x0f, 0x85, 0x4a, 0xfe, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551178] 6) := by dec_rfl

def j17 : List Byte := [0xe9, 0x7d, 0xfe, 0xff, 0xff]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551229] 5) := by dec_rfl

/-- The stretch at `664`. -/
def p35 : List Byte := [
  0x8b, 0x6f, 0x08, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x41, 0xbb, 0x01, 0x00, 0x00,
  0x00, 0x48, 0x85, 0xc0]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .mov 32 [gr 32 5, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p35_3 : ∀ feat, Dec feat p35 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p35_7 : ∀ feat, Dec feat p35 7 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p35_11 : ∀ feat, Dec feat p35 11 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p35_17 : ∀ feat, Dec feat p35 17 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.ld 32 5 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.mov 32 11 (.i 1),
  Op.test 64 0 (.r 0)]

theorem b35 (prof : Profile) : Blk prof p35 0 20 o35 :=
  .cons (p35_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p35_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p35_7 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p35_11 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p35_17 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 20

def j18 : List Byte := [0x0f, 0x85, 0x26, 0xfe, 0xff, 0xff]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551142] 6) := by dec_rfl

def j19 : List Byte := [0xe9, 0x59, 0xfe, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551193] 5) := by dec_rfl

/-- The stretch at `704`. -/
def p36 : List Byte := [
  0x48, 0x8b, 0x47, 0x08, 0x48, 0x83, 0xc7, 0x10, 0xc6, 0x44, 0x24, 0xfc, 0x01, 0x48, 0x89, 0x44,
  0x24, 0xd0, 0x48, 0x8b, 0x07, 0x48, 0x85, 0xc0]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p36_4 : ∀ feat, Dec feat p36 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p36_8 : ∀ feat, Dec feat p36 8 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18446744073709551612 8), .imm 8 1] 5) := by dec_rfl
theorem p36_13 : ∀ feat, Dec feat p36 13 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551568 64), gr 64 0] 5) := by dec_rfl
theorem p36_18 : ∀ feat, Dec feat p36 18 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p36_21 : ∀ feat, Dec feat p36 21 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.ld 64 0 (some 7) none 1 8,
  Op.add 64 7 (.i 16),
  Op.sti 8 (some 4) none 1 18446744073709551612 1,
  Op.st 64 (some 4) none 1 18446744073709551568 0,
  Op.ld 64 0 (some 7) none 1 0,
  Op.test 64 0 (.r 0)]

theorem b36 (prof : Profile) : Blk prof p36 0 24 o36 :=
  .cons (p36_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p36_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p36_8 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p36_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p36_18 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p36_21 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 24

def j20 : List Byte := [0x0f, 0x85, 0xfa, 0xfd, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551098] 6) := by dec_rfl

def j21 : List Byte := [0xe9, 0x2d, 0xfe, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk .jmp 64 [.rel 18446744073709551149] 5) := by dec_rfl

/-- The stretch at `744`. -/
def p37 : List Byte := [
  0x48, 0x8b, 0x47, 0x08, 0x48, 0x83, 0xc7, 0x10, 0x41, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x44, 0x24, 0xc8, 0x48, 0x8b, 0x07, 0x48, 0x85, 0xc0]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p37_4 : ∀ feat, Dec feat p37 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p37_8 : ∀ feat, Dec feat p37 8 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p37_14 : ∀ feat, Dec feat p37 14 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551560 64), gr 64 0] 5) := by dec_rfl
theorem p37_19 : ∀ feat, Dec feat p37 19 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p37_22 : ∀ feat, Dec feat p37 22 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.ld 64 0 (some 7) none 1 8,
  Op.add 64 7 (.i 16),
  Op.mov 32 14 (.i 1),
  Op.st 64 (some 4) none 1 18446744073709551560 0,
  Op.ld 64 0 (some 7) none 1 0,
  Op.test 64 0 (.r 0)]

theorem b37 (prof : Profile) : Blk prof p37 0 25 o37 :=
  .cons (p37_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p37_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p37_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p37_14 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p37_19 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p37_22 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 25

def j22 : List Byte := [0x0f, 0x85, 0xd1, 0xfd, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551057] 6) := by dec_rfl

def j23 : List Byte := [0xe9, 0x04, 0xfe, 0xff, 0xff]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk .jmp 64 [.rel 18446744073709551108] 5) := by dec_rfl

/-- The stretch at `784`. -/
def p38 : List Byte := [
  0x33, 0x77, 0x08, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x83, 0xc9, 0x08, 0x48, 0x85,
  0xc0]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .xor 32 [gr 32 6, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p38_3 : ∀ feat, Dec feat p38 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p38_7 : ∀ feat, Dec feat p38 7 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p38_11 : ∀ feat, Dec feat p38 11 (FV7z.mk .or 32 [gr 32 1, Src.opd 32 (.i 8)] 3) := by dec_rfl
theorem p38_14 : ∀ feat, Dec feat p38 14 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.xorm 32 6 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.or 32 1 (.i 8),
  Op.test 64 0 (.r 0)]

theorem b38 (prof : Profile) : Blk prof p38 0 17 o38 :=
  .cons (p38_0 _) (OpI.xorm (.inl rfl)) (by decide) <|
  .cons (p38_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p38_7 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p38_11 _) (OpI.or (.i 8) (.inl rfl)) (by decide) <|
  .cons (p38_14 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 17

def j24 : List Byte := [0x0f, 0x85, 0xb1, 0xfd, 0xff, 0xff]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551025] 6) := by dec_rfl

def j25 : List Byte := [0xe9, 0xe4, 0xfd, 0xff, 0xff]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk .jmp 64 [.rel 18446744073709551076] 5) := by dec_rfl

/-- The stretch at `816`. -/
def p39 : List Byte := [
  0x33, 0x77, 0x08, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x83, 0xc9, 0x04, 0x48, 0x85,
  0xc0]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .xor 32 [gr 32 6, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p39_3 : ∀ feat, Dec feat p39 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p39_7 : ∀ feat, Dec feat p39 7 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p39_11 : ∀ feat, Dec feat p39 11 (FV7z.mk .or 32 [gr 32 1, Src.opd 32 (.i 4)] 3) := by dec_rfl
theorem p39_14 : ∀ feat, Dec feat p39 14 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.xorm 32 6 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.or 32 1 (.i 4),
  Op.test 64 0 (.r 0)]

theorem b39 (prof : Profile) : Blk prof p39 0 17 o39 :=
  .cons (p39_0 _) (OpI.xorm (.inl rfl)) (by decide) <|
  .cons (p39_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p39_7 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p39_11 _) (OpI.or (.i 4) (.inl rfl)) (by decide) <|
  .cons (p39_14 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 17

def j26 : List Byte := [0x0f, 0x85, 0x91, 0xfd, 0xff, 0xff]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709550993] 6) := by dec_rfl

def j27 : List Byte := [0xe9, 0xc4, 0xfd, 0xff, 0xff]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk .jmp 64 [.rel 18446744073709551044] 5) := by dec_rfl

/-- The stretch at `848`. -/
def p40 : List Byte := [
  0x44, 0x33, 0x47, 0x08, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x83, 0xc9, 0x02, 0x48,
  0x85, 0xc0]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .xor 32 [gr 32 8, .mem (mg (some 7) none 1 8 32)] 4) := by dec_rfl
theorem p40_4 : ∀ feat, Dec feat p40 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p40_8 : ∀ feat, Dec feat p40 8 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p40_12 : ∀ feat, Dec feat p40 12 (FV7z.mk .or 32 [gr 32 1, Src.opd 32 (.i 2)] 3) := by dec_rfl
theorem p40_15 : ∀ feat, Dec feat p40 15 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.xorm 32 8 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.or 32 1 (.i 2),
  Op.test 64 0 (.r 0)]

theorem b40 (prof : Profile) : Blk prof p40 0 18 o40 :=
  .cons (p40_0 _) (OpI.xorm (.inl rfl)) (by decide) <|
  .cons (p40_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p40_8 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p40_12 _) (OpI.or (.i 2) (.inl rfl)) (by decide) <|
  .cons (p40_15 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 18

def j28 : List Byte := [0x0f, 0x85, 0x70, 0xfd, 0xff, 0xff]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709550960] 6) := by dec_rfl

def j29 : List Byte := [0xe9, 0xa3, 0xfd, 0xff, 0xff]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk .jmp 64 [.rel 18446744073709551011] 5) := by dec_rfl

/-- The stretch at `880`. -/
def p41 : List Byte := [
  0x44, 0x33, 0x47, 0x08, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x83, 0xc9, 0x01, 0x48,
  0x85, 0xc0]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .xor 32 [gr 32 8, .mem (mg (some 7) none 1 8 32)] 4) := by dec_rfl
theorem p41_4 : ∀ feat, Dec feat p41 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p41_8 : ∀ feat, Dec feat p41 8 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p41_12 : ∀ feat, Dec feat p41 12 (FV7z.mk .or 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p41_15 : ∀ feat, Dec feat p41 15 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.xorm 32 8 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.or 32 1 (.i 1),
  Op.test 64 0 (.r 0)]

theorem b41 (prof : Profile) : Blk prof p41 0 18 o41 :=
  .cons (p41_0 _) (OpI.xorm (.inl rfl)) (by decide) <|
  .cons (p41_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p41_8 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p41_12 _) (OpI.or (.i 1) (.inl rfl)) (by decide) <|
  .cons (p41_15 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 18

def j30 : List Byte := [0x0f, 0x85, 0x50, 0xfd, 0xff, 0xff]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709550928] 6) := by dec_rfl

def j31 : List Byte := [0xe9, 0x83, 0xfd, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk .jmp 64 [.rel 18446744073709550979] 5) := by dec_rfl

/-- The stretch at `912`. -/
def p42 : List Byte := [
  0x48, 0x8b, 0x47, 0x08, 0x48, 0x85, 0xc0, 0x4c, 0x0f, 0x45, 0xd0, 0xb8, 0x01, 0x00, 0x00, 0x00,
  0x44, 0x0f, 0x45, 0xc8, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x48, 0x85, 0xc0]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p42_4 : ∀ feat, Dec feat p42 4 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p42_7 : ∀ feat, Dec feat p42 7 (FV7z.mk (.cmovcc 5) 64 [gr 64 10, gr 64 0] 4) := by dec_rfl
theorem p42_11 : ∀ feat, Dec feat p42 11 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p42_16 : ∀ feat, Dec feat p42 16 (FV7z.mk (.cmovcc 5) 32 [gr 32 9, gr 32 0] 4) := by dec_rfl
theorem p42_20 : ∀ feat, Dec feat p42 20 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p42_24 : ∀ feat, Dec feat p42 24 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p42_28 : ∀ feat, Dec feat p42 28 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.ld 64 0 (some 7) none 1 8,
  Op.test 64 0 (.r 0),
  Op.cmov64 5 10 0,
  Op.mov 32 0 (.i 1),
  Op.cmov32 5 9 0,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.test 64 0 (.r 0)]

theorem b42 (prof : Profile) : Blk prof p42 0 31 o42 :=
  .cons (p42_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p42_4 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .cons (p42_7 _) (OpI.cmov64) (by decide) <|
  .cons (p42_11 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p42_16 _) (OpI.cmov32) (by decide) <|
  .cons (p42_20 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p42_24 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p42_28 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 31

def j32 : List Byte := [0x0f, 0x85, 0x23, 0xfd, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709550883] 6) := by dec_rfl

def j33 : List Byte := [0xe9, 0x56, 0xfd, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk .jmp 64 [.rel 18446744073709550934] 5) := by dec_rfl

/-- The stretch at `960`. -/
def p43 : List Byte := [
  0x4c, 0x8b, 0x7f, 0x08, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0x41, 0xbc, 0x01, 0x00,
  0x00, 0x00, 0x48, 0x85, 0xc0]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .mov 64 [gr 64 15, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p43_4 : ∀ feat, Dec feat p43 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p43_8 : ∀ feat, Dec feat p43 8 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p43_12 : ∀ feat, Dec feat p43 12 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p43_18 : ∀ feat, Dec feat p43 18 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.ld 64 15 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.mov 32 12 (.i 1),
  Op.test 64 0 (.r 0)]

theorem b43 (prof : Profile) : Blk prof p43 0 21 o43 :=
  .cons (p43_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p43_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p43_8 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p43_12 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p43_18 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 21

def j34 : List Byte := [0x0f, 0x85, 0xfd, 0xfc, 0xff, 0xff]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709550845] 6) := by dec_rfl

def j35 : List Byte := [0xe9, 0x30, 0xfd, 0xff, 0xff]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk .jmp 64 [.rel 18446744073709550896] 5) := by dec_rfl

/-- The stretch at `992`. -/
def p44 : List Byte := [
  0x4c, 0x8b, 0x6f, 0x08, 0x48, 0x8b, 0x47, 0x10, 0x48, 0x83, 0xc7, 0x10, 0xbb, 0x01, 0x00, 0x00,
  0x00, 0x48, 0x85, 0xc0]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p44_4 : ∀ feat, Dec feat p44 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p44_8 : ∀ feat, Dec feat p44 8 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p44_12 : ∀ feat, Dec feat p44 12 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p44_17 : ∀ feat, Dec feat p44 17 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.ld 64 13 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 16,
  Op.add 64 7 (.i 16),
  Op.mov 32 3 (.i 1),
  Op.test 64 0 (.r 0)]

theorem b44 (prof : Profile) : Blk prof p44 0 20 o44 :=
  .cons (p44_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p44_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p44_8 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p44_12 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p44_17 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 20

def j36 : List Byte := [0x0f, 0x85, 0xde, 0xfc, 0xff, 0xff]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709550814] 6) := by dec_rfl

def j37 : List Byte := [0xe9, 0x11, 0xfd, 0xff, 0xff]
theorem j37_0 : ∀ feat, Dec feat j37 0 (FV7z.mk .jmp 64 [.rel 18446744073709550865] 5) := by dec_rfl

/-- The stretch at `1024`. -/
def p45 : List Byte := [
  0x4c, 0x89, 0x15, 0xc1, 0x3b, 0x12, 0x00]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .mov 64 [.mem (mrip 1194945 64), gr 64 10] 7) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.sta 64 7943128 10]

theorem b45 (prof : Profile) : BlkA prof p45 (0x66f810 : Addr) 0 7 o45 :=
  .cons (p45_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 7

def j38 : List Byte := [0xe9, 0x0d, 0xfd, 0xff, 0xff]
theorem j38_0 : ∀ feat, Dec feat j38 0 (FV7z.mk .jmp 64 [.rel 18446744073709550861] 5) := by dec_rfl

end FV7z.Auxv
