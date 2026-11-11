import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_dl_non_dynamic_init` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 42 of them) and each distinct jump (`j*`, 21) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ndi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x50]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 80)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 80)]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.sub (.i 80) (.inr rfl)) (by decide) <|
  .nil 16

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x48, 0x83, 0x3d, 0xbb, 0x8c, 0x13, 0x00, 0x00, 0x48, 0x89, 0x05, 0xd4, 0x3f, 0x12, 0x00, 0x48,
  0x8b, 0x05, 0x25, 0x8d, 0x13, 0x00, 0x48, 0x89, 0x05, 0x26, 0x3f, 0x12, 0x00, 0x48, 0x8b, 0x05,
  0x2f, 0x8d, 0x13, 0x00, 0x66, 0x89, 0x05, 0x28, 0x3f, 0x12, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [.mem (mrip 1281211 64), .imm 64 0] 8) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .mov 64 [.mem (mrip 1195988 64), gr 64 0] 7) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1281317 64)] 7) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .mov 64 [.mem (mrip 1195814 64), gr 64 0] 7) := by dec_rfl
theorem p1_29 : ∀ feat, Dec feat p1 29 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1281327 64)] 7) := by dec_rfl
theorem p1_36 : ∀ feat, Dec feat p1 36 (FV7z.mk .mov 16 [.mem (mrip 1195816 16), gr 16 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmia 64 8029448 0,
  Op.sta 64 7944232 0,
  Op.lda 64 0 8029568,
  Op.sta 64 7944072 0,
  Op.lda 64 0 8029592,
  Op.sta 16 7944088 0]

theorem b1 (prof : Profile) : BlkA prof p1 (0x66f845 : Addr) 0 43 o1 :=
  .cons (p1_0 _) (OpIA.cmpmi_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_8 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p1_15 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_22 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p1_29 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_36 _) (OpIA.st_rip (.inl rfl) (by decide)) (by decide) <|
  .nil 43

def j0 : List Byte := [0x0f, 0x84, 0xaa, 0x0a, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 2730] 6) := by dec_rfl

/-- The stretch at `1945`. -/
def p2 : List Byte := [
  0x8b, 0x15, 0x11, 0x1d, 0x12, 0x00, 0x48, 0x89, 0x05, 0xe2, 0x1c, 0x12, 0x00, 0x85, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip 1187089 32)] 6) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 64 [.mem (mrip 1187042 64), gr 64 0] 7) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lda 32 2 7937248,
  Op.sta 64 7937208 0,
  Op.test 32 2 (.r 2)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x66ffc9 : Addr) 0 15 o2 :=
  .cons (p2_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p2_6 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p2_13 _) ((OpI.test (.r 2) (.inl rfl)).at _) (by decide) <|
  .nil 15

def j1 : List Byte := [0x74, 0x31]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `2011`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x3d, 0x1e, 0x39, 0x08, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 538910 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 7 (.i 7289136)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x67000b : Addr) 0 7 o3 :=
  .cons (p3_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `2023`. -/
def p4 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x09]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `2037`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x3d, 0x0c, 0x39, 0x08, 0x00, 0x89, 0x05, 0x2a, 0x85, 0x13, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 538892 0)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .mov 32 [.mem (mrip 1279274 32), gr 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 7 (.i 7289144),
  Op.sta 32 8029532 0]

theorem b5 (prof : Profile) : BlkA prof p5 (0x670025 : Addr) 0 13 o5 :=
  .cons (p5_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_7 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 13

/-- The stretch at `2055`. -/
def p6 : List Byte := [
  0x48, 0x89, 0xc7]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 7 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `2063`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x05, 0x2a, 0x85, 0x13, 0x00, 0x48, 0x8d, 0x3d, 0xfb, 0x38, 0x08, 0x00, 0x48, 0x89,
  0x05, 0x5c, 0x85, 0x13, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1279274 64)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 538875 0)] 7) := by dec_rfl
theorem p7_14 : ∀ feat, Dec feat p7 14 (FV7z.mk .mov 64 [.mem (mrip 1279324 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lda 64 0 8029552,
  Op.mov 64 7 (.i 7289160),
  Op.sta 64 8029616 0]

theorem b7 (prof : Profile) : BlkA prof p7 (0x67003f : Addr) 0 21 o7 :=
  .cons (p7_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p7_7 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_14 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 21

/-- The stretch at `2089`. -/
def p8 : List Byte := [
  0xba, 0x01, 0x00, 0x00, 0x00, 0x48, 0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 2 (.i 1),
  Op.test 64 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 8 o8 :=
  .cons (p8_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p8_5 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x74, 0x08]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `2107`. -/
def p9 : List Byte := [
  0x48, 0x8d, 0x3d, 0xe2, 0x38, 0x08, 0x00, 0x89, 0x15, 0x18, 0x85, 0x13, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 538850 0)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 32 [.mem (mrip 1279256 32), gr 32 2] 6) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 7 (.i 7289172),
  Op.sta 32 8029584 2]

theorem b9 (prof : Profile) : BlkA prof p9 (0x67006b : Addr) 0 13 o9 :=
  .cons (p9_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_7 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 13

/-- The stretch at `2125`. -/
def p10 : List Byte := [
  0x31, 0xd2, 0x48, 0x85, 0xc0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.test 64 0 (.r 0)]

theorem b10 (prof : Profile) : Blk prof p10 0 5 o10 :=
  .cons (p10_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `2140`. -/
def p11 : List Byte := [
  0x48, 0x8d, 0x3d, 0xcd, 0x38, 0x08, 0x00, 0x89, 0x15, 0x0f, 0x85, 0x13, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 538829 0)] 7) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .mov 32 [.mem (mrip 1279247 32), gr 32 2] 6) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 7 (.i 7289184),
  Op.sta 32 8029608 2]

theorem b11 (prof : Profile) : BlkA prof p11 (0x67008c : Addr) 0 13 o11 :=
  .cons (p11_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p11_7 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 13

/-- The stretch at `2176`. -/
def p12 : List Byte := [
  0x48, 0x8d, 0x3d, 0xb9, 0x38, 0x08, 0x00, 0x89, 0x15, 0xa3, 0x84, 0x13, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 538809 0)] 7) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .mov 32 [.mem (mrip 1279139 32), gr 32 2] 6) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 7 (.i 7289200),
  Op.sta 32 8029536 2]

theorem b12 (prof : Profile) : BlkA prof p12 (0x6700b0 : Addr) 0 13 o12 :=
  .cons (p12_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p12_7 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 13

/-- The stretch at `2194`. -/
def p13 : List Byte := [
  0x48, 0x89, 0x05, 0xd7, 0x84, 0x13, 0x00, 0x48, 0x85, 0xc0]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mrip 1279191 64), gr 64 0] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sta 64 8029600 0,
  Op.test 64 0 (.r 0)]

theorem b13 (prof : Profile) : BlkA prof p13 (0x6700c2 : Addr) 0 10 o13 :=
  .cons (p13_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p13_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j4 : List Byte := [0x74, 0x05]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `2211`. -/
def p14 : List Byte := [
  0x8b, 0x05, 0x07, 0x1c, 0x12, 0x00, 0x85, 0xc0, 0x48, 0x8d, 0x05, 0x03, 0x36, 0x08, 0x00, 0x48,
  0x8d, 0x50, 0xf7, 0x48, 0x0f, 0x44, 0xc2, 0x48, 0x89, 0x05, 0xaf, 0x84, 0x13, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1186823 32)] 6) := by dec_rfl
theorem p14_6 : ∀ feat, Dec feat p14 6 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p14_8 : ∀ feat, Dec feat p14 8 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 538115 0)] 7) := by dec_rfl
theorem p14_15 : ∀ feat, Dec feat p14 15 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 18446744073709551607 0)] 4) := by dec_rfl
theorem p14_19 : ∀ feat, Dec feat p14 19 (FV7z.mk (.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem p14_23 : ∀ feat, Dec feat p14 23 (FV7z.mk .mov 64 [.mem (mrip 1279151 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.lda 32 0 7937248,
  Op.test 32 0 (.r 0),
  Op.mov 64 0 (.i 7288549),
  Op.lea 64 2 (some 0) none 1 18446744073709551607,
  Op.cmov64 4 0 2,
  Op.sta 64 8029600 0]

theorem b14 (prof : Profile) : BlkA prof p14 (0x6700d3 : Addr) 0 30 o14 :=
  .cons (p14_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p14_6 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p14_8 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p14_15 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p14_19 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p14_23 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 30

/-- The stretch at `2241`. -/
def p15 : List Byte := [
  0x48, 0x8b, 0x05, 0x50, 0x84, 0x13, 0x00, 0x48, 0x85, 0xc0]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1279056 64)] 7) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.lda 64 0 8029512,
  Op.test 64 0 (.r 0)]

theorem b15 (prof : Profile) : BlkA prof p15 (0x6700f1 : Addr) 0 10 o15 :=
  .cons (p15_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p15_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j5 : List Byte := [0x74, 0x10]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `2253`. -/
def p16 : List Byte := [
  0x80, 0x38, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.cmpmi 8 (some 0) none 1 0 0]

theorem b16 (prof : Profile) : Blk prof p16 0 3 o16 :=
  .cons (p16_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0x75, 0x0b]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `2269`. -/
def p17 : List Byte := [
  0x48, 0x8d, 0x3d, 0x6e, 0x38, 0x08, 0x00]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 538734 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 64 7 (.i 7289218)]

theorem b17 (prof : Profile) : BlkA prof p17 (0x67010d : Addr) 0 7 o17 :=
  .cons (p17_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `2281`. -/
def p18 : List Byte := [
  0x48, 0x89, 0xc5, 0x48, 0x85, 0xc0]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p18_3 : ∀ feat, Dec feat p18 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.mov 64 5 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b18 (prof : Profile) : Blk prof p18 0 6 o18 :=
  .cons (p18_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p18_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0x0f, 0x84, 0x02, 0x01, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 258] 6) := by dec_rfl

/-- The stretch at `2551`. -/
def p19 : List Byte := [
  0x48, 0x8b, 0x3d, 0x1a, 0x83, 0x13, 0x00, 0x48, 0x85, 0xff]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mrip 1278746 64)] 7) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.lda 64 7 8029512,
  Op.test 64 7 (.r 7)]

theorem b19 (prof : Profile) : BlkA prof p19 (0x670227 : Addr) 0 10 o19 :=
  .cons (p19_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p19_7 _) ((OpI.test (.r 7) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j8 : List Byte := [0x74, 0x0c]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `2568`. -/
def p20 : List Byte := [
  0x48, 0x89, 0x05, 0x11, 0x83, 0x13, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [.mem (mrip 1278737 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.sta 64 8029520 0]

theorem b20 (prof : Profile) : BlkA prof p20 (0x670238 : Addr) 0 7 o20 :=
  .cons (p20_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `2575`. -/
def p21 : List Byte := [
  0x48, 0x8b, 0x05, 0x3a, 0x83, 0x13, 0x00, 0x4c, 0x8b, 0x15, 0x03, 0x37, 0x12, 0x00, 0x48, 0x85,
  0xc0]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1278778 64)] 7) := by dec_rfl
theorem p21_7 : ∀ feat, Dec feat p21 7 (FV7z.mk .mov 64 [gr 64 10, .mem (mrip 1193731 64)] 7) := by dec_rfl
theorem p21_14 : ∀ feat, Dec feat p21 14 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.lda 64 0 8029568,
  Op.lda 64 10 7944528,
  Op.test 64 0 (.r 0)]

theorem b21 (prof : Profile) : BlkA prof p21 (0x67023f : Addr) 0 17 o21 :=
  .cons (p21_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p21_7 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p21_14 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 17

def j9 : List Byte := [0x0f, 0x84, 0x97, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 151] 6) := by dec_rfl

/-- The stretch at `2598`. -/
def p22 : List Byte := [
  0x48, 0x8b, 0x0d, 0x3b, 0x83, 0x13, 0x00, 0x48, 0x8d, 0x14, 0xcd, 0x00, 0x00, 0x00, 0x00, 0x48,
  0x29, 0xca, 0x48, 0x8d, 0x0c, 0xd0, 0x48, 0x39, 0xc8]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mrip 1278779 64)] 7) := by dec_rfl
theorem p22_7 : ∀ feat, Dec feat p22 7 (FV7z.mk .lea 64 [gr 64 2, .mem (mg none (some 1) 8 0 0)] 8) := by dec_rfl
theorem p22_15 : ∀ feat, Dec feat p22 15 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p22_18 : ∀ feat, Dec feat p22 18 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) (some 2) 8 0 0)] 4) := by dec_rfl
theorem p22_22 : ∀ feat, Dec feat p22 22 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.lda 64 1 8029592,
  Op.lea 64 2 none (some 1) 8 0,
  Op.sub 64 2 (.r 1),
  Op.lea 64 1 (some 0) (some 2) 8 0,
  Op.cmp 64 0 (.r 1)]

theorem b22 (prof : Profile) : BlkA prof p22 (0x670256 : Addr) 0 25 o22 :=
  .cons (p22_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p22_7 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p22_15 _) ((OpI.sub (.r 1) (.inr rfl)).at _) (by decide) <|
  .cons (p22_18 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p22_22 _) ((OpI.cmp (.r 1) (.inr rfl)).at _) (by decide) <|
  .nil 25

def j10 : List Byte := [0x73, 0x7c]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 3) 64 [.rel 124] 2) := by dec_rfl

/-- The stretch at `2625`. -/
def p23 : List Byte := [
  0x4c, 0x8b, 0x1d, 0xd0, 0x36, 0x12, 0x00, 0x4c, 0x89, 0xd7, 0x45, 0x31, 0xc0, 0x31, 0xf6, 0x44,
  0x8b, 0x0d, 0x41, 0x31, 0x12, 0x00]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 11, .mem (mrip 1193680 64)] 7) := by dec_rfl
theorem p23_7 : ∀ feat, Dec feat p23 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p23_10 : ∀ feat, Dec feat p23 10 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p23_13 : ∀ feat, Dec feat p23 13 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p23_15 : ∀ feat, Dec feat p23 15 (FV7z.mk .mov 32 [gr 32 9, .mem (mrip 1192257 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.lda 64 11 7944520,
  Op.mov 64 7 (.r 10),
  Op.xor 32 8 (.r 8),
  Op.xor 32 6 (.r 6),
  Op.lda 32 9 7943112]

theorem b23 (prof : Profile) : BlkA prof p23 (0x670271 : Addr) 0 22 o23 :=
  .cons (p23_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p23_7 _) ((OpI.mov (.r 10) (.inr rfl)).at _) (by decide) <|
  .cons (p23_10 _) ((OpI.xor (.r 8) (.inl rfl)).at _) (by decide) <|
  .cons (p23_13 _) ((OpI.xor (.r 6) (.inl rfl)).at _) (by decide) <|
  .cons (p23_15 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .nil 22

def j11 : List Byte := [0xeb, 0x26]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 38] 2) := by dec_rfl

/-- The stretch at `2656`. -/
def p24 : List Byte := [
  0x81, 0xfa, 0x52, 0xe5, 0x74, 0x64]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1685382482)] 6) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.cmp 32 2 (.i 1685382482)]

theorem b24 (prof : Profile) : Blk prof p24 0 6 o24 :=
  .cons (p24_0 _) (OpI.cmp (.i 1685382482) (.inl rfl)) (by decide) <|
  .nil 6

def j12 : List Byte := [0x75, 0x0e]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `2664`. -/
def p25 : List Byte := [
  0x4c, 0x8b, 0x58, 0x10, 0x48, 0x8b, 0x78, 0x28, 0x41, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 0) none 1 16 64)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 40 64)] 4) := by dec_rfl
theorem p25_8 : ∀ feat, Dec feat p25 8 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.ld 64 11 (some 0) none 1 16,
  Op.ld 64 7 (some 0) none 1 40,
  Op.mov 32 8 (.i 1)]

theorem b25 (prof : Profile) : Blk prof p25 0 14 o25 :=
  .cons (p25_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 14

/-- The stretch at `2678`. -/
def p26 : List Byte := [
  0x48, 0x83, 0xc0, 0x38, 0x48, 0x39, 0xc8]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p26_4 : ∀ feat, Dec feat p26 4 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.add 64 0 (.i 56),
  Op.cmp 64 0 (.r 1)]

theorem b26 (prof : Profile) : Blk prof p26 0 7 o26 :=
  .cons (p26_0 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p26_4 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 7

def j13 : List Byte := [0x73, 0x1c]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 3) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `2687`. -/
def p27 : List Byte := [
  0x8b, 0x10, 0x81, 0xfa, 0x51, 0xe5, 0x74, 0x64]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 0) none 1 0 32)] 2) := by dec_rfl
theorem p27_2 : ∀ feat, Dec feat p27 2 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1685382481)] 6) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.ld 32 2 (some 0) none 1 0,
  Op.cmp 32 2 (.i 1685382481)]

theorem b27 (prof : Profile) : Blk prof p27 0 8 o27 :=
  .cons (p27_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p27_2 _) (OpI.cmp (.i 1685382481) (.inl rfl)) (by decide) <|
  .nil 8

def j14 : List Byte := [0x75, 0xd7]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551575] 2) := by dec_rfl

/-- The stretch at `2697`. -/
def p28 : List Byte := [
  0x44, 0x8b, 0x48, 0x04, 0x48, 0x83, 0xc0, 0x38, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x48, 0x39, 0xc8]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 32 [gr 32 9, .mem (mg (some 0) none 1 4 32)] 4) := by dec_rfl
theorem p28_4 : ∀ feat, Dec feat p28 4 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p28_8 : ∀ feat, Dec feat p28 8 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p28_13 : ∀ feat, Dec feat p28 13 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.ld 32 9 (some 0) none 1 4,
  Op.add 64 0 (.i 56),
  Op.mov 32 6 (.i 1),
  Op.cmp 64 0 (.r 1)]

theorem b28 (prof : Profile) : Blk prof p28 0 16 o28 :=
  .cons (p28_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p28_4 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p28_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p28_13 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 16

def j15 : List Byte := [0x72, 0xe4]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551588] 2) := by dec_rfl

/-- The stretch at `2715`. -/
def p29 : List Byte := [
  0x40, 0x84, 0xf6]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .test 8 [gr 8 6, Src.opd 8 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.test 8 6 (.r 6)]

theorem b29 (prof : Profile) : Blk prof p29 0 3 o29 :=
  .cons (p29_0 _) (OpI.test8 (.r 6)) (by decide) <|
  .nil 3

def j16 : List Byte := [0x74, 0x07]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `2720`. -/
def p30 : List Byte := [
  0x44, 0x89, 0x0d, 0xf1, 0x30, 0x12, 0x00]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 32 [.mem (mrip 1192177 32), gr 32 9] 7) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.sta 32 7943112 9]

theorem b30 (prof : Profile) : BlkA prof p30 (0x6702d0 : Addr) 0 7 o30 :=
  .cons (p30_0 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `2727`. -/
def p31 : List Byte := [
  0x45, 0x84, 0xc0]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .test 8 [gr 8 8, Src.opd 8 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.test 8 8 (.r 8)]

theorem b31 (prof : Profile) : Blk prof p31 0 3 o31 :=
  .cons (p31_0 _) (OpI.test8 (.r 8)) (by decide) <|
  .nil 3

def j17 : List Byte := [0x74, 0x11]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 4) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `2732`. -/
def p32 : List Byte := [
  0x4c, 0x89, 0x1d, 0x65, 0x36, 0x12, 0x00, 0x49, 0x89, 0xfa, 0x48, 0x89, 0x3d, 0x63, 0x36, 0x12,
  0x00]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 64 [.mem (mrip 1193573 64), gr 64 11] 7) := by dec_rfl
theorem p32_7 : ∀ feat, Dec feat p32 7 (FV7z.mk .mov 64 [gr 64 10, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p32_10 : ∀ feat, Dec feat p32 10 (FV7z.mk .mov 64 [.mem (mrip 1193571 64), gr 64 7] 7) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.sta 64 7944520 11,
  Op.mov 64 10 (.r 7),
  Op.sta 64 7944528 7]

theorem b32 (prof : Profile) : BlkA prof p32 (0x6702dc : Addr) 0 17 o32 :=
  .cons (p32_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p32_7 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p32_10 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 17

/-- The stretch at `2749`. -/
def p33 : List Byte := [
  0x4d, 0x85, 0xd2]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .test 64 [gr 64 10, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.test 64 10 (.r 10)]

theorem b33 (prof : Profile) : Blk prof p33 0 3 o33 :=
  .cons (p33_0 _) (OpI.test (.r 10) (.inr rfl)) (by decide) <|
  .nil 3

def j18 : List Byte := [0x75, 0x76]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 5) 64 [.rel 118] 2) := by dec_rfl

/-- The stretch at `2754`. -/
def p34 : List Byte := [
  0x48, 0x83, 0xc4, 0x50, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 80)] 4) := by dec_rfl
theorem p34_4 : ∀ feat, Dec feat p34 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p34_5 : ∀ feat, Dec feat p34 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p34_6 : ∀ feat, Dec feat p34 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p34_8 : ∀ feat, Dec feat p34 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p34_10 : ∀ feat, Dec feat p34 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.add 64 4 (.i 80),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b34 (prof : Profile) : Blk prof p34 0 12 o34 :=
  .cons (p34_0 _) (OpI.add (.i 80) (.inr rfl)) (by decide) <|
  .cons (p34_4 _) (OpI.pop) (by decide) <|
  .cons (p34_5 _) (OpI.pop) (by decide) <|
  .cons (p34_6 _) (OpI.pop) (by decide) <|
  .cons (p34_8 _) (OpI.pop) (by decide) <|
  .cons (p34_10 _) (OpI.pop) (by decide) <|
  .nil 12

/-- The stretch at `2800`. -/
def p35 : List Byte := [
  0x48, 0x8b, 0x2d, 0xc9, 0x81, 0x13, 0x00, 0x48, 0x85, 0xed]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mrip 1278409 64)] 7) := by dec_rfl
theorem p35_7 : ∀ feat, Dec feat p35 7 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.lda 64 5 8029424,
  Op.test 64 5 (.r 5)]

theorem b35 (prof : Profile) : BlkA prof p35 (0x670320 : Addr) 0 10 o35 :=
  .cons (p35_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p35_7 _) ((OpI.test (.r 5) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j19 : List Byte := [0x0f, 0x85, 0x8c, 0xf9, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709549964] 6) := by dec_rfl

/-- The stretch at `2816`. -/
def p36 : List Byte := [
  0x48, 0xc7, 0x05, 0x9d, 0x19, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .mov 64 [.mem (mrip 1186205 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.stia 64 7937240 0]

theorem b36 (prof : Profile) : BlkA prof p36 (0x670330 : Addr) 0 11 o36 :=
  .cons (p36_0 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 11

/-- The stretch at `2827`. -/
def p37 : List Byte := [
  0x48, 0xc7, 0x05, 0x8a, 0x19, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .mov 64 [.mem (mrip 1186186 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.stia 64 7937232 0]

theorem b37 (prof : Profile) : BlkA prof p37 (0x67033b : Addr) 0 11 o37 :=
  .cons (p37_0 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 11

/-- The stretch at `2838`. -/
def p38 : List Byte := [
  0x48, 0xc7, 0x05, 0x77, 0x19, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .mov 64 [.mem (mrip 1186167 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.stia 64 7937224 0]

theorem b38 (prof : Profile) : BlkA prof p38 (0x670346 : Addr) 0 11 o38 :=
  .cons (p38_0 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 11

/-- The stretch at `2849`. -/
def p39 : List Byte := [
  0x48, 0xc7, 0x05, 0x64, 0x19, 0x12, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .mov 64 [.mem (mrip 1186148 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.stia 64 7937216 0]

theorem b39 (prof : Profile) : BlkA prof p39 (0x670351 : Addr) 0 11 o39 :=
  .cons (p39_0 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 11

/-- The stretch at `2860`. -/
def p40 : List Byte := [
  0x31, 0xc0]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b40 (prof : Profile) : Blk prof p40 0 2 o40 :=
  .cons (p40_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j20 : List Byte := [0xe9, 0x66, 0xfc, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk .jmp 64 [.rel 18446744073709550694] 5) := by dec_rfl

/-- The stretch at `2872`. -/
def p41 : List Byte := [
  0x48, 0x8d, 0x3d, 0x71, 0x31, 0x12, 0x00]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1192305 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.mov 64 7 (.i 7943392)]

theorem b41 (prof : Profile) : BlkA prof p41 (0x670368 : Addr) 0 7 o41 :=
  .cons (p41_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

end FV7z.Ndi
