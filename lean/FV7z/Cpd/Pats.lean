import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `NCommandLineParser::CParser::~CParser` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 23 of them) and each distinct jump (`j*`, 11) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cpd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x53, 0x48,
  0x8b, 0x07, 0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.push 3,
  Op.ld 64 0 (some 7) none 1 0,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 21 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 21

def j0 : List Byte := [0x0f, 0x84, 0x8f, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 143] 6) := by dec_rfl

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x50, 0xf8, 0x48, 0x8d, 0x34, 0x52, 0x48, 0xc1, 0xe6, 0x03, 0x48, 0x8d, 0x1c, 0x30,
  0x48, 0x39, 0xd8]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) none 1 18446744073709551608 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 2) (some 2) 2 0 0)] 4) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .shl 64 [gr 64 6, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 0) (some 6) 1 0 0)] 4) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 0) none 1 18446744073709551608,
  Op.lea 64 6 (some 2) (some 2) 2 0,
  Op.shl64 6 (.i 3),
  Op.lea 64 3 (some 0) (some 6) 1 0,
  Op.cmp 64 0 (.r 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 19 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p1_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_16 _) (OpI.cmp (.r 3) (.inr rfl)) (by decide) <|
  .nil 19

def j1 : List Byte := [0x74, 0x6d]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 109] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x49, 0x89, 0xdd, 0x8b, 0x43, 0xf8, 0x48, 0x83, 0xeb, 0x18, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 18446744073709551608 32)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 13 (.r 3),
  Op.ld 32 0 (some 3) none 1 18446744073709551608,
  Op.sub 64 3 (.i 24),
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 12 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 12

def j2 : List Byte := [0x0f, 0x84, 0xe6, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 230] 6) := by dec_rfl

/-- The stretch at `66`. -/
def p3 : List Byte := [
  0x8d, 0x68, 0xff, 0x48, 0x8b, 0x7b, 0x08, 0x48, 0xc1, 0xe5, 0x03, 0x0f, 0x1f, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 32 [gr 32 5, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 8 64)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .shl 64 [gr 64 5, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 32 5 (some 0) none 1 18446744073709551615,
  Op.ld 64 7 (some 3) none 1 8,
  Op.shl64 5 (.i 3),
  Op.nop]

theorem b3 (prof : Profile) : Blk prof p3 0 14 o3 :=
  .cons (p3_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p3_11 _) (OpI.nop) (by decide) <|
  .nil 14

/-- The stretch at `80`. -/
def p4 : List Byte := [
  0x4c, 0x8b, 0x34, 0x2f, 0x4d, 0x85, 0xf6]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 7) (some 5) 1 0 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .test 64 [gr 64 14, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 14 (some 7) (some 5) 1 0,
  Op.test 64 14 (.r 14)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.test (.r 14) (.inr rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x74, 0x1e]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `89`. -/
def p5 : List Byte := [
  0x49, 0x8b, 0x3e, 0x48, 0x85, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 14) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 6

def j4 : List Byte := [0x74, 0x05]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `102`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xf7, 0xbe, 0x10, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 7 (.r 14),
  Op.mov 32 6 (.i 16)]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `115`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x7b, 0x08]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 8 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 7 (some 3) none 1 8]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `119`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xed, 0x08, 0x48, 0x83, 0xfd, 0xf8]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .sub 64 [gr 64 5, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.sub 64 5 (.i 8),
  Op.cmp 64 5 (.i 18446744073709551608)]

theorem b8 (prof : Profile) : Blk prof p8 0 8 o8 :=
  .cons (p8_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j5 : List Byte := [0x75, 0xcf]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551567] 2) := by dec_rfl

/-- The stretch at `129`. -/
def p9 : List Byte := [
  0x48, 0x85, 0xff]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `139`. -/
def p10 : List Byte := [
  0x49, 0x39, 0x1c, 0x24]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 64 [.mem (mg (some 12) none 1 0 64), gr 64 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmpmr 64 (some 12) none 1 0 3]

theorem b10 (prof : Profile) : Blk prof p10 0 4 o10 :=
  .cons (p10_0 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 4

def j6 : List Byte := [0x75, 0x9f]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551519] 2) := by dec_rfl

/-- The stretch at `145`. -/
def p11 : List Byte := [
  0x49, 0x8b, 0x45, 0xe0, 0x48, 0x8d, 0x34, 0x40, 0x48, 0xc1, 0xe6, 0x03]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 13) none 1 18446744073709551584 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 0) (some 0) 2 0 0)] 4) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .shl 64 [gr 64 6, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 0 (some 13) none 1 18446744073709551584,
  Op.lea 64 6 (some 0) (some 0) 2 0,
  Op.shl64 6 (.i 3)]

theorem b11 (prof : Profile) : Blk prof p11 0 12 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_8 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 12

/-- The stretch at `157`. -/
def p12 : List Byte := [
  0x48, 0x83, 0xc6, 0x08, 0x48, 0x8d, 0x7b, 0xf8]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 18446744073709551608 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.add 64 6 (.i 8),
  Op.lea 64 7 (some 3) none 1 18446744073709551608]

theorem b12 (prof : Profile) : Blk prof p12 0 8 o12 :=
  .cons (p12_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `170`. -/
def p13 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x30, 0x48, 0x85, 0xff]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 48 64)] 5) := by dec_rfl
theorem p13_5 : ∀ feat, Dec feat p13 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 64 7 (some 12) none 1 48,
  Op.test 64 7 (.r 7)]

theorem b13 (prof : Profile) : Blk prof p13 0 8 o13 :=
  .cons (p13_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `185`. -/
def p14 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x20, 0x48, 0x85, 0xff]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 32 64)] 5) := by dec_rfl
theorem p14_5 : ∀ feat, Dec feat p14 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 64 7 (some 12) none 1 32,
  Op.test 64 7 (.r 7)]

theorem b14 (prof : Profile) : Blk prof p14 0 8 o14 :=
  .cons (p14_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `200`. -/
def p15 : List Byte := [
  0x41, 0x8b, 0x44, 0x24, 0x10, 0x49, 0x8b, 0x7c, 0x24, 0x08, 0x85, 0xc0]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 16 32)] 5) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 8 64)] 5) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 32 0 (some 12) none 1 16,
  Op.ld 64 7 (some 12) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 12 o15 :=
  .cons (p15_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p15_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p15_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 12

def j7 : List Byte := [0x74, 0x3d]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `214`. -/
def p16 : List Byte := [
  0x8d, 0x58, 0xff, 0x48, 0xc1, 0xe3, 0x03, 0x0f, 0x1f, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .shl 64 [gr 64 3, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p16_7 : ∀ feat, Dec feat p16 7 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.lea 32 3 (some 0) none 1 18446744073709551615,
  Op.shl64 3 (.i 3),
  Op.nop]

theorem b16 (prof : Profile) : Blk prof p16 0 10 o16 :=
  .cons (p16_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p16_7 _) (OpI.nop) (by decide) <|
  .nil 10

/-- The stretch at `224`. -/
def p17 : List Byte := [
  0x48, 0x8b, 0x2c, 0x1f, 0x48, 0x85, 0xed]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 7) (some 3) 1 0 64)] 4) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ld 64 5 (some 7) (some 3) 1 0,
  Op.test 64 5 (.r 5)]

theorem b17 (prof : Profile) : Blk prof p17 0 7 o17 :=
  .cons (p17_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p17_4 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

def j8 : List Byte := [0x74, 0x20]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `233`. -/
def p18 : List Byte := [
  0x48, 0x8b, 0x7d, 0x00, 0x48, 0x85, 0xff]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.ld 64 7 (some 5) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b18 (prof : Profile) : Blk prof p18 0 7 o18 :=
  .cons (p18_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p18_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `247`. -/
def p19 : List Byte := [
  0x48, 0x89, 0xef, 0xbe, 0x10, 0x00, 0x00, 0x00]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p19_3 : ∀ feat, Dec feat p19 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.mov 64 7 (.r 5),
  Op.mov 32 6 (.i 16)]

theorem b19 (prof : Profile) : Blk prof p19 0 8 o19 :=
  .cons (p19_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p19_3 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `260`. -/
def p20 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x08]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 8 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.ld 64 7 (some 12) none 1 8]

theorem b20 (prof : Profile) : Blk prof p20 0 5 o20 :=
  .cons (p20_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `265`. -/
def p21 : List Byte := [
  0x48, 0x83, 0xeb, 0x08, 0x48, 0x83, 0xfb, 0xf8]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p21_4 : ∀ feat, Dec feat p21 4 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.sub 64 3 (.i 8),
  Op.cmp 64 3 (.i 18446744073709551608)]

theorem b21 (prof : Profile) : Blk prof p21 0 8 o21 :=
  .cons (p21_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p21_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j9 : List Byte := [0x75, 0xcd]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `280`. -/
def p22 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p22_1 : ∀ feat, Dec feat p22 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p22_2 : ∀ feat, Dec feat p22 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p22_4 : ∀ feat, Dec feat p22 4 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p22_6 : ∀ feat, Dec feat p22 6 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b22 (prof : Profile) : Blk prof p22 0 8 o22 :=
  .cons (p22_0 _) (OpI.pop) (by decide) <|
  .cons (p22_1 _) (OpI.pop) (by decide) <|
  .cons (p22_2 _) (OpI.pop) (by decide) <|
  .cons (p22_4 _) (OpI.pop) (by decide) <|
  .cons (p22_6 _) (OpI.pop) (by decide) <|
  .nil 8

def j10 : List Byte := [0xe9, 0x50, 0xff, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551440] 5) := by dec_rfl

end FV7z.Cpd
