import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `Utf16_To_Utf8_Calc` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 21 of them) and each distinct jump (`j*`, 18) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.U8c
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x89, 0xf0, 0x48, 0x29, 0xf8, 0x48, 0xc1, 0xf8, 0x02, 0x48, 0x39, 0xfe]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .sar 64 [gr 64 0, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.mov 64 0 (.r 6),
  Op.sub 64 0 (.r 7),
  Op.sar64 0 (.i 2),
  Op.cmp 64 6 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 13 o0 :=
  .cons (p0_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.sub (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.sar64 (.i 2)) (by decide) <|
  .cons (p0_10 _) (OpI.cmp (.r 7) (.inr rfl)) (by decide) <|
  .nil 13

def j0 : List Byte := [0x74, 0x6b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 107] 2) := by dec_rfl

/-- The stretch at `15`. -/
def p1 : List Byte := [
  0x81, 0xe2, 0x00, 0x02, 0x00, 0x00, 0x0f, 0x1f, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 512)] 6) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.and 32 2 (.i 512),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.and (.i 512) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.nop) (by decide) <|
  .nil 9

/-- The stretch at `24`. -/
def p2 : List Byte := [
  0x8b, 0x0f, 0x4c, 0x8d, 0x47, 0x04, 0x83, 0xf9, 0x7f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 7) none 1 4 0)] 4) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 127)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 1 (some 7) none 1 0,
  Op.lea 64 8 (some 7) none 1 4,
  Op.cmp 32 1 (.i 127)]

theorem b2 (prof : Profile) : Blk prof p2 0 9 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x76, 0x5d]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 93] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p3 : List Byte := [
  0x81, 0xf9, 0xff, 0x07, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 2047)] 6) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 1 (.i 2047)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 2047) (.inl rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x0f, 0x86, 0x99, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 153] 6) := by dec_rfl

/-- The stretch at `47`. -/
def p4 : List Byte := [
  0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0x10]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `51`. -/
def p5 : List Byte := [
  0x41, 0x89, 0xc9, 0x41, 0x83, 0xe1, 0x80, 0x41, 0x81, 0xf9, 0x80, 0xef, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .and 32 [gr 32 9, Src.opd 32 (.i 4294967168)] 4) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 61312)] 7) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 9 (.r 1),
  Op.and 32 9 (.i 4294967168),
  Op.cmp 32 9 (.i 61312)]

theorem b5 (prof : Profile) : Blk prof p5 0 14 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.and (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.cmp (.i 61312) (.inl rfl)) (by decide) <|
  .nil 14

def j4 : List Byte := [0x74, 0x3d]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `67`. -/
def p6 : List Byte := [
  0x41, 0x89, 0xc9, 0x41, 0x81, 0xe1, 0x00, 0xf8, 0xff, 0xff, 0x41, 0x81, 0xf9, 0x00, 0xd8, 0x00,
  0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .and 32 [gr 32 9, Src.opd 32 (.i 4294965248)] 7) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 55296)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 9 (.r 1),
  Op.and 32 9 (.i 4294965248),
  Op.cmp 32 9 (.i 55296)]

theorem b6 (prof : Profile) : Blk prof p6 0 17 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.and (.i 4294965248) (.inl rfl)) (by decide) <|
  .cons (p6_10 _) (OpI.cmp (.i 55296) (.inl rfl)) (by decide) <|
  .nil 17

def j5 : List Byte := [0x74, 0x3a]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 58] 2) := by dec_rfl

/-- The stretch at `86`. -/
def p7 : List Byte := [
  0x81, 0xf9, 0xff, 0xff, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 65535)] 6) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 32 1 (.i 65535)]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.cmp (.i 65535) (.inl rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x76, 0x5a]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 6) 64 [.rel 90] 2) := by dec_rfl

/-- The stretch at `94`. -/
def p8 : List Byte := [
  0x81, 0xf9, 0xff, 0xff, 0x1f, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 2097151)] 6) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmp 32 1 (.i 2097151)]

theorem b8 (prof : Profile) : Blk prof p8 0 6 o8 :=
  .cons (p8_0 _) (OpI.cmp (.i 2097151) (.inl rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0x76, 0x7a]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 6) 64 [.rel 122] 2) := by dec_rfl

/-- The stretch at `102`. -/
def p9 : List Byte := [
  0x81, 0xf9, 0xff, 0xff, 0xff, 0x03]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 67108863)] 6) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmp 32 1 (.i 67108863)]

theorem b9 (prof : Profile) : Blk prof p9 0 6 o9 :=
  .cons (p9_0 _) (OpI.cmp (.i 67108863) (.inl rfl)) (by decide) <|
  .nil 6

def j8 : List Byte := [0x77, 0x6a]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 7) 64 [.rel 106] 2) := by dec_rfl

/-- The stretch at `110`. -/
def p10 : List Byte := [
  0x48, 0x83, 0xc0, 0x04, 0x4c, 0x89, 0xc7, 0x4c, 0x39, 0xc6]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.add 64 0 (.i 4),
  Op.mov 64 7 (.r 8),
  Op.cmp 64 6 (.r 8)]

theorem b10 (prof : Profile) : Blk prof p10 0 10 o10 :=
  .cons (p10_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.cmp (.r 8) (.inr rfl)) (by decide) <|
  .nil 10

def j9 : List Byte := [0x75, 0x9e]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551518] 2) := by dec_rfl

/-- The stretch at `128`. -/
def p11 : List Byte := [
  0x4c, 0x89, 0xc7]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 7 (.r 8)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `131`. -/
def p12 : List Byte := [
  0x4c, 0x39, 0xc6]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cmp 64 6 (.r 8)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.cmp (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0x75, 0x90]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551504] 2) := by dec_rfl

/-- The stretch at `144`. -/
def p13 : List Byte := [
  0x81, 0xf9, 0xff, 0xdb, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 56319)] 6) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmp 32 1 (.i 56319)]

theorem b13 (prof : Profile) : Blk prof p13 0 6 o13 :=
  .cons (p13_0 _) (OpI.cmp (.i 56319) (.inl rfl)) (by decide) <|
  .nil 6

def j11 : List Byte := [0x77, 0x20]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 7) 64 [.rel 32] 2) := by dec_rfl

def j12 : List Byte := [0x74, 0x1b]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `157`. -/
def p14 : List Byte := [
  0x8b, 0x4f, 0x04, 0x48, 0x83, 0xc7, 0x08, 0x81, 0xe9, 0x00, 0xdc, 0x00, 0x00, 0x81, 0xf9, 0x00,
  0x04, 0x00, 0x00, 0x4c, 0x0f, 0x42, 0xc7, 0x0f, 0x1f, 0x40, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 4 32)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 56320)] 6) := by dec_rfl
theorem p14_13 : ∀ feat, Dec feat p14 13 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 1024)] 6) := by dec_rfl
theorem p14_19 : ∀ feat, Dec feat p14 19 (FV7z.mk (.cmovcc 2) 64 [gr 64 8, gr 64 7] 4) := by dec_rfl
theorem p14_23 : ∀ feat, Dec feat p14 23 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 32 1 (some 7) none 1 4,
  Op.add 64 7 (.i 8),
  Op.sub 32 1 (.i 56320),
  Op.cmp 32 1 (.i 1024),
  Op.cmov64 2 8 7,
  Op.nop]

theorem b14 (prof : Profile) : Blk prof p14 0 27 o14 :=
  .cons (p14_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.sub (.i 56320) (.inl rfl)) (by decide) <|
  .cons (p14_13 _) (OpI.cmp (.i 1024) (.inl rfl)) (by decide) <|
  .cons (p14_19 _) (OpI.cmov64) (by decide) <|
  .cons (p14_23 _) (OpI.nop) (by decide) <|
  .nil 27

/-- The stretch at `184`. -/
def p15 : List Byte := [
  0x48, 0x83, 0xc0, 0x02, 0x4c, 0x89, 0xc7]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.add 64 0 (.i 2),
  Op.mov 64 7 (.r 8)]

theorem b15 (prof : Profile) : Blk prof p15 0 7 o15 :=
  .cons (p15_0 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 7

def j13 : List Byte := [0xeb, 0xc2]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk .jmp 64 [.rel 18446744073709551554] 2) := by dec_rfl

/-- The stretch at `200`. -/
def p16 : List Byte := [
  0x48, 0x83, 0xc0, 0x01, 0x4c, 0x89, 0xc7]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.add 64 0 (.i 1),
  Op.mov 64 7 (.r 8)]

theorem b16 (prof : Profile) : Blk prof p16 0 7 o16 :=
  .cons (p16_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p16_4 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 7

def j14 : List Byte := [0xeb, 0xb2]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk .jmp 64 [.rel 18446744073709551538] 2) := by dec_rfl

/-- The stretch at `216`. -/
def p17 : List Byte := [
  0x85, 0xc9]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.test 32 1 (.r 1)]

theorem b17 (prof : Profile) : Blk prof p17 0 2 o17 :=
  .cons (p17_0 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 2

def j15 : List Byte := [0x79, 0x14]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 9) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `220`. -/
def p18 : List Byte := [
  0x0f, 0x1f, 0x40, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.nop]

theorem b18 (prof : Profile) : Blk prof p18 0 4 o18 :=
  .cons (p18_0 _) (OpI.nop) (by decide) <|
  .nil 4

/-- The stretch at `224`. -/
def p19 : List Byte := [
  0x48, 0x83, 0xc0, 0x03, 0x4c, 0x89, 0xc7]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 3)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.add 64 0 (.i 3),
  Op.mov 64 7 (.r 8)]

theorem b19 (prof : Profile) : Blk prof p19 0 7 o19 :=
  .cons (p19_0 _) (OpI.add (.i 3) (.inr rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 7

def j16 : List Byte := [0xeb, 0x9a]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 18446744073709551514] 2) := by dec_rfl

/-- The stretch at `240`. -/
def p20 : List Byte := [
  0x48, 0x83, 0xc0, 0x05, 0x4c, 0x89, 0xc7]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 5)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.add 64 0 (.i 5),
  Op.mov 64 7 (.r 8)]

theorem b20 (prof : Profile) : Blk prof p20 0 7 o20 :=
  .cons (p20_0 _) (OpI.add (.i 5) (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 7

def j17 : List Byte := [0xeb, 0x8a]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551498] 2) := by dec_rfl

end FV7z.U8c
