import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CompareFileNames` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 31 of them) and each distinct jump (`j*`, 33) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cfn
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x48, 0x89, 0xfb,
  0x48, 0x83, 0xec, 0x08, 0x48, 0xc7, 0xc0, 0x80, 0x21, 0x79, 0x00, 0x80, 0x38, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7938432)] 7) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8),
  Op.mov 64 0 (.i 7938432),
  Op.cmpmi 8 (some 0) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 30 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.mov (.i 7938432) (.inr rfl)) (by decide) <|
  .cons (p0_27 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 30

def j0 : List Byte := [0x74, 0x5d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 93] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p1 : List Byte := [
  0x31, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `34`. -/
def p2 : List Byte := [
  0x44, 0x8b, 0x23, 0x8b, 0x45, 0x00, 0x48, 0x83, 0xc3, 0x04, 0x48, 0x83, 0xc5, 0x04, 0x41, 0x39,
  0xc4]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 3) none 1 0 32)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 0 32)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 12 (some 3) none 1 0,
  Op.ld 32 0 (some 5) none 1 0,
  Op.add 64 3 (.i 4),
  Op.add 64 5 (.i 4),
  Op.cmp 32 12 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 17 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 17

def j1 : List Byte := [0x0f, 0x84, 0xcf, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 207] 6) := by dec_rfl

/-- The stretch at `57`. -/
def p3 : List Byte := [
  0x45, 0x85, 0xe4]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 32 12 (.r 12)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x0f, 0x84, 0x4e, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 334] 6) := by dec_rfl

/-- The stretch at `66`. -/
def p4 : List Byte := [
  0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0x1b]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `70`. -/
def p5 : List Byte := [
  0x41, 0x83, 0xfc, 0x2f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 47)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 32 12 (.i 47)]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x0f, 0x84, 0xe0, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 224] 6) := by dec_rfl

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x83, 0xf8, 0x2f, 0x0f, 0x44, 0xc2]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 47)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk (.cmovcc 4) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 0 (.i 47),
  Op.cmov32 4 0 2]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.cmov32) (by decide) <|
  .nil 6

/-- The stretch at `86`. -/
def p7 : List Byte := [
  0x44, 0x39, 0xe0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 32 0 (.r 12)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.cmp (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x0f, 0x8f, 0x31, 0x01, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 15) 64 [.rel 305] 6) := by dec_rfl

def j6 : List Byte := [0x7d, 0xc1]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 13) 64 [.rel 18446744073709551553] 2) := by dec_rfl

/-- The stretch at `97`. -/
def p8 : List Byte := [
  0x41, 0xbc, 0x01, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 1)] 6) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 12 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 6 o8 :=
  .cons (p8_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `103`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_9 : ∀ feat, Dec feat p9 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b9 (prof : Profile) : Blk prof p9 0 13 o9 :=
  .cons (p9_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.pop) (by decide) <|
  .cons (p9_8 _) (OpI.pop) (by decide) <|
  .cons (p9_9 _) (OpI.pop) (by decide) <|
  .cons (p9_11 _) (OpI.pop) (by decide) <|
  .nil 13

def j7 : List Byte := [0x74, 0xea]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551594] 2) := by dec_rfl

/-- The stretch at `125`. -/
def p10 : List Byte := [
  0x44, 0x8b, 0x23, 0x44, 0x8b, 0x6d, 0x00, 0x48, 0x83, 0xc3, 0x04, 0x48, 0x83, 0xc5, 0x04, 0x45,
  0x39, 0xec]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 3) none 1 0 32)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 5) none 1 0 32)] 4) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p10_15 : ∀ feat, Dec feat p10 15 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 32 12 (some 3) none 1 0,
  Op.ld 32 13 (some 5) none 1 0,
  Op.add 64 3 (.i 4),
  Op.add 64 5 (.i 4),
  Op.cmp 32 12 (.r 13)]

theorem b10 (prof : Profile) : Blk prof p10 0 18 o10 :=
  .cons (p10_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p10_11 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p10_15 _) (OpI.cmp (.r 13) (.inl rfl)) (by decide) <|
  .nil 18

def j8 : List Byte := [0x74, 0xe7]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551591] 2) := by dec_rfl

def j9 : List Byte := [0x0f, 0x84, 0xf6, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 246] 6) := by dec_rfl

/-- The stretch at `154`. -/
def p11 : List Byte := [
  0x45, 0x85, 0xed]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .test 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.test 32 13 (.r 13)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.test (.r 13) (.inl rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0x74, 0xc2]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551554] 2) := by dec_rfl

def j11 : List Byte := [0x74, 0x7b]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 123] 2) := by dec_rfl

/-- The stretch at `165`. -/
def p12 : List Byte := [
  0x41, 0x83, 0xfd, 0x2f]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.i 47)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cmp 32 13 (.i 47)]

theorem b12 (prof : Profile) : Blk prof p12 0 4 o12 :=
  .cons (p12_0 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .nil 4

def j12 : List Byte := [0x0f, 0x84, 0x99, 0x00, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 153] 6) := by dec_rfl

/-- The stretch at `175`. -/
def p13 : List Byte := [
  0x41, 0x83, 0xfc, 0x60]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 96)] 4) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmp 32 12 (.i 96)]

theorem b13 (prof : Profile) : Blk prof p13 0 4 o13 :=
  .cons (p13_0 _) (OpI.cmp (.i 96) (.inl rfl)) (by decide) <|
  .nil 4

def j13 : List Byte := [0x7e, 0x1b]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 14) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `181`. -/
def p14 : List Byte := [
  0x41, 0x83, 0xfc, 0x7a]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 122)] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 32 12 (.i 122)]

theorem b14 (prof : Profile) : Blk prof p14 0 4 o14 :=
  .cons (p14_0 _) (OpI.cmp (.i 122) (.inl rfl)) (by decide) <|
  .nil 4

def j14 : List Byte := [0x0f, 0x8e, 0xc1, 0x00, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 14) 64 [.rel 193] 6) := by dec_rfl

/-- The stretch at `191`. -/
def p15 : List Byte := [
  0x41, 0x83, 0xfc, 0x7f]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 127)] 4) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.cmp 32 12 (.i 127)]

theorem b15 (prof : Profile) : Blk prof p15 0 4 o15 :=
  .cons (p15_0 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 4

def j15 : List Byte := [0x7e, 0x0b]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 14) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `197`. -/
def p16 : List Byte := [
  0x44, 0x89, 0xe7]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 32 7 (.r 12)]

theorem b16 (prof : Profile) : Blk prof p16 0 3 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `205`. -/
def p17 : List Byte := [
  0x41, 0x89, 0xc4]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 32 12 (.r 0)]

theorem b17 (prof : Profile) : Blk prof p17 0 3 o17 :=
  .cons (p17_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `208`. -/
def p18 : List Byte := [
  0x41, 0x83, 0xfd, 0x60]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.i 96)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmp 32 13 (.i 96)]

theorem b18 (prof : Profile) : Blk prof p18 0 4 o18 :=
  .cons (p18_0 _) (OpI.cmp (.i 96) (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `214`. -/
def p19 : List Byte := [
  0x41, 0x83, 0xfd, 0x7a]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.i 122)] 4) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmp 32 13 (.i 122)]

theorem b19 (prof : Profile) : Blk prof p19 0 4 o19 :=
  .cons (p19_0 _) (OpI.cmp (.i 122) (.inl rfl)) (by decide) <|
  .nil 4

def j16 : List Byte := [0x0f, 0x8e, 0x90, 0x00, 0x00, 0x00]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 14) 64 [.rel 144] 6) := by dec_rfl

/-- The stretch at `224`. -/
def p20 : List Byte := [
  0x41, 0x83, 0xfd, 0x7f]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.i 127)] 4) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.cmp 32 13 (.i 127)]

theorem b20 (prof : Profile) : Blk prof p20 0 4 o20 :=
  .cons (p20_0 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `230`. -/
def p21 : List Byte := [
  0x44, 0x89, 0xef]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.mov 32 7 (.r 13)]

theorem b21 (prof : Profile) : Blk prof p21 0 3 o21 :=
  .cons (p21_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `238`. -/
def p22 : List Byte := [
  0x41, 0x89, 0xc5]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.mov 32 13 (.r 0)]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `241`. -/
def p23 : List Byte := [
  0x45, 0x39, 0xe5]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.cmp 32 13 (.r 12)]

theorem b23 (prof : Profile) : Blk prof p23 0 3 o23 :=
  .cons (p23_0 _) (OpI.cmp (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

def j17 : List Byte := [0x0f, 0x8f, 0x96, 0x00, 0x00, 0x00]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 15) 64 [.rel 150] 6) := by dec_rfl

def j18 : List Byte := [0x0f, 0x8c, 0x61, 0xff, 0xff, 0xff]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 12) 64 [.rel 18446744073709551457] 6) := by dec_rfl

def j19 : List Byte := [0xe9, 0x78, 0xff, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551480] 5) := by dec_rfl

def j20 : List Byte := [0x0f, 0x85, 0x11, 0xff, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551377] 6) := by dec_rfl

def j21 : List Byte := [0xe9, 0x51, 0xff, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk .jmp 64 [.rel 18446744073709551441] 5) := by dec_rfl

/-- The stretch at `288`. -/
def p24 : List Byte := [
  0x45, 0x31, 0xe4, 0x41, 0x83, 0xfd, 0x2f]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p24_3 : ∀ feat, Dec feat p24 3 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.i 47)] 4) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.xor 32 12 (.r 12),
  Op.cmp 32 13 (.i 47)]

theorem b24 (prof : Profile) : Blk prof p24 0 7 o24 :=
  .cons (p24_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p24_3 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .nil 7

def j22 : List Byte := [0x75, 0xa7]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551527] 2) := by dec_rfl

def j23 : List Byte := [0xe9, 0x4f, 0xff, 0xff, 0xff]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk .jmp 64 [.rel 18446744073709551439] 5) := by dec_rfl

/-- The stretch at `304`. -/
def p25 : List Byte := [
  0x45, 0x31, 0xe4, 0x83, 0xf8, 0x2f]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p25_3 : ∀ feat, Dec feat p25 3 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 47)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.xor 32 12 (.r 12),
  Op.cmp 32 0 (.i 47)]

theorem b25 (prof : Profile) : Blk prof p25 0 6 o25 :=
  .cons (p25_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p25_3 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .nil 6

def j24 : List Byte := [0x0f, 0x85, 0x1a, 0xff, 0xff, 0xff]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551386] 6) := by dec_rfl

def j25 : List Byte := [0xe9, 0xe1, 0xfe, 0xff, 0xff]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk .jmp 64 [.rel 18446744073709551329] 5) := by dec_rfl

def j26 : List Byte := [0x7e, 0x52]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 14) 64 [.rel 82] 2) := by dec_rfl

def j27 : List Byte := [0x0f, 0x8e, 0x09, 0xff, 0xff, 0xff]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 14) 64 [.rel 18446744073709551369] 6) := by dec_rfl

/-- The stretch at `344`. -/
def p26 : List Byte := [
  0x45, 0x31, 0xed, 0x41, 0x83, 0xfc, 0x7f]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p26_3 : ∀ feat, Dec feat p26 3 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 127)] 4) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.xor 32 13 (.r 13),
  Op.cmp 32 12 (.i 127)]

theorem b26 (prof : Profile) : Blk prof p26 0 7 o26 :=
  .cons (p26_0 _) (OpI.xor (.r 13) (.inl rfl)) (by decide) <|
  .cons (p26_3 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 7

def j28 : List Byte := [0x7e, 0x90]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 14) 64 [.rel 18446744073709551504] 2) := by dec_rfl

def j29 : List Byte := [0xeb, 0x83]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk .jmp 64 [.rel 18446744073709551491] 2) := by dec_rfl

/-- The stretch at `368`. -/
def p27 : List Byte := [
  0x41, 0x83, 0xed, 0x20]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .sub 32 [gr 32 13, Src.opd 32 (.i 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.sub 32 13 (.i 32)]

theorem b27 (prof : Profile) : Blk prof p27 0 4 o27 :=
  .cons (p27_0 _) (OpI.sub (.i 32) (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `384`. -/
def p28 : List Byte := [
  0x41, 0x83, 0xec, 0x20]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .sub 32 [gr 32 12, Src.opd 32 (.i 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.sub 32 12 (.i 32)]

theorem b28 (prof : Profile) : Blk prof p28 0 4 o28 :=
  .cons (p28_0 _) (OpI.sub (.i 32) (.inl rfl)) (by decide) <|
  .nil 4

def j30 : List Byte := [0xe9, 0x47, 0xff, 0xff, 0xff]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk .jmp 64 [.rel 18446744073709551431] 5) := by dec_rfl

/-- The stretch at `400`. -/
def p29 : List Byte := [
  0x41, 0xbc, 0xff, 0xff, 0xff, 0xff]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 4294967295)] 6) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.mov 32 12 (.i 4294967295)]

theorem b29 (prof : Profile) : Blk prof p29 0 6 o29 :=
  .cons (p29_0 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 6

def j31 : List Byte := [0xe9, 0xcc, 0xfe, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk .jmp 64 [.rel 18446744073709551308] 5) := by dec_rfl

/-- The stretch at `416`. -/
def p30 : List Byte := [
  0x45, 0x31, 0xed]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.xor 32 13 (.r 13)]

theorem b30 (prof : Profile) : Blk prof p30 0 3 o30 :=
  .cons (p30_0 _) (OpI.xor (.r 13) (.inl rfl)) (by decide) <|
  .nil 3

def j32 : List Byte := [0xe9, 0x49, 0xff, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk .jmp 64 [.rel 18446744073709551433] 5) := by dec_rfl

end FV7z.Cfn
