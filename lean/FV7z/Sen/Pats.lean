import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `StringsAreEqualNoCase` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 18 of them) and each distinct jump (`j*`, 13) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sen
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x49, 0x89, 0xfd, 0x41, 0x54, 0x49, 0x89, 0xf4,
  0x55, 0x53]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.mov 64 13 (.r 7),
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.push 5,
  Op.push 3]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.push) (by decide) <|
  .cons (p0_17 _) (OpI.push) (by decide) <|
  .nil 18

def j0 : List Byte := [0xeb, 0x2a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk .jmp 64 [.rel 42] 2) := by dec_rfl

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x44, 0x8d, 0x73, 0xe0, 0x83, 0xfb, 0x7a]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 14, .mem (mg (some 3) none 1 18446744073709551584 0)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.i 122)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 14 (some 3) none 1 18446744073709551584,
  Op.cmp 32 3 (.i 122)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.cmp (.i 122) (.inl rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x7e, 0x0f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 14) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p2 : List Byte := [
  0x83, 0xfb, 0x7f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.i 127)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 32 3 (.i 127)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x7e, 0x31]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 14) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `38`. -/
def p3 : List Byte := [
  0x89, 0xdf]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 7 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `45`. -/
def p4 : List Byte := [
  0x41, 0x89, 0xc6]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 14 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `48`. -/
def p5 : List Byte := [
  0x83, 0xfd, 0x60]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 96)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 32 5 (.i 96)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.cmp (.i 96) (.inl rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x7f, 0x2a]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 15) 64 [.rel 42] 2) := by dec_rfl

/-- The stretch at `53`. -/
def p6 : List Byte := [
  0x44, 0x39, 0xf5]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 5 (.r 14)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.cmp (.r 14) (.inl rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x75, 0x56]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 86] 2) := by dec_rfl

/-- The stretch at `58`. -/
def p7 : List Byte := [
  0x85, 0xdb]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 32 3 (.r 3)]

theorem b7 (prof : Profile) : Blk prof p7 0 2 o7 :=
  .cons (p7_0 _) (OpI.test (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

def j5 : List Byte := [0x74, 0x42]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `62`. -/
def p8 : List Byte := [
  0x41, 0x8b, 0x5d, 0x00, 0x41, 0x8b, 0x2c, 0x24, 0x49, 0x83, 0xc5, 0x04, 0x49, 0x83, 0xc4, 0x04,
  0x39, 0xeb]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 3, .mem (mg (some 13) none 1 0 32)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 32 [gr 32 5, .mem (mg (some 12) none 1 0 32)] 4) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .add 64 [gr 64 13, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .add 64 [gr 64 12, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p8_16 : ∀ feat, Dec feat p8 16 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 3 (some 13) none 1 0,
  Op.ld 32 5 (some 12) none 1 0,
  Op.add 64 13 (.i 4),
  Op.add 64 12 (.i 4),
  Op.cmp 32 3 (.r 5)]

theorem b8 (prof : Profile) : Blk prof p8 0 18 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_8 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p8_12 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p8_16 _) (OpI.cmp (.r 5) (.inl rfl)) (by decide) <|
  .nil 18

def j6 : List Byte := [0x74, 0xe8]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551592] 2) := by dec_rfl

/-- The stretch at `82`. -/
def p9 : List Byte := [
  0x83, 0xfb, 0x60]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.i 96)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmp 32 3 (.i 96)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.cmp (.i 96) (.inl rfl)) (by decide) <|
  .nil 3

def j7 : List Byte := [0x7f, 0xc1]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 15) 64 [.rel 18446744073709551553] 2) := by dec_rfl

def j8 : List Byte := [0x7e, 0x34]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 14) 64 [.rel 52] 2) := by dec_rfl

/-- The stretch at `92`. -/
def p10 : List Byte := [
  0x41, 0x89, 0xde]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 14 (.r 3)]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `95`. -/
def p11 : List Byte := [
  0x83, 0xfd, 0x7a]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 122)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.cmp 32 5 (.i 122)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.cmp (.i 122) (.inl rfl)) (by decide) <|
  .nil 3

def j9 : List Byte := [0x7e, 0x14]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 14) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `100`. -/
def p12 : List Byte := [
  0x83, 0xfd, 0x7f]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 127)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cmp 32 5 (.i 127)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0x7e, 0xcc]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 14) 64 [.rel 18446744073709551564] 2) := by dec_rfl

/-- The stretch at `105`. -/
def p13 : List Byte := [
  0x89, 0xef]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 32 7 (.r 5)]

theorem b13 (prof : Profile) : Blk prof p13 0 2 o13 :=
  .cons (p13_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `112`. -/
def p14 : List Byte := [
  0x89, 0xc5]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 32 5 (.r 0)]

theorem b14 (prof : Profile) : Blk prof p14 0 2 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j11 : List Byte := [0xeb, 0xc1]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551553] 2) := by dec_rfl

/-- The stretch at `120`. -/
def p15 : List Byte := [
  0x83, 0xed, 0x20]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.i 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.sub 32 5 (.i 32)]

theorem b15 (prof : Profile) : Blk prof p15 0 3 o15 :=
  .cons (p15_0 _) (OpI.sub (.i 32) (.inl rfl)) (by decide) <|
  .nil 3

def j12 : List Byte := [0xeb, 0xb8]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk .jmp 64 [.rel 18446744073709551544] 2) := by dec_rfl

/-- The stretch at `128`. -/
def p16 : List Byte := [
  0x5b, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p16_1 : ∀ feat, Dec feat p16 1 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p16_6 : ∀ feat, Dec feat p16 6 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p16_7 : ∀ feat, Dec feat p16 7 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p16_9 : ∀ feat, Dec feat p16 9 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p16_11 : ∀ feat, Dec feat p16 11 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.pop 3,
  Op.mov 32 0 (.i 1),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b16 (prof : Profile) : Blk prof p16 0 13 o16 :=
  .cons (p16_0 _) (OpI.pop) (by decide) <|
  .cons (p16_1 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p16_6 _) (OpI.pop) (by decide) <|
  .cons (p16_7 _) (OpI.pop) (by decide) <|
  .cons (p16_9 _) (OpI.pop) (by decide) <|
  .cons (p16_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `144`. -/
def p17 : List Byte := [
  0x5b, 0x31, 0xc0, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p17_1 : ∀ feat, Dec feat p17 1 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p17_6 : ∀ feat, Dec feat p17 6 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p17_8 : ∀ feat, Dec feat p17 8 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.pop 3,
  Op.xor 32 0 (.r 0),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b17 (prof : Profile) : Blk prof p17 0 10 o17 :=
  .cons (p17_0 _) (OpI.pop) (by decide) <|
  .cons (p17_1 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.pop) (by decide) <|
  .cons (p17_4 _) (OpI.pop) (by decide) <|
  .cons (p17_6 _) (OpI.pop) (by decide) <|
  .cons (p17_8 _) (OpI.pop) (by decide) <|
  .nil 10

end FV7z.Sen
