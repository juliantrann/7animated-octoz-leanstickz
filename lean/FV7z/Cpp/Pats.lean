import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `Correct_PathPart` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 16 of them) and each distinct jump (`j*`, 13) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cpp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x8b, 0x17, 0x8b, 0x32, 0x83, 0xfe, 0x2e]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 2) none 1 0 32)] 2) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 46)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.ld 64 2 (some 7) none 1 0,
  Op.ld 32 6 (some 2) none 1 0,
  Op.cmp 32 6 (.i 46)]

theorem b0 (prof : Profile) : Blk prof p0 0 8 o0 :=
  .cons (p0_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.cmp (.i 46) (.inl rfl)) (by decide) <|
  .nil 8

def j0 : List Byte := [0x75, 0x1b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `10`. -/
def p1 : List Byte := [
  0x8b, 0x42, 0x04, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 2) none 1 4 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 0 (some 2) none 1 4,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x75, 0x0f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p2 : List Byte := [
  0xc7, 0x47, 0x08, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x02, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 0 32), .imm 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 32 (some 7) none 1 8 0,
  Op.sti 32 (some 2) none 1 0 0]

theorem b2 (prof : Profile) : Blk prof p2 0 13 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_7 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 13

/-- The stretch at `32`. -/
def p3 : List Byte := [
  0x83, 0xf8, 0x2e]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 46)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 0 (.i 46)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 46) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x6b]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 107] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p4 : List Byte := [
  0x8b, 0x47, 0x08, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 0 (some 7) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j3 : List Byte := [0x74, 0x39]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 57] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p5 : List Byte := [
  0x83, 0xe8, 0x01, 0x48, 0x89, 0xd1, 0x48, 0xc1, 0xe0, 0x02, 0x48, 0x8d, 0x7c, 0x02, 0x04]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 2)] 4) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 2) (some 0) 1 4 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sub 32 0 (.i 1),
  Op.mov 64 1 (.r 2),
  Op.shl64 0 (.i 2),
  Op.lea 64 7 (some 2) (some 0) 1 4]

theorem b5 (prof : Profile) : Blk prof p5 0 15 o5 :=
  .cons (p5_0 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.shl64 (.i 2)) (by decide) <|
  .cons (p5_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 15

def j4 : List Byte := [0xeb, 0x05]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `64`. -/
def p6 : List Byte := [
  0x8b, 0x31]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 1) none 1 0 32)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 32 6 (some 1) none 1 0]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `66`. -/
def p7 : List Byte := [
  0x83, 0xfe, 0x2f]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 47)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 32 6 (.i 47)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x75, 0x06]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `71`. -/
def p8 : List Byte := [
  0xc7, 0x01, 0x5f, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 0 32), .imm 32 95] 6) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.sti 32 (some 1) none 1 0 95]

theorem b8 (prof : Profile) : Blk prof p8 0 6 o8 :=
  .cons (p8_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 6

/-- The stretch at `77`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc1, 0x04, 0x48, 0x39, 0xf9]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 1 (.i 4),
  Op.cmp 64 1 (.r 7)]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.cmp (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x75, 0xea]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551594] 2) := by dec_rfl

/-- The stretch at `86`. -/
def p10 : List Byte := [
  0x48, 0xc7, 0xc1, 0xa0, 0xed, 0x79, 0x00, 0x48, 0x01, 0xd0, 0x80, 0x39, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7990688)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .cmp 8 [.mem (mg (some 1) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 1 (.i 7990688),
  Op.add 64 0 (.r 2),
  Op.cmpmi 8 (some 1) none 1 0 0]

theorem b10 (prof : Profile) : Blk prof p10 0 13 o10 :=
  .cons (p10_0 _) (OpI.mov (.i 7990688) (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p10_10 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 13

def j7 : List Byte := [0x75, 0x1d]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `112`. -/
def p11 : List Byte := [
  0xc7, 0x00, 0x5f, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x48, 0xfc, 0x48, 0x39, 0xc2]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 95] 6) := by dec_rfl
theorem p11_6 : ∀ feat, Dec feat p11 6 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 18446744073709551612 0)] 4) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.sti 32 (some 0) none 1 0 95,
  Op.lea 64 1 (some 0) none 1 18446744073709551612,
  Op.cmp 64 2 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 13 o11 :=
  .cons (p11_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p11_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_10 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 13

def j8 : List Byte := [0x74, 0xe6]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551590] 2) := by dec_rfl

/-- The stretch at `127`. -/
def p12 : List Byte := [
  0x48, 0x89, 0xc8]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 0 (.r 1)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `130`. -/
def p13 : List Byte := [
  0x8b, 0x08, 0x83, 0xf9, 0x2e]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 0) none 1 0 32)] 2) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 46)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 32 1 (some 0) none 1 0,
  Op.cmp 32 1 (.i 46)]

theorem b13 (prof : Profile) : Blk prof p13 0 5 o13 :=
  .cons (p13_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_2 _) (OpI.cmp (.i 46) (.inl rfl)) (by decide) <|
  .nil 5

def j9 : List Byte := [0x74, 0xe7]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551591] 2) := by dec_rfl

/-- The stretch at `137`. -/
def p14 : List Byte := [
  0x83, 0xf9, 0x20]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 32 1 (.i 32)]

theorem b14 (prof : Profile) : Blk prof p14 0 3 o14 :=
  .cons (p14_0 _) (OpI.cmp (.i 32) (.inl rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0x74, 0xe2]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551586] 2) := by dec_rfl

/-- The stretch at `144`. -/
def p15 : List Byte := [
  0x8b, 0x42, 0x08, 0x85, 0xc0]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 2) none 1 8 32)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 32 0 (some 2) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 5 o15 :=
  .cons (p15_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j11 : List Byte := [0x75, 0x8e]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551502] 2) := by dec_rfl

def j12 : List Byte := [0xe9, 0x75, 0xff, 0xff, 0xff]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk .jmp 64 [.rel 18446744073709551477] 5) := by dec_rfl

end FV7z.Cpp
