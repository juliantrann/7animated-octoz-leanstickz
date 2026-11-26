import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps23
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `ConvertStringToUInt64` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Stu
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x07, 0x83, 0xe8, 0x30, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 0,
  Op.sub 32 0 (.i 48),
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 12 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.sub (.i 48) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 12

def j0 : List Byte := [0x74, 0x62]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 98] 2) := by dec_rfl

/-- The stretch at `14`. -/
def p1 : List Byte := [
  0x48, 0x89, 0x3e, 0x83, 0xf8, 0x09]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 0 64), gr 64 7] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.st 64 (some 6) none 1 0 7,
  Op.cmp 32 0 (.i 9)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_3 _) (OpI.cmp (.i 9) (.inl rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x77, 0x62]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 98] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p2 : List Byte := [
  0x49, 0xb8, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x99, 0x19, 0x31, 0xc9, 0x66, 0x0f, 0x1f, 0x44,
  0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.i 1844674407370955161)] 10) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 8 (.i 1844674407370955161),
  Op.xor 32 1 (.r 1),
  Op.nop]

theorem b2 (prof : Profile) : Blk prof p2 0 18 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 1844674407370955161) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.nop) (by decide) <|
  .nil 18

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc7, 0x04, 0x48, 0x01, 0xc8, 0x8b, 0x0f, 0x8d, 0x51, 0xd0, 0x83, 0xfa, 0x09]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 1) none 1 18446744073709551568 0)] 3) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 7 (.i 4),
  Op.add 64 0 (.r 1),
  Op.ld 32 1 (some 7) none 1 0,
  Op.lea 32 2 (some 1) none 1 18446744073709551568,
  Op.cmp 32 2 (.i 9)]

theorem b3 (prof : Profile) : Blk prof p3 0 15 o3 :=
  .cons (p3_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p3_12 _) (OpI.cmp (.i 9) (.inl rfl)) (by decide) <|
  .nil 15

def j2 : List Byte := [0x77, 0x27]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `57`. -/
def p4 : List Byte := [
  0x4c, 0x39, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 64 0 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.cmp (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x77, 0x15]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 7) 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `62`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x04, 0x80, 0x48, 0x8d, 0x0c, 0x00, 0x89, 0xd0, 0x48, 0x89, 0xc2, 0x48, 0xf7, 0xd2,
  0x48, 0x39, 0xca]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 0) 4 0 0)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) (some 0) 1 0 0)] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_13 : ∀ feat, Dec feat p5 13 (FV7z.mk .not 64 [gr 64 2] 3) := by dec_rfl
theorem p5_16 : ∀ feat, Dec feat p5 16 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 64 0 (some 0) (some 0) 4 0,
  Op.lea 64 1 (some 0) (some 0) 1 0,
  Op.mov 32 0 (.r 2),
  Op.mov 64 2 (.r 0),
  Op.not64 2,
  Op.cmp 64 2 (.r 1)]

theorem b5 (prof : Profile) : Blk prof p5 0 19 o5 :=
  .cons (p5_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_10 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_13 _) (OpI.not64) (by decide) <|
  .cons (p5_16 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 19

def j4 : List Byte := [0x73, 0xd5]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551573] 2) := by dec_rfl

/-- The stretch at `83`. -/
def p6 : List Byte := [
  0x31, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x48, 0x85, 0xf6]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 64 6 (.r 6)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x74, 0x12]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `101`. -/
def p8 : List Byte := [
  0x48, 0x89, 0x3e]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 0 64), gr 64 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 64 (some 6) none 1 0 7]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 3

/-- The stretch at `112`. -/
def p9 : List Byte := [
  0x83, 0xf8, 0x09]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmp 32 0 (.i 9)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.cmp (.i 9) (.inl rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0x76, 0xa1]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551521] 2) := by dec_rfl

def j7 : List Byte := [0xeb, 0xdc]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551580] 2) := by dec_rfl

def j8 : List Byte := [0xeb, 0xe9]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551593] 2) := by dec_rfl

end FV7z.Stu
