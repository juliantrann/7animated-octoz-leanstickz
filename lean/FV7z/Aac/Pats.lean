import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::operator= (const char *)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Aac
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x49, 0x89, 0xfd, 0x41, 0x54, 0x55, 0x48, 0x89, 0xf5, 0x53,
  0x31, 0xdb, 0x48, 0x83, 0xec, 0x08, 0x80, 0x3e, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 64 13 (.r 7),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.xor 32 3 (.r 3),
  Op.sub 64 4 (.i 8),
  Op.cmpmi 8 (some 6) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 25 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 25

def j0 : List Byte := [0x74, 0x18]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.nop) (by decide) <|
  .nil 5

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x8d, 0x7b, 0x01, 0x80, 0x7c, 0x3d, 0x00, 0x00, 0x48, 0x89, 0xfb]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 3) none 1 1 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .cmp 8 [.mem (mg (some 5) (some 7) 1 0 8), .imm 8 0] 5) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 7 (some 3) none 1 1,
  Op.cmpmi 8 (some 5) (some 7) 1 0 0,
  Op.mov 64 3 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x75, 0xf3]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551603] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x41, 0x39, 0x7d, 0x0c]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [.mem (mg (some 13) none 1 12 32), gr 32 7] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpmr 32 (some 13) none 1 12 7]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x72, 0x2d]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 2) 64 [.rel 45] 2) := by dec_rfl

/-- The stretch at `51`. -/
def p4 : List Byte := [
  0x4d, 0x8b, 0x65, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 13) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 12 (some 13) none 1 0]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `55`. -/
def p5 : List Byte := [
  0x41, 0x89, 0x5d, 0x08, 0x31, 0xd2, 0x0f, 0x1f, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [.mem (mg (some 13) none 1 8 32), gr 32 3] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 32 (some 13) none 1 8 3,
  Op.xor 32 2 (.r 2),
  Op.nop]

theorem b5 (prof : Profile) : Blk prof p5 0 9 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_4 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.nop) (by decide) <|
  .nil 9

/-- The stretch at `64`. -/
def p6 : List Byte := [
  0x0f, 0xb6, 0x4c, 0x15, 0x00, 0x41, 0x88, 0x0c, 0x14, 0x48, 0x83, 0xc2, 0x01, 0x84, 0xc9]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 5) (some 2) 1 0 8)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .mov 8 [.mem (mg (some 12) (some 2) 1 0 8), gr 8 1] 4) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p6_13 : ∀ feat, Dec feat p6 13 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ldzx 8 1 (some 5) (some 2) 1 0,
  Op.st 8 (some 12) (some 2) 1 0 1,
  Op.add 64 2 (.i 1),
  Op.test 8 1 (.r 1)]

theorem b6 (prof : Profile) : Blk prof p6 0 15 o6 :=
  .cons (p6_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p6_9 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p6_13 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 15

def j3 : List Byte := [0x75, 0xef]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551599] 2) := by dec_rfl

/-- The stretch at `81`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe8, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 13),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b7 (prof : Profile) : Blk prof p7 0 13 o7 :=
  .cons (p7_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.pop) (by decide) <|
  .cons (p7_8 _) (OpI.pop) (by decide) <|
  .cons (p7_9 _) (OpI.pop) (by decide) <|
  .cons (p7_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `96`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xc7, 0x01]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 7 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `105`. -/
def p9 : List Byte := [
  0x49, 0x8b, 0x7d, 0x00, 0x49, 0x89, 0xc4, 0x48, 0x85, 0xff]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 13) none 1 0 64)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 7 (some 13) none 1 0,
  Op.mov 64 12 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b9 (prof : Profile) : Blk prof p9 0 10 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j4 : List Byte := [0x74, 0x05]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `122`. -/
def p10 : List Byte := [
  0x4d, 0x89, 0x65, 0x00, 0x41, 0x89, 0x5d, 0x0c]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [.mem (mg (some 13) none 1 0 64), gr 64 12] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 32 [.mem (mg (some 13) none 1 12 32), gr 32 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.st 64 (some 13) none 1 0 12,
  Op.st 32 (some 13) none 1 12 3]

theorem b10 (prof : Profile) : Blk prof p10 0 8 o10 :=
  .cons (p10_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 8

def j5 : List Byte := [0xeb, 0xb3]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551539] 2) := by dec_rfl

end FV7z.Aac
