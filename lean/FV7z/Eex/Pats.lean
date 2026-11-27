import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `NWildcard::CCensor::ExtendExclude` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Eex
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x53, 0x48, 0x83, 0xec,
  0x08, 0x8b, 0x7f, 0x08, 0x85, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.ld 32 7 (some 7) none 1 8,
  Op.test 32 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 22 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .nil 22

def j0 : List Byte := [0x74, 0x61]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 97] 2) := by dec_rfl

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x49, 0x8b, 0x0c, 0x24, 0x8d, 0x77, 0xff, 0x31, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 7) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 1 (some 12) none 1 0,
  Op.lea 32 6 (some 7) none 1 18446744073709551615,
  Op.xor 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0xeb, 0x14]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p2 : List Byte := [
  0x8d, 0x68, 0x01, 0x48, 0x8d, 0x50, 0x01, 0x48, 0x39, 0xf0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 5, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 5 (some 0) none 1 1,
  Op.lea 64 2 (some 0) none 1 1,
  Op.cmp 64 0 (.r 6)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x74, 0x54]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 84] 2) := by dec_rfl

/-- The stretch at `52`. -/
def p3 : List Byte := [
  0x48, 0x89, 0xd0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 0 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `55`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x14, 0xc1, 0x89, 0xc5, 0x8b, 0x52, 0x08, 0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 1) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 2) none 1 8 32)] 3) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 2 (some 1) (some 0) 8 0,
  Op.mov 32 5 (.r 0),
  Op.ld 32 2 (some 2) none 1 8,
  Op.test 32 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 11 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 11

def j3 : List Byte := [0x75, 0xe4]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551588] 2) := by dec_rfl

/-- The stretch at `68`. -/
def p5 : List Byte := [
  0x41, 0x89, 0xed, 0x31, 0xdb, 0x49, 0xc1, 0xe5, 0x03, 0x0f, 0x1f, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 5)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .shl 64 [gr 64 13, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 13 (.r 5),
  Op.xor 32 3 (.r 3),
  Op.shl64 13 (.i 3),
  Op.nop]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p5_9 _) (OpI.nop) (by decide) <|
  .nil 12

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x39, 0xeb]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 3 (.r 5)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.cmp (.r 5) (.inl rfl)) (by decide) <|
  .nil 2

def j4 : List Byte := [0x74, 0x1b]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `84`. -/
def p7 : List Byte := [
  0x49, 0x8b, 0x04, 0x24, 0x89, 0xda, 0x4a, 0x8b, 0x0c, 0x28, 0x48, 0x8b, 0x3c, 0xd0, 0x48, 0x8d,
  0x71, 0x10, 0x48, 0x83, 0xc7, 0x10]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 0) (some 13) 1 0 64)] 4) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) (some 2) 8 0 64)] 4) := by dec_rfl
theorem p7_14 : ∀ feat, Dec feat p7 14 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 1) none 1 16 0)] 4) := by dec_rfl
theorem p7_18 : ∀ feat, Dec feat p7 18 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 0 (some 12) none 1 0,
  Op.mov 32 2 (.r 3),
  Op.ld 64 1 (some 0) (some 13) 1 0,
  Op.ld 64 7 (some 0) (some 2) 8 0,
  Op.lea 64 6 (some 1) none 1 16,
  Op.add 64 7 (.i 16)]

theorem b7 (prof : Profile) : Blk prof p7 0 22 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_14 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_18 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .nil 22

/-- The stretch at `111`. -/
def p8 : List Byte := [
  0x83, 0xc3, 0x01, 0x41, 0x3b, 0x5c, 0x24, 0x08]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .cmp 32 [gr 32 3, .mem (mg (some 12) none 1 8 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 32 3 (.i 1),
  Op.cmpm 32 3 (some 12) none 1 8]

theorem b8 (prof : Profile) : Blk prof p8 0 8 o8 :=
  .cons (p8_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 8

def j5 : List Byte := [0x72, 0xd7]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551575] 2) := by dec_rfl

/-- The stretch at `121`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b9 (prof : Profile) : Blk prof p9 0 10 o9 :=
  .cons (p9_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.pop) (by decide) <|
  .cons (p9_5 _) (OpI.pop) (by decide) <|
  .cons (p9_6 _) (OpI.pop) (by decide) <|
  .cons (p9_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `136`. -/
def p10 : List Byte := [
  0x39, 0xfd]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmp 32 5 (.r 7)]

theorem b10 (prof : Profile) : Blk prof p10 0 2 o10 :=
  .cons (p10_0 _) (OpI.cmp (.r 7) (.inl rfl)) (by decide) <|
  .nil 2

def j6 : List Byte := [0x75, 0xb8]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551544] 2) := by dec_rfl

end FV7z.Eex
