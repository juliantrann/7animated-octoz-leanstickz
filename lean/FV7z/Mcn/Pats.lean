import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `malloc_consolidate` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 22 of them) and each distinct jump (`j*`, 11) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mcn
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x57, 0x48, 0x8d, 0x47, 0x60, 0x49, 0x89, 0xff, 0x41, 0x56, 0x41, 0x55, 0x4c, 0x8d, 0x6f,
  0x10, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x18, 0xc7, 0x47, 0x08, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x89, 0x44, 0x24, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 96 0)] 4) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 7) none 1 16 0)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 15,
  Op.lea 64 0 (some 7) none 1 96,
  Op.mov 64 15 (.r 7),
  Op.push 14,
  Op.push 13,
  Op.lea 64 13 (some 7) none 1 16,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 24),
  Op.sti 32 (some 7) none 1 8 0,
  Op.st 64 (some 4) none 1 8 0]

theorem b0 (prof : Profile) : Blk prof p0 0 37 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.push) (by decide) <|
  .cons (p0_19 _) (OpI.push) (by decide) <|
  .cons (p0_20 _) (OpI.push) (by decide) <|
  .cons (p0_21 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_32 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 37

/-- The stretch at `37`. -/
def p1 : List Byte := [
  0x31, 0xdb]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 3 (.r 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `43`. -/
def p2 : List Byte := [
  0x48, 0x85, 0xdb]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 3 (.r 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j0 : List Byte := [0x75, 0x74]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 116] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0x49, 0x83, 0xc5, 0x08, 0x4c, 0x39, 0x6c, 0x24, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 13, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .cmp 64 [.mem (mg (some 4) none 1 8 64), gr 64 13] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 13 (.i 8),
  Op.cmpmr 64 (some 4) none 1 8 13]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x75, 0xea]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551594] 2) := by dec_rfl

/-- The stretch at `59`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b4 (prof : Profile) : Blk prof p4 0 14 o4 :=
  .cons (p4_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.pop) (by decide) <|
  .cons (p4_5 _) (OpI.pop) (by decide) <|
  .cons (p4_6 _) (OpI.pop) (by decide) <|
  .cons (p4_8 _) (OpI.pop) (by decide) <|
  .cons (p4_10 _) (OpI.pop) (by decide) <|
  .cons (p4_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `80`. -/
def p5 : List Byte := [
  0x43, 0xf6, 0x44, 0x34, 0x08, 0x01]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 8 [.mem (mg (some 12) (some 14) 1 8 8), .imm 8 1] 6) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.testmi 8 (some 12) (some 14) 1 8 1]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.testmi8) (by decide) <|
  .nil 6

def j2 : List Byte := [0x0f, 0x84, 0xc4, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 196] 6) := by dec_rfl

/-- The stretch at `98`. -/
def p6 : List Byte := [
  0x49, 0x8b, 0x47, 0x70, 0x49, 0x89, 0x5f, 0x70, 0x48, 0x89, 0x58, 0x18, 0x48, 0x81, 0xfd, 0xff,
  0x03, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 15) none 1 112 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 112 64), gr 64 3] 4) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 24 64), gr 64 3] 4) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.i 1023)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 0 (some 15) none 1 112,
  Op.st 64 (some 15) none 1 112 3,
  Op.st 64 (some 0) none 1 24 3,
  Op.cmp 64 5 (.i 1023)]

theorem b6 (prof : Profile) : Blk prof p6 0 19 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_8 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_12 _) (OpI.cmp (.i 1023) (.inr rfl)) (by decide) <|
  .nil 19

def j3 : List Byte := [0x76, 0x08]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `127`. -/
def p7 : List Byte := [
  0x48, 0x89, 0xee]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 6 (.r 5)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `135`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xce, 0x01]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.or 64 6 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.or (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `144`. -/
def p9 : List Byte := [
  0x48, 0x89, 0x73, 0x08]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 8 64), gr 64 6] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.st 64 (some 3) none 1 8 6]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 4

/-- The stretch at `152`. -/
def p10 : List Byte := [
  0x49, 0x89, 0x2c, 0x24]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 0 64), gr 64 5] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.st 64 (some 12) none 1 0 5]

theorem b10 (prof : Profile) : Blk prof p10 0 4 o10 :=
  .cons (p10_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 4

/-- The stretch at `156`. -/
def p11 : List Byte := [
  0x48, 0x85, 0xd2]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.test 64 2 (.r 2)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0x8f]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551503] 2) := by dec_rfl

/-- The stretch at `161`. -/
def p12 : List Byte := [
  0x48, 0x89, 0xd3]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 3 (.r 2)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `164`. -/
def p13 : List Byte := [
  0x48, 0x8b, 0x43, 0x08, 0x89, 0xc2, 0xc1, 0xea, 0x04, 0x83, 0xea, 0x02, 0x49, 0x8d, 0x54, 0xd7,
  0x10, 0x49, 0x39, 0xd5]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 8 64)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p13_6 : ∀ feat, Dec feat p13 6 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 4)] 3) := by dec_rfl
theorem p13_9 : ∀ feat, Dec feat p13 9 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 2)] 3) := by dec_rfl
theorem p13_12 : ∀ feat, Dec feat p13 12 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 15) (some 2) 8 16 0)] 5) := by dec_rfl
theorem p13_17 : ∀ feat, Dec feat p13 17 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 64 0 (some 3) none 1 8,
  Op.mov 32 2 (.r 0),
  Op.shr 2 (.i 4),
  Op.sub 32 2 (.i 2),
  Op.lea 64 2 (some 15) (some 2) 8 16,
  Op.cmp 64 13 (.r 2)]

theorem b13 (prof : Profile) : Blk prof p13 0 20 o13 :=
  .cons (p13_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p13_6 _) (OpI.shr (.i 4)) (by decide) <|
  .cons (p13_9 _) (OpI.sub (.i 2) (.inl rfl)) (by decide) <|
  .cons (p13_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_17 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 20

def j5 : List Byte := [0x0f, 0x85, 0x8e, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 142] 6) := by dec_rfl

/-- The stretch at `190`. -/
def p14 : List Byte := [
  0x48, 0x89, 0xc5, 0x48, 0x8b, 0x53, 0x10, 0x48, 0x83, 0xe5, 0xf8, 0x4c, 0x8d, 0x24, 0x2b, 0x4d,
  0x8b, 0x74, 0x24, 0x08, 0x49, 0x83, 0xe6, 0xf8, 0xa8, 0x01]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) none 1 16 64)] 4) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .and 64 [gr 64 5, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p14_11 : ∀ feat, Dec feat p14 11 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 3) (some 5) 1 0 0)] 4) := by dec_rfl
theorem p14_15 : ∀ feat, Dec feat p14 15 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 12) none 1 8 64)] 5) := by dec_rfl
theorem p14_20 : ∀ feat, Dec feat p14 20 (FV7z.mk .and 64 [gr 64 14, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p14_24 : ∀ feat, Dec feat p14 24 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 5 (.r 0),
  Op.ld 64 2 (some 3) none 1 16,
  Op.and 64 5 (.i 18446744073709551608),
  Op.lea 64 12 (some 3) (some 5) 1 0,
  Op.ld 64 14 (some 12) none 1 8,
  Op.and 64 14 (.i 18446744073709551608),
  Op.test 8 0 (.i 1)]

theorem b14 (prof : Profile) : Blk prof p14 0 26 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p14_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p14_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_20 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p14_24 _) (OpI.test8 (.i 1)) (by decide) <|
  .nil 26

def j6 : List Byte := [0x75, 0x26]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 38] 2) := by dec_rfl

/-- The stretch at `218`. -/
def p15 : List Byte := [
  0x48, 0x8b, 0x03, 0x48, 0x29, 0xc3, 0x48, 0x01, 0xc5, 0x48, 0x8b, 0x73, 0x08, 0x48, 0x83, 0xe6,
  0xf8, 0x48, 0x39, 0xc6]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p15_6 : ∀ feat, Dec feat p15 6 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p15_9 : ∀ feat, Dec feat p15 9 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) none 1 8 64)] 4) := by dec_rfl
theorem p15_13 : ∀ feat, Dec feat p15 13 (FV7z.mk .and 64 [gr 64 6, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p15_17 : ∀ feat, Dec feat p15 17 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 0 (some 3) none 1 0,
  Op.sub 64 3 (.r 0),
  Op.add 64 5 (.r 0),
  Op.ld 64 6 (some 3) none 1 8,
  Op.and 64 6 (.i 18446744073709551608),
  Op.cmp 64 6 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 20 o15 :=
  .cons (p15_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .cons (p15_6 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p15_9 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p15_13 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p15_17 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 20

def j7 : List Byte := [0x75, 0x50]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 80] 2) := by dec_rfl

/-- The stretch at `240`. -/
def p16 : List Byte := [
  0x48, 0x89, 0xdf, 0x48, 0x89, 0x14, 0x24]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 64 7 (.r 3),
  Op.st 64 (some 4) none 1 0 2]

theorem b16 (prof : Profile) : Blk prof p16 0 7 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `252`. -/
def p17 : List Byte := [
  0x48, 0x8b, 0x14, 0x24]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ld 64 2 (some 4) none 1 0]

theorem b17 (prof : Profile) : Blk prof p17 0 4 o17 :=
  .cons (p17_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `256`. -/
def p18 : List Byte := [
  0x4d, 0x39, 0x67, 0x60]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 64 [.mem (mg (some 15) none 1 96 64), gr 64 12] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmpmr 64 (some 15) none 1 96 12]

theorem b18 (prof : Profile) : Blk prof p18 0 4 o18 :=
  .cons (p18_0 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 4

def j8 : List Byte := [0x0f, 0x85, 0x46, 0xff, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551430] 6) := by dec_rfl

/-- The stretch at `266`. -/
def p19 : List Byte := [
  0x4c, 0x01, 0xf5, 0x48, 0x83, 0xcd, 0x01, 0x48, 0x89, 0x6b, 0x08, 0x49, 0x89, 0x5f, 0x60]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p19_3 : ∀ feat, Dec feat p19 3 (FV7z.mk .or 64 [gr 64 5, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 8 64), gr 64 5] 4) := by dec_rfl
theorem p19_11 : ∀ feat, Dec feat p19 11 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 96 64), gr 64 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.add 64 5 (.r 14),
  Op.or 64 5 (.i 1),
  Op.st 64 (some 3) none 1 8 5,
  Op.st 64 (some 15) none 1 96 3]

theorem b19 (prof : Profile) : Blk prof p19 0 15 o19 :=
  .cons (p19_0 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .cons (p19_3 _) (OpI.or (.i 1) (.inr rfl)) (by decide) <|
  .cons (p19_7 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p19_11 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 15

def j9 : List Byte := [0xeb, 0x81]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551489] 2) := by dec_rfl

/-- The stretch at `288`. -/
def p20 : List Byte := [
  0x4c, 0x89, 0xe7, 0x4c, 0x01, 0xf5, 0x48, 0x89, 0x14, 0x24]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p20_6 : ∀ feat, Dec feat p20 6 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 64 7 (.r 12),
  Op.add 64 5 (.r 14),
  Op.st 64 (some 4) none 1 0 2]

theorem b20 (prof : Profile) : Blk prof p20 0 10 o20 :=
  .cons (p20_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .cons (p20_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 10

/-- The stretch at `303`. -/
def p21 : List Byte := [
  0x4c, 0x8d, 0x24, 0x2b, 0x48, 0x8b, 0x14, 0x24]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 3) (some 5) 1 0 0)] 4) := by dec_rfl
theorem p21_4 : ∀ feat, Dec feat p21 4 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.lea 64 12 (some 3) (some 5) 1 0,
  Op.ld 64 2 (some 4) none 1 0]

theorem b21 (prof : Profile) : Blk prof p21 0 8 o21 :=
  .cons (p21_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p21_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 8

def j10 : List Byte := [0xe9, 0x26, 0xff, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551398] 5) := by dec_rfl

end FV7z.Mcn
