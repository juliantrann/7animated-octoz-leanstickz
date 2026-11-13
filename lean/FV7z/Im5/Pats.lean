import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps13
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps9
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `_int_malloc` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 19 of them) and each distinct jump (`j*`, 16) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Im5
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 3 o0 :=
  .cons (p0_0 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

def j0 : List Byte := [0x0f, 0x88, 0x07, 0x06, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 8) 64 [.rel 1543] 6) := by dec_rfl

/-- The stretch at `9`. -/
def p1 : List Byte := [
  0x41, 0x57, 0x48, 0x8d, 0x46, 0x17, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x48, 0x89, 0xf5,
  0x53, 0x48, 0x89, 0xfb, 0x48, 0x81, 0xec, 0x88, 0x00, 0x00, 0x00, 0x48, 0x83, 0xf8, 0x1f]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 6) none 1 23 0)] 4) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 136)] 7) := by dec_rfl
theorem p1_27 : ∀ feat, Dec feat p1 27 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 31)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 15,
  Op.lea 64 0 (some 6) none 1 23,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 136),
  Op.cmp 64 0 (.i 31)]

theorem b1 (prof : Profile) : Blk prof p1 0 31 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.push) (by decide) <|
  .cons (p1_8 _) (OpI.push) (by decide) <|
  .cons (p1_10 _) (OpI.push) (by decide) <|
  .cons (p1_12 _) (OpI.push) (by decide) <|
  .cons (p1_13 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_16 _) (OpI.push) (by decide) <|
  .cons (p1_17 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_20 _) (OpI.sub (.i 136) (.inr rfl)) (by decide) <|
  .cons (p1_27 _) (OpI.cmp (.i 31) (.inr rfl)) (by decide) <|
  .nil 31

def j1 : List Byte := [0x0f, 0x87, 0x02, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 258] 6) := by dec_rfl

/-- The stretch at `304`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xe0, 0xf0, 0x49, 0x89, 0xc5, 0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551600)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.and 64 0 (.i 18446744073709551600),
  Op.mov 64 13 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.and (.i 18446744073709551600) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x0f, 0x84, 0xfe, 0x04, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 1278] 6) := by dec_rfl

/-- The stretch at `320`. -/
def p3 : List Byte := [
  0x41, 0x89, 0xc6, 0x41, 0xc1, 0xee, 0x04, 0x48, 0x3b, 0x05, 0x7a, 0x38, 0x17, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .shr 32 [gr 32 14, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .cmp 64 [gr 64 0, .mem (mrip 1521786 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 14 (.r 0),
  Op.shr 14 (.i 4),
  Op.cmpma 64 0 8013224]

theorem b3 (prof : Profile) : BlkA prof p3 (0x630d20 : Addr) 0 14 o3 :=
  .cons (p3_0 _) ((OpI.mov (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p3_3 _) ((OpI.shr (.i 4)).at _) (by decide) <|
  .cons (p3_7 _) (OpIA.cmpm_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 14

def j3 : List Byte := [0x0f, 0x86, 0x6c, 0x02, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 620] 6) := by dec_rfl

/-- The stretch at `340`. -/
def p4 : List Byte := [
  0x48, 0x3d, 0xff, 0x03, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 1023)] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 64 0 (.i 1023)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.cmp (.i 1023) (.inr rfl)) (by decide) <|
  .nil 6

def j4 : List Byte := [0x0f, 0x86, 0xf0, 0x01, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 6) 64 [.rel 496] 6) := by dec_rfl

/-- The stretch at `352`. -/
def p5 : List Byte := [
  0x48, 0x89, 0xc1, 0x48, 0x89, 0xc7, 0x48, 0x89, 0xc6, 0x49, 0x89, 0xc7, 0x48, 0xc1, 0xee, 0x0c,
  0x49, 0xc1, 0xef, 0x0f, 0xba, 0x02, 0x00, 0x00, 0x00, 0x48, 0xc1, 0xe9, 0x06, 0x48, 0xc1, 0xef,
  0x09, 0x45, 0x8d, 0x57, 0x77, 0x48, 0x89, 0x74, 0x24, 0x58, 0x48, 0xc1, 0xe8, 0x12, 0x49, 0x81,
  0xfd, 0xff, 0xff, 0x0b, 0x00, 0x4c, 0x89, 0x7c, 0x24, 0x60, 0x44, 0x8d, 0x59, 0x30, 0x48, 0x0f,
  0x47, 0xc2, 0x4c, 0x89, 0xfa, 0x44, 0x8d, 0x7e, 0x6e, 0x48, 0x89, 0x4c, 0x24, 0x40, 0x48, 0x89,
  0x7c, 0x24, 0x50, 0x44, 0x8d, 0x48, 0x7c, 0x48, 0x89, 0xf0, 0x89, 0xfe, 0x44, 0x89, 0x5c, 0x24,
  0x4c, 0x83, 0xc6, 0x5b, 0x44, 0x89, 0x4c, 0x24, 0x68, 0x44, 0x89, 0x54, 0x24, 0x6c, 0x44, 0x89,
  0x7c, 0x24, 0x70, 0x89, 0x74, 0x24, 0x74, 0x44, 0x89, 0x5c, 0x24, 0x28, 0x48, 0x83, 0xf9, 0x30]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_12 : ∀ feat, Dec feat p5 12 (FV7z.mk .shr 64 [gr 64 6, Src.opd 8 (.i 12)] 4) := by dec_rfl
theorem p5_16 : ∀ feat, Dec feat p5 16 (FV7z.mk .shr 64 [gr 64 15, Src.opd 8 (.i 15)] 4) := by dec_rfl
theorem p5_20 : ∀ feat, Dec feat p5 20 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p5_25 : ∀ feat, Dec feat p5 25 (FV7z.mk .shr 64 [gr 64 1, Src.opd 8 (.i 6)] 4) := by dec_rfl
theorem p5_29 : ∀ feat, Dec feat p5 29 (FV7z.mk .shr 64 [gr 64 7, Src.opd 8 (.i 9)] 4) := by dec_rfl
theorem p5_33 : ∀ feat, Dec feat p5 33 (FV7z.mk .lea 32 [gr 32 10, .mem (mg (some 15) none 1 119 0)] 4) := by dec_rfl
theorem p5_37 : ∀ feat, Dec feat p5 37 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 88 64), gr 64 6] 5) := by dec_rfl
theorem p5_42 : ∀ feat, Dec feat p5 42 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 18)] 4) := by dec_rfl
theorem p5_46 : ∀ feat, Dec feat p5 46 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.i 786431)] 7) := by dec_rfl
theorem p5_53 : ∀ feat, Dec feat p5 53 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 96 64), gr 64 15] 5) := by dec_rfl
theorem p5_58 : ∀ feat, Dec feat p5 58 (FV7z.mk .lea 32 [gr 32 11, .mem (mg (some 1) none 1 48 0)] 4) := by dec_rfl
theorem p5_62 : ∀ feat, Dec feat p5 62 (FV7z.mk (.cmovcc 7) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem p5_66 : ∀ feat, Dec feat p5 66 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p5_69 : ∀ feat, Dec feat p5 69 (FV7z.mk .lea 32 [gr 32 15, .mem (mg (some 6) none 1 110 0)] 4) := by dec_rfl
theorem p5_73 : ∀ feat, Dec feat p5 73 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 64 64), gr 64 1] 5) := by dec_rfl
theorem p5_78 : ∀ feat, Dec feat p5 78 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 80 64), gr 64 7] 5) := by dec_rfl
theorem p5_83 : ∀ feat, Dec feat p5 83 (FV7z.mk .lea 32 [gr 32 9, .mem (mg (some 0) none 1 124 0)] 4) := by dec_rfl
theorem p5_87 : ∀ feat, Dec feat p5 87 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p5_90 : ∀ feat, Dec feat p5 90 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p5_92 : ∀ feat, Dec feat p5 92 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 76 32), gr 32 11] 5) := by dec_rfl
theorem p5_97 : ∀ feat, Dec feat p5 97 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 91)] 3) := by dec_rfl
theorem p5_100 : ∀ feat, Dec feat p5 100 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 104 32), gr 32 9] 5) := by dec_rfl
theorem p5_105 : ∀ feat, Dec feat p5 105 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 108 32), gr 32 10] 5) := by dec_rfl
theorem p5_110 : ∀ feat, Dec feat p5 110 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 112 32), gr 32 15] 5) := by dec_rfl
theorem p5_115 : ∀ feat, Dec feat p5 115 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 116 32), gr 32 6] 4) := by dec_rfl
theorem p5_119 : ∀ feat, Dec feat p5 119 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 40 32), gr 32 11] 5) := by dec_rfl
theorem p5_124 : ∀ feat, Dec feat p5 124 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 48)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 1 (.r 0),
  Op.mov 64 7 (.r 0),
  Op.mov 64 6 (.r 0),
  Op.mov 64 15 (.r 0),
  Op.shr64 6 (.i 12),
  Op.shr64 15 (.i 15),
  Op.mov 32 2 (.i 2),
  Op.shr64 1 (.i 6),
  Op.shr64 7 (.i 9),
  Op.lea 32 10 (some 15) none 1 119,
  Op.st 64 (some 4) none 1 88 6,
  Op.shr64 0 (.i 18),
  Op.cmp 64 13 (.i 786431),
  Op.st 64 (some 4) none 1 96 15,
  Op.lea 32 11 (some 1) none 1 48,
  Op.cmov64 7 0 2,
  Op.mov 64 2 (.r 15),
  Op.lea 32 15 (some 6) none 1 110,
  Op.st 64 (some 4) none 1 64 1,
  Op.st 64 (some 4) none 1 80 7,
  Op.lea 32 9 (some 0) none 1 124,
  Op.mov 64 0 (.r 6),
  Op.mov 32 6 (.r 7),
  Op.st 32 (some 4) none 1 76 11,
  Op.add 32 6 (.i 91),
  Op.st 32 (some 4) none 1 104 9,
  Op.st 32 (some 4) none 1 108 10,
  Op.st 32 (some 4) none 1 112 15,
  Op.st 32 (some 4) none 1 116 6,
  Op.st 32 (some 4) none 1 40 11,
  Op.cmp 64 1 (.i 48)]

theorem b5 (prof : Profile) : Blk prof p5 0 128 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_12 _) (OpI.shr64 (.i 12)) (by decide) <|
  .cons (p5_16 _) (OpI.shr64 (.i 15)) (by decide) <|
  .cons (p5_20 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p5_25 _) (OpI.shr64 (.i 6)) (by decide) <|
  .cons (p5_29 _) (OpI.shr64 (.i 9)) (by decide) <|
  .cons (p5_33 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p5_37 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_42 _) (OpI.shr64 (.i 18)) (by decide) <|
  .cons (p5_46 _) (OpI.cmp (.i 786431) (.inr rfl)) (by decide) <|
  .cons (p5_53 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_58 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p5_62 _) (OpI.cmov64) (by decide) <|
  .cons (p5_66 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p5_69 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p5_73 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_78 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_83 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p5_87 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p5_90 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p5_92 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_97 _) (OpI.add (.i 91) (.inl rfl)) (by decide) <|
  .cons (p5_100 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_105 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_110 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_115 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_119 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_124 _) (OpI.cmp (.i 48) (.inr rfl)) (by decide) <|
  .nil 128

def j5 : List Byte := [0x76, 0x1e]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 6) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `482`. -/
def p6 : List Byte := [
  0x89, 0x74, 0x24, 0x28, 0x48, 0x83, 0xff, 0x14]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 40 32), gr 32 6] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.i 20)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.st 32 (some 4) none 1 40 6,
  Op.cmp 64 7 (.i 20)]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_4 _) (OpI.cmp (.i 20) (.inr rfl)) (by decide) <|
  .nil 8

def j6 : List Byte := [0x76, 0x14]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 6) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `512`. -/
def p7 : List Byte := [
  0x8b, 0x43, 0x08, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 32 0 (some 3) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j7 : List Byte := [0x0f, 0x84, 0x22, 0x02, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 546] 6) := by dec_rfl

/-- The stretch at `1069`. -/
def p8 : List Byte := [
  0x49, 0x8d, 0x45, 0xef, 0x48, 0xc1, 0xe8, 0x04, 0x49, 0x89, 0xc7, 0x31, 0xc0, 0x48, 0x89, 0x44,
  0x24, 0x10, 0x64, 0x48, 0x83, 0x3c, 0x25, 0xd8, 0xff, 0xff, 0xff, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 13) none 1 18446744073709551599 0)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_13 : ∀ feat, Dec feat p8 13 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl
theorem p8_18 : ∀ feat, Dec feat p8 18 (FV7z.mk .cmp 64 [.mem (mf none none 1 18446744073709551576 64), .imm 64 0] 10) := by dec_rfl

/-- What the stretch does. -/
def o8 (fb : Addr) : List Op := [
  Op.lea 64 0 (some 13) none 1 18446744073709551599,
  Op.shr64 0 (.i 4),
  Op.mov 64 15 (.r 0),
  Op.xor 32 0 (.r 0),
  Op.st 64 (some 4) none 1 16 0,
  Op.cmpmif fb 64 none none 1 18446744073709551576 0]

theorem b8 (prof : Profile) (fb : Addr) : BlkF prof p8 (0x63100d : Addr) fb 0 28 (o8 fb) :=
  .cons (p8_0 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p8_4 _) (((OpI.shr64 (.i 4)).at _).fs _) (by decide) <|
  .cons (p8_8 _) (((OpI.mov (.r 0) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p8_11 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p8_13 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p8_18 _) (OpIF.cmpmif (.inr rfl)) (by decide) <|
  .nil 28

def j8 : List Byte := [0x74, 0x10]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `1099`. -/
def p9 : List Byte := [
  0x4c, 0x39, 0x3d, 0xbe, 0x19, 0x16, 0x00, 0x49, 0x0f, 0x47, 0xc5, 0x48, 0x89, 0x44, 0x24, 0x10]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 64 [.mem (mrip 1448382 64), gr 64 15] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk (.cmovcc 7) 64 [gr 64 0, gr 64 13] 4) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmpmra 64 7940592 15,
  Op.cmov64 7 0 13,
  Op.st 64 (some 4) none 1 16 0]

theorem b9 (prof : Profile) : BlkA prof p9 (0x63102b : Addr) 0 16 o9 :=
  .cons (p9_0 _) (OpIA.cmpmr_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p9_7 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p9_11 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 16

/-- The stretch at `1115`. -/
def p10 : List Byte := [
  0x48, 0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0x5b, 0x60, 0x44, 0x89, 0x74,
  0x24, 0x48, 0x48, 0x89, 0x6c, 0x24, 0x20]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), .imm 64 0] 9) := by dec_rfl
theorem p10_9 : ∀ feat, Dec feat p10 9 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 3) none 1 96 0)] 4) := by dec_rfl
theorem p10_13 : ∀ feat, Dec feat p10 13 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 72 32), gr 32 14] 5) := by dec_rfl
theorem p10_18 : ∀ feat, Dec feat p10 18 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 32 64), gr 64 5] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.sti 64 (some 4) none 1 8 0,
  Op.lea 64 11 (some 3) none 1 96,
  Op.st 32 (some 4) none 1 72 14,
  Op.st 64 (some 4) none 1 32 5]

theorem b10 (prof : Profile) : Blk prof p10 0 23 o10 :=
  .cons (p10_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_13 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p10_18 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 23

/-- The stretch at `1138`. -/
def p11 : List Byte := [
  0x4c, 0x8b, 0x53, 0x78, 0x4d, 0x39, 0xda]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 10, .mem (mg (some 3) none 1 120 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .cmp 64 [gr 64 10, Src.opd 64 (.r 11)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 10 (some 3) none 1 120,
  Op.cmp 64 10 (.r 11)]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.cmp (.r 11) (.inr rfl)) (by decide) <|
  .nil 7

def j9 : List Byte := [0x0f, 0x84, 0x31, 0x03, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 817] 6) := by dec_rfl

/-- The stretch at `1968`. -/
def p12 : List Byte := [
  0x49, 0x81, 0xfd, 0xff, 0x03, 0x00, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.i 1023)] 7) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cmp 64 13 (.i 1023)]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.cmp (.i 1023) (.inr rfl)) (by decide) <|
  .nil 7

def j10 : List Byte := [0x76, 0x23]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 6) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `1977`. -/
def p13 : List Byte := [
  0x8b, 0x44, 0x24, 0x28, 0x8d, 0x44, 0x00, 0xfe, 0x48, 0x8d, 0x44, 0xc3, 0x70, 0x48, 0x8b, 0x10,
  0x48, 0x8d, 0x48, 0xf0, 0x48, 0x39, 0xca]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 0) (some 0) 1 18446744073709551614 0)] 4) := by dec_rfl
theorem p13_8 : ∀ feat, Dec feat p13 8 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) (some 0) 8 112 0)] 5) := by dec_rfl
theorem p13_13 : ∀ feat, Dec feat p13 13 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl
theorem p13_16 : ∀ feat, Dec feat p13 16 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 18446744073709551600 0)] 4) := by dec_rfl
theorem p13_20 : ∀ feat, Dec feat p13 20 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 32 0 (some 4) none 1 40,
  Op.lea 32 0 (some 0) (some 0) 1 18446744073709551614,
  Op.lea 64 0 (some 3) (some 0) 8 112,
  Op.ld 64 2 (some 0) none 1 0,
  Op.lea 64 1 (some 0) none 1 18446744073709551600,
  Op.cmp 64 2 (.r 1)]

theorem b13 (prof : Profile) : Blk prof p13 0 23 o13 :=
  .cons (p13_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p13_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_13 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_16 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_20 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 23

def j11 : List Byte := [0x74, 0x0a]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `2012`. -/
def p14 : List Byte := [
  0x8b, 0x44, 0x24, 0x28, 0x8d, 0x48, 0x01, 0x01, 0xc0, 0x89, 0xcf, 0x48, 0x8d, 0x54, 0xc3, 0x60,
  0xc1, 0xef, 0x05, 0x89, 0xf8, 0x8b, 0xb4, 0x83, 0x60, 0x08, 0x00, 0x00, 0xb8, 0x01, 0x00, 0x00,
  0x00, 0xd3, 0xe0, 0x90]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p14_9 : ∀ feat, Dec feat p14 9 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p14_11 : ∀ feat, Dec feat p14 11 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 3) (some 0) 8 96 0)] 5) := by dec_rfl
theorem p14_16 : ∀ feat, Dec feat p14 16 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p14_19 : ∀ feat, Dec feat p14 19 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p14_21 : ∀ feat, Dec feat p14 21 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 3) (some 0) 4 2144 32)] 7) := by dec_rfl
theorem p14_28 : ∀ feat, Dec feat p14 28 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p14_33 : ∀ feat, Dec feat p14 33 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p14_35 : ∀ feat, Dec feat p14 35 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 32 0 (some 4) none 1 40,
  Op.lea 32 1 (some 0) none 1 1,
  Op.add 32 0 (.r 0),
  Op.mov 32 7 (.r 1),
  Op.lea 64 2 (some 3) (some 0) 8 96,
  Op.shr 7 (.i 5),
  Op.mov 32 0 (.r 7),
  Op.ld 32 6 (some 3) (some 0) 4 2144,
  Op.mov 32 0 (.i 1),
  Op.shl 0 (.r 1),
  Op.nop]

theorem b14 (prof : Profile) : Blk prof p14 0 36 o14 :=
  .cons (p14_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.add (.r 0) (.inl rfl)) (by decide) <|
  .cons (p14_9 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p14_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p14_16 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p14_19 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p14_21 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p14_28 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p14_33 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p14_35 _) (OpI.nop) (by decide) <|
  .nil 36

/-- The stretch at `2048`. -/
def p15 : List Byte := [
  0x39, 0xf0]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.cmp 32 0 (.r 6)]

theorem b15 (prof : Profile) : Blk prof p15 0 2 o15 :=
  .cons (p15_0 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

def j12 : List Byte := [0x0f, 0x87, 0xa8, 0x01, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 7) 64 [.rel 424] 6) := by dec_rfl

/-- The stretch at `2480`. -/
def p16 : List Byte := [
  0x8d, 0x47, 0x01, 0x83, 0xff, 0x03]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 1 0)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.lea 32 0 (some 7) none 1 1,
  Op.cmp 32 7 (.i 3)]

theorem b16 (prof : Profile) : Blk prof p16 0 6 o16 :=
  .cons (p16_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 6

def j13 : List Byte := [0x74, 0x3d]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `2488`. -/
def p17 : List Byte := [
  0x89, 0xc2, 0x8b, 0xb4, 0x93, 0x60, 0x08, 0x00, 0x00, 0x85, 0xf6]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p17_2 : ∀ feat, Dec feat p17 2 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 3) (some 2) 4 2144 32)] 7) := by dec_rfl
theorem p17_9 : ∀ feat, Dec feat p17 9 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 32 2 (.r 0),
  Op.ld 32 6 (some 3) (some 2) 4 2144,
  Op.test 32 6 (.r 6)]

theorem b17 (prof : Profile) : Blk prof p17 0 11 o17 :=
  .cons (p17_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p17_2 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p17_9 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 11

def j14 : List Byte := [0x0f, 0x85, 0x3e, 0x02, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 574] 6) := by dec_rfl

/-- The stretch at `2505`. -/
def p18 : List Byte := [
  0x8d, 0x47, 0x02, 0x83, 0xff, 0x02]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 2 0)] 3) := by dec_rfl
theorem p18_3 : ∀ feat, Dec feat p18 3 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.lea 32 0 (some 7) none 1 2,
  Op.cmp 32 7 (.i 2)]

theorem b18 (prof : Profile) : Blk prof p18 0 6 o18 :=
  .cons (p18_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p18_3 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 6

def j15 : List Byte := [0x74, 0x24]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 4) 64 [.rel 36] 2) := by dec_rfl

end FV7z.Im5
