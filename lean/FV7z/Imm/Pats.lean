import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps9
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `_int_malloc` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 25 of them) and each distinct jump (`j*`, 21) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Imm
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

/-- The stretch at `86`. -/
def p2 : List Byte := [
  0x48, 0x01, 0xd8, 0x4c, 0x8b, 0x40, 0x08, 0x48, 0x8d, 0x48, 0xf0, 0x4c, 0x39, 0xc1]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 18446744073709551600 0)] 4) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 0 (.r 3),
  Op.ld 64 8 (some 0) none 1 8,
  Op.lea 64 1 (some 0) none 1 18446744073709551600,
  Op.cmp 64 1 (.r 8)]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.cmp (.r 8) (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x0f, 0x84, 0x6e, 0x03, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 878] 6) := by dec_rfl

/-- The stretch at `304`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xe0, 0xf0, 0x49, 0x89, 0xc5, 0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551600)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.and 64 0 (.i 18446744073709551600),
  Op.mov 64 13 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.and (.i 18446744073709551600) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j3 : List Byte := [0x0f, 0x84, 0xfe, 0x04, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 1278] 6) := by dec_rfl

/-- The stretch at `320`. -/
def p4 : List Byte := [
  0x41, 0x89, 0xc6, 0x41, 0xc1, 0xee, 0x04, 0x48, 0x3b, 0x05, 0x7a, 0x38, 0x17, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .shr 32 [gr 32 14, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .cmp 64 [gr 64 0, .mem (mrip 1521786 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 14 (.r 0),
  Op.shr 14 (.i 4),
  Op.cmpma 64 0 8013224]

theorem b4 (prof : Profile) : BlkA prof p4 (0x630d20 : Addr) 0 14 o4 :=
  .cons (p4_0 _) ((OpI.mov (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p4_3 _) ((OpI.shr (.i 4)).at _) (by decide) <|
  .cons (p4_7 _) (OpIA.cmpm_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 14

def j4 : List Byte := [0x0f, 0x86, 0x6c, 0x02, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 6) 64 [.rel 620] 6) := by dec_rfl

/-- The stretch at `340`. -/
def p5 : List Byte := [
  0x48, 0x3d, 0xff, 0x03, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 1023)] 6) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 64 0 (.i 1023)]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.cmp (.i 1023) (.inr rfl)) (by decide) <|
  .nil 6

def j5 : List Byte := [0x0f, 0x86, 0xf0, 0x01, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 6) 64 [.rel 496] 6) := by dec_rfl

/-- The stretch at `848`. -/
def p6 : List Byte := [
  0x43, 0x8d, 0x44, 0x36, 0xfe, 0x48, 0x8d, 0x04, 0xc5, 0x70, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 14) (some 14) 1 18446744073709551614 0)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 0) 8 112 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 32 0 (some 14) (some 14) 1 18446744073709551614,
  Op.lea 64 0 none (some 0) 8 112]

theorem b6 (prof : Profile) : Blk prof p6 0 13 o6 :=
  .cons (p6_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 13

def j6 : List Byte := [0xe9, 0xf4, 0xfc, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709550836] 5) := by dec_rfl

/-- The stretch at `930`. -/
def p7 : List Byte := [
  0x48, 0x81, 0xc4, 0x88, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xc0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d,
  0x41, 0x5e, 0x41, 0x5f]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 136)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_12 : ∀ feat, Dec feat p7 12 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p7_14 : ∀ feat, Dec feat p7 14 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p7_16 : ∀ feat, Dec feat p7 16 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p7_18 : ∀ feat, Dec feat p7 18 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 136),
  Op.mov 64 0 (.r 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b7 (prof : Profile) : Blk prof p7 0 20 o7 :=
  .cons (p7_0 _) (OpI.add (.i 136) (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.pop) (by decide) <|
  .cons (p7_11 _) (OpI.pop) (by decide) <|
  .cons (p7_12 _) (OpI.pop) (by decide) <|
  .cons (p7_14 _) (OpI.pop) (by decide) <|
  .cons (p7_16 _) (OpI.pop) (by decide) <|
  .cons (p7_18 _) (OpI.pop) (by decide) <|
  .nil 20

/-- The stretch at `984`. -/
def p8 : List Byte := [
  0x4c, 0x89, 0xe8, 0x4c, 0x89, 0xef, 0x44, 0x89, 0x74, 0x24, 0x28, 0x48, 0xc1, 0xe8, 0x06, 0x48,
  0xc1, 0xef, 0x09, 0xc7, 0x44, 0x24, 0x70, 0x6e, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x40,
  0x83, 0xc0, 0x30, 0x48, 0x89, 0x7c, 0x24, 0x50, 0x83, 0xc7, 0x5b, 0x89, 0x7c, 0x24, 0x74, 0x89,
  0x44, 0x24, 0x4c, 0xc7, 0x44, 0x24, 0x6c, 0x77, 0x00, 0x00, 0x00, 0xc7, 0x44, 0x24, 0x68, 0x7c,
  0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x60, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24,
  0x58, 0x00, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p8_6 : ∀ feat, Dec feat p8 6 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 40 32), gr 32 14] 5) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 6)] 4) := by dec_rfl
theorem p8_15 : ∀ feat, Dec feat p8 15 (FV7z.mk .shr 64 [gr 64 7, Src.opd 8 (.i 9)] 4) := by dec_rfl
theorem p8_19 : ∀ feat, Dec feat p8 19 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 112 32), .imm 32 110] 8) := by dec_rfl
theorem p8_27 : ∀ feat, Dec feat p8 27 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 64 64), gr 64 0] 5) := by dec_rfl
theorem p8_32 : ∀ feat, Dec feat p8 32 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p8_35 : ∀ feat, Dec feat p8 35 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 80 64), gr 64 7] 5) := by dec_rfl
theorem p8_40 : ∀ feat, Dec feat p8 40 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 91)] 3) := by dec_rfl
theorem p8_43 : ∀ feat, Dec feat p8 43 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 116 32), gr 32 7] 4) := by dec_rfl
theorem p8_47 : ∀ feat, Dec feat p8 47 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 76 32), gr 32 0] 4) := by dec_rfl
theorem p8_51 : ∀ feat, Dec feat p8 51 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 108 32), .imm 32 119] 8) := by dec_rfl
theorem p8_59 : ∀ feat, Dec feat p8 59 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 104 32), .imm 32 124] 8) := by dec_rfl
theorem p8_67 : ∀ feat, Dec feat p8 67 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 96 64), .imm 64 0] 9) := by dec_rfl
theorem p8_76 : ∀ feat, Dec feat p8 76 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 88 64), .imm 64 0] 9) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 0 (.r 13),
  Op.mov 64 7 (.r 13),
  Op.st 32 (some 4) none 1 40 14,
  Op.shr64 0 (.i 6),
  Op.shr64 7 (.i 9),
  Op.sti 32 (some 4) none 1 112 110,
  Op.st 64 (some 4) none 1 64 0,
  Op.add 32 0 (.i 48),
  Op.st 64 (some 4) none 1 80 7,
  Op.add 32 7 (.i 91),
  Op.st 32 (some 4) none 1 116 7,
  Op.st 32 (some 4) none 1 76 0,
  Op.sti 32 (some 4) none 1 108 119,
  Op.sti 32 (some 4) none 1 104 124,
  Op.sti 64 (some 4) none 1 96 0,
  Op.sti 64 (some 4) none 1 88 0]

theorem b8 (prof : Profile) : Blk prof p8 0 85 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p8_6 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_11 _) (OpI.shr64 (.i 6)) (by decide) <|
  .cons (p8_15 _) (OpI.shr64 (.i 9)) (by decide) <|
  .cons (p8_19 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_27 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_32 _) (OpI.add (.i 48) (.inl rfl)) (by decide) <|
  .cons (p8_35 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_40 _) (OpI.add (.i 91) (.inl rfl)) (by decide) <|
  .cons (p8_43 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_47 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_51 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_59 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_67 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_76 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 85

/-- The stretch at `1069`. -/
def p9 : List Byte := [
  0x49, 0x8d, 0x45, 0xef, 0x48, 0xc1, 0xe8, 0x04, 0x49, 0x89, 0xc7, 0x31, 0xc0, 0x48, 0x89, 0x44,
  0x24, 0x10]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 13) none 1 18446744073709551599 0)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_13 : ∀ feat, Dec feat p9 13 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lea 64 0 (some 13) none 1 18446744073709551599,
  Op.shr64 0 (.i 4),
  Op.mov 64 15 (.r 0),
  Op.xor 32 0 (.r 0),
  Op.st 64 (some 4) none 1 16 0]

theorem b9 (prof : Profile) : Blk prof p9 0 18 o9 :=
  .cons (p9_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.shr64 (.i 4)) (by decide) <|
  .cons (p9_8 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p9_11 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p9_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 18

def j7 : List Byte := [0x74, 0x10]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

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

def j8 : List Byte := [0x0f, 0x84, 0x31, 0x03, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 817] 6) := by dec_rfl

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

def j9 : List Byte := [0x76, 0x23]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 6) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `2012`. -/
def p13 : List Byte := [
  0x8b, 0x44, 0x24, 0x28, 0x8d, 0x48, 0x01, 0x01, 0xc0, 0x89, 0xcf, 0x48, 0x8d, 0x54, 0xc3, 0x60,
  0xc1, 0xef, 0x05, 0x89, 0xf8, 0x8b, 0xb4, 0x83, 0x60, 0x08, 0x00, 0x00, 0xb8, 0x01, 0x00, 0x00,
  0x00, 0xd3, 0xe0, 0x90]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 40 32)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p13_9 : ∀ feat, Dec feat p13 9 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 3) (some 0) 8 96 0)] 5) := by dec_rfl
theorem p13_16 : ∀ feat, Dec feat p13 16 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p13_19 : ∀ feat, Dec feat p13 19 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p13_21 : ∀ feat, Dec feat p13 21 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 3) (some 0) 4 2144 32)] 7) := by dec_rfl
theorem p13_28 : ∀ feat, Dec feat p13 28 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p13_33 : ∀ feat, Dec feat p13 33 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p13_35 : ∀ feat, Dec feat p13 35 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
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

theorem b13 (prof : Profile) : Blk prof p13 0 36 o13 :=
  .cons (p13_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p13_7 _) (OpI.add (.r 0) (.inl rfl)) (by decide) <|
  .cons (p13_9 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p13_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_16 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p13_19 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p13_21 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_28 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p13_33 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p13_35 _) (OpI.nop) (by decide) <|
  .nil 36

/-- The stretch at `2048`. -/
def p14 : List Byte := [
  0x39, 0xf0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 32 0 (.r 6)]

theorem b14 (prof : Profile) : Blk prof p14 0 2 o14 :=
  .cons (p14_0 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

def j10 : List Byte := [0x0f, 0x87, 0xa8, 0x01, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 7) 64 [.rel 424] 6) := by dec_rfl

/-- The stretch at `2480`. -/
def p15 : List Byte := [
  0x8d, 0x47, 0x01, 0x83, 0xff, 0x03]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 1 0)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.lea 32 0 (some 7) none 1 1,
  Op.cmp 32 7 (.i 3)]

theorem b15 (prof : Profile) : Blk prof p15 0 6 o15 :=
  .cons (p15_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 6

def j11 : List Byte := [0x74, 0x3d]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `2488`. -/
def p16 : List Byte := [
  0x89, 0xc2, 0x8b, 0xb4, 0x93, 0x60, 0x08, 0x00, 0x00, 0x85, 0xf6]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_2 : ∀ feat, Dec feat p16 2 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 3) (some 2) 4 2144 32)] 7) := by dec_rfl
theorem p16_9 : ∀ feat, Dec feat p16 9 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 32 2 (.r 0),
  Op.ld 32 6 (some 3) (some 2) 4 2144,
  Op.test 32 6 (.r 6)]

theorem b16 (prof : Profile) : Blk prof p16 0 11 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_2 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p16_9 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 11

def j12 : List Byte := [0x0f, 0x85, 0x3e, 0x02, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 574] 6) := by dec_rfl

/-- The stretch at `2505`. -/
def p17 : List Byte := [
  0x8d, 0x47, 0x02, 0x83, 0xff, 0x02]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 2 0)] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.lea 32 0 (some 7) none 1 2,
  Op.cmp 32 7 (.i 2)]

theorem b17 (prof : Profile) : Blk prof p17 0 6 o17 :=
  .cons (p17_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 6

def j13 : List Byte := [0x74, 0x24]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 36] 2) := by dec_rfl

def j14 : List Byte := [0x0f, 0x85, 0x25, 0x02, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 549] 6) := by dec_rfl

/-- The stretch at `2530`. -/
def p18 : List Byte := [
  0x83, 0xff, 0x01]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmp 32 7 (.i 1)]

theorem b18 (prof : Profile) : Blk prof p18 0 3 o18 :=
  .cons (p18_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j15 : List Byte := [0x74, 0x0e]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `2549`. -/
def p19 : List Byte := [
  0x4c, 0x8b, 0x43, 0x60, 0x49, 0x8b, 0x40, 0x08, 0x48, 0x83, 0xe0, 0xf8, 0x48, 0x39, 0x83, 0x88,
  0x08, 0x00, 0x00]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 3) none 1 96 64)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 8) none 1 8 64)] 4) := by dec_rfl
theorem p19_8 : ∀ feat, Dec feat p19 8 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p19_12 : ∀ feat, Dec feat p19 12 (FV7z.mk .cmp 64 [.mem (mg (some 3) none 1 2184 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 64 8 (some 3) none 1 96,
  Op.ld 64 0 (some 8) none 1 8,
  Op.and 64 0 (.i 18446744073709551608),
  Op.cmpmr 64 (some 3) none 1 2184 0]

theorem b19 (prof : Profile) : Blk prof p19 0 19 o19 :=
  .cons (p19_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p19_8 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p19_12 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 19

def j16 : List Byte := [0x0f, 0x82, 0x12, 0x02, 0x00, 0x00]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 2) 64 [.rel 530] 6) := by dec_rfl

/-- The stretch at `2574`. -/
def p20 : List Byte := [
  0x49, 0x8d, 0x55, 0x20, 0x48, 0x39, 0xc2]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 13) none 1 32 0)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.lea 64 2 (some 13) none 1 32,
  Op.cmp 64 2 (.r 0)]

theorem b20 (prof : Profile) : Blk prof p20 0 7 o20 :=
  .cons (p20_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

def j17 : List Byte := [0x0f, 0x86, 0x5c, 0x02, 0x00, 0x00]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 6) 64 [.rel 604] 6) := by dec_rfl

/-- The stretch at `2587`. -/
def p21 : List Byte := [
  0x4c, 0x89, 0x5c, 0x24, 0x18, 0x8b, 0x43, 0x08, 0x85, 0xc0]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 11] 5) := by dec_rfl
theorem p21_5 : ∀ feat, Dec feat p21 5 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p21_8 : ∀ feat, Dec feat p21 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.st 64 (some 4) none 1 24 11,
  Op.ld 32 0 (some 3) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b21 (prof : Profile) : Blk prof p21 0 10 o21 :=
  .cons (p21_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p21_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p21_8 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 10

def j18 : List Byte := [0x0f, 0x84, 0x9a, 0x02, 0x00, 0x00]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 4) 64 [.rel 666] 6) := by dec_rfl

/-- The stretch at `3269`. -/
def p22 : List Byte := [
  0x48, 0x89, 0xde, 0x4c, 0x89, 0xef, 0x48, 0x8b, 0x6c, 0x24, 0x20]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p22_3 : ∀ feat, Dec feat p22 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p22_6 : ∀ feat, Dec feat p22 6 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.mov 64 6 (.r 3),
  Op.mov 64 7 (.r 13),
  Op.ld 64 5 (some 4) none 1 32]

theorem b22 (prof : Profile) : Blk prof p22 0 11 o22 :=
  .cons (p22_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p22_3 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p22_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `3285`. -/
def p23 : List Byte := [
  0x49, 0x89, 0xc0, 0x48, 0x85, 0xc0]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p23_3 : ∀ feat, Dec feat p23 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 64 8 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b23 (prof : Profile) : Blk prof p23 0 6 o23 :=
  .cons (p23_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p23_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j19 : List Byte := [0x0f, 0x84, 0xa7, 0xfc, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709550759] 6) := by dec_rfl

/-- The stretch at `3297`. -/
def p24 : List Byte := [
  0x8b, 0x05, 0xdd, 0x2c, 0x17, 0x00, 0x85, 0xc0]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1518813 32)] 6) := by dec_rfl
theorem p24_6 : ∀ feat, Dec feat p24 6 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.lda 32 0 8013220,
  Op.test 32 0 (.r 0)]

theorem b24 (prof : Profile) : BlkA prof p24 (0x6318c1 : Addr) 0 8 o24 :=
  .cons (p24_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p24_6 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 8

def j20 : List Byte := [0x0f, 0x84, 0xb3, 0xf6, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709549235] 6) := by dec_rfl

end FV7z.Imm
