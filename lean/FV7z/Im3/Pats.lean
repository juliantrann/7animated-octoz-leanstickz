import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps13
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `_int_malloc` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Im3
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

/-- The stretch at `46`. -/
def p2 : List Byte := [
  0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x0f, 0x84, 0x01, 0x06, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 1537] 6) := by dec_rfl

/-- The stretch at `55`. -/
def p3 : List Byte := [
  0x48, 0x83, 0x3d, 0x89, 0x39, 0x17, 0x00, 0x1f]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [.mem (mrip 1522057 64), .imm 64 31] 8) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpmia 64 8013224 31]

theorem b3 (prof : Profile) : BlkA prof p3 (0x630c17 : Addr) 0 8 o3 :=
  .cons (p3_0 _) (OpIA.cmpmi_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x0f, 0x87, 0xdb, 0x01, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 7) 64 [.rel 475] 6) := by dec_rfl

/-- The stretch at `86`. -/
def p4 : List Byte := [
  0x48, 0x01, 0xd8, 0x4c, 0x8b, 0x40, 0x08, 0x48, 0x8d, 0x48, 0xf0, 0x4c, 0x39, 0xc1]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 18446744073709551600 0)] 4) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 0 (.r 3),
  Op.ld 64 8 (some 0) none 1 8,
  Op.lea 64 1 (some 0) none 1 18446744073709551600,
  Op.cmp 64 1 (.r 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 14 o4 :=
  .cons (p4_0 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.cmp (.r 8) (.inr rfl)) (by decide) <|
  .nil 14

def j4 : List Byte := [0x0f, 0x84, 0x6e, 0x03, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 878] 6) := by dec_rfl

/-- The stretch at `544`. -/
def p5 : List Byte := [
  0xb9, 0x10, 0x00, 0x00, 0x00, 0x41, 0xbe, 0x02, 0x00, 0x00, 0x00, 0x41, 0xbd, 0x20, 0x00, 0x00,
  0x00, 0x31, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.i 2)] 6) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.i 32)] 6) := by dec_rfl
theorem p5_17 : ∀ feat, Dec feat p5 17 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 1 (.i 16),
  Op.mov 32 14 (.i 2),
  Op.mov 32 13 (.i 32),
  Op.xor 32 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 19 o5 :=
  .cons (p5_0 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p5_11 _) (OpI.mov (.i 32) (.inl rfl)) (by decide) <|
  .cons (p5_17 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 19

/-- The stretch at `563`. -/
def p6 : List Byte := [
  0x48, 0x8d, 0x3c, 0xc3, 0x4c, 0x8b, 0x47, 0x10, 0x4d, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) (some 0) 8 0 0)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 7 (some 3) (some 0) 8 0,
  Op.ld 64 8 (some 7) none 1 16,
  Op.test 64 8 (.r 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 11 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_8 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 11

def j5 : List Byte := [0x0f, 0x84, 0x0c, 0x01, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 268] 6) := by dec_rfl

/-- The stretch at `848`. -/
def p7 : List Byte := [
  0x43, 0x8d, 0x44, 0x36, 0xfe, 0x48, 0x8d, 0x04, 0xc5, 0x70, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 14) (some 14) 1 18446744073709551614 0)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 0) 8 112 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 32 0 (some 14) (some 14) 1 18446744073709551614,
  Op.lea 64 0 none (some 0) 8 112]

theorem b7 (prof : Profile) : Blk prof p7 0 13 o7 :=
  .cons (p7_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 13

def j6 : List Byte := [0xe9, 0xf4, 0xfc, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709550836] 5) := by dec_rfl

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
  0x24, 0x10, 0x64, 0x48, 0x83, 0x3c, 0x25, 0xd8, 0xff, 0xff, 0xff, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 13) none 1 18446744073709551599 0)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_13 : ∀ feat, Dec feat p9 13 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl
theorem p9_18 : ∀ feat, Dec feat p9 18 (FV7z.mk .cmp 64 [.mem (mf none none 1 18446744073709551576 64), .imm 64 0] 10) := by dec_rfl

/-- What the stretch does. -/
def o9 (fb : Addr) : List Op := [
  Op.lea 64 0 (some 13) none 1 18446744073709551599,
  Op.shr64 0 (.i 4),
  Op.mov 64 15 (.r 0),
  Op.xor 32 0 (.r 0),
  Op.st 64 (some 4) none 1 16 0,
  Op.cmpmif fb 64 none none 1 18446744073709551576 0]

theorem b9 (prof : Profile) (fb : Addr) : BlkF prof p9 (0x63100d : Addr) fb 0 28 (o9 fb) :=
  .cons (p9_0 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p9_4 _) (((OpI.shr64 (.i 4)).at _).fs _) (by decide) <|
  .cons (p9_8 _) (((OpI.mov (.r 0) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p9_11 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p9_13 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p9_18 _) (OpIF.cmpmif (.inr rfl)) (by decide) <|
  .nil 28

def j7 : List Byte := [0x74, 0x10]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `1099`. -/
def p10 : List Byte := [
  0x4c, 0x39, 0x3d, 0xbe, 0x19, 0x16, 0x00, 0x49, 0x0f, 0x47, 0xc5, 0x48, 0x89, 0x44, 0x24, 0x10]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 64 [.mem (mrip 1448382 64), gr 64 15] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk (.cmovcc 7) 64 [gr 64 0, gr 64 13] 4) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmpmra 64 7940592 15,
  Op.cmov64 7 0 13,
  Op.st 64 (some 4) none 1 16 0]

theorem b10 (prof : Profile) : BlkA prof p10 (0x63102b : Addr) 0 16 o10 :=
  .cons (p10_0 _) (OpIA.cmpmr_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p10_7 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p10_11 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 16

end FV7z.Im3
