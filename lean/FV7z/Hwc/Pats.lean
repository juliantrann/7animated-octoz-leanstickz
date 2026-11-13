import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps16
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `_dl_important_hwcaps` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 64 of them) and each distinct jump (`j*`, 43) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Hwc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xe5, 0x41, 0x57, 0x49, 0x89, 0xff, 0x41, 0x56, 0x48,
  0x8d, 0x45, 0xc8, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xec, 0x88, 0x00, 0x00, 0x00, 0x48,
  0x89, 0x7d, 0xa0, 0xbf, 0x0b, 0x00, 0x00, 0x00, 0x48, 0x89, 0x75, 0x98, 0x48, 0x89, 0xc6, 0x48,
  0x89, 0x55, 0xa8, 0x31, 0xd2, 0x48, 0x89, 0x45, 0x80, 0x48, 0x89, 0x4d, 0x90]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 5) none 1 18446744073709551560 0)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 136)] 7) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551520 64), gr 64 7] 4) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 11)] 5) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551512 64), gr 64 6] 4) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551528 64), gr 64 2] 4) := by dec_rfl
theorem p0_51 : ∀ feat, Dec feat p0 51 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_53 : ∀ feat, Dec feat p0 53 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551488 64), gr 64 0] 4) := by dec_rfl
theorem p0_57 : ∀ feat, Dec feat p0 57 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551504 64), gr 64 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 4),
  Op.push 15,
  Op.mov 64 15 (.r 7),
  Op.push 14,
  Op.lea 64 0 (some 5) none 1 18446744073709551560,
  Op.push 13,
  Op.push 12,
  Op.push 3,
  Op.sub 64 4 (.i 136),
  Op.st 64 (some 5) none 1 18446744073709551520 7,
  Op.mov 32 7 (.i 11),
  Op.st 64 (some 5) none 1 18446744073709551512 6,
  Op.mov 64 6 (.r 0),
  Op.st 64 (some 5) none 1 18446744073709551528 2,
  Op.xor 32 2 (.r 2),
  Op.st 64 (some 5) none 1 18446744073709551488 0,
  Op.st 64 (some 5) none 1 18446744073709551504 1]

theorem b0 (prof : Profile) : Blk prof p0 0 61 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.push) (by decide) <|
  .cons (p0_21 _) (OpI.push) (by decide) <|
  .cons (p0_23 _) (OpI.push) (by decide) <|
  .cons (p0_24 _) (OpI.sub (.i 136) (.inr rfl)) (by decide) <|
  .cons (p0_31 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_35 _) (OpI.mov (.i 11) (.inl rfl)) (by decide) <|
  .cons (p0_40 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_44 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p0_47 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_51 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_53 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_57 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 61

/-- The stretch at `66`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x5d, 0xc8, 0x48, 0x8b, 0x05, 0x3b, 0x79, 0x0f, 0x00, 0x31, 0xd2, 0x4d, 0x85, 0xff,
  0x48, 0x89, 0x45, 0xb0, 0x0f, 0x95, 0xc2, 0x48, 0x21, 0xd8, 0x48, 0x89, 0x5d, 0x88, 0x49, 0x89,
  0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 5) none 1 18446744073709551560 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1014075 64)] 7) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .test 64 [gr 64 15, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551536 64), gr 64 0] 4) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk (.setcc 5) 8 [gr 8 2] 3) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p1_26 : ∀ feat, Dec feat p1 26 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551496 64), gr 64 3] 4) := by dec_rfl
theorem p1_30 : ∀ feat, Dec feat p1 30 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 3 (some 5) none 1 18446744073709551560,
  Op.lda 64 0 8014536,
  Op.xor 32 2 (.r 2),
  Op.test 64 15 (.r 15),
  Op.st 64 (some 5) none 1 18446744073709551536 0,
  Op.setcc 5 2,
  Op.and 64 0 (.r 3),
  Op.st 64 (some 5) none 1 18446744073709551496 3,
  Op.mov 64 8 (.r 0)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x6ad182 : Addr) 0 33 o1 :=
  .cons (p1_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p1_4 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_11 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p1_13 _) ((OpI.test (.r 15) (.inr rfl)).at _) (by decide) <|
  .cons (p1_16 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_20 _) ((OpI.setcc).at _) (by decide) <|
  .cons (p1_23 _) ((OpI.and (.r 3) (.inr rfl)).at _) (by decide) <|
  .cons (p1_26 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_30 _) ((OpI.mov (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 33

def j0 : List Byte := [0x0f, 0x84, 0x6f, 0x08, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 2159] 6) := by dec_rfl

/-- The stretch at `105`. -/
def p2 : List Byte := [
  0x31, 0xc9, 0xbe, 0x01, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.mov 32 6 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `112`. -/
def p3 : List Byte := [
  0x49, 0x0f, 0xa3, 0xc8, 0x4c, 0x8d, 0x62, 0x01]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk (.bit (BitMn.bt)) 64 [gr 64 8, gr 64 1] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 2) none 1 1 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.bt64 8 1,
  Op.lea 64 12 (some 2) none 1 1]

theorem b3 (prof : Profile) : Blk prof p3 0 8 o3 :=
  .cons (p3_0 _) (OpI.bt64) (by decide) <|
  .cons (p3_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x73, 0x0a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 3) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `122`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x42, 0x02, 0x4c, 0x89, 0xe2, 0x49, 0x89, 0xc4]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) none 1 2 0)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lea 64 0 (some 2) none 1 2,
  Op.mov 64 2 (.r 12),
  Op.mov 64 12 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `132`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xc1, 0x01, 0x48, 0x89, 0xf0, 0x48, 0xd3, 0xe0, 0x48, 0xf7, 0xd8, 0x4c, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .neg 64 [gr 64 0] 3) := by dec_rfl
theorem p5_13 : ∀ feat, Dec feat p5 13 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 1 (.i 1),
  Op.mov 64 0 (.r 6),
  Op.shl64 0 (.r 1),
  Op.neg 64 0,
  Op.test 64 0 (.r 8)]

theorem b5 (prof : Profile) : Blk prof p5 0 16 o5 :=
  .cons (p5_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.shl64 (.r 1)) (by decide) <|
  .cons (p5_10 _) (OpI.neg (.inr rfl)) (by decide) <|
  .cons (p5_13 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 16

def j2 : List Byte := [0x75, 0xda]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551578] 2) := by dec_rfl

/-- The stretch at `150`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x05, 0x13, 0xb3, 0x0f, 0x00, 0x48, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1028883 64)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lda 64 0 8029424,
  Op.test 64 0 (.r 0)]

theorem b6 (prof : Profile) : BlkA prof p6 (0x6ad1d6 : Addr) 0 10 o6 :=
  .cons (p6_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p6_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j3 : List Byte := [0x0f, 0x84, 0xfd, 0x06, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 1789] 6) := by dec_rfl

/-- The stretch at `682`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x75, 0xa0, 0x48, 0x85, 0xf6]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 18446744073709551520 64)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 6 (some 5) none 1 18446744073709551520,
  Op.test 64 6 (.r 6)]

theorem b7 (prof : Profile) : Blk prof p7 0 7 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x74, 0x19]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `691`. -/
def p8 : List Byte := [
  0x48, 0x89, 0x30, 0x48, 0x8b, 0x75, 0x98, 0x48, 0x89, 0x70, 0x08, 0x48, 0x89, 0xc8, 0x48, 0x83,
  0xc1, 0x01, 0x48, 0xc1, 0xe0, 0x04, 0x48, 0x01, 0xd8]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 6] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 18446744073709551512 64)] 4) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), gr 64 6] 4) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p8_14 : ∀ feat, Dec feat p8 14 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p8_18 : ∀ feat, Dec feat p8 18 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p8_22 : ∀ feat, Dec feat p8 22 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 64 (some 0) none 1 0 6,
  Op.ld 64 6 (some 5) none 1 18446744073709551512,
  Op.st 64 (some 0) none 1 8 6,
  Op.mov 64 0 (.r 1),
  Op.add 64 1 (.i 1),
  Op.shl64 0 (.i 4),
  Op.add 64 0 (.r 3)]

theorem b8 (prof : Profile) : Blk prof p8 0 25 o8 :=
  .cons (p8_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_11 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p8_14 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p8_18 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p8_22 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .nil 25

/-- The stretch at `716`. -/
def p9 : List Byte := [
  0x48, 0x8d, 0x35, 0xc7, 0x91, 0x05, 0x00, 0x48, 0xc7, 0x40, 0x08, 0x03, 0x00, 0x00, 0x00, 0x48,
  0x89, 0x30, 0x49, 0x39, 0xcc]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 364999 0)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), .imm 64 3] 8) := by dec_rfl
theorem p9_15 : ∀ feat, Dec feat p9 15 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 6] 3) := by dec_rfl
theorem p9_18 : ∀ feat, Dec feat p9 18 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 6 (.i 7366106),
  Op.sti 64 (some 0) none 1 8 3,
  Op.st 64 (some 0) none 1 0 6,
  Op.cmp 64 12 (.r 1)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x6ad40c : Addr) 0 21 o9 :=
  .cons (p9_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_7 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p9_15 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p9_18 _) ((OpI.cmp (.r 1) (.inr rfl)).at _) (by decide) <|
  .nil 21

def j5 : List Byte := [0x0f, 0x85, 0x23, 0x06, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 1571] 6) := by dec_rfl

/-- The stretch at `743`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x43, 0x08, 0x48, 0x89, 0x45, 0xb8, 0x49, 0x83, 0xfc, 0x01]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 8 64)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551544 64), gr 64 0] 4) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 0 (some 3) none 1 8,
  Op.st 64 (some 5) none 1 18446744073709551544 0,
  Op.cmp 64 12 (.i 1)]

theorem b10 (prof : Profile) : Blk prof p10 0 12 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_8 _) (OpI.cmp (.i 1) (.inr rfl)) (by decide) <|
  .nil 12

def j6 : List Byte := [0x0f, 0x84, 0x25, 0x05, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 1317] 6) := by dec_rfl

/-- The stretch at `761`. -/
def p11 : List Byte := [
  0x48, 0x89, 0xc1, 0x4c, 0x89, 0xe0, 0x48, 0xc1, 0xe0, 0x04, 0x48, 0x8d, 0x54, 0x03, 0xf0, 0x48,
  0x89, 0x85, 0x68, 0xff, 0xff, 0xff, 0x48, 0x8b, 0x42, 0x08, 0x48, 0x89, 0x45, 0xb0, 0x48, 0x8d,
  0x44, 0x08, 0x02, 0x49, 0x83, 0xfc, 0x02]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p11_6 : ∀ feat, Dec feat p11 6 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 3) (some 0) 1 18446744073709551600 0)] 5) := by dec_rfl
theorem p11_15 : ∀ feat, Dec feat p11 15 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551464 64), gr 64 0] 7) := by dec_rfl
theorem p11_22 : ∀ feat, Dec feat p11 22 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 8 64)] 4) := by dec_rfl
theorem p11_26 : ∀ feat, Dec feat p11 26 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551536 64), gr 64 0] 4) := by dec_rfl
theorem p11_30 : ∀ feat, Dec feat p11 30 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 1) 1 2 0)] 5) := by dec_rfl
theorem p11_35 : ∀ feat, Dec feat p11 35 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 1 (.r 0),
  Op.mov 64 0 (.r 12),
  Op.shl64 0 (.i 4),
  Op.lea 64 2 (some 3) (some 0) 1 18446744073709551600,
  Op.st 64 (some 5) none 1 18446744073709551464 0,
  Op.ld 64 0 (some 2) none 1 8,
  Op.st 64 (some 5) none 1 18446744073709551536 0,
  Op.lea 64 0 (some 0) (some 1) 1 2,
  Op.cmp 64 12 (.i 2)]

theorem b11 (prof : Profile) : Blk prof p11 0 39 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p11_6 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p11_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_15 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_22 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_26 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_30 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_35 _) (OpI.cmp (.i 2) (.inr rfl)) (by decide) <|
  .nil 39

def j7 : List Byte := [0x0f, 0x86, 0x2d, 0x05, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 6) 64 [.rel 1325] 6) := by dec_rfl

/-- The stretch at `806`. -/
def p12 : List Byte := [
  0x49, 0x8d, 0x74, 0x24, 0xfd, 0x48, 0x8d, 0x0c, 0x00, 0x48, 0x83, 0xfe, 0x03]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 12) none 1 18446744073709551613 0)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) (some 0) 1 0 0)] 4) := by dec_rfl
theorem p12_9 : ∀ feat, Dec feat p12 9 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.lea 64 6 (some 12) none 1 18446744073709551613,
  Op.lea 64 1 (some 0) (some 0) 1 0,
  Op.cmp 64 6 (.i 3)]

theorem b12 (prof : Profile) : Blk prof p12 0 13 o12 :=
  .cons (p12_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_9 _) (OpI.cmp (.i 3) (.inr rfl)) (by decide) <|
  .nil 13

def j8 : List Byte := [0x0f, 0x86, 0xb5, 0x05, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 6) 64 [.rel 1461] 6) := by dec_rfl

/-- The stretch at `920`. -/
def p13 : List Byte := [
  0x48, 0xc1, 0xe6, 0x04, 0x48, 0x8b, 0x44, 0x33, 0x08, 0x48, 0x8d, 0x77, 0x01, 0x48, 0x8d, 0x44,
  0x01, 0x01, 0x4c, 0x39, 0xe6]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .shl 64 [gr 64 6, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) (some 6) 1 8 64)] 5) := by dec_rfl
theorem p13_9 : ∀ feat, Dec feat p13 9 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 7) none 1 1 0)] 4) := by dec_rfl
theorem p13_13 : ∀ feat, Dec feat p13 13 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 1) (some 0) 1 1 0)] 5) := by dec_rfl
theorem p13_18 : ∀ feat, Dec feat p13 18 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.shl64 6 (.i 4),
  Op.ld 64 0 (some 3) (some 6) 1 8,
  Op.lea 64 6 (some 7) none 1 1,
  Op.lea 64 0 (some 1) (some 0) 1 1,
  Op.cmp 64 6 (.r 12)]

theorem b13 (prof : Profile) : Blk prof p13 0 21 o13 :=
  .cons (p13_0 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p13_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_18 _) (OpI.cmp (.r 12) (.inr rfl)) (by decide) <|
  .nil 21

def j9 : List Byte := [0x0f, 0x83, 0x11, 0x05, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 3) 64 [.rel 1297] 6) := by dec_rfl

/-- The stretch at `947`. -/
def p14 : List Byte := [
  0x48, 0x89, 0xf9, 0x48, 0xc1, 0xe1, 0x04, 0x48, 0x8b, 0x4c, 0x0b, 0x08, 0x48, 0x8d, 0x44, 0x08,
  0x01, 0x48, 0x8d, 0x4f, 0x02, 0x49, 0x39, 0xcc]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 3) (some 1) 1 8 64)] 5) := by dec_rfl
theorem p14_12 : ∀ feat, Dec feat p14 12 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 1) 1 1 0)] 5) := by dec_rfl
theorem p14_17 : ∀ feat, Dec feat p14 17 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 7) none 1 2 0)] 4) := by dec_rfl
theorem p14_21 : ∀ feat, Dec feat p14 21 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 1 (.r 7),
  Op.shl64 1 (.i 4),
  Op.ld 64 1 (some 3) (some 1) 1 8,
  Op.lea 64 0 (some 0) (some 1) 1 1,
  Op.lea 64 1 (some 7) none 1 2,
  Op.cmp 64 12 (.r 1)]

theorem b14 (prof : Profile) : Blk prof p14 0 24 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p14_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_12 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p14_17 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p14_21 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 24

def j10 : List Byte := [0x76, 0x25]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 6) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `1010`. -/
def p15 : List Byte := [
  0x49, 0x83, 0xfc, 0x3f]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.i 63)] 4) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.cmp 64 12 (.i 63)]

theorem b15 (prof : Profile) : Blk prof p15 0 4 o15 :=
  .cons (p15_0 _) (OpI.cmp (.i 63) (.inr rfl)) (by decide) <|
  .nil 4

def j11 : List Byte := [0x0f, 0x87, 0x42, 0x04, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 7) 64 [.rel 1090] 6) := by dec_rfl

/-- The stretch at `1020`. -/
def p16 : List Byte := [
  0xb9, 0x43, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xb8, 0x80, 0x00, 0x00, 0x00, 0x44, 0x89, 0xe6, 0x44,
  0x29, 0xe1, 0x48, 0xd3, 0xef, 0x48, 0x85, 0xff]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 67)] 5) := by dec_rfl
theorem p16_5 : ∀ feat, Dec feat p16 5 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 0) none 1 128 0)] 7) := by dec_rfl
theorem p16_12 : ∀ feat, Dec feat p16 12 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p16_15 : ∀ feat, Dec feat p16 15 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p16_18 : ∀ feat, Dec feat p16 18 (FV7z.mk .shr 64 [gr 64 7, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p16_21 : ∀ feat, Dec feat p16 21 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 32 1 (.i 67),
  Op.lea 64 7 (some 0) none 1 128,
  Op.mov 32 6 (.r 12),
  Op.sub 32 1 (.r 12),
  Op.shr64 7 (.r 1),
  Op.test 64 7 (.r 7)]

theorem b16 (prof : Profile) : Blk prof p16 0 24 o16 :=
  .cons (p16_0 _) (OpI.mov (.i 67) (.inl rfl)) (by decide) <|
  .cons (p16_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p16_12 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p16_15 _) (OpI.sub (.r 12) (.inl rfl)) (by decide) <|
  .cons (p16_18 _) (OpI.shr64 (.r 1)) (by decide) <|
  .cons (p16_21 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 24

def j12 : List Byte := [0x0f, 0x85, 0x24, 0x04, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 1060] 6) := by dec_rfl

/-- The stretch at `1050`. -/
def p17 : List Byte := [
  0x8d, 0x4e, 0xfd, 0x48, 0xd3, 0xe0]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 6) none 1 18446744073709551613 0)] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.lea 32 1 (some 6) none 1 18446744073709551613,
  Op.shl64 0 (.r 1)]

theorem b17 (prof : Profile) : Blk prof p17 0 6 o17 :=
  .cons (p17_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.shl64 (.r 1)) (by decide) <|
  .nil 6

/-- The stretch at `1056`. -/
def p18 : List Byte := [
  0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x89, 0xf1, 0x48, 0x89, 0x55, 0x98, 0x44, 0x89, 0xc7, 0x89,
  0x75, 0xa0, 0xd3, 0xe7, 0x48, 0x8b, 0x4d, 0xa8, 0x89, 0xbd, 0x74, 0xff, 0xff, 0xff, 0x48, 0x63,
  0xff, 0x48, 0x89, 0x39, 0x49, 0x89, 0xfd, 0x49, 0xc1, 0xe5, 0x04, 0x48, 0x89, 0xbd, 0x78, 0xff,
  0xff, 0xff, 0x49, 0x8d, 0x7c, 0x05, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p18_6 : ∀ feat, Dec feat p18 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p18_8 : ∀ feat, Dec feat p18 8 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551512 64), gr 64 2] 4) := by dec_rfl
theorem p18_12 : ∀ feat, Dec feat p18 12 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p18_15 : ∀ feat, Dec feat p18 15 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 18446744073709551520 32), gr 32 6] 3) := by dec_rfl
theorem p18_18 : ∀ feat, Dec feat p18 18 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p18_20 : ∀ feat, Dec feat p18 20 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 18446744073709551528 64)] 4) := by dec_rfl
theorem p18_24 : ∀ feat, Dec feat p18 24 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 18446744073709551476 32), gr 32 7] 6) := by dec_rfl
theorem p18_30 : ∀ feat, Dec feat p18 30 (FV7z.mk .movsxd 64 [gr 64 7, gr 32 7] 3) := by dec_rfl
theorem p18_33 : ∀ feat, Dec feat p18 33 (FV7z.mk .mov 64 [.mem (mg (some 1) none 1 0 64), gr 64 7] 3) := by dec_rfl
theorem p18_36 : ∀ feat, Dec feat p18 36 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p18_39 : ∀ feat, Dec feat p18 39 (FV7z.mk .shl 64 [gr 64 13, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p18_43 : ∀ feat, Dec feat p18 43 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551480 64), gr 64 7] 7) := by dec_rfl
theorem p18_50 : ∀ feat, Dec feat p18 50 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 13) (some 0) 1 0 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.mov 32 8 (.i 1),
  Op.mov 32 1 (.r 6),
  Op.st 64 (some 5) none 1 18446744073709551512 2,
  Op.mov 32 7 (.r 8),
  Op.st 32 (some 5) none 1 18446744073709551520 6,
  Op.shl 7 (.r 1),
  Op.ld 64 1 (some 5) none 1 18446744073709551528,
  Op.st 32 (some 5) none 1 18446744073709551476 7,
  Op.sxr 7 7,
  Op.st 64 (some 1) none 1 0 7,
  Op.mov 64 13 (.r 7),
  Op.shl64 13 (.i 4),
  Op.st 64 (some 5) none 1 18446744073709551480 7,
  Op.lea 64 7 (some 13) (some 0) 1 0]

theorem b18 (prof : Profile) : Blk prof p18 0 55 o18 :=
  .cons (p18_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p18_6 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p18_8 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p18_12 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p18_15 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p18_18 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p18_20 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p18_24 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p18_30 _) (OpI.sxr) (by decide) <|
  .cons (p18_33 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p18_36 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p18_39 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p18_43 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p18_50 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 55

/-- The stretch at `1116`. -/
def p19 : List Byte := [
  0x8b, 0x75, 0xa0, 0x48, 0x8b, 0x55, 0x98, 0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x48, 0x85, 0xc0,
  0x49, 0x89, 0xc6]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 5) none 1 18446744073709551520 32)] 3) := by dec_rfl
theorem p19_3 : ∀ feat, Dec feat p19 3 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 18446744073709551512 64)] 4) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p19_13 : ∀ feat, Dec feat p19 13 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p19_16 : ∀ feat, Dec feat p19 16 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 32 6 (some 5) none 1 18446744073709551520,
  Op.ld 64 2 (some 5) none 1 18446744073709551512,
  Op.mov 32 8 (.i 1),
  Op.test 64 0 (.r 0),
  Op.mov 64 14 (.r 0)]

theorem b19 (prof : Profile) : Blk prof p19 0 19 o19 :=
  .cons (p19_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p19_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p19_7 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p19_13 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .cons (p19_16 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 19

def j13 : List Byte := [0x0f, 0x84, 0xc9, 0x03, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 969] 6) := by dec_rfl

/-- The stretch at `1141`. -/
def p20 : List Byte := [
  0x8d, 0x46, 0xff, 0x4b, 0x8d, 0x3c, 0x2e, 0x89, 0xc1, 0x89, 0x45, 0x88, 0xb8, 0x01, 0x00, 0x00,
  0x00, 0x41, 0xd3, 0xe0, 0x89, 0xf1, 0x49, 0x89, 0x3e, 0x48, 0xd3, 0xe0, 0x49, 0x89, 0x7e, 0x10,
  0x44, 0x89, 0x45, 0x98, 0x48, 0x89, 0x45, 0x80, 0x49, 0x83, 0xfc, 0x02]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 6) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 14) (some 13) 1 0 0)] 4) := by dec_rfl
theorem p20_7 : ∀ feat, Dec feat p20 7 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p20_9 : ∀ feat, Dec feat p20 9 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 18446744073709551496 32), gr 32 0] 3) := by dec_rfl
theorem p20_12 : ∀ feat, Dec feat p20 12 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p20_17 : ∀ feat, Dec feat p20 17 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p20_20 : ∀ feat, Dec feat p20 20 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p20_22 : ∀ feat, Dec feat p20 22 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 0 64), gr 64 7] 3) := by dec_rfl
theorem p20_25 : ∀ feat, Dec feat p20 25 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p20_28 : ∀ feat, Dec feat p20 28 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 16 64), gr 64 7] 4) := by dec_rfl
theorem p20_32 : ∀ feat, Dec feat p20 32 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 18446744073709551512 32), gr 32 8] 4) := by dec_rfl
theorem p20_36 : ∀ feat, Dec feat p20 36 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551488 64), gr 64 0] 4) := by dec_rfl
theorem p20_40 : ∀ feat, Dec feat p20 40 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.lea 32 0 (some 6) none 1 18446744073709551615,
  Op.lea 64 7 (some 14) (some 13) 1 0,
  Op.mov 32 1 (.r 0),
  Op.st 32 (some 5) none 1 18446744073709551496 0,
  Op.mov 32 0 (.i 1),
  Op.shl 8 (.r 1),
  Op.mov 32 1 (.r 6),
  Op.st 64 (some 14) none 1 0 7,
  Op.shl64 0 (.r 1),
  Op.st 64 (some 14) none 1 16 7,
  Op.st 32 (some 5) none 1 18446744073709551512 8,
  Op.st 64 (some 5) none 1 18446744073709551488 0,
  Op.cmp 64 12 (.i 2)]

theorem b20 (prof : Profile) : Blk prof p20 0 44 o20 :=
  .cons (p20_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p20_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p20_9 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p20_12 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p20_17 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p20_20 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p20_22 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p20_25 _) (OpI.shl64 (.r 1)) (by decide) <|
  .cons (p20_28 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p20_32 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p20_36 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p20_40 _) (OpI.cmp (.i 2) (.inr rfl)) (by decide) <|
  .nil 44

def j14 : List Byte := [0x0f, 0x84, 0xb4, 0x03, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 4) 64 [.rel 948] 6) := by dec_rfl

/-- The stretch at `1191`. -/
def p21 : List Byte := [
  0x48, 0x8b, 0x02, 0x49, 0x8d, 0x74, 0x24, 0xfe, 0x4c, 0x63, 0x7d, 0x98, 0x4c, 0x89, 0xb5, 0x58,
  0xff, 0xff, 0xff, 0x48, 0x89, 0x75, 0xa0, 0x41, 0xbd, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45,
  0xa8, 0x48, 0x8b, 0x03, 0x4c, 0x89, 0xa5, 0x60, 0xff, 0xff, 0xff, 0x4d, 0x89, 0xfc, 0x49, 0x89,
  0xc7, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p21_3 : ∀ feat, Dec feat p21 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 12) none 1 18446744073709551614 0)] 5) := by dec_rfl
theorem p21_8 : ∀ feat, Dec feat p21 8 (FV7z.mk .movsxd 64 [gr 64 15, .mem (mg (some 5) none 1 18446744073709551512 32)] 4) := by dec_rfl
theorem p21_12 : ∀ feat, Dec feat p21 12 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551448 64), gr 64 14] 7) := by dec_rfl
theorem p21_19 : ∀ feat, Dec feat p21 19 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551520 64), gr 64 6] 4) := by dec_rfl
theorem p21_23 : ∀ feat, Dec feat p21 23 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p21_29 : ∀ feat, Dec feat p21 29 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551528 64), gr 64 0] 4) := by dec_rfl
theorem p21_33 : ∀ feat, Dec feat p21 33 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p21_36 : ∀ feat, Dec feat p21 36 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551456 64), gr 64 12] 7) := by dec_rfl
theorem p21_43 : ∀ feat, Dec feat p21 43 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p21_46 : ∀ feat, Dec feat p21 46 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p21_49 : ∀ feat, Dec feat p21 49 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.ld 64 0 (some 2) none 1 0,
  Op.lea 64 6 (some 12) none 1 18446744073709551614,
  Op.ldsx 15 (some 5) none 1 18446744073709551512,
  Op.st 64 (some 5) none 1 18446744073709551448 14,
  Op.st 64 (some 5) none 1 18446744073709551520 6,
  Op.mov 32 13 (.i 1),
  Op.st 64 (some 5) none 1 18446744073709551528 0,
  Op.ld 64 0 (some 3) none 1 0,
  Op.st 64 (some 5) none 1 18446744073709551456 12,
  Op.mov 64 12 (.r 15),
  Op.mov 64 15 (.r 0),
  Op.nop]

theorem b21 (prof : Profile) : Blk prof p21 0 57 o21 :=
  .cons (p21_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p21_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p21_8 _) (OpI.ldsx) (by decide) <|
  .cons (p21_12 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p21_19 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p21_23 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p21_29 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p21_33 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p21_36 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p21_43 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p21_46 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p21_49 _) (OpI.nop) (by decide) <|
  .nil 57

/-- The stretch at `1248`. -/
def p22 : List Byte := [
  0x48, 0x8b, 0x55, 0xb0, 0x48, 0x8b, 0x75, 0xa8, 0x49, 0x83, 0xec, 0x02]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 18446744073709551536 64)] 4) := by dec_rfl
theorem p22_4 : ∀ feat, Dec feat p22 4 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 18446744073709551528 64)] 4) := by dec_rfl
theorem p22_8 : ∀ feat, Dec feat p22 8 (FV7z.mk .sub 64 [gr 64 12, Src.opd 64 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ld 64 2 (some 5) none 1 18446744073709551536,
  Op.ld 64 6 (some 5) none 1 18446744073709551528,
  Op.sub 64 12 (.i 2)]

theorem b22 (prof : Profile) : Blk prof p22 0 12 o22 :=
  .cons (p22_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_8 _) (OpI.sub (.i 2) (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `1265`. -/
def p23 : List Byte := [
  0x4c, 0x8b, 0x75, 0xa0, 0x48, 0x89, 0xc7, 0xc6, 0x00, 0x2f, 0x48, 0x83, 0xc7, 0x01]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 5) none 1 18446744073709551520 64)] 4) := by dec_rfl
theorem p23_4 : ∀ feat, Dec feat p23 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p23_7 : ∀ feat, Dec feat p23 7 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 47] 3) := by dec_rfl
theorem p23_10 : ∀ feat, Dec feat p23 10 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.ld 64 14 (some 5) none 1 18446744073709551520,
  Op.mov 64 7 (.r 0),
  Op.sti 8 (some 0) none 1 0 47,
  Op.add 64 7 (.i 1)]

theorem b23 (prof : Profile) : Blk prof p23 0 14 o23 :=
  .cons (p23_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p23_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p23_7 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p23_10 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 14

def j15 : List Byte := [0xeb, 0x0d]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `1288`. -/
def p24 : List Byte := [
  0x49, 0x83, 0xee, 0x01]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .sub 64 [gr 64 14, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.sub 64 14 (.i 1)]

theorem b24 (prof : Profile) : Blk prof p24 0 4 o24 :=
  .cons (p24_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

def j16 : List Byte := [0x74, 0x31]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 4) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `1294`. -/
def p25 : List Byte := [
  0x44, 0x89, 0xe8, 0x44, 0x89, 0xf1, 0xd3, 0xe0, 0x48, 0x98, 0x4c, 0x85, 0xe0]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p25_3 : ∀ feat, Dec feat p25 3 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p25_6 : ∀ feat, Dec feat p25 6 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p25_8 : ∀ feat, Dec feat p25 8 (FV7z.mk .cbw 64 [] 2) := by dec_rfl
theorem p25_10 : ∀ feat, Dec feat p25 10 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 32 0 (.r 13),
  Op.mov 32 1 (.r 14),
  Op.shl 0 (.r 1),
  Op.cdqe,
  Op.test 64 0 (.r 12)]

theorem b25 (prof : Profile) : Blk prof p25 0 13 o25 :=
  .cons (p25_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p25_3 _) (OpI.mov (.r 14) (.inl rfl)) (by decide) <|
  .cons (p25_6 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p25_8 _) (OpI.cdqe) (by decide) <|
  .cons (p25_10 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 13

def j17 : List Byte := [0x74, 0xeb]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `1309`. -/
def p26 : List Byte := [
  0x4c, 0x89, 0xf0, 0x48, 0xc1, 0xe0, 0x04, 0x48, 0x8b, 0x54, 0x03, 0x08, 0x48, 0x8b, 0x34, 0x03]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p26_3 : ∀ feat, Dec feat p26 3 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p26_7 : ∀ feat, Dec feat p26 7 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) (some 0) 1 8 64)] 5) := by dec_rfl
theorem p26_12 : ∀ feat, Dec feat p26 12 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) (some 0) 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.mov 64 0 (.r 14),
  Op.shl64 0 (.i 4),
  Op.ld 64 2 (some 3) (some 0) 1 8,
  Op.ld 64 6 (some 3) (some 0) 1 0]

theorem b26 (prof : Profile) : Blk prof p26 0 16 o26 :=
  .cons (p26_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p26_3 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p26_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p26_12 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 16

/-- The stretch at `1330`. -/
def p27 : List Byte := [
  0xc6, 0x00, 0x2f, 0x48, 0x8d, 0x78, 0x01, 0x49, 0x83, 0xee, 0x01]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 47] 3) := by dec_rfl
theorem p27_3 : ∀ feat, Dec feat p27 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p27_7 : ∀ feat, Dec feat p27 7 (FV7z.mk .sub 64 [gr 64 14, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.sti 8 (some 0) none 1 0 47,
  Op.lea 64 7 (some 0) none 1 1,
  Op.sub 64 14 (.i 1)]

theorem b27 (prof : Profile) : Blk prof p27 0 11 o27 :=
  .cons (p27_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p27_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p27_7 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 11

def j18 : List Byte := [0x75, 0xcf]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551567] 2) := by dec_rfl

/-- The stretch at `1343`. -/
def p28 : List Byte := [
  0x48, 0x8b, 0x55, 0xb8, 0x4c, 0x89, 0xfe]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 18446744073709551544 64)] 4) := by dec_rfl
theorem p28_4 : ∀ feat, Dec feat p28 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.ld 64 2 (some 5) none 1 18446744073709551544,
  Op.mov 64 6 (.r 15)]

theorem b28 (prof : Profile) : Blk prof p28 0 7 o28 :=
  .cons (p28_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p28_4 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `1355`. -/
def p29 : List Byte := [
  0xc6, 0x00, 0x2f, 0x48, 0x8d, 0x78, 0x01, 0x4d, 0x85, 0xe4]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 47] 3) := by dec_rfl
theorem p29_3 : ∀ feat, Dec feat p29 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p29_7 : ∀ feat, Dec feat p29 7 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.sti 8 (some 0) none 1 0 47,
  Op.lea 64 7 (some 0) none 1 1,
  Op.test 64 12 (.r 12)]

theorem b29 (prof : Profile) : Blk prof p29 0 10 o29 :=
  .cons (p29_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p29_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p29_7 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 10

def j19 : List Byte := [0x75, 0x89]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551497] 2) := by dec_rfl

/-- The stretch at `1367`. -/
def p30 : List Byte := [
  0x4c, 0x8b, 0xa5, 0x60, 0xff, 0xff, 0xff, 0x4c, 0x8b, 0xb5, 0x58, 0xff, 0xff, 0xff]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 5) none 1 18446744073709551456 64)] 7) := by dec_rfl
theorem p30_7 : ∀ feat, Dec feat p30 7 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 5) none 1 18446744073709551448 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.ld 64 12 (some 5) none 1 18446744073709551456,
  Op.ld 64 14 (some 5) none 1 18446744073709551448]

theorem b30 (prof : Profile) : Blk prof p30 0 14 o30 :=
  .cons (p30_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p30_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `1381`. -/
def p31 : List Byte := [
  0x48, 0x8b, 0x4d, 0x80, 0x31, 0xc0, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 18446744073709551488 64)] 4) := by dec_rfl
theorem p31_4 : ∀ feat, Dec feat p31 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p31_6 : ∀ feat, Dec feat p31 6 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.ld 64 1 (some 5) none 1 18446744073709551488,
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b31 (prof : Profile) : Blk prof p31 0 11 o31 :=
  .cons (p31_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p31_6 _) (OpI.nop) (by decide) <|
  .nil 11

/-- The stretch at `1392`. -/
def p32 : List Byte := [
  0x48, 0x89, 0xc2, 0x48, 0x83, 0xc0, 0x01, 0x48, 0xc1, 0xe2, 0x04, 0x49, 0xc7, 0x44, 0x16, 0x08,
  0x00, 0x00, 0x00, 0x00, 0x48, 0x39, 0xc8]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p32_3 : ∀ feat, Dec feat p32 3 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p32_7 : ∀ feat, Dec feat p32 7 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p32_11 : ∀ feat, Dec feat p32 11 (FV7z.mk .mov 64 [.mem (mg (some 14) (some 2) 1 8 64), .imm 64 0] 9) := by dec_rfl
theorem p32_20 : ∀ feat, Dec feat p32 20 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.mov 64 2 (.r 0),
  Op.add 64 0 (.i 1),
  Op.shl64 2 (.i 4),
  Op.sti 64 (some 14) (some 2) 1 8 0,
  Op.cmp 64 0 (.r 1)]

theorem b32 (prof : Profile) : Blk prof p32 0 23 o32 :=
  .cons (p32_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p32_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p32_7 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p32_11 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p32_20 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 23

def j20 : List Byte := [0x72, 0xe7]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551591] 2) := by dec_rfl

/-- The stretch at `1417`. -/
def p33 : List Byte := [
  0x4c, 0x8b, 0x95, 0x78, 0xff, 0xff, 0xff, 0x4d, 0x85, 0xd2]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 64 [gr 64 10, .mem (mg (some 5) none 1 18446744073709551480 64)] 7) := by dec_rfl
theorem p33_7 : ∀ feat, Dec feat p33 7 (FV7z.mk .test 64 [gr 64 10, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.ld 64 10 (some 5) none 1 18446744073709551480,
  Op.test 64 10 (.r 10)]

theorem b33 (prof : Profile) : Blk prof p33 0 10 o33 :=
  .cons (p33_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p33_7 _) (OpI.test (.r 10) (.inr rfl)) (by decide) <|
  .nil 10

def j21 : List Byte := [0x74, 0x5d]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 4) 64 [.rel 93] 2) := by dec_rfl

/-- The stretch at `1429`. -/
def p34 : List Byte := [
  0x48, 0x03, 0x9d, 0x68, 0xff, 0xff, 0xff, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe1, 0x0f,
  0x1f, 0x40, 0x00]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .add 64 [gr 64 3, .mem (mg (some 5) none 1 18446744073709551464 64)] 7) := by dec_rfl
theorem p34_7 : ∀ feat, Dec feat p34 7 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p34_12 : ∀ feat, Dec feat p34 12 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p34_15 : ∀ feat, Dec feat p34 15 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.addm 64 3 (some 5) none 1 18446744073709551464,
  Op.mov 32 7 (.i 1),
  Op.mov 64 1 (.r 12),
  Op.nop]

theorem b34 (prof : Profile) : Blk prof p34 0 19 o34 :=
  .cons (p34_0 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p34_7 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p34_12 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p34_15 _) (OpI.nop) (by decide) <|
  .nil 19

/-- The stretch at `1448`. -/
def p35 : List Byte := [
  0x48, 0x83, 0xe9, 0x01, 0x89, 0xfe, 0x4c, 0x89, 0xf2, 0x4c, 0x89, 0xd0, 0xd3, 0xe6, 0x48, 0x63,
  0xf6]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p35_4 : ∀ feat, Dec feat p35 4 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p35_6 : ∀ feat, Dec feat p35 6 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p35_9 : ∀ feat, Dec feat p35 9 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p35_12 : ∀ feat, Dec feat p35 12 (FV7z.mk .shl 32 [gr 32 6, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p35_14 : ∀ feat, Dec feat p35 14 (FV7z.mk .movsxd 64 [gr 64 6, gr 32 6] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.sub 64 1 (.i 1),
  Op.mov 32 6 (.r 7),
  Op.mov 64 2 (.r 14),
  Op.mov 64 0 (.r 10),
  Op.shl 6 (.r 1),
  Op.sxr 6 6]

theorem b35 (prof : Profile) : Blk prof p35 0 17 o35 :=
  .cons (p35_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p35_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p35_6 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p35_9 _) (OpI.mov (.r 10) (.inr rfl)) (by decide) <|
  .cons (p35_12 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p35_14 _) (OpI.sxr) (by decide) <|
  .nil 17

/-- The stretch at `1465`. -/
def p36 : List Byte := [
  0x48, 0x83, 0xe8, 0x01, 0x48, 0x83, 0xc2, 0x10, 0x48, 0x85, 0xc6]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p36_4 : ∀ feat, Dec feat p36 4 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p36_8 : ∀ feat, Dec feat p36 8 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.sub 64 0 (.i 1),
  Op.add 64 2 (.i 16),
  Op.test 64 6 (.r 0)]

theorem b36 (prof : Profile) : Blk prof p36 0 11 o36 :=
  .cons (p36_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p36_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p36_8 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 11

def j22 : List Byte := [0x74, 0x1e]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 4) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `1478`. -/
def p37 : List Byte := [
  0x4c, 0x8b, 0x4a, 0xf8, 0x4c, 0x8b, 0x43, 0xf8, 0x48, 0x83, 0xe8, 0x01, 0x48, 0x83, 0xc2, 0x10,
  0x4f, 0x8d, 0x44, 0x01, 0x01, 0x4c, 0x89, 0x42, 0xe8, 0x48, 0x85, 0xc6]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .mov 64 [gr 64 9, .mem (mg (some 2) none 1 18446744073709551608 64)] 4) := by dec_rfl
theorem p37_4 : ∀ feat, Dec feat p37 4 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 3) none 1 18446744073709551608 64)] 4) := by dec_rfl
theorem p37_8 : ∀ feat, Dec feat p37 8 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p37_12 : ∀ feat, Dec feat p37 12 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p37_16 : ∀ feat, Dec feat p37 16 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 9) (some 8) 1 1 0)] 5) := by dec_rfl
theorem p37_21 : ∀ feat, Dec feat p37 21 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 18446744073709551592 64), gr 64 8] 4) := by dec_rfl
theorem p37_25 : ∀ feat, Dec feat p37 25 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.ld 64 9 (some 2) none 1 18446744073709551608,
  Op.ld 64 8 (some 3) none 1 18446744073709551608,
  Op.sub 64 0 (.i 1),
  Op.add 64 2 (.i 16),
  Op.lea 64 8 (some 9) (some 8) 1 1,
  Op.st 64 (some 2) none 1 18446744073709551592 8,
  Op.test 64 6 (.r 0)]

theorem b37 (prof : Profile) : Blk prof p37 0 28 o37 :=
  .cons (p37_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p37_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p37_8 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p37_12 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p37_16 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p37_21 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p37_25 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 28

def j23 : List Byte := [0x75, 0xe2]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551586] 2) := by dec_rfl

/-- The stretch at `1508`. -/
def p38 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b38 (prof : Profile) : Blk prof p38 0 3 o38 :=
  .cons (p38_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j24 : List Byte := [0x75, 0xd0]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551568] 2) := by dec_rfl

/-- The stretch at `1513`. -/
def p39 : List Byte := [
  0x48, 0x83, 0xeb, 0x10, 0x48, 0x85, 0xc9]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p39_4 : ∀ feat, Dec feat p39 4 (FV7z.mk .test 64 [gr 64 1, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.sub 64 3 (.i 16),
  Op.test 64 1 (.r 1)]

theorem b39 (prof : Profile) : Blk prof p39 0 7 o39 :=
  .cons (p39_0 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
  .cons (p39_4 _) (OpI.test (.r 1) (.inr rfl)) (by decide) <|
  .nil 7

def j25 : List Byte := [0x75, 0xb6]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551542] 2) := by dec_rfl

/-- The stretch at `1522`. -/
def p40 : List Byte := [
  0x44, 0x8b, 0x85, 0x74, 0xff, 0xff, 0xff, 0x0f, 0xb6, 0x4d, 0x88, 0xb8, 0x01, 0x00, 0x00, 0x00,
  0x49, 0x8d, 0x76, 0x20, 0x41, 0x83, 0xe8, 0x02, 0x48, 0xd3, 0xe0, 0x4d, 0x63, 0xc0, 0x48, 0x89,
  0xc1, 0x49, 0x39, 0xc0]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .mov 32 [gr 32 8, .mem (mg (some 5) none 1 18446744073709551476 32)] 7) := by dec_rfl
theorem p40_7 : ∀ feat, Dec feat p40 7 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 5) none 1 18446744073709551496 8)] 4) := by dec_rfl
theorem p40_11 : ∀ feat, Dec feat p40 11 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p40_16 : ∀ feat, Dec feat p40 16 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 14) none 1 32 0)] 4) := by dec_rfl
theorem p40_20 : ∀ feat, Dec feat p40 20 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.i 2)] 4) := by dec_rfl
theorem p40_24 : ∀ feat, Dec feat p40 24 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p40_27 : ∀ feat, Dec feat p40 27 (FV7z.mk .movsxd 64 [gr 64 8, gr 32 8] 3) := by dec_rfl
theorem p40_30 : ∀ feat, Dec feat p40 30 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p40_33 : ∀ feat, Dec feat p40 33 (FV7z.mk .cmp 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.ld 32 8 (some 5) none 1 18446744073709551476,
  Op.ldzx 8 1 (some 5) none 1 18446744073709551496,
  Op.mov 32 0 (.i 1),
  Op.lea 64 6 (some 14) none 1 32,
  Op.sub 32 8 (.i 2),
  Op.shl64 0 (.r 1),
  Op.sxr 8 8,
  Op.mov 64 1 (.r 0),
  Op.cmp 64 8 (.r 0)]

theorem b40 (prof : Profile) : Blk prof p40 0 36 o40 :=
  .cons (p40_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p40_7 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p40_11 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p40_16 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p40_20 _) (OpI.sub (.i 2) (.inl rfl)) (by decide) <|
  .cons (p40_24 _) (OpI.shl64 (.r 1)) (by decide) <|
  .cons (p40_27 _) (OpI.sxr) (by decide) <|
  .cons (p40_30 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p40_33 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 36

def j26 : List Byte := [0x74, 0x34]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 4) 64 [.rel 52] 2) := by dec_rfl

/-- The stretch at `1560`. -/
def p41 : List Byte := [
  0x48, 0x89, 0xf0, 0x4c, 0x89, 0xc2, 0x66, 0x90]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p41_3 : ∀ feat, Dec feat p41 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p41_6 : ∀ feat, Dec feat p41 6 (FV7z.mk .nop 16 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.mov 64 0 (.r 6),
  Op.mov 64 2 (.r 8),
  Op.nop]

theorem b41 (prof : Profile) : Blk prof p41 0 8 o41 :=
  .cons (p41_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p41_3 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p41_6 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `1568`. -/
def p42 : List Byte := [
  0x48, 0x83, 0xea, 0x01, 0xf6, 0xc2, 0x01]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p42_4 : ∀ feat, Dec feat p42 4 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.sub 64 2 (.i 1),
  Op.test 8 2 (.i 1)]

theorem b42 (prof : Profile) : Blk prof p42 0 7 o42 :=
  .cons (p42_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p42_4 _) (OpI.test8 (.i 1)) (by decide) <|
  .nil 7

def j27 : List Byte := [0x0f, 0x84, 0xcb, 0x01, 0x00, 0x00]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 4) 64 [.rel 459] 6) := by dec_rfl

/-- The stretch at `1581`. -/
def p43 : List Byte := [
  0x48, 0x8b, 0x78, 0xe8, 0x48, 0x03, 0x78, 0xe0, 0x48, 0x83, 0xc0, 0x10, 0x48, 0x89, 0x78, 0xf0,
  0x48, 0x39, 0xca]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 18446744073709551592 64)] 4) := by dec_rfl
theorem p43_4 : ∀ feat, Dec feat p43 4 (FV7z.mk .add 64 [gr 64 7, .mem (mg (some 0) none 1 18446744073709551584 64)] 4) := by dec_rfl
theorem p43_8 : ∀ feat, Dec feat p43 8 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p43_12 : ∀ feat, Dec feat p43 12 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 18446744073709551600 64), gr 64 7] 4) := by dec_rfl
theorem p43_16 : ∀ feat, Dec feat p43 16 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.ld 64 7 (some 0) none 1 18446744073709551592,
  Op.addm 64 7 (some 0) none 1 18446744073709551584,
  Op.add 64 0 (.i 16),
  Op.st 64 (some 0) none 1 18446744073709551600 7,
  Op.cmp 64 2 (.r 1)]

theorem b43 (prof : Profile) : Blk prof p43 0 19 o43 :=
  .cons (p43_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p43_4 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p43_8 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p43_12 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p43_16 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 19

def j28 : List Byte := [0x75, 0xde]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551582] 2) := by dec_rfl

/-- The stretch at `1602`. -/
def p44 : List Byte := [
  0x49, 0x29, 0xc8, 0x49, 0xc1, 0xe0, 0x04, 0x4c, 0x01, 0xc6]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .sub 64 [gr 64 8, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p44_3 : ∀ feat, Dec feat p44 3 (FV7z.mk .shl 64 [gr 64 8, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p44_7 : ∀ feat, Dec feat p44 7 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.sub 64 8 (.r 1),
  Op.shl64 8 (.i 4),
  Op.add 64 6 (.r 8)]

theorem b44 (prof : Profile) : Blk prof p44 0 10 o44 :=
  .cons (p44_0 _) (OpI.sub (.r 1) (.inr rfl)) (by decide) <|
  .cons (p44_3 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p44_7 _) (OpI.add (.r 8) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `1612`. -/
def p45 : List Byte := [
  0x8b, 0x55, 0x98, 0x48, 0x8b, 0x7d, 0xb0, 0xf7, 0xda, 0x48, 0x83, 0xc7, 0x01, 0x48, 0x63, 0xd2,
  0x48, 0xc1, 0xe2, 0x04]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 5) none 1 18446744073709551512 32)] 3) := by dec_rfl
theorem p45_3 : ∀ feat, Dec feat p45 3 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 18446744073709551536 64)] 4) := by dec_rfl
theorem p45_7 : ∀ feat, Dec feat p45 7 (FV7z.mk .neg 32 [gr 32 2] 2) := by dec_rfl
theorem p45_9 : ∀ feat, Dec feat p45 9 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p45_13 : ∀ feat, Dec feat p45 13 (FV7z.mk .movsxd 64 [gr 64 2, gr 32 2] 3) := by dec_rfl
theorem p45_16 : ∀ feat, Dec feat p45 16 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 4)] 4) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.ld 32 2 (some 5) none 1 18446744073709551512,
  Op.ld 64 7 (some 5) none 1 18446744073709551536,
  Op.neg 32 2,
  Op.add 64 7 (.i 1),
  Op.sxr 2 2,
  Op.shl64 2 (.i 4)]

theorem b45 (prof : Profile) : Blk prof p45 0 20 o45 :=
  .cons (p45_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p45_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p45_7 _) (OpI.neg (.inl rfl)) (by decide) <|
  .cons (p45_9 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p45_13 _) (OpI.sxr) (by decide) <|
  .cons (p45_16 _) (OpI.shl64 (.i 4)) (by decide) <|
  .nil 20

/-- The stretch at `1632`. -/
def p46 : List Byte := [
  0x48, 0x8b, 0x04, 0x16, 0x48, 0x83, 0xc6, 0x10, 0x48, 0x01, 0xf8, 0x48, 0x89, 0x46, 0xf0, 0x48,
  0x83, 0xe9, 0x01]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) (some 2) 1 0 64)] 4) := by dec_rfl
theorem p46_4 : ∀ feat, Dec feat p46 4 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p46_8 : ∀ feat, Dec feat p46 8 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p46_11 : ∀ feat, Dec feat p46 11 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 18446744073709551600 64), gr 64 0] 4) := by dec_rfl
theorem p46_15 : ∀ feat, Dec feat p46 15 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.ld 64 0 (some 6) (some 2) 1 0,
  Op.add 64 6 (.i 16),
  Op.add 64 0 (.r 7),
  Op.st 64 (some 6) none 1 18446744073709551600 0,
  Op.sub 64 1 (.i 1)]

theorem b46 (prof : Profile) : Blk prof p46 0 19 o46 :=
  .cons (p46_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p46_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p46_8 _) (OpI.add (.r 7) (.inr rfl)) (by decide) <|
  .cons (p46_11 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p46_15 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 19

def j29 : List Byte := [0x75, 0xeb]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `1653`. -/
def p47 : List Byte := [
  0x49, 0x8b, 0x46, 0x08, 0x48, 0x8b, 0x5d, 0x90, 0x48, 0x89, 0x03]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 8 64)] 4) := by dec_rfl
theorem p47_4 : ∀ feat, Dec feat p47 4 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 5) none 1 18446744073709551504 64)] 4) := by dec_rfl
theorem p47_8 : ∀ feat, Dec feat p47 8 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.ld 64 0 (some 14) none 1 8,
  Op.ld 64 3 (some 5) none 1 18446744073709551504,
  Op.st 64 (some 3) none 1 0 0]

theorem b47 (prof : Profile) : Blk prof p47 0 11 o47 :=
  .cons (p47_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p47_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p47_8 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 11

/-- The stretch at `1664`. -/
def p48 : List Byte := [
  0x48, 0x8d, 0x65, 0xd8, 0x4c, 0x89, 0xf0, 0x5b, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f,
  0x5d]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .lea 64 [gr 64 4, .mem (mg (some 5) none 1 18446744073709551576 0)] 4) := by dec_rfl
theorem p48_4 : ∀ feat, Dec feat p48 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p48_7 : ∀ feat, Dec feat p48 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p48_8 : ∀ feat, Dec feat p48 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p48_10 : ∀ feat, Dec feat p48 10 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p48_12 : ∀ feat, Dec feat p48 12 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p48_14 : ∀ feat, Dec feat p48 14 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl
theorem p48_16 : ∀ feat, Dec feat p48 16 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.lea 64 4 (some 5) none 1 18446744073709551576,
  Op.mov 64 0 (.r 14),
  Op.pop 3,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15,
  Op.pop 5]

theorem b48 (prof : Profile) : Blk prof p48 0 17 o48 :=
  .cons (p48_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p48_4 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p48_7 _) (OpI.pop) (by decide) <|
  .cons (p48_8 _) (OpI.pop) (by decide) <|
  .cons (p48_10 _) (OpI.pop) (by decide) <|
  .cons (p48_12 _) (OpI.pop) (by decide) <|
  .cons (p48_14 _) (OpI.pop) (by decide) <|
  .cons (p48_16 _) (OpI.pop) (by decide) <|
  .nil 17

/-- The stretch at `1759`. -/
def p49 : List Byte := [
  0x25, 0xff, 0x0f, 0x00, 0x00, 0x48, 0x29, 0xc4, 0x48, 0x85, 0xc0]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4095)] 5) := by dec_rfl
theorem p49_5 : ∀ feat, Dec feat p49 5 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p49_8 : ∀ feat, Dec feat p49 8 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.and 32 0 (.i 4095),
  Op.sub 64 4 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b49 (prof : Profile) : Blk prof p49 0 11 o49 :=
  .cons (p49_0 _) (OpI.and (.i 4095) (.inl rfl)) (by decide) <|
  .cons (p49_5 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .cons (p49_8 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 11

def j30 : List Byte := [0x74, 0x06]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `1778`. -/
def p50 : List Byte := [
  0x48, 0x8d, 0x44, 0x24, 0x0f, 0xb9, 0x01, 0x00, 0x00, 0x00, 0x45, 0x31, 0xed, 0x48, 0x83, 0xe0,
  0xf0, 0x48, 0x89, 0xc3]

theorem p50_0 : ∀ feat, Dec feat p50 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 4) none 1 15 0)] 5) := by dec_rfl
theorem p50_5 : ∀ feat, Dec feat p50 5 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p50_10 : ∀ feat, Dec feat p50 10 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p50_13 : ∀ feat, Dec feat p50 13 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551600)] 4) := by dec_rfl
theorem p50_17 : ∀ feat, Dec feat p50 17 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o50 : List Op := [
  Op.lea 64 0 (some 4) none 1 15,
  Op.mov 32 1 (.i 1),
  Op.xor 32 13 (.r 13),
  Op.and 64 0 (.i 18446744073709551600),
  Op.mov 64 3 (.r 0)]

theorem b50 (prof : Profile) : Blk prof p50 0 20 o50 :=
  .cons (p50_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p50_5 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p50_10 _) (OpI.xor (.r 13) (.inl rfl)) (by decide) <|
  .cons (p50_13 _) (OpI.and (.i 18446744073709551600) (.inr rfl)) (by decide) <|
  .cons (p50_17 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `1798`. -/
def p51 : List Byte := [
  0x4d, 0x85, 0xc0]

theorem p51_0 : ∀ feat, Dec feat p51 0 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o51 : List Op := [
  Op.test 64 8 (.r 8)]

theorem b51 (prof : Profile) : Blk prof p51 0 3 o51 :=
  .cons (p51_0 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j31 : List Byte := [0x0f, 0x84, 0x9b, 0xfb, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709550491] 6) := by dec_rfl

/-- The stretch at `1807`. -/
def p52 : List Byte := [
  0x4d, 0x8d, 0x75, 0x01, 0x4c, 0x89, 0x65, 0x88, 0x48, 0x89, 0xda, 0x45, 0x31, 0xff, 0x4c, 0x89,
  0xf0, 0x4c, 0x89, 0xeb, 0x4d, 0x89, 0xc6, 0x49, 0x89, 0xc0, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00,
  0x00]

theorem p52_0 : ∀ feat, Dec feat p52 0 (FV7z.mk .lea 64 [gr 64 14, .mem (mg (some 13) none 1 1 0)] 4) := by dec_rfl
theorem p52_4 : ∀ feat, Dec feat p52 4 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551496 64), gr 64 12] 4) := by dec_rfl
theorem p52_8 : ∀ feat, Dec feat p52 8 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p52_11 : ∀ feat, Dec feat p52 11 (FV7z.mk .xor 32 [gr 32 15, Src.opd 32 (.r 15)] 3) := by dec_rfl
theorem p52_14 : ∀ feat, Dec feat p52 14 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p52_17 : ∀ feat, Dec feat p52 17 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p52_20 : ∀ feat, Dec feat p52 20 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p52_23 : ∀ feat, Dec feat p52 23 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p52_26 : ∀ feat, Dec feat p52 26 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o52 : List Op := [
  Op.lea 64 14 (some 13) none 1 1,
  Op.st 64 (some 5) none 1 18446744073709551496 12,
  Op.mov 64 2 (.r 3),
  Op.xor 32 15 (.r 15),
  Op.mov 64 0 (.r 14),
  Op.mov 64 3 (.r 13),
  Op.mov 64 14 (.r 8),
  Op.mov 64 8 (.r 0),
  Op.nop]

theorem b52 (prof : Profile) : Blk prof p52 0 33 o52 :=
  .cons (p52_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p52_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p52_8 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p52_11 _) (OpI.xor (.r 15) (.inl rfl)) (by decide) <|
  .cons (p52_14 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p52_17 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p52_20 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p52_23 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p52_26 _) (OpI.nop) (by decide) <|
  .nil 33

/-- The stretch at `1840`. -/
def p53 : List Byte := [
  0x49, 0x89, 0xdd, 0x49, 0xc1, 0xe5, 0x04, 0x4d, 0x0f, 0xa3, 0xfe, 0x4e, 0x8d, 0x24, 0x2a]

theorem p53_0 : ∀ feat, Dec feat p53 0 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p53_3 : ∀ feat, Dec feat p53 3 (FV7z.mk .shl 64 [gr 64 13, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p53_7 : ∀ feat, Dec feat p53 7 (FV7z.mk (.bit (BitMn.bt)) 64 [gr 64 14, gr 64 15] 4) := by dec_rfl
theorem p53_11 : ∀ feat, Dec feat p53 11 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 2) (some 13) 1 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o53 : List Op := [
  Op.mov 64 13 (.r 3),
  Op.shl64 13 (.i 4),
  Op.bt64 14 15,
  Op.lea 64 12 (some 2) (some 13) 1 0]

theorem b53 (prof : Profile) : Blk prof p53 0 15 o53 :=
  .cons (p53_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p53_3 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p53_7 _) (OpI.bt64) (by decide) <|
  .cons (p53_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 15

def j32 : List Byte := [0x0f, 0x83, 0xa3, 0x00, 0x00, 0x00]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk (.jcc 3) 64 [.rel 163] 6) := by dec_rfl

/-- The stretch at `1861`. -/
def p54 : List Byte := [
  0x49, 0x63, 0xc7, 0x4c, 0x89, 0x45, 0xb0, 0x48, 0x8d, 0x3c, 0xc0, 0x48, 0x8d, 0x05, 0xd9, 0x5f,
  0x04, 0x00, 0x48, 0x89, 0x55, 0xb8, 0x48, 0x01, 0xc7, 0x49, 0x89, 0x3c, 0x24]

theorem p54_0 : ∀ feat, Dec feat p54 0 (FV7z.mk .movsxd 64 [gr 64 0, gr 32 15] 3) := by dec_rfl
theorem p54_3 : ∀ feat, Dec feat p54 3 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551536 64), gr 64 8] 4) := by dec_rfl
theorem p54_7 : ∀ feat, Dec feat p54 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 0) (some 0) 8 0 0)] 4) := by dec_rfl
theorem p54_11 : ∀ feat, Dec feat p54 11 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 286681 0)] 7) := by dec_rfl
theorem p54_18 : ∀ feat, Dec feat p54 18 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551544 64), gr 64 2] 4) := by dec_rfl
theorem p54_22 : ∀ feat, Dec feat p54 22 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p54_25 : ∀ feat, Dec feat p54 25 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 0 64), gr 64 7] 4) := by dec_rfl

/-- What the stretch does. -/
def o54 : List Op := [
  Op.sxr 0 15,
  Op.st 64 (some 5) none 1 18446744073709551536 8,
  Op.lea 64 7 (some 0) (some 0) 8 0,
  Op.mov 64 0 (.i 7288944),
  Op.st 64 (some 5) none 1 18446744073709551544 2,
  Op.add 64 7 (.r 0),
  Op.st 64 (some 12) none 1 0 7]

theorem b54 (prof : Profile) : BlkA prof p54 (0x6ad885 : Addr) 0 29 o54 :=
  .cons (p54_0 _) ((OpI.sxr).at _) (by decide) <|
  .cons (p54_3 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p54_7 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p54_11 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p54_18 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p54_22 _) ((OpI.add (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p54_25 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 29

/-- The stretch at `1895`. -/
def p55 : List Byte := [
  0x44, 0x89, 0xf9, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xf7, 0x48, 0xd3, 0xe6, 0x48, 0x8b,
  0x55, 0xb8, 0x49, 0x83, 0xc7, 0x01, 0x49, 0x89, 0x44, 0x24, 0x08, 0x48, 0x31, 0xf7, 0x49, 0x39,
  0xf6, 0x4c, 0x8b, 0x45, 0xb0, 0x48, 0x8d, 0x4b, 0x02, 0x4a, 0x8d, 0x44, 0x2a, 0x10]

theorem p55_0 : ∀ feat, Dec feat p55 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 15)] 3) := by dec_rfl
theorem p55_3 : ∀ feat, Dec feat p55 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p55_8 : ∀ feat, Dec feat p55 8 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p55_11 : ∀ feat, Dec feat p55 11 (FV7z.mk .shl 64 [gr 64 6, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p55_14 : ∀ feat, Dec feat p55 14 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 18446744073709551544 64)] 4) := by dec_rfl
theorem p55_18 : ∀ feat, Dec feat p55 18 (FV7z.mk .add 64 [gr 64 15, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p55_22 : ∀ feat, Dec feat p55 22 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p55_27 : ∀ feat, Dec feat p55 27 (FV7z.mk .xor 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p55_30 : ∀ feat, Dec feat p55 30 (FV7z.mk .cmp 64 [gr 64 14, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p55_33 : ∀ feat, Dec feat p55 33 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 5) none 1 18446744073709551536 64)] 4) := by dec_rfl
theorem p55_37 : ∀ feat, Dec feat p55 37 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 3) none 1 2 0)] 4) := by dec_rfl
theorem p55_41 : ∀ feat, Dec feat p55 41 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) (some 13) 1 16 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o55 : List Op := [
  Op.mov 32 1 (.r 15),
  Op.mov 32 6 (.i 1),
  Op.mov 64 7 (.r 14),
  Op.shl64 6 (.r 1),
  Op.ld 64 2 (some 5) none 1 18446744073709551544,
  Op.add 64 15 (.i 1),
  Op.st 64 (some 12) none 1 8 0,
  Op.xor 64 7 (.r 6),
  Op.cmp 64 14 (.r 6),
  Op.ld 64 8 (some 5) none 1 18446744073709551536,
  Op.lea 64 1 (some 3) none 1 2,
  Op.lea 64 0 (some 2) (some 13) 1 16]

theorem b55 (prof : Profile) : Blk prof p55 0 46 o55 :=
  .cons (p55_0 _) (OpI.mov (.r 15) (.inl rfl)) (by decide) <|
  .cons (p55_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p55_8 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p55_11 _) (OpI.shl64 (.r 1)) (by decide) <|
  .cons (p55_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p55_18 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p55_22 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p55_27 _) (OpI.xor (.r 6) (.inr rfl)) (by decide) <|
  .cons (p55_30 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .cons (p55_33 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p55_37 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p55_41 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 46

def j33 : List Byte := [0x74, 0x7b]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk (.jcc 4) 64 [.rel 123] 2) := by dec_rfl

/-- The stretch at `1943`. -/
def p56 : List Byte := [
  0x4c, 0x89, 0xc3, 0x49, 0x89, 0xfe, 0x49, 0x83, 0xc0, 0x01]

theorem p56_0 : ∀ feat, Dec feat p56 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p56_3 : ∀ feat, Dec feat p56 3 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p56_6 : ∀ feat, Dec feat p56 6 (FV7z.mk .add 64 [gr 64 8, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o56 : List Op := [
  Op.mov 64 3 (.r 8),
  Op.mov 64 14 (.r 7),
  Op.add 64 8 (.i 1)]

theorem b56 (prof : Profile) : Blk prof p56 0 10 o56 :=
  .cons (p56_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p56_3 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p56_6 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 10

def j34 : List Byte := [0xeb, 0x8d]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk .jmp 64 [.rel 18446744073709551501] 2) := by dec_rfl

/-- The stretch at `1955`. -/
def p57 : List Byte := [
  0x4c, 0x89, 0xe0, 0x48, 0x89, 0xe3, 0x48, 0xc1, 0xe0, 0x04, 0x48, 0x83, 0xc0, 0x10, 0x48, 0x89,
  0xc2, 0x48, 0x81, 0xe2, 0x00, 0xf0, 0xff, 0xff, 0x48, 0x29, 0xd3, 0x48, 0x89, 0xda, 0x48, 0x39,
  0xd4]

theorem p57_0 : ∀ feat, Dec feat p57 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p57_3 : ∀ feat, Dec feat p57 3 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p57_6 : ∀ feat, Dec feat p57 6 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p57_10 : ∀ feat, Dec feat p57 10 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p57_14 : ∀ feat, Dec feat p57 14 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p57_17 : ∀ feat, Dec feat p57 17 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.i 18446744073709547520)] 7) := by dec_rfl
theorem p57_24 : ∀ feat, Dec feat p57 24 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p57_27 : ∀ feat, Dec feat p57 27 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p57_30 : ∀ feat, Dec feat p57 30 (FV7z.mk .cmp 64 [gr 64 4, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o57 : List Op := [
  Op.mov 64 0 (.r 12),
  Op.mov 64 3 (.r 4),
  Op.shl64 0 (.i 4),
  Op.add 64 0 (.i 16),
  Op.mov 64 2 (.r 0),
  Op.and 64 2 (.i 18446744073709547520),
  Op.sub 64 3 (.r 2),
  Op.mov 64 2 (.r 3),
  Op.cmp 64 4 (.r 2)]

theorem b57 (prof : Profile) : Blk prof p57 0 33 o57 :=
  .cons (p57_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p57_3 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p57_6 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p57_10 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p57_14 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p57_17 _) (OpI.and (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .cons (p57_24 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p57_27 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p57_30 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 33

def j35 : List Byte := [0x0f, 0x84, 0x15, 0xff, 0xff, 0xff]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551381] 6) := by dec_rfl

/-- The stretch at `2024`. -/
def p58 : List Byte := [
  0x49, 0x83, 0xc7, 0x01]

theorem p58_0 : ∀ feat, Dec feat p58 0 (FV7z.mk .add 64 [gr 64 15, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o58 : List Op := [
  Op.add 64 15 (.i 1)]

theorem b58 (prof : Profile) : Blk prof p58 0 4 o58 :=
  .cons (p58_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

def j36 : List Byte := [0xe9, 0x3f, 0xff, 0xff, 0xff]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk .jmp 64 [.rel 18446744073709551423] 5) := by dec_rfl

/-- The stretch at `2040`. -/
def p59 : List Byte := [
  0x48, 0x8b, 0x78, 0xf0, 0x48, 0x83, 0xc0, 0x10, 0x48, 0x89, 0x78, 0xf0, 0x48, 0x39, 0xca]

theorem p59_0 : ∀ feat, Dec feat p59 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 18446744073709551600 64)] 4) := by dec_rfl
theorem p59_4 : ∀ feat, Dec feat p59 4 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p59_8 : ∀ feat, Dec feat p59 8 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 18446744073709551600 64), gr 64 7] 4) := by dec_rfl
theorem p59_12 : ∀ feat, Dec feat p59 12 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o59 : List Op := [
  Op.ld 64 7 (some 0) none 1 18446744073709551600,
  Op.add 64 0 (.i 16),
  Op.st 64 (some 0) none 1 18446744073709551600 7,
  Op.cmp 64 2 (.r 1)]

theorem b59 (prof : Profile) : Blk prof p59 0 15 o59 :=
  .cons (p59_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p59_4 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p59_8 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p59_12 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 15

def j37 : List Byte := [0x0f, 0x85, 0x13, 0xfe, 0xff, 0xff]
theorem j37_0 : ∀ feat, Dec feat j37 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551123] 6) := by dec_rfl

def j38 : List Byte := [0xe9, 0x30, 0xfe, 0xff, 0xff]
theorem j38_0 : ∀ feat, Dec feat j38 0 (FV7z.mk .jmp 64 [.rel 18446744073709551152] 5) := by dec_rfl

/-- The stretch at `2066`. -/
def p60 : List Byte := [
  0x4c, 0x8b, 0x65, 0x88, 0x48, 0x89, 0xd3]

theorem p60_0 : ∀ feat, Dec feat p60 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 5) none 1 18446744073709551496 64)] 4) := by dec_rfl
theorem p60_4 : ∀ feat, Dec feat p60 4 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o60 : List Op := [
  Op.ld 64 12 (some 5) none 1 18446744073709551496,
  Op.mov 64 3 (.r 2)]

theorem b60 (prof : Profile) : Blk prof p60 0 7 o60 :=
  .cons (p60_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p60_4 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j39 : List Byte := [0xe9, 0x8c, 0xfa, 0xff, 0xff]
theorem j39_0 : ∀ feat, Dec feat j39 0 (FV7z.mk .jmp 64 [.rel 18446744073709550220] 5) := by dec_rfl

/-- The stretch at `2244`. -/
def p61 : List Byte := [
  0x49, 0x83, 0xfc, 0x03]

theorem p61_0 : ∀ feat, Dec feat p61 0 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o61 : List Op := [
  Op.cmp 64 12 (.i 3)]

theorem b61 (prof : Profile) : Blk prof p61 0 4 o61 :=
  .cons (p61_0 _) (OpI.cmp (.i 3) (.inr rfl)) (by decide) <|
  .nil 4

def j40 : List Byte := [0x0f, 0x85, 0x24, 0xfb, 0xff, 0xff]
theorem j40_0 : ∀ feat, Dec feat j40 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709550372] 6) := by dec_rfl

/-- The stretch at `2254`. -/
def p62 : List Byte := [
  0xbe, 0x03, 0x00, 0x00, 0x00]

theorem p62_0 : ∀ feat, Dec feat p62 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 3)] 5) := by dec_rfl

/-- What the stretch does. -/
def o62 : List Op := [
  Op.mov 32 6 (.i 3)]

theorem b62 (prof : Profile) : Blk prof p62 0 5 o62 :=
  .cons (p62_0 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .nil 5

def j41 : List Byte := [0xe9, 0x42, 0xfb, 0xff, 0xff]
theorem j41_0 : ∀ feat, Dec feat j41 0 (FV7z.mk .jmp 64 [.rel 18446744073709550402] 5) := by dec_rfl

/-- The stretch at `2286`. -/
def p63 : List Byte := [
  0xbe, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x02, 0x00, 0x00, 0x00]

theorem p63_0 : ∀ feat, Dec feat p63 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p63_5 : ∀ feat, Dec feat p63 5 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o63 : List Op := [
  Op.mov 32 6 (.i 1),
  Op.mov 32 7 (.i 2)]

theorem b63 (prof : Profile) : Blk prof p63 0 10 o63 :=
  .cons (p63_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p63_5 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 10

def j42 : List Byte := [0xe9, 0x9b, 0xfa, 0xff, 0xff]
theorem j42_0 : ∀ feat, Dec feat j42 0 (FV7z.mk .jmp 64 [.rel 18446744073709550235] 5) := by dec_rfl

end FV7z.Hwc
