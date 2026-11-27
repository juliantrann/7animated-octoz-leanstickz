import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps26
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps4
/-!
# The stretches of straight-line code of `____strtoul_l_internal` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 55 of them) and each distinct jump (`j*`, 49) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Stl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x45, 0x31, 0xf6, 0x41, 0x55, 0x49, 0x89, 0xfd,
  0x41, 0x54, 0x45, 0x31, 0xe4, 0x55, 0x53, 0x48, 0x83, 0xec, 0x28, 0x48, 0x89, 0x74, 0x24, 0x08,
  0x85, 0xc9]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 6] 5) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.xor 32 14 (.r 14),
  Op.push 13,
  Op.mov 64 13 (.r 7),
  Op.push 12,
  Op.xor 32 12 (.r 12),
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 40),
  Op.st 64 (some 4) none 1 8 6,
  Op.test 32 1 (.r 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 34 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.push) (by decide) <|
  .cons (p0_18 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p0_21 _) (OpI.push) (by decide) <|
  .cons (p0_22 _) (OpI.push) (by decide) <|
  .cons (p0_23 _) (OpI.sub (.i 40) (.inr rfl)) (by decide) <|
  .cons (p0_27 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_32 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 34

def j0 : List Byte := [0x0f, 0x85, 0x90, 0x02, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 656] 6) := by dec_rfl

/-- The stretch at `40`. -/
def p1 : List Byte := [
  0x83, 0xfa, 0x01]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 2 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x0f, 0x84, 0x7f, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 383] 6) := by dec_rfl

/-- The stretch at `49`. -/
def p2 : List Byte := [
  0x83, 0xfa, 0x24]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 36)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 32 2 (.i 36)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 36) (.inl rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x0f, 0x87, 0x76, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 374] 6) := by dec_rfl

/-- The stretch at `58`. -/
def p3 : List Byte := [
  0x49, 0x0f, 0xbe, 0x45, 0x00, 0x49, 0x8b, 0x70, 0x68, 0x4c, 0x89, 0xeb, 0x48, 0x89, 0xc1, 0xf6,
  0x44, 0x46, 0x01, 0x20]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movsx 64 [gr 64 0, .mem (mg (some 13) none 1 0 8)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 8) none 1 104 64)] 4) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .test 8 [.mem (mg (some 6) (some 0) 2 1 8), .imm 8 32] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldsxq 0 (some 13) none 1 0,
  Op.ld 64 6 (some 8) none 1 104,
  Op.mov 64 3 (.r 13),
  Op.mov 64 1 (.r 0),
  Op.testmi 8 (some 6) (some 0) 2 1 32]

theorem b3 (prof : Profile) : Blk prof p3 0 20 o3 :=
  .cons (p3_0 _) (OpI.ldsxq) (by decide) <|
  .cons (p3_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p3_12 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_15 _) (OpI.testmi8) (by decide) <|
  .nil 20

def j3 : List Byte := [0x74, 0x13]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p4 : List Byte := [
  0x48, 0x0f, 0xbe, 0x43, 0x01, 0x48, 0x83, 0xc3, 0x01, 0x48, 0x89, 0xc1, 0xf6, 0x44, 0x46, 0x01,
  0x20]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movsx 64 [gr 64 0, .mem (mg (some 3) none 1 1 8)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .test 8 [.mem (mg (some 6) (some 0) 2 1 8), .imm 8 32] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldsxq 0 (some 3) none 1 1,
  Op.add 64 3 (.i 1),
  Op.mov 64 1 (.r 0),
  Op.testmi 8 (some 6) (some 0) 2 1 32]

theorem b4 (prof : Profile) : Blk prof p4 0 17 o4 :=
  .cons (p4_0 _) (OpI.ldsxq) (by decide) <|
  .cons (p4_5 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.testmi8) (by decide) <|
  .nil 17

def j4 : List Byte := [0x75, 0xed]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551597] 2) := by dec_rfl

/-- The stretch at `99`. -/
def p5 : List Byte := [
  0x84, 0xc9]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 8 1 (.r 1)]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 2

def j5 : List Byte := [0x0f, 0x84, 0x5e, 0x03, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 862] 6) := by dec_rfl

/-- The stretch at `107`. -/
def p6 : List Byte := [
  0x80, 0xf9, 0x2d]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 8 [gr 8 1, Src.opd 8 (.i 45)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 8 1 (.i 45)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.cmp8 (.i 45)) (by decide) <|
  .nil 3

def j6 : List Byte := [0x0f, 0x84, 0x2c, 0x02, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 556] 6) := by dec_rfl

/-- The stretch at `116`. -/
def p7 : List Byte := [
  0xc7, 0x44, 0x24, 0x14, 0x00, 0x00, 0x00, 0x00, 0x80, 0xf9, 0x2b]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 20 32), .imm 32 0] 8) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .cmp 8 [gr 8 1, Src.opd 8 (.i 43)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.sti 32 (some 4) none 1 20 0,
  Op.cmp 8 1 (.i 43)]

theorem b7 (prof : Profile) : Blk prof p7 0 11 o7 :=
  .cons (p7_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p7_8 _) (OpI.cmp8 (.i 43)) (by decide) <|
  .nil 11

def j7 : List Byte := [0x0f, 0x84, 0x6b, 0x01, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 363] 6) := by dec_rfl

/-- The stretch at `133`. -/
def p8 : List Byte := [
  0x80, 0xf9, 0x30]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 8 [gr 8 1, Src.opd 8 (.i 48)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmp 8 1 (.i 48)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.cmp8 (.i 48)) (by decide) <|
  .nil 3

def j8 : List Byte := [0x0f, 0x84, 0xc2, 0x01, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 450] 6) := by dec_rfl

/-- The stretch at `142`. -/
def p9 : List Byte := [
  0x85, 0xd2]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.test 32 2 (.r 2)]

theorem b9 (prof : Profile) : Blk prof p9 0 2 o9 :=
  .cons (p9_0 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j9 : List Byte := [0x0f, 0x85, 0x3a, 0x01, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 314] 6) := by dec_rfl

/-- The stretch at `150`. -/
def p10 : List Byte := [
  0x4d, 0x85, 0xf6]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .test 64 [gr 64 14, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.test 64 14 (.r 14)]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.test (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0x0f, 0x85, 0x41, 0x03, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 833] 6) := by dec_rfl

/-- The stretch at `159`. -/
def p11 : List Byte := [
  0xb8, 0x08, 0x00, 0x00, 0x00, 0xba, 0x0a, 0x00, 0x00, 0x00, 0x31, 0xed]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 10)] 5) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 32 0 (.i 8),
  Op.mov 32 2 (.i 10),
  Op.xor 32 5 (.r 5)]

theorem b11 (prof : Profile) : Blk prof p11 0 12 o11 :=
  .cons (p11_0 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p11_5 _) (OpI.mov (.i 10) (.inl rfl)) (by decide) <|
  .cons (p11_10 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `171`. -/
def p12 : List Byte := [
  0x48, 0x98, 0x48, 0x8d, 0x35, 0x3c, 0xfc, 0x0d, 0x00, 0x4c, 0x8b, 0x04, 0xc6, 0x48, 0x8d, 0x35,
  0xf1, 0xfb, 0x0d, 0x00, 0x0f, 0xb6, 0x04, 0x06, 0x88, 0x44, 0x24, 0x12, 0x84, 0xc9]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cbw 64 [] 2) := by dec_rfl
theorem p12_2 : ∀ feat, Dec feat p12 2 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 916540 0)] 7) := by dec_rfl
theorem p12_9 : ∀ feat, Dec feat p12 9 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 6) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p12_13 : ∀ feat, Dec feat p12 13 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 916465 0)] 7) := by dec_rfl
theorem p12_20 : ∀ feat, Dec feat p12 20 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) (some 0) 1 0 8)] 4) := by dec_rfl
theorem p12_24 : ∀ feat, Dec feat p12 24 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18 8), gr 8 0] 4) := by dec_rfl
theorem p12_28 : ∀ feat, Dec feat p12 28 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cdqe,
  Op.mov 64 6 (.i 7353760),
  Op.ld 64 8 (some 6) (some 0) 8 0,
  Op.mov 64 6 (.i 7353696),
  Op.ldzx 8 0 (some 6) (some 0) 1 0,
  Op.st 8 (some 4) none 1 18 0,
  Op.test 8 1 (.r 1)]

theorem b12 (prof : Profile) : BlkA prof p12 (0x62395b : Addr) 0 30 o12 :=
  .cons (p12_0 _) ((OpI.cdqe).at _) (by decide) <|
  .cons (p12_2 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p12_9 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p12_13 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p12_20 _) ((OpI.ldzx (.inl rfl)).at _) (by decide) <|
  .cons (p12_24 _) ((OpI.st (.inl rfl)).at _) (by decide) <|
  .cons (p12_28 _) ((OpI.test8 (.r 1)).at _) (by decide) <|
  .nil 30

def j11 : List Byte := [0x0f, 0x84, 0x1a, 0x02, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 538] 6) := by dec_rfl

/-- The stretch at `207`. -/
def p13 : List Byte := [
  0x49, 0x39, 0xde]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 64 [gr 64 14, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmp 64 14 (.r 3)]

theorem b13 (prof : Profile) : Blk prof p13 0 3 o13 :=
  .cons (p13_0 _) (OpI.cmp (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j12 : List Byte := [0x0f, 0x84, 0x11, 0x02, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 529] 6) := by dec_rfl

/-- The stretch at `216`. -/
def p14 : List Byte := [
  0x4c, 0x8b, 0x15, 0x49, 0xdb, 0x16, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 10, .mem (mrip 1497929 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.lda 64 10 7935192]

theorem b14 (prof : Profile) : BlkA prof p14 (0x623988 : Addr) 0 7 o14 :=
  .cons (p14_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `223`. -/
def p15 : List Byte := [
  0x48, 0x8d, 0x75, 0xff, 0x4c, 0x8b, 0x1d, 0x2e, 0xdb, 0x16, 0x00, 0x48, 0x89, 0xdf, 0x31, 0xc0,
  0x48, 0x89, 0x74, 0x24, 0x18, 0x45, 0x31, 0xc9, 0x4c, 0x63, 0xfa]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 5) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 64 [gr 64 11, .mem (mrip 1497902 64)] 7) := by dec_rfl
theorem p15_11 : ∀ feat, Dec feat p15 11 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p15_14 : ∀ feat, Dec feat p15 14 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p15_16 : ∀ feat, Dec feat p15 16 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 6] 5) := by dec_rfl
theorem p15_21 : ∀ feat, Dec feat p15 21 (FV7z.mk .xor 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p15_24 : ∀ feat, Dec feat p15 24 (FV7z.mk .movsxd 64 [gr 64 15, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.lea 64 6 (some 5) none 1 18446744073709551615,
  Op.lda 64 11 7935176,
  Op.mov 64 7 (.r 3),
  Op.xor 32 0 (.r 0),
  Op.st 64 (some 4) none 1 24 6,
  Op.xor 32 9 (.r 9),
  Op.sxr 15 2]

theorem b15 (prof : Profile) : BlkA prof p15 (0x62398f : Addr) 0 27 o15 :=
  .cons (p15_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p15_4 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p15_11 _) ((OpI.mov (.r 3) (.inr rfl)).at _) (by decide) <|
  .cons (p15_14 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p15_16 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p15_21 _) ((OpI.xor (.r 9) (.inl rfl)).at _) (by decide) <|
  .cons (p15_24 _) ((OpI.sxr).at _) (by decide) <|
  .nil 27

def j13 : List Byte := [0xeb, 0x2c]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk .jmp 64 [.rel 44] 2) := by dec_rfl

def j14 : List Byte := [0x75, 0x07]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `258`. -/
def p16 : List Byte := [
  0x40, 0x3a, 0x74, 0x24, 0x12]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .cmp 8 [gr 8 6, .mem (mg (some 4) none 1 18 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.cmpm 8 6 (some 4) none 1 18]

theorem b16 (prof : Profile) : Blk prof p16 0 5 o16 :=
  .cons (p16_0 _) (OpI.cmpm8) (by decide) <|
  .nil 5

def j15 : List Byte := [0x77, 0x50]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 7) 64 [.rel 80] 2) := by dec_rfl

/-- The stretch at `265`. -/
def p17 : List Byte := [
  0x49, 0x0f, 0xaf, 0xc7, 0x40, 0x0f, 0xb6, 0xf6, 0x48, 0x89, 0xf9, 0x48, 0x01, 0xf0]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .imul 64 [gr 64 0, gr 64 15] 4) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .movzx 32 [gr 32 6, gr 8 6] 4) := by dec_rfl
theorem p17_8 : ∀ feat, Dec feat p17 8 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p17_11 : ∀ feat, Dec feat p17 11 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.imul64 0 15,
  Op.zxr 6 6,
  Op.mov 64 1 (.r 7),
  Op.add 64 0 (.r 6)]

theorem b17 (prof : Profile) : Blk prof p17 0 14 o17 :=
  .cons (p17_0 _) (OpI.imul64) (by decide) <|
  .cons (p17_4 _) (OpI.zxr) (by decide) <|
  .cons (p17_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p17_11 _) (OpI.add (.r 6) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `279`. -/
def p18 : List Byte := [
  0x48, 0x8d, 0x79, 0x01, 0x0f, 0xb6, 0x49, 0x01, 0x84, 0xc9]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 1) none 1 1 0)] 4) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 1) none 1 1 8)] 4) := by dec_rfl
theorem p18_8 : ∀ feat, Dec feat p18 8 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.lea 64 7 (some 1) none 1 1,
  Op.ldzx 8 1 (some 1) none 1 1,
  Op.test 8 1 (.r 1)]

theorem b18 (prof : Profile) : Blk prof p18 0 10 o18 :=
  .cons (p18_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p18_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p18_8 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 10

def j16 : List Byte := [0x74, 0x4d]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 4) 64 [.rel 77] 2) := by dec_rfl

/-- The stretch at `291`. -/
def p19 : List Byte := [
  0x4c, 0x39, 0xf7]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmp 64 7 (.r 14)]

theorem b19 (prof : Profile) : Blk prof p19 0 3 o19 :=
  .cons (p19_0 _) (OpI.cmp (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

def j17 : List Byte := [0x74, 0x48]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 4) 64 [.rel 72] 2) := by dec_rfl

/-- The stretch at `296`. -/
def p20 : List Byte := [
  0x8d, 0x71, 0xd0, 0x40, 0x80, 0xfe, 0x09]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 1) none 1 18446744073709551568 0)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .cmp 8 [gr 8 6, Src.opd 8 (.i 9)] 4) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.lea 32 6 (some 1) none 1 18446744073709551568,
  Op.cmp 8 6 (.i 9)]

theorem b20 (prof : Profile) : Blk prof p20 0 7 o20 :=
  .cons (p20_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.cmp8 (.i 9)) (by decide) <|
  .nil 7

def j18 : List Byte := [0x76, 0x1b]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 6) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `305`. -/
def p21 : List Byte := [
  0x48, 0x85, 0xed]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b21 (prof : Profile) : Blk prof p21 0 3 o21 :=
  .cons (p21_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j19 : List Byte := [0x0f, 0x85, 0xc6, 0x00, 0x00, 0x00]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 5) 64 [.rel 198] 6) := by dec_rfl

/-- The stretch at `314`. -/
def p22 : List Byte := [
  0x0f, 0xb6, 0xc9]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .movzx 32 [gr 32 1, gr 8 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.zxr 1 1]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.zxr) (by decide) <|
  .nil 3

/-- The stretch at `317`. -/
def p23 : List Byte := [
  0x41, 0xf6, 0x44, 0x4b, 0x01, 0x04]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .test 8 [.mem (mg (some 11) (some 1) 2 1 8), .imm 8 4] 6) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.testmi 8 (some 11) (some 1) 2 1 4]

theorem b23 (prof : Profile) : Blk prof p23 0 6 o23 :=
  .cons (p23_0 _) (OpI.testmi8) (by decide) <|
  .nil 6

def j20 : List Byte := [0x74, 0x2b]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 4) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `325`. -/
def p24 : List Byte := [
  0x41, 0x8b, 0x34, 0x8a, 0x83, 0xee, 0x37]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 10) (some 1) 4 0 32)] 4) := by dec_rfl
theorem p24_4 : ∀ feat, Dec feat p24 4 (FV7z.mk .sub 32 [gr 32 6, Src.opd 32 (.i 55)] 3) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.ld 32 6 (some 10) (some 1) 4 0,
  Op.sub 32 6 (.i 55)]

theorem b24 (prof : Profile) : Blk prof p24 0 7 o24 :=
  .cons (p24_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p24_4 _) (OpI.sub (.i 55) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `332`. -/
def p25 : List Byte := [
  0x40, 0x0f, 0xb6, 0xce, 0x39, 0xd1]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .movzx 32 [gr 32 1, gr 8 6] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.zxr 1 6,
  Op.cmp 32 1 (.r 2)]

theorem b25 (prof : Profile) : Blk prof p25 0 6 o25 :=
  .cons (p25_0 _) (OpI.zxr) (by decide) <|
  .cons (p25_4 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

def j21 : List Byte := [0x7d, 0x1c]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 13) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `340`. -/
def p26 : List Byte := [
  0x49, 0x39, 0xc0]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .cmp 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.cmp 64 8 (.r 0)]

theorem b26 (prof : Profile) : Blk prof p26 0 3 o26 :=
  .cons (p26_0 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j22 : List Byte := [0x73, 0xa7]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551527] 2) := by dec_rfl

/-- The stretch at `345`. -/
def p27 : List Byte := [
  0x48, 0x89, 0xf9, 0x41, 0xb9, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x79, 0x01, 0x0f, 0xb6, 0x49,
  0x01, 0x84, 0xc9]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p27_3 : ∀ feat, Dec feat p27 3 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p27_9 : ∀ feat, Dec feat p27 9 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 1) none 1 1 0)] 4) := by dec_rfl
theorem p27_13 : ∀ feat, Dec feat p27 13 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 1) none 1 1 8)] 4) := by dec_rfl
theorem p27_17 : ∀ feat, Dec feat p27 17 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.mov 64 1 (.r 7),
  Op.mov 32 9 (.i 1),
  Op.lea 64 7 (some 1) none 1 1,
  Op.ldzx 8 1 (some 1) none 1 1,
  Op.test 8 1 (.r 1)]

theorem b27 (prof : Profile) : Blk prof p27 0 19 o27 :=
  .cons (p27_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p27_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p27_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p27_13 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p27_17 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 19

def j23 : List Byte := [0x75, 0xb5]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551541] 2) := by dec_rfl

/-- The stretch at `366`. -/
def p28 : List Byte := [
  0x66, 0x90]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .nop 16 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.nop]

theorem b28 (prof : Profile) : Blk prof p28 0 2 o28 :=
  .cons (p28_0 _) (OpI.nop) (by decide) <|
  .nil 2

/-- The stretch at `368`. -/
def p29 : List Byte := [
  0x48, 0x39, 0xfb]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.cmp 64 3 (.r 7)]

theorem b29 (prof : Profile) : Blk prof p29 0 3 o29 :=
  .cons (p29_0 _) (OpI.cmp (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j24 : List Byte := [0x0f, 0x84, 0x73, 0x01, 0x00, 0x00]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 4) 64 [.rel 371] 6) := by dec_rfl

/-- The stretch at `377`. -/
def p30 : List Byte := [
  0x48, 0x8b, 0x5c, 0x24, 0x08, 0x48, 0x85, 0xdb]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p30_5 : ∀ feat, Dec feat p30 5 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.ld 64 3 (some 4) none 1 8,
  Op.test 64 3 (.r 3)]

theorem b30 (prof : Profile) : Blk prof p30 0 8 o30 :=
  .cons (p30_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p30_5 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 8

def j25 : List Byte := [0x74, 0x03]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 4) 64 [.rel 3] 2) := by dec_rfl

/-- The stretch at `387`. -/
def p31 : List Byte := [
  0x48, 0x89, 0x3b]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.st 64 (some 3) none 1 0 7]

theorem b31 (prof : Profile) : Blk prof p31 0 3 o31 :=
  .cons (p31_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 3

/-- The stretch at `390`. -/
def p32 : List Byte := [
  0x45, 0x85, 0xc9]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.test 32 9 (.r 9)]

theorem b32 (prof : Profile) : Blk prof p32 0 3 o32 :=
  .cons (p32_0 _) (OpI.test (.r 9) (.inl rfl)) (by decide) <|
  .nil 3

def j26 : List Byte := [0x0f, 0x85, 0x1b, 0x03, 0x00, 0x00]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 5) 64 [.rel 795] 6) := by dec_rfl

/-- The stretch at `399`. -/
def p33 : List Byte := [
  0x8b, 0x4c, 0x24, 0x14, 0x48, 0x89, 0xc2, 0x48, 0xf7, 0xda, 0x85, 0xc9, 0x48, 0x0f, 0x45, 0xc2,
  0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 20 32)] 4) := by dec_rfl
theorem p33_4 : ∀ feat, Dec feat p33 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p33_7 : ∀ feat, Dec feat p33 7 (FV7z.mk .neg 64 [gr 64 2] 3) := by dec_rfl
theorem p33_10 : ∀ feat, Dec feat p33 10 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p33_12 : ∀ feat, Dec feat p33 12 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem p33_16 : ∀ feat, Dec feat p33 16 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p33_20 : ∀ feat, Dec feat p33 20 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p33_21 : ∀ feat, Dec feat p33 21 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p33_22 : ∀ feat, Dec feat p33 22 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p33_24 : ∀ feat, Dec feat p33 24 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p33_26 : ∀ feat, Dec feat p33 26 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p33_28 : ∀ feat, Dec feat p33 28 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.ld 32 1 (some 4) none 1 20,
  Op.mov 64 2 (.r 0),
  Op.neg 64 2,
  Op.test 32 1 (.r 1),
  Op.cmov64 5 0 2,
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b33 (prof : Profile) : Blk prof p33 0 30 o33 :=
  .cons (p33_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p33_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p33_7 _) (OpI.neg (.inr rfl)) (by decide) <|
  .cons (p33_10 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .cons (p33_12 _) (OpI.cmov64) (by decide) <|
  .cons (p33_16 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p33_20 _) (OpI.pop) (by decide) <|
  .cons (p33_21 _) (OpI.pop) (by decide) <|
  .cons (p33_22 _) (OpI.pop) (by decide) <|
  .cons (p33_24 _) (OpI.pop) (by decide) <|
  .cons (p33_26 _) (OpI.pop) (by decide) <|
  .cons (p33_28 _) (OpI.pop) (by decide) <|
  .nil 30

/-- The stretch at `432`. -/
def p34 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0xc7, 0x00, 0x16, 0x00, 0x00, 0x00, 0x31, 0xc0]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p34_7 : ∀ feat, Dec feat p34 7 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 22] 7) := by dec_rfl
theorem p34_14 : ∀ feat, Dec feat p34 14 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o34 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.stfi fb 32 (some 0) none 1 0 22,
  Op.xor 32 0 (.r 0)]

theorem b34 (prof : Profile) (fb : Addr) : BlkF prof p34 (0x623a60 : Addr) fb 0 16 (o34 fb) :=
  .cons (p34_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p34_7 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p34_14 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 16

/-- The stretch at `448`. -/
def p35 : List Byte := [
  0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p35_4 : ∀ feat, Dec feat p35 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p35_5 : ∀ feat, Dec feat p35 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p35_6 : ∀ feat, Dec feat p35 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p35_8 : ∀ feat, Dec feat p35 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p35_10 : ∀ feat, Dec feat p35 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p35_12 : ∀ feat, Dec feat p35 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b35 (prof : Profile) : Blk prof p35 0 14 o35 :=
  .cons (p35_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p35_4 _) (OpI.pop) (by decide) <|
  .cons (p35_5 _) (OpI.pop) (by decide) <|
  .cons (p35_6 _) (OpI.pop) (by decide) <|
  .cons (p35_8 _) (OpI.pop) (by decide) <|
  .cons (p35_10 _) (OpI.pop) (by decide) <|
  .cons (p35_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `464`. -/
def p36 : List Byte := [
  0x83, 0xfa, 0x0a]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.cmp 32 2 (.i 10)]

theorem b36 (prof : Profile) : Blk prof p36 0 3 o36 :=
  .cons (p36_0 _) (OpI.cmp (.i 10) (.inl rfl)) (by decide) <|
  .nil 3

def j27 : List Byte := [0x0f, 0x84, 0xbd, 0xfe, 0xff, 0xff]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551293] 6) := by dec_rfl

/-- The stretch at `473`. -/
def p37 : List Byte := [
  0x8d, 0x42, 0xfe, 0x31, 0xed, 0x45, 0x31, 0xf6]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 2) none 1 18446744073709551614 0)] 3) := by dec_rfl
theorem p37_3 : ∀ feat, Dec feat p37 3 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p37_5 : ∀ feat, Dec feat p37 5 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.lea 32 0 (some 2) none 1 18446744073709551614,
  Op.xor 32 5 (.r 5),
  Op.xor 32 14 (.r 14)]

theorem b37 (prof : Profile) : Blk prof p37 0 8 o37 :=
  .cons (p37_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p37_3 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p37_5 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .nil 8

def j28 : List Byte := [0xe9, 0xc5, 0xfe, 0xff, 0xff]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk .jmp 64 [.rel 18446744073709551301] 5) := by dec_rfl

/-- The stretch at `496`. -/
def p38 : List Byte := [
  0x0f, 0xb6, 0x4b, 0x01, 0x48, 0x83, 0xc3, 0x01]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 3) none 1 1 8)] 4) := by dec_rfl
theorem p38_4 : ∀ feat, Dec feat p38 4 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.ldzx 8 1 (some 3) none 1 1,
  Op.add 64 3 (.i 1)]

theorem b38 (prof : Profile) : Blk prof p38 0 8 o38 :=
  .cons (p38_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p38_4 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 8

def j29 : List Byte := [0xe9, 0x88, 0xfe, 0xff, 0xff]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk .jmp 64 [.rel 18446744073709551240] 5) := by dec_rfl

/-- The stretch at `592`. -/
def p39 : List Byte := [
  0xf7, 0xc2, 0xef, 0xff, 0xff, 0xff]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.i 4294967279)] 6) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.test 32 2 (.i 4294967279)]

theorem b39 (prof : Profile) : Blk prof p39 0 6 o39 :=
  .cons (p39_0 _) (OpI.test (.i 4294967279) (.inl rfl)) (by decide) <|
  .nil 6

def j30 : List Byte := [0x0f, 0x84, 0xcc, 0x00, 0x00, 0x00]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 4) 64 [.rel 204] 6) := by dec_rfl

def j31 : List Byte := [0x0f, 0x84, 0x41, 0x01, 0x00, 0x00]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk (.jcc 4) 64 [.rel 321] 6) := by dec_rfl

/-- The stretch at `613`. -/
def p40 : List Byte := [
  0x8d, 0x42, 0xfe, 0x48, 0x8d, 0x0d, 0x81, 0xfa, 0x0d, 0x00, 0x45, 0x31, 0xf6, 0x31, 0xed, 0x48,
  0x98, 0x4c, 0x8b, 0x15, 0xab, 0xd9, 0x16, 0x00, 0x4c, 0x8b, 0x04, 0xc1, 0x48, 0x8d, 0x0d, 0x28,
  0xfa, 0x0d, 0x00, 0x0f, 0xb6, 0x04, 0x01, 0xb9, 0x30, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x12]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 2) none 1 18446744073709551614 0)] 3) := by dec_rfl
theorem p40_3 : ∀ feat, Dec feat p40 3 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 916097 0)] 7) := by dec_rfl
theorem p40_10 : ∀ feat, Dec feat p40 10 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p40_13 : ∀ feat, Dec feat p40 13 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p40_15 : ∀ feat, Dec feat p40 15 (FV7z.mk .cbw 64 [] 2) := by dec_rfl
theorem p40_17 : ∀ feat, Dec feat p40 17 (FV7z.mk .mov 64 [gr 64 10, .mem (mrip 1497515 64)] 7) := by dec_rfl
theorem p40_24 : ∀ feat, Dec feat p40 24 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 1) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p40_28 : ∀ feat, Dec feat p40 28 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 916008 0)] 7) := by dec_rfl
theorem p40_35 : ∀ feat, Dec feat p40 35 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 1) (some 0) 1 0 8)] 4) := by dec_rfl
theorem p40_39 : ∀ feat, Dec feat p40 39 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 48)] 5) := by dec_rfl
theorem p40_44 : ∀ feat, Dec feat p40 44 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18 8), gr 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.lea 32 0 (some 2) none 1 18446744073709551614,
  Op.mov 64 1 (.i 7353760),
  Op.xor 32 14 (.r 14),
  Op.xor 32 5 (.r 5),
  Op.cdqe,
  Op.lda 64 10 7935192,
  Op.ld 64 8 (some 1) (some 0) 8 0,
  Op.mov 64 1 (.i 7353696),
  Op.ldzx 8 0 (some 1) (some 0) 1 0,
  Op.mov 32 1 (.i 48),
  Op.st 8 (some 4) none 1 18 0]

theorem b40 (prof : Profile) : BlkA prof p40 (0x623b15 : Addr) 0 48 o40 :=
  .cons (p40_0 _) ((OpI.lea (.inl rfl)).at _) (by decide) <|
  .cons (p40_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p40_10 _) ((OpI.xor (.r 14) (.inl rfl)).at _) (by decide) <|
  .cons (p40_13 _) ((OpI.xor (.r 5) (.inl rfl)).at _) (by decide) <|
  .cons (p40_15 _) ((OpI.cdqe).at _) (by decide) <|
  .cons (p40_17 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p40_24 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p40_28 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p40_35 _) ((OpI.ldzx (.inl rfl)).at _) (by decide) <|
  .cons (p40_39 _) ((OpI.mov (.i 48) (.inl rfl)).at _) (by decide) <|
  .cons (p40_44 _) ((OpI.st (.inl rfl)).at _) (by decide) <|
  .nil 48

def j32 : List Byte := [0xe9, 0x45, 0xfe, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk .jmp 64 [.rel 18446744073709551173] 5) := by dec_rfl

/-- The stretch at `672`. -/
def p41 : List Byte := [
  0x0f, 0xb6, 0x4b, 0x01, 0xc7, 0x44, 0x24, 0x14, 0x01, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc3, 0x01]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 3) none 1 1 8)] 4) := by dec_rfl
theorem p41_4 : ∀ feat, Dec feat p41 4 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 20 32), .imm 32 1] 8) := by dec_rfl
theorem p41_12 : ∀ feat, Dec feat p41 12 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.ldzx 8 1 (some 3) none 1 1,
  Op.sti 32 (some 4) none 1 20 1,
  Op.add 64 3 (.i 1)]

theorem b41 (prof : Profile) : Blk prof p41 0 16 o41 :=
  .cons (p41_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p41_4 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p41_12 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 16

def j33 : List Byte := [0xe9, 0xd0, 0xfd, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk .jmp 64 [.rel 18446744073709551056] 5) := by dec_rfl

/-- The stretch at `745`. -/
def p42 : List Byte := [
  0x48, 0x89, 0xdf]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.mov 64 7 (.r 3)]

theorem b42 (prof : Profile) : Blk prof p42 0 3 o42 :=
  .cons (p42_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `748`. -/
def p43 : List Byte := [
  0x48, 0x83, 0x7c, 0x24, 0x08, 0x00]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .cmp 64 [.mem (mg (some 4) none 1 8 64), .imm 64 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.cmpmi 64 (some 4) none 1 8 0]

theorem b43 (prof : Profile) : Blk prof p43 0 6 o43 :=
  .cons (p43_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 6

def j34 : List Byte := [0x0f, 0x84, 0xa7, 0x00, 0x00, 0x00]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk (.jcc 4) 64 [.rel 167] 6) := by dec_rfl

/-- The stretch at `760`. -/
def p44 : List Byte := [
  0x48, 0x89, 0xf8, 0x4c, 0x29, 0xe8, 0x48, 0x83, 0xf8, 0x01]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p44_3 : ∀ feat, Dec feat p44 3 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p44_6 : ∀ feat, Dec feat p44 6 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.mov 64 0 (.r 7),
  Op.sub 64 0 (.r 13),
  Op.cmp 64 0 (.i 1)]

theorem b44 (prof : Profile) : Blk prof p44 0 10 o44 :=
  .cons (p44_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p44_3 _) (OpI.sub (.r 13) (.inr rfl)) (by decide) <|
  .cons (p44_6 _) (OpI.cmp (.i 1) (.inr rfl)) (by decide) <|
  .nil 10

def j35 : List Byte := [0x7e, 0x12]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk (.jcc 14) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `772`. -/
def p45 : List Byte := [
  0x48, 0x0f, 0xbe, 0x57, 0xff, 0x48, 0x8b, 0x05, 0x18, 0xd9, 0x16, 0x00, 0x83, 0x3c, 0x90, 0x58]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .movsx 64 [gr 64 2, .mem (mg (some 7) none 1 18446744073709551615 8)] 5) := by dec_rfl
theorem p45_5 : ∀ feat, Dec feat p45 5 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1497368 64)] 7) := by dec_rfl
theorem p45_12 : ∀ feat, Dec feat p45 12 (FV7z.mk .cmp 32 [.mem (mg (some 0) (some 2) 4 0 32), .imm 32 88] 4) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.ldsxq 2 (some 7) none 1 18446744073709551615,
  Op.lda 64 0 7935192,
  Op.cmpmi 32 (some 0) (some 2) 4 0 88]

theorem b45 (prof : Profile) : BlkA prof p45 (0x623bb4 : Addr) 0 16 o45 :=
  .cons (p45_0 _) ((OpI.ldsxq).at _) (by decide) <|
  .cons (p45_5 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p45_12 _) ((OpI.cmpmi (.inr rfl)).at _) (by decide) <|
  .nil 16

def j36 : List Byte := [0x74, 0x77]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk (.jcc 4) 64 [.rel 119] 2) := by dec_rfl

/-- The stretch at `790`. -/
def p46 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x4c, 0x89, 0x28, 0x31, 0xc0]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p46_5 : ∀ feat, Dec feat p46 5 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 13] 3) := by dec_rfl
theorem p46_8 : ∀ feat, Dec feat p46 8 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.st 64 (some 0) none 1 0 13,
  Op.xor 32 0 (.r 0)]

theorem b46 (prof : Profile) : Blk prof p46 0 10 o46 :=
  .cons (p46_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p46_5 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p46_8 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 10

def j37 : List Byte := [0xe9, 0x9b, 0xfe, 0xff, 0xff]
theorem j37_0 : ∀ feat, Dec feat j37 0 (FV7z.mk .jmp 64 [.rel 18446744073709551259] 5) := by dec_rfl

/-- The stretch at `808`. -/
def p47 : List Byte := [
  0x4c, 0x8b, 0x15, 0xf9, 0xd8, 0x16, 0x00, 0x48, 0x0f, 0xbe, 0x43, 0x01, 0x41, 0x83, 0x3c, 0x82,
  0x58]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .mov 64 [gr 64 10, .mem (mrip 1497337 64)] 7) := by dec_rfl
theorem p47_7 : ∀ feat, Dec feat p47 7 (FV7z.mk .movsx 64 [gr 64 0, .mem (mg (some 3) none 1 1 8)] 5) := by dec_rfl
theorem p47_12 : ∀ feat, Dec feat p47 12 (FV7z.mk .cmp 32 [.mem (mg (some 10) (some 0) 4 0 32), .imm 32 88] 5) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.lda 64 10 7935192,
  Op.ldsxq 0 (some 3) none 1 1,
  Op.cmpmi 32 (some 10) (some 0) 4 0 88]

theorem b47 (prof : Profile) : BlkA prof p47 (0x623bd8 : Addr) 0 17 o47 :=
  .cons (p47_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p47_7 _) ((OpI.ldsxq).at _) (by decide) <|
  .cons (p47_12 _) ((OpI.cmpmi (.inr rfl)).at _) (by decide) <|
  .nil 17

def j38 : List Byte := [0x74, 0x36]
theorem j38_0 : ∀ feat, Dec feat j38 0 (FV7z.mk (.jcc 4) 64 [.rel 54] 2) := by dec_rfl

def j39 : List Byte := [0x0f, 0x85, 0x19, 0xff, 0xff, 0xff]
theorem j39_0 : ∀ feat, Dec feat j39 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551385] 6) := by dec_rfl

/-- The stretch at `835`. -/
def p48 : List Byte := [
  0xba, 0x08, 0x00, 0x00, 0x00, 0x45, 0x31, 0xf6, 0x31, 0xed, 0xb9, 0x30, 0x00, 0x00, 0x00, 0x0f,
  0xb6, 0x05, 0x5d, 0xf9, 0x0d, 0x00, 0x4c, 0x8b, 0x05, 0xc0, 0xf9, 0x0d, 0x00, 0x88, 0x44, 0x24,
  0x12]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p48_5 : ∀ feat, Dec feat p48 5 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p48_8 : ∀ feat, Dec feat p48 8 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p48_10 : ∀ feat, Dec feat p48 10 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 48)] 5) := by dec_rfl
theorem p48_15 : ∀ feat, Dec feat p48 15 (FV7z.mk .movzx 32 [gr 32 0, .mem (mrip 915805 8)] 7) := by dec_rfl
theorem p48_22 : ∀ feat, Dec feat p48 22 (FV7z.mk .mov 64 [gr 64 8, .mem (mrip 915904 64)] 7) := by dec_rfl
theorem p48_29 : ∀ feat, Dec feat p48 29 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18 8), gr 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.mov 32 2 (.i 8),
  Op.xor 32 14 (.r 14),
  Op.xor 32 5 (.r 5),
  Op.mov 32 1 (.i 48),
  Op.ldzxa 8 0 7353702,
  Op.lda 64 8 7353808,
  Op.st 8 (some 4) none 1 18 0]

theorem b48 (prof : Profile) : BlkA prof p48 (0x623bf3 : Addr) 0 33 o48 :=
  .cons (p48_0 _) ((OpI.mov (.i 8) (.inl rfl)).at _) (by decide) <|
  .cons (p48_5 _) ((OpI.xor (.r 14) (.inl rfl)).at _) (by decide) <|
  .cons (p48_8 _) ((OpI.xor (.r 5) (.inl rfl)).at _) (by decide) <|
  .cons (p48_10 _) ((OpI.mov (.i 48) (.inl rfl)).at _) (by decide) <|
  .cons (p48_15 _) (OpIA.ldzx_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p48_22 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p48_29 _) ((OpI.st (.inl rfl)).at _) (by decide) <|
  .nil 33

def j40 : List Byte := [0xe9, 0x76, 0xfd, 0xff, 0xff]
theorem j40_0 : ∀ feat, Dec feat j40 0 (FV7z.mk .jmp 64 [.rel 18446744073709550966] 5) := by dec_rfl

/-- The stretch at `881`. -/
def p49 : List Byte := [
  0x0f, 0xb6, 0x4b, 0x02, 0xb8, 0x0e, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc3, 0x02, 0x31, 0xed, 0xba,
  0x10, 0x00, 0x00, 0x00, 0x45, 0x31, 0xf6]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 3) none 1 2 8)] 4) := by dec_rfl
theorem p49_4 : ∀ feat, Dec feat p49 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 14)] 5) := by dec_rfl
theorem p49_9 : ∀ feat, Dec feat p49 9 (FV7z.mk .add 64 [gr 64 3, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p49_13 : ∀ feat, Dec feat p49 13 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p49_15 : ∀ feat, Dec feat p49 15 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p49_20 : ∀ feat, Dec feat p49 20 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.ldzx 8 1 (some 3) none 1 2,
  Op.mov 32 0 (.i 14),
  Op.add 64 3 (.i 2),
  Op.xor 32 5 (.r 5),
  Op.mov 32 2 (.i 16),
  Op.xor 32 14 (.r 14)]

theorem b49 (prof : Profile) : Blk prof p49 0 23 o49 :=
  .cons (p49_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p49_4 _) (OpI.mov (.i 14) (.inl rfl)) (by decide) <|
  .cons (p49_9 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p49_13 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p49_15 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p49_20 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .nil 23

def j41 : List Byte := [0xe9, 0x1e, 0xfd, 0xff, 0xff]
theorem j41_0 : ∀ feat, Dec feat j41 0 (FV7z.mk .jmp 64 [.rel 18446744073709550878] 5) := by dec_rfl

/-- The stretch at `909`. -/
def p50 : List Byte := [
  0x80, 0x7f, 0xfe, 0x30]

theorem p50_0 : ∀ feat, Dec feat p50 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 18446744073709551614 8), .imm 8 48] 4) := by dec_rfl

/-- What the stretch does. -/
def o50 : List Op := [
  Op.cmpmi 8 (some 7) none 1 18446744073709551614 48]

theorem b50 (prof : Profile) : Blk prof p50 0 4 o50 :=
  .cons (p50_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j42 : List Byte := [0x75, 0x83]
theorem j42_0 : ∀ feat, Dec feat j42 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551491] 2) := by dec_rfl

/-- The stretch at `915`. -/
def p51 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x48, 0x83, 0xef, 0x01, 0x48, 0x89, 0x38]

theorem p51_0 : ∀ feat, Dec feat p51 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p51_5 : ∀ feat, Dec feat p51 5 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p51_9 : ∀ feat, Dec feat p51 9 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o51 : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.sub 64 7 (.i 1),
  Op.st 64 (some 0) none 1 0 7]

theorem b51 (prof : Profile) : Blk prof p51 0 12 o51 :=
  .cons (p51_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p51_5 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p51_9 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 12

/-- The stretch at `927`. -/
def p52 : List Byte := [
  0x31, 0xc0]

theorem p52_0 : ∀ feat, Dec feat p52 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o52 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b52 (prof : Profile) : Blk prof p52 0 2 o52 :=
  .cons (p52_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j43 : List Byte := [0xe9, 0x1a, 0xfe, 0xff, 0xff]
theorem j43_0 : ∀ feat, Dec feat j43 0 (FV7z.mk .jmp 64 [.rel 18446744073709551130] 5) := by dec_rfl

def j44 : List Byte := [0x75, 0x35]
theorem j44_0 : ∀ feat, Dec feat j44 0 (FV7z.mk (.jcc 5) 64 [.rel 53] 2) := by dec_rfl

/-- The stretch at `939`. -/
def p53 : List Byte := [
  0x0f, 0xb6, 0x05, 0x06, 0xf9, 0x0d, 0x00, 0x4c, 0x8b, 0x05, 0x77, 0xf9, 0x0d, 0x00, 0x31, 0xed,
  0xb9, 0x30, 0x00, 0x00, 0x00, 0x88, 0x44, 0x24, 0x12]

theorem p53_0 : ∀ feat, Dec feat p53 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mrip 915718 8)] 7) := by dec_rfl
theorem p53_7 : ∀ feat, Dec feat p53 7 (FV7z.mk .mov 64 [gr 64 8, .mem (mrip 915831 64)] 7) := by dec_rfl
theorem p53_14 : ∀ feat, Dec feat p53 14 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p53_16 : ∀ feat, Dec feat p53 16 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 48)] 5) := by dec_rfl
theorem p53_21 : ∀ feat, Dec feat p53 21 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 18 8), gr 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o53 : List Op := [
  Op.ldzxa 8 0 7353704,
  Op.lda 64 8 7353824,
  Op.xor 32 5 (.r 5),
  Op.mov 32 1 (.i 48),
  Op.st 8 (some 4) none 1 18 0]

theorem b53 (prof : Profile) : BlkA prof p53 (0x623c5b : Addr) 0 25 o53 :=
  .cons (p53_0 _) (OpIA.ldzx_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p53_7 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p53_14 _) ((OpI.xor (.r 5) (.inl rfl)).at _) (by decide) <|
  .cons (p53_16 _) ((OpI.mov (.i 48) (.inl rfl)).at _) (by decide) <|
  .cons (p53_21 _) ((OpI.st (.inl rfl)).at _) (by decide) <|
  .nil 25

def j45 : List Byte := [0xe9, 0x0f, 0xfd, 0xff, 0xff]
theorem j45_0 : ∀ feat, Dec feat j45 0 (FV7z.mk .jmp 64 [.rel 18446744073709550863] 5) := by dec_rfl

def j46 : List Byte := [0x0f, 0x85, 0x41, 0xff, 0xff, 0xff]
theorem j46_0 : ∀ feat, Dec feat j46 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551425] 6) := by dec_rfl

def j47 : List Byte := [0xe9, 0xe4, 0xfd, 0xff, 0xff]
theorem j47_0 : ∀ feat, Dec feat j47 0 (FV7z.mk .jmp 64 [.rel 18446744073709551076] 5) := by dec_rfl

/-- The stretch at `1194`. -/
def p54 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0xc7, 0x00, 0x22, 0x00, 0x00, 0x00, 0x48, 0xc7,
  0xc0, 0xff, 0xff, 0xff, 0xff]

theorem p54_0 : ∀ feat, Dec feat p54 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p54_7 : ∀ feat, Dec feat p54 7 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 34] 7) := by dec_rfl
theorem p54_14 : ∀ feat, Dec feat p54 14 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 7) := by dec_rfl

/-- What the stretch does. -/
def o54 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.stfi fb 32 (some 0) none 1 0 34,
  Op.mov 64 0 (.i 18446744073709551615)]

theorem b54 (prof : Profile) (fb : Addr) : BlkF prof p54 (0x623d5a : Addr) fb 0 21 (o54 fb) :=
  .cons (p54_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p54_7 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p54_14 _) (((OpI.mov (.i 18446744073709551615) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 21

def j48 : List Byte := [0xe9, 0xfc, 0xfc, 0xff, 0xff]
theorem j48_0 : ∀ feat, Dec feat j48 0 (FV7z.mk .jmp 64 [.rel 18446744073709550844] 5) := by dec_rfl

end FV7z.Stl
