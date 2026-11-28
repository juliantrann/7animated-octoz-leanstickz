import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Utf8_To_Utf16` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 44 of them) and each distinct jump (`j*`, 37) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.U16
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0x74, 0x24, 0xf8, 0x48,
  0x39, 0xca]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 18446744073709551608 64), gr 64 6] 5) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.st 64 (some 4) none 1 18446744073709551608 6,
  Op.cmp 64 2 (.r 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.push) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_15 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 18

def j0 : List Byte := [0x0f, 0x84, 0x2b, 0x02, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 555] 6) := by dec_rfl

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x45, 0x89, 0xc7, 0x45, 0x89, 0xc4, 0x41, 0x83, 0xe0, 0x04, 0x48, 0x89, 0xfb, 0x44, 0x89, 0x44,
  0x24, 0xf4, 0x49, 0x89, 0xca, 0x45, 0x31, 0xdb, 0x41, 0x83, 0xe7, 0x01, 0x41, 0xbd, 0x80, 0x00,
  0x00, 0x00, 0x41, 0x83, 0xe4, 0x02, 0x41, 0xbe, 0xfd, 0xff, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 15, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .and 32 [gr 32 8, Src.opd 32 (.i 4)] 4) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 18446744073709551604 32), gr 32 8] 5) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .mov 64 [gr 64 10, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p1_21 : ∀ feat, Dec feat p1 21 (FV7z.mk .xor 32 [gr 32 11, Src.opd 32 (.r 11)] 3) := by dec_rfl
theorem p1_24 : ∀ feat, Dec feat p1 24 (FV7z.mk .and 32 [gr 32 15, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p1_28 : ∀ feat, Dec feat p1 28 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.i 128)] 6) := by dec_rfl
theorem p1_34 : ∀ feat, Dec feat p1 34 (FV7z.mk .and 32 [gr 32 12, Src.opd 32 (.i 2)] 4) := by dec_rfl
theorem p1_38 : ∀ feat, Dec feat p1 38 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.i 65533)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 15 (.r 8),
  Op.mov 32 12 (.r 8),
  Op.and 32 8 (.i 4),
  Op.mov 64 3 (.r 7),
  Op.st 32 (some 4) none 1 18446744073709551604 8,
  Op.mov 64 10 (.r 1),
  Op.xor 32 11 (.r 11),
  Op.and 32 15 (.i 1),
  Op.mov 32 13 (.i 128),
  Op.and 32 12 (.i 2),
  Op.mov 32 14 (.i 65533)]

theorem b1 (prof : Profile) : Blk prof p1 0 44 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.and (.i 4) (.inl rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_18 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p1_21 _) (OpI.xor (.r 11) (.inl rfl)) (by decide) <|
  .cons (p1_24 _) (OpI.and (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_28 _) (OpI.mov (.i 128) (.inl rfl)) (by decide) <|
  .cons (p1_34 _) (OpI.and (.i 2) (.inl rfl)) (by decide) <|
  .cons (p1_38 _) (OpI.mov (.i 65533) (.inl rfl)) (by decide) <|
  .nil 44

def j1 : List Byte := [0xeb, 0x37]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 55] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p2 : List Byte := [
  0x8d, 0x50, 0x3e, 0x80, 0xfa, 0x32]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 62 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 50)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 2 (some 0) none 1 62,
  Op.cmp 8 2 (.i 50)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.cmp8 (.i 50)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x76, 0x40]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 64] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xdb]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 3 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x10]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `93`. -/
def p4 : List Byte := [
  0x05, 0x00, 0xef, 0x00, 0x00, 0x45, 0x85, 0xe4, 0x41, 0x0f, 0x44, 0xc6, 0x42, 0x89, 0x04, 0x9b]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 61184)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk (.cmovcc 4) 32 [gr 32 0, gr 32 14] 4) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 11) 4 0 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 32 0 (.i 61184),
  Op.test 32 12 (.r 12),
  Op.cmov32 4 0 14,
  Op.st 32 (some 3) (some 11) 4 0 0]

theorem b4 (prof : Profile) : Blk prof p4 0 16 o4 :=
  .cons (p4_0 _) (OpI.add (.i 61184) (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .cons (p4_8 _) (OpI.cmov32) (by decide) <|
  .cons (p4_12 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 16

/-- The stretch at `109`. -/
def p5 : List Byte := [
  0x49, 0x83, 0xc3, 0x01, 0x4c, 0x89, 0xca]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 11 (.i 1),
  Op.mov 64 2 (.r 9)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `116`. -/
def p6 : List Byte := [
  0x4c, 0x39, 0xd2]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 64 2 (.r 10)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.cmp (.r 10) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x0f, 0x84, 0xbb, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 187] 6) := by dec_rfl

/-- The stretch at `125`. -/
def p7 : List Byte := [
  0x0f, 0xb6, 0x02, 0x4c, 0x8d, 0x4a, 0x01, 0x84, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 2) none 1 0 8)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 2) none 1 1 0)] 4) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldzx 8 0 (some 2) none 1 0,
  Op.lea 64 9 (some 2) none 1 1,
  Op.test 8 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 9 o7 :=
  .cons (p7_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 9

def j5 : List Byte := [0x78, 0xc8]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 8) 64 [.rel 18446744073709551560] 2) := by dec_rfl

def j6 : List Byte := [0x74, 0xe0]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551584] 2) := by dec_rfl

/-- The stretch at `141`. -/
def p8 : List Byte := [
  0x42, 0x89, 0x04, 0x9b]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 11) 4 0 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 32 (some 3) (some 11) 4 0 0]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 4

def j7 : List Byte := [0xeb, 0xda]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551578] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p9 : List Byte := [
  0x0f, 0xb6, 0xe8, 0x3c, 0xdf]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .movzx 32 [gr 32 5, gr 8 0] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .cmp 8 [gr 8 0, Src.opd 8 (.i 223)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.zxr 5 0,
  Op.cmp 8 0 (.i 223)]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.zxr) (by decide) <|
  .cons (p9_3 _) (OpI.cmp8 (.i 223)) (by decide) <|
  .nil 5

def j8 : List Byte := [0x0f, 0x87, 0x0d, 0x01, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 7) 64 [.rel 269] 6) := by dec_rfl

/-- The stretch at `163`. -/
def p10 : List Byte := [
  0x8d, 0x95, 0x40, 0xff, 0xff, 0xff, 0xb9, 0x01, 0x00, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 5) none 1 18446744073709551424 0)] 6) := by dec_rfl
theorem p10_6 : ∀ feat, Dec feat p10 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.lea 32 2 (some 5) none 1 18446744073709551424,
  Op.mov 32 1 (.i 1)]

theorem b10 (prof : Profile) : Blk prof p10 0 11 o10 :=
  .cons (p10_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p10_6 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `174`. -/
def p11 : List Byte := [
  0x44, 0x89, 0xe8, 0x44, 0x8d, 0x41, 0xff, 0x4c, 0x89, 0xcf, 0x31, 0xf6, 0xd3, 0xe8, 0x89, 0xc1]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .lea 32 [gr 32 8, .mem (mg (some 1) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p11_12 : ∀ feat, Dec feat p11 12 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p11_14 : ∀ feat, Dec feat p11 14 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 32 0 (.r 13),
  Op.lea 32 8 (some 1) none 1 18446744073709551615,
  Op.mov 64 7 (.r 9),
  Op.xor 32 6 (.r 6),
  Op.shr 0 (.r 1),
  Op.mov 32 1 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 16 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p11_7 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p11_10 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p11_12 _) (OpI.shr (.r 1)) (by decide) <|
  .cons (p11_14 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 16

def j9 : List Byte := [0xeb, 0x11]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `192`. -/
def p12 : List Byte := [
  0x45, 0x85, 0xc0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.test 32 8 (.r 8)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

def j10 : List Byte := [0x0f, 0x84, 0xa7, 0x00, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 167] 6) := by dec_rfl

/-- The stretch at `201`. -/
def p13 : List Byte := [
  0x48, 0x83, 0xc7, 0x01, 0x41, 0x83, 0xe8, 0x01]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.add 64 7 (.i 1),
  Op.sub 32 8 (.i 1)]

theorem b13 (prof : Profile) : Blk prof p13 0 8 o13 :=
  .cons (p13_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `209`. -/
def p14 : List Byte := [
  0x4c, 0x39, 0xd7]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 64 7 (.r 10)]

theorem b14 (prof : Profile) : Blk prof p14 0 3 o14 :=
  .cons (p14_0 _) (OpI.cmp (.r 10) (.inr rfl)) (by decide) <|
  .nil 3

def j11 : List Byte := [0x74, 0x3a]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 58] 2) := by dec_rfl

/-- The stretch at `214`. -/
def p15 : List Byte := [
  0x0f, 0xb6, 0x07, 0x83, 0xc0, 0x80, 0x83, 0xf8, 0x3f]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 8)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p15_6 : ∀ feat, Dec feat p15 6 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 63)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ldzx 8 0 (some 7) none 1 0,
  Op.add 32 0 (.i 4294967168),
  Op.cmp 32 0 (.i 63)]

theorem b15 (prof : Profile) : Blk prof p15 0 9 o15 :=
  .cons (p15_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p15_6 _) (OpI.cmp (.i 63) (.inl rfl)) (by decide) <|
  .nil 9

def j12 : List Byte := [0x77, 0x2f]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 7) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `225`. -/
def p16 : List Byte := [
  0xc1, 0xe2, 0x06, 0x83, 0xc6, 0x01, 0x09, 0xc2, 0x83, 0xfe, 0x01]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .shl 32 [gr 32 2, Src.opd 8 (.i 6)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p16_6 : ∀ feat, Dec feat p16 6 (FV7z.mk .or 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_8 : ∀ feat, Dec feat p16 8 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.shl 2 (.i 6),
  Op.add 32 6 (.i 1),
  Op.or 32 2 (.r 0),
  Op.cmp 32 6 (.i 1)]

theorem b16 (prof : Profile) : Blk prof p16 0 11 o16 :=
  .cons (p16_0 _) (OpI.shl (.i 6)) (by decide) <|
  .cons (p16_3 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p16_6 _) (OpI.or (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_8 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 11

def j13 : List Byte := [0x75, 0xd2]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `238`. -/
def p17 : List Byte := [
  0x39, 0xd1]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.cmp 32 1 (.r 2)]

theorem b17 (prof : Profile) : Blk prof p17 0 2 o17 :=
  .cons (p17_0 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j14 : List Byte := [0x77, 0x1e]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 7) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `242`. -/
def p18 : List Byte := [
  0x41, 0x8d, 0x40, 0x01, 0x41, 0x83, 0xf8, 0x01]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 8) none 1 1 0)] 4) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.lea 32 0 (some 8) none 1 1,
  Op.cmp 32 8 (.i 1)]

theorem b18 (prof : Profile) : Blk prof p18 0 8 o18 :=
  .cons (p18_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p18_4 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 8

def j15 : List Byte := [0x74, 0x54]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 4) 64 [.rel 84] 2) := by dec_rfl

/-- The stretch at `252`. -/
def p19 : List Byte := [
  0x83, 0xf8, 0x03]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmp 32 0 (.i 3)]

theorem b19 (prof : Profile) : Blk prof p19 0 3 o19 :=
  .cons (p19_0 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 3

def j16 : List Byte := [0x75, 0xbf]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551551] 2) := by dec_rfl

/-- The stretch at `257`. -/
def p20 : List Byte := [
  0x81, 0xfa, 0x0f, 0x01, 0x00, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 271)] 6) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.cmp 32 2 (.i 271)]

theorem b20 (prof : Profile) : Blk prof p20 0 6 o20 :=
  .cons (p20_0 _) (OpI.cmp (.i 271) (.inl rfl)) (by decide) <|
  .nil 6

def j17 : List Byte := [0x76, 0xb7]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551543] 2) := by dec_rfl

/-- The stretch at `265`. -/
def p21 : List Byte := [
  0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.nop]

theorem b21 (prof : Profile) : Blk prof p21 0 7 o21 :=
  .cons (p21_0 _) (OpI.nop) (by decide) <|
  .nil 7

/-- The stretch at `272`. -/
def p22 : List Byte := [
  0x45, 0x85, 0xe4]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.test 32 12 (.r 12)]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

def j18 : List Byte := [0x0f, 0x84, 0xf7, 0x00, 0x00, 0x00]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 4) 64 [.rel 247] 6) := by dec_rfl

/-- The stretch at `281`. -/
def p23 : List Byte := [
  0x81, 0xc5, 0x00, 0xef, 0x00, 0x00, 0x4c, 0x89, 0xca, 0x48, 0x85, 0xdb]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .add 32 [gr 32 5, Src.opd 32 (.i 61184)] 6) := by dec_rfl
theorem p23_6 : ∀ feat, Dec feat p23 6 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p23_9 : ∀ feat, Dec feat p23 9 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.add 32 5 (.i 61184),
  Op.mov 64 2 (.r 9),
  Op.test 64 3 (.r 3)]

theorem b23 (prof : Profile) : Blk prof p23 0 12 o23 :=
  .cons (p23_0 _) (OpI.add (.i 61184) (.inl rfl)) (by decide) <|
  .cons (p23_6 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p23_9 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 12

def j19 : List Byte := [0x74, 0x04]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `295`. -/
def p24 : List Byte := [
  0x42, 0x89, 0x2c, 0x9b]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 11) 4 0 32), gr 32 5] 4) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.st 32 (some 3) (some 11) 4 0 5]

theorem b24 (prof : Profile) : Blk prof p24 0 4 o24 :=
  .cons (p24_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 4

/-- The stretch at `299`. -/
def p25 : List Byte := [
  0x49, 0x83, 0xc3, 0x01, 0x4c, 0x39, 0xd2]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.add 64 11 (.i 1),
  Op.cmp 64 2 (.r 10)]

theorem b25 (prof : Profile) : Blk prof p25 0 7 o25 :=
  .cons (p25_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p25_4 _) (OpI.cmp (.r 10) (.inr rfl)) (by decide) <|
  .nil 7

def j20 : List Byte := [0x0f, 0x85, 0x45, 0xff, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551429] 6) := by dec_rfl

/-- The stretch at `312`. -/
def p26 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0xf8, 0x4c, 0x89, 0x18, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x5b, 0x5d, 0x41,
  0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 18446744073709551608 64)] 5) := by dec_rfl
theorem p26_5 : ∀ feat, Dec feat p26 5 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), gr 64 11] 3) := by dec_rfl
theorem p26_8 : ∀ feat, Dec feat p26 8 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p26_13 : ∀ feat, Dec feat p26 13 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p26_14 : ∀ feat, Dec feat p26 14 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p26_15 : ∀ feat, Dec feat p26 15 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p26_17 : ∀ feat, Dec feat p26 17 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p26_19 : ∀ feat, Dec feat p26 19 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p26_21 : ∀ feat, Dec feat p26 21 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.ld 64 0 (some 4) none 1 18446744073709551608,
  Op.st 64 (some 0) none 1 0 11,
  Op.mov 32 0 (.i 1),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b26 (prof : Profile) : Blk prof p26 0 23 o26 :=
  .cons (p26_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p26_5 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p26_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p26_13 _) (OpI.pop) (by decide) <|
  .cons (p26_14 _) (OpI.pop) (by decide) <|
  .cons (p26_15 _) (OpI.pop) (by decide) <|
  .cons (p26_17 _) (OpI.pop) (by decide) <|
  .cons (p26_19 _) (OpI.pop) (by decide) <|
  .cons (p26_21 _) (OpI.pop) (by decide) <|
  .nil 23

/-- The stretch at `336`. -/
def p27 : List Byte := [
  0x45, 0x85, 0xff]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .test 32 [gr 32 15, Src.opd 32 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.test 32 15 (.r 15)]

theorem b27 (prof : Profile) : Blk prof p27 0 3 o27 :=
  .cons (p27_0 _) (OpI.test (.r 15) (.inl rfl)) (by decide) <|
  .nil 3

def j21 : List Byte := [0x0f, 0x84, 0x70, 0xff, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551472] 6) := by dec_rfl

/-- The stretch at `345`. -/
def p28 : List Byte := [
  0x89, 0xd0, 0x25, 0xe0, 0x03, 0x00, 0x00, 0x3d, 0x60, 0x03, 0x00, 0x00]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p28_2 : ∀ feat, Dec feat p28 2 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 992)] 5) := by dec_rfl
theorem p28_7 : ∀ feat, Dec feat p28 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 864)] 5) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.mov 32 0 (.r 2),
  Op.and 32 0 (.i 992),
  Op.cmp 32 0 (.i 864)]

theorem b28 (prof : Profile) : Blk prof p28 0 12 o28 :=
  .cons (p28_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p28_2 _) (OpI.and (.i 992) (.inl rfl)) (by decide) <|
  .cons (p28_7 _) (OpI.cmp (.i 864) (.inl rfl)) (by decide) <|
  .nil 12

def j22 : List Byte := [0x0f, 0x85, 0x5e, 0xff, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551454] 6) := by dec_rfl

/-- The stretch at `363`. -/
def p29 : List Byte := [
  0x44, 0x89, 0xfe]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.mov 32 6 (.r 15)]

theorem b29 (prof : Profile) : Blk prof p29 0 3 o29 :=
  .cons (p29_0 _) (OpI.mov (.r 15) (.inl rfl)) (by decide) <|
  .nil 3

def j23 : List Byte := [0xeb, 0xa0]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk .jmp 64 [.rel 18446744073709551520] 2) := by dec_rfl

/-- The stretch at `368`. -/
def p30 : List Byte := [
  0x8b, 0x44, 0x24, 0xf4, 0x85, 0xc0]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 18446744073709551604 32)] 4) := by dec_rfl
theorem p30_4 : ∀ feat, Dec feat p30 4 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.ld 32 0 (some 4) none 1 18446744073709551604,
  Op.test 32 0 (.r 0)]

theorem b30 (prof : Profile) : Blk prof p30 0 6 o30 :=
  .cons (p30_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p30_4 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `376`. -/
def p31 : List Byte := [
  0x89, 0xd0, 0x83, 0xe0, 0x80, 0x3d, 0x80, 0xef, 0x00, 0x00]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p31_2 : ∀ feat, Dec feat p31 2 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p31_5 : ∀ feat, Dec feat p31 5 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 61312)] 5) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.mov 32 0 (.r 2),
  Op.and 32 0 (.i 4294967168),
  Op.cmp 32 0 (.i 61312)]

theorem b31 (prof : Profile) : Blk prof p31 0 10 o31 :=
  .cons (p31_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p31_2 _) (OpI.and (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p31_5 _) (OpI.cmp (.i 61312) (.inl rfl)) (by decide) <|
  .nil 10

def j24 : List Byte := [0x0f, 0x84, 0xa0, 0x00, 0x00, 0x00]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 4) 64 [.rel 160] 6) := by dec_rfl

/-- The stretch at `392`. -/
def p32 : List Byte := [
  0x81, 0xfa, 0xff, 0xff, 0x00, 0x00]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 65535)] 6) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.cmp 32 2 (.i 65535)]

theorem b32 (prof : Profile) : Blk prof p32 0 6 o32 :=
  .cons (p32_0 _) (OpI.cmp (.i 65535) (.inl rfl)) (by decide) <|
  .nil 6

def j25 : List Byte := [0x77, 0x38]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 7) 64 [.rel 56] 2) := by dec_rfl

/-- The stretch at `405`. -/
def p33 : List Byte := [
  0x42, 0x89, 0x14, 0x9b]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 11) 4 0 32), gr 32 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.st 32 (some 3) (some 11) 4 0 2]

theorem b33 (prof : Profile) : Blk prof p33 0 4 o33 :=
  .cons (p33_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 4

/-- The stretch at `409`. -/
def p34 : List Byte := [
  0x49, 0x83, 0xc3, 0x01]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.add 64 11 (.i 1)]

theorem b34 (prof : Profile) : Blk prof p34 0 4 o34 :=
  .cons (p34_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `413`. -/
def p35 : List Byte := [
  0x49, 0x8d, 0x14, 0x31]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 9) (some 6) 1 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.lea 64 2 (some 9) (some 6) 1 0]

theorem b35 (prof : Profile) : Blk prof p35 0 4 o35 :=
  .cons (p35_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

def j26 : List Byte := [0xe9, 0xce, 0xfe, 0xff, 0xff]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk .jmp 64 [.rel 18446744073709551310] 5) := by dec_rfl

/-- The stretch at `432`. -/
def p36 : List Byte := [
  0x3c, 0xef]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .cmp 8 [gr 8 0, Src.opd 8 (.i 239)] 2) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.cmp 8 0 (.i 239)]

theorem b36 (prof : Profile) : Blk prof p36 0 2 o36 :=
  .cons (p36_0 _) (OpI.cmp8 (.i 239)) (by decide) <|
  .nil 2

def j27 : List Byte := [0x77, 0x44]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 7) 64 [.rel 68] 2) := by dec_rfl

/-- The stretch at `436`. -/
def p37 : List Byte := [
  0x8d, 0x95, 0x20, 0xff, 0xff, 0xff, 0xb9, 0x02, 0x00, 0x00, 0x00]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 5) none 1 18446744073709551392 0)] 6) := by dec_rfl
theorem p37_6 : ∀ feat, Dec feat p37 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.lea 32 2 (some 5) none 1 18446744073709551392,
  Op.mov 32 1 (.i 2)]

theorem b37 (prof : Profile) : Blk prof p37 0 11 o37 :=
  .cons (p37_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p37_6 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 11

def j28 : List Byte := [0xe9, 0xea, 0xfe, 0xff, 0xff]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk .jmp 64 [.rel 18446744073709551338] 5) := by dec_rfl

def j29 : List Byte := [0x74, 0x1f]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 4) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `461`. -/
def p38 : List Byte := [
  0x89, 0xd0, 0x81, 0xe2, 0xff, 0x03, 0x00, 0x00, 0xc1, 0xe8, 0x0a, 0x05, 0xc0, 0xd7, 0x00, 0x00,
  0x42, 0x89, 0x04, 0x9b, 0x8d, 0x82, 0x00, 0xdc, 0x00, 0x00, 0x42, 0x89, 0x44, 0x9b, 0x04]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p38_2 : ∀ feat, Dec feat p38 2 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 1023)] 6) := by dec_rfl
theorem p38_8 : ∀ feat, Dec feat p38 8 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 10)] 3) := by dec_rfl
theorem p38_11 : ∀ feat, Dec feat p38 11 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 55232)] 5) := by dec_rfl
theorem p38_16 : ∀ feat, Dec feat p38 16 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 11) 4 0 32), gr 32 0] 4) := by dec_rfl
theorem p38_20 : ∀ feat, Dec feat p38 20 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 2) none 1 56320 0)] 6) := by dec_rfl
theorem p38_26 : ∀ feat, Dec feat p38 26 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 11) 4 4 32), gr 32 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.mov 32 0 (.r 2),
  Op.and 32 2 (.i 1023),
  Op.shr 0 (.i 10),
  Op.add 32 0 (.i 55232),
  Op.st 32 (some 3) (some 11) 4 0 0,
  Op.lea 32 0 (some 2) none 1 56320,
  Op.st 32 (some 3) (some 11) 4 4 0]

theorem b38 (prof : Profile) : Blk prof p38 0 31 o38 :=
  .cons (p38_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p38_2 _) (OpI.and (.i 1023) (.inl rfl)) (by decide) <|
  .cons (p38_8 _) (OpI.shr (.i 10)) (by decide) <|
  .cons (p38_11 _) (OpI.add (.i 55232) (.inl rfl)) (by decide) <|
  .cons (p38_16 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p38_20 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p38_26 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 31

/-- The stretch at `492`. -/
def p39 : List Byte := [
  0x49, 0x83, 0xc3, 0x02]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.add 64 11 (.i 2)]

theorem b39 (prof : Profile) : Blk prof p39 0 4 o39 :=
  .cons (p39_0 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .nil 4

def j30 : List Byte := [0xeb, 0xab]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk .jmp 64 [.rel 18446744073709551531] 2) := by dec_rfl

/-- The stretch at `504`. -/
def p40 : List Byte := [
  0x8d, 0x95, 0x10, 0xff, 0xff, 0xff, 0xb9, 0x03, 0x00, 0x00, 0x00]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 5) none 1 18446744073709551376 0)] 6) := by dec_rfl
theorem p40_6 : ∀ feat, Dec feat p40 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 3)] 5) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.lea 32 2 (some 5) none 1 18446744073709551376,
  Op.mov 32 1 (.i 3)]

theorem b40 (prof : Profile) : Blk prof p40 0 11 o40 :=
  .cons (p40_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p40_6 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .nil 11

def j31 : List Byte := [0xe9, 0xa6, 0xfe, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk .jmp 64 [.rel 18446744073709551270] 5) := by dec_rfl

/-- The stretch at `528`. -/
def p41 : List Byte := [
  0x89, 0xf2, 0xbd, 0xfd, 0xff, 0x00, 0x00, 0x4c, 0x01, 0xca, 0x48, 0x85, 0xdb]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p41_2 : ∀ feat, Dec feat p41 2 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 65533)] 5) := by dec_rfl
theorem p41_7 : ∀ feat, Dec feat p41 7 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p41_10 : ∀ feat, Dec feat p41 10 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.mov 32 2 (.r 6),
  Op.mov 32 5 (.i 65533),
  Op.add 64 2 (.r 9),
  Op.test 64 3 (.r 3)]

theorem b41 (prof : Profile) : Blk prof p41 0 13 o41 :=
  .cons (p41_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p41_2 _) (OpI.mov (.i 65533) (.inl rfl)) (by decide) <|
  .cons (p41_7 _) (OpI.add (.r 9) (.inr rfl)) (by decide) <|
  .cons (p41_10 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 13

def j32 : List Byte := [0x0f, 0x85, 0x04, 0xff, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551364] 6) := by dec_rfl

def j33 : List Byte := [0xe9, 0x03, 0xff, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk .jmp 64 [.rel 18446744073709551363] 5) := by dec_rfl

def j34 : List Byte := [0x0f, 0x84, 0x3c, 0xfe, 0xff, 0xff]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551164] 6) := by dec_rfl

/-- The stretch at `561`. -/
def p42 : List Byte := [
  0x8d, 0x85, 0x00, 0xef, 0x00, 0x00, 0x45, 0x85, 0xe4, 0x41, 0x0f, 0x44, 0xc6]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 5) none 1 61184 0)] 6) := by dec_rfl
theorem p42_6 : ∀ feat, Dec feat p42 6 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p42_9 : ∀ feat, Dec feat p42 9 (FV7z.mk (.cmovcc 4) 32 [gr 32 0, gr 32 14] 4) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.lea 32 0 (some 5) none 1 61184,
  Op.test 32 12 (.r 12),
  Op.cmov32 4 0 14]

theorem b42 (prof : Profile) : Blk prof p42 0 13 o42 :=
  .cons (p42_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p42_6 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .cons (p42_9 _) (OpI.cmov32) (by decide) <|
  .nil 13

def j35 : List Byte := [0xe9, 0x4a, 0xfe, 0xff, 0xff]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk .jmp 64 [.rel 18446744073709551178] 5) := by dec_rfl

/-- The stretch at `579`. -/
def p43 : List Byte := [
  0x45, 0x31, 0xdb]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .xor 32 [gr 32 11, Src.opd 32 (.r 11)] 3) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.xor 32 11 (.r 11)]

theorem b43 (prof : Profile) : Blk prof p43 0 3 o43 :=
  .cons (p43_0 _) (OpI.xor (.r 11) (.inl rfl)) (by decide) <|
  .nil 3

def j36 : List Byte := [0xe9, 0xed, 0xfe, 0xff, 0xff]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk .jmp 64 [.rel 18446744073709551341] 5) := by dec_rfl

end FV7z.U16
