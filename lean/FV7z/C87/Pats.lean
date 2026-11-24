import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `csuTg 87` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C87
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `2160`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xc9, 0x31, 0xd2, 0x4c, 0x8d, 0x05, 0x61, 0x12, 0x38, 0x00, 0xb8,
  0x08, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0x0d, 0xd5, 0x9f, 0x2c, 0x00, 0x41, 0x89, 0xd2, 0x8d, 0x3c,
  0x08, 0x89, 0xce, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .lea 64 [gr 64 8, .mem (mrip 3674721 0)] 7) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .lea 64 [gr 64 9, .mem (mrip 2924501 0)] 7) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 0) (some 1) 1 0 0)] 3) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.xor 32 1 (.r 1),
  Op.xor 32 2 (.r 2),
  Op.mov 64 8 (.i 7986208),
  Op.mov 32 0 (.i 8),
  Op.mov 64 9 (.i 7236000),
  Op.mov 32 10 (.r 2),
  Op.lea 32 7 (some 0) (some 1) 1 0,
  Op.mov 32 6 (.r 1),
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x41c9b0 : Addr) 0 37 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.xor (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p0_8 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_15 _) ((OpI.mov (.i 8) (.inl rfl)).at _) (by decide) <|
  .cons (p0_20 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_27 _) ((OpI.mov (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p0_30 _) ((OpI.lea (.inl rfl)).at _) (by decide) <|
  .cons (p0_33 _) ((OpI.mov (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p0_35 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 37

def j0 : List Byte := [0x74, 0x33]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 51] 2) := by dec_rfl

/-- The stretch at `2199`. -/
def p1 : List Byte := [
  0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 9) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.nop) (by decide) <|
  .nil 9

/-- The stretch at `2208`. -/
def p2 : List Byte := [
  0x89, 0xf0, 0x83, 0xc6, 0x01, 0x45, 0x88, 0x14, 0x00, 0x39, 0xf7]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 8 [.mem (mg (some 8) (some 0) 1 0 8), gr 8 10] 4) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 0 (.r 6),
  Op.add 32 6 (.i 1),
  Op.st 8 (some 8) (some 0) 1 0 10,
  Op.cmp 32 7 (.r 6)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x75, 0xf3]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551603] 2) := by dec_rfl

/-- The stretch at `2221`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc2, 0x01, 0x89, 0xf9, 0x48, 0x83, 0xfa, 0x1f]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 31)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 2 (.i 1),
  Op.mov 32 1 (.r 7),
  Op.cmp 64 2 (.i 31)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.cmp (.i 31) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x74, 0x27]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `2233`. -/
def p4 : List Byte := [
  0x41, 0x0f, 0xb6, 0x04, 0x11, 0x41, 0x89, 0xd2, 0x89, 0xce, 0x8d, 0x3c, 0x08, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 9) (some 2) 1 0 8)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 0) (some 1) 1 0 0)] 3) := by dec_rfl
theorem p4_13 : ∀ feat, Dec feat p4 13 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 0 (some 9) (some 2) 1 0,
  Op.mov 32 10 (.r 2),
  Op.mov 32 6 (.r 1),
  Op.lea 32 7 (some 0) (some 1) 1 0,
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 15 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p4_8 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p4_10 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p4_13 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 15

def j3 : List Byte := [0x75, 0xd6]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551574] 2) := by dec_rfl

/-- The stretch at `2250`. -/
def p5 : List Byte := [
  0x89, 0xcf, 0x48, 0x83, 0xc2, 0x01, 0x89, 0xf9, 0x48, 0x83, 0xfa, 0x1f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 31)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 7 (.r 1),
  Op.add 64 2 (.i 1),
  Op.mov 32 1 (.r 7),
  Op.cmp 64 2 (.i 31)]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.cmp (.i 31) (.inr rfl)) (by decide) <|
  .nil 12

def j4 : List Byte := [0x75, 0xe1]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551585] 2) := by dec_rfl

/-- The stretch at `2264`. -/
def p6 : List Byte := [
  0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.nop]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `2272`. -/
def p7 : List Byte := [
  0x31, 0xc0, 0xba, 0x01, 0x00, 0x00, 0x00, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0x0d,
  0x15, 0x38, 0x00, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_2 : ∀ feat, Dec feat p7 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p7_12 : ∀ feat, Dec feat p7 12 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3675405 0)] 7) := by dec_rfl
theorem p7_19 : ∀ feat, Dec feat p7 19 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.mov 32 2 (.i 1),
  Op.mov 32 6 (.i 1),
  Op.mov 64 7 (.i 7987008),
  Op.nop]

theorem b7 (prof : Profile) : BlkA prof p7 (0x41ca20 : Addr) 0 24 o7 :=
  .cons (p7_0 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p7_2 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p7_7 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p7_12 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_19 _) ((OpI.nop).at _) (by decide) <|
  .nil 24

/-- The stretch at `2296`. -/
def p8 : List Byte := [
  0x41, 0x0f, 0xb6, 0x0c, 0x00, 0x41, 0x89, 0xf3, 0x89, 0x14, 0x87, 0x48, 0x83, 0xc0, 0x01, 0x41,
  0xd3, 0xe3, 0x44, 0x01, 0xda, 0x48, 0x3d, 0x1f, 0x03, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 8) (some 0) 1 0 8)] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.r 6)] 3) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 32 [.mem (mg (some 7) (some 0) 4 0 32), gr 32 2] 3) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p8_15 : ∀ feat, Dec feat p8 15 (FV7z.mk .shl 32 [gr 32 11, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p8_18 : ∀ feat, Dec feat p8 18 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 11)] 3) := by dec_rfl
theorem p8_21 : ∀ feat, Dec feat p8 21 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 799)] 6) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ldzx 8 1 (some 8) (some 0) 1 0,
  Op.mov 32 11 (.r 6),
  Op.st 32 (some 7) (some 0) 4 0 2,
  Op.add 64 0 (.i 1),
  Op.shl 11 (.r 1),
  Op.add 32 2 (.r 11),
  Op.cmp 64 0 (.i 799)]

theorem b8 (prof : Profile) : Blk prof p8 0 27 o8 :=
  .cons (p8_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p8_5 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p8_8 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_11 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p8_15 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p8_18 _) (OpI.add (.r 11) (.inl rfl)) (by decide) <|
  .cons (p8_21 _) (OpI.cmp (.i 799) (.inr rfl)) (by decide) <|
  .nil 27

def j5 : List Byte := [0x75, 0xe3]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551587] 2) := by dec_rfl

/-- The stretch at `2325`. -/
def p9 : List Byte := [
  0x31, 0xc0, 0x31, 0xc9, 0xba, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x4c, 0x8d,
  0x05, 0xd6, 0x10, 0x38, 0x00, 0x48, 0x8d, 0x35, 0xef, 0x9e, 0x2c, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p9_9 : ∀ feat, Dec feat p9 9 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p9_14 : ∀ feat, Dec feat p9 14 (FV7z.mk .lea 64 [gr 64 8, .mem (mrip 3674326 0)] 7) := by dec_rfl
theorem p9_21 : ∀ feat, Dec feat p9 21 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 2924271 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.xor 32 1 (.r 1),
  Op.mov 32 2 (.i 1),
  Op.mov 32 7 (.i 1),
  Op.mov 64 8 (.i 7985984),
  Op.mov 64 6 (.i 7235936)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x41ca55 : Addr) 0 28 o9 :=
  .cons (p9_0 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p9_2 _) ((OpI.xor (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p9_4 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p9_9 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p9_14 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_21 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 28

def j6 : List Byte := [0xeb, 0x09]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `2360`. -/
def p10 : List Byte := [
  0x0f, 0xb6, 0x0c, 0x06]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 6) (some 0) 1 0 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ldzx 8 1 (some 6) (some 0) 1 0]

theorem b10 (prof : Profile) : Blk prof p10 0 4 o10 :=
  .cons (p10_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `2364`. -/
def p11 : List Byte := [
  0x41, 0x89, 0xf9, 0x41, 0x89, 0x14, 0x80, 0x48, 0x83, 0xc0, 0x01, 0x41, 0xd3, 0xe1, 0x44, 0x01,
  0xca, 0x48, 0x83, 0xf8, 0x36]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .mov 32 [.mem (mg (some 8) (some 0) 4 0 32), gr 32 2] 4) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_11 : ∀ feat, Dec feat p11 11 (FV7z.mk .shl 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p11_14 : ∀ feat, Dec feat p11 14 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p11_17 : ∀ feat, Dec feat p11 17 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 54)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 32 9 (.r 7),
  Op.st 32 (some 8) (some 0) 4 0 2,
  Op.add 64 0 (.i 1),
  Op.shl 9 (.r 1),
  Op.add 32 2 (.r 9),
  Op.cmp 64 0 (.i 54)]

theorem b11 (prof : Profile) : Blk prof p11 0 21 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p11_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p11_11 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p11_14 _) (OpI.add (.r 9) (.inl rfl)) (by decide) <|
  .cons (p11_17 _) (OpI.cmp (.i 54) (.inr rfl)) (by decide) <|
  .nil 21

def j7 : List Byte := [0x75, 0xe5]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551589] 2) := by dec_rfl

end FV7z.C87
