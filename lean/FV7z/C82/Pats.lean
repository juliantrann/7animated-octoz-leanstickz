import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `csuTg 82` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 13 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C82
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `1888`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x4c, 0x8d, 0x15, 0x94, 0x11, 0x38, 0x00, 0x31, 0xd2, 0x31, 0xc9,
  0x31, 0xc0, 0x41, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x4d, 0x8d, 0x4a, 0x01, 0x4c, 0x8d, 0x05, 0x3d,
  0x9d, 0x2c, 0x00, 0x48, 0x8d, 0x3d, 0xf6, 0x9c, 0x2c, 0x00, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .lea 64 [gr 64 10, .mem (mrip 3674516 0)] 7) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .lea 64 [gr 64 9, .mem (mg (some 10) none 1 1 0)] 4) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .lea 64 [gr 64 8, .mem (mrip 2923837 0)] 7) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 2923766 0)] 7) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 10 (.i 7985728),
  Op.xor 32 2 (.r 2),
  Op.xor 32 1 (.r 1),
  Op.xor 32 0 (.r 0),
  Op.mov 32 11 (.i 1),
  Op.lea 64 9 (some 10) none 1 1,
  Op.mov 64 8 (.i 7235072),
  Op.mov 64 7 (.i 7235008),
  Op.nop]

theorem b0 (prof : Profile) : BlkA prof p0 (0x41c8a0 : Addr) 0 48 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_12 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p0_14 _) ((OpI.xor (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p0_16 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p0_18 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p0_24 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p0_28 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_35 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_42 _) ((OpI.nop).at _) (by decide) <|
  .nil 48

/-- The stretch at `1936`. -/
def p1 : List Byte := [
  0x44, 0x89, 0xde, 0xd3, 0xe6, 0x85, 0xf6]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 11)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .shl 32 [gr 32 6, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 6 (.r 11),
  Op.shl 6 (.r 1),
  Op.test 32 6 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 11) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p1_5 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x74, 0x22]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `1945`. -/
def p2 : List Byte := [
  0x4a, 0x8d, 0x0c, 0x10, 0x83, 0xee, 0x01, 0x4c, 0x01, 0xc8, 0x89, 0xd3, 0x48, 0x01, 0xf0, 0x0f,
  0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) (some 10) 1 0 0)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .sub 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p2_15 : ∀ feat, Dec feat p2 15 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 64 1 (some 0) (some 10) 1 0,
  Op.sub 32 6 (.i 1),
  Op.add 64 0 (.r 9),
  Op.mov 32 3 (.r 2),
  Op.add 64 0 (.r 6),
  Op.nop]

theorem b2 (prof : Profile) : Blk prof p2 0 23 o2 :=
  .cons (p2_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.add (.r 9) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.add (.r 6) (.inr rfl)) (by decide) <|
  .cons (p2_15 _) (OpI.nop) (by decide) <|
  .nil 23

/-- The stretch at `1968`. -/
def p3 : List Byte := [
  0x88, 0x19, 0x48, 0x83, 0xc1, 0x01, 0x48, 0x39, 0xc1]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 8 [.mem (mg (some 1) none 1 0 8), gr 8 3] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 8 (some 1) none 1 0 3,
  Op.add 64 1 (.i 1),
  Op.cmp 64 1 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x75, 0xf5]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551605] 2) := by dec_rfl

/-- The stretch at `1979`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc2, 0x01, 0x48, 0x83, 0xfa, 0x1d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 29)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 2 (.i 1),
  Op.cmp 64 2 (.i 29)]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.cmp (.i 29) (.inr rfl)) (by decide) <|
  .nil 8

def j2 : List Byte := [0x74, 0x0b]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `1989`. -/
def p5 : List Byte := [
  0x41, 0x0f, 0xb6, 0x04, 0x10, 0x0f, 0xb6, 0x0c, 0x17]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 8) (some 2) 1 0 8)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 7) (some 2) 1 0 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 8 0 (some 8) (some 2) 1 0,
  Op.ldzx 8 1 (some 7) (some 2) 1 0]

theorem b5 (prof : Profile) : Blk prof p5 0 9 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 9

def j3 : List Byte := [0xeb, 0xc0]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551552] 2) := by dec_rfl

/-- The stretch at `2000`. -/
def p6 : List Byte := [
  0x31, 0xd2, 0x31, 0xc9, 0x31, 0xc0, 0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0x1d,
  0x0f, 0x38, 0x00, 0x48, 0x8d, 0x35, 0xd6, 0x9b, 0x2c, 0x00, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p6_2 : ∀ feat, Dec feat p6 2 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 3673885 0)] 7) := by dec_rfl
theorem p6_19 : ∀ feat, Dec feat p6 19 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 2923478 0)] 7) := by dec_rfl
theorem p6_26 : ∀ feat, Dec feat p6 26 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.xor 32 1 (.r 1),
  Op.xor 32 0 (.r 0),
  Op.mov 32 8 (.i 1),
  Op.mov 64 7 (.i 7985216),
  Op.mov 64 6 (.i 7234816),
  Op.nop]

theorem b6 (prof : Profile) : BlkA prof p6 (0x41c910 : Addr) 0 32 o6 :=
  .cons (p6_0 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p6_2 _) ((OpI.xor (.r 1) (.inl rfl)).at _) (by decide) <|
  .cons (p6_4 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p6_6 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p6_12 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_19 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_26 _) ((OpI.nop).at _) (by decide) <|
  .nil 32

/-- The stretch at `2032`. -/
def p7 : List Byte := [
  0x44, 0x89, 0xc3, 0x41, 0x89, 0xd1, 0xd3, 0xe3, 0x89, 0xd9, 0x85, 0xdb]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .shl 32 [gr 32 3, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .test 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 32 3 (.r 8),
  Op.mov 32 9 (.r 2),
  Op.shl 3 (.r 1),
  Op.mov 32 1 (.r 3),
  Op.test 32 3 (.r 3)]

theorem b7 (prof : Profile) : Blk prof p7 0 12 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p7_8 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.test (.r 3) (.inl rfl)) (by decide) <|
  .nil 12

def j4 : List Byte := [0x74, 0x10]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `2046`. -/
def p8 : List Byte := [
  0x01, 0xc1]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 32 1 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.add (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `2048`. -/
def p9 : List Byte := [
  0x41, 0x89, 0xc2, 0x83, 0xc0, 0x01, 0x46, 0x88, 0x0c, 0x17, 0x39, 0xc8]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .mov 8 [.mem (mg (some 7) (some 10) 1 0 8), gr 8 9] 4) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 10 (.r 0),
  Op.add 32 0 (.i 1),
  Op.st 8 (some 7) (some 10) 1 0 9,
  Op.cmp 32 0 (.r 1)]

theorem b9 (prof : Profile) : Blk prof p9 0 12 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p9_3 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p9_6 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p9_10 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .nil 12

def j5 : List Byte := [0x75, 0xf2]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551602] 2) := by dec_rfl

/-- The stretch at `2062`. -/
def p10 : List Byte := [
  0x48, 0x83, 0xc2, 0x01, 0x48, 0x83, 0xfa, 0x12]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 18)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.add 64 2 (.i 1),
  Op.cmp 64 2 (.i 18)]

theorem b10 (prof : Profile) : Blk prof p10 0 8 o10 :=
  .cons (p10_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.cmp (.i 18) (.inr rfl)) (by decide) <|
  .nil 8

def j6 : List Byte := [0x74, 0x08]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `2072`. -/
def p11 : List Byte := [
  0x0f, 0xb6, 0x0c, 0x16]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 6) (some 2) 1 0 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ldzx 8 1 (some 6) (some 2) 1 0]

theorem b11 (prof : Profile) : Blk prof p11 0 4 o11 :=
  .cons (p11_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 4

def j7 : List Byte := [0xeb, 0xd2]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `2080`. -/
def p12 : List Byte := [
  0x5b]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.pop 3]

theorem b12 (prof : Profile) : Blk prof p12 0 1 o12 :=
  .cons (p12_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.C82
