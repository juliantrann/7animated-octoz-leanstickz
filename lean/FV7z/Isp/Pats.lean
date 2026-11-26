import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `IsString1PrefixedByString2_NoCase_Ascii` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Isp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x0f, 0xb6, 0x06, 0x84, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ldzx 8 0 (some 6) none 1 0,
  Op.test 8 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x4d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 77] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x31, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0xeb, 0x1f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p2 : List Byte := [
  0x41, 0x80, 0xf9, 0x19]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [gr 8 9, Src.opd 8 (.i 25)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 8 9 (.i 25)]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmp8 (.i 25)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x77, 0x4a]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 74] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p3 : List Byte := [
  0x83, 0xc0, 0x20, 0x44, 0x0f, 0xb6, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 32)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .movzx 32 [gr 32 8, gr 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 32 0 (.i 32),
  Op.zxr 8 0]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.add (.i 32) (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.zxr) (by decide) <|
  .nil 7

/-- The stretch at `29`. -/
def p4 : List Byte := [
  0x41, 0x39, 0xc8]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 32 8 (.r 1)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x75, 0x3e]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 62] 2) := by dec_rfl

/-- The stretch at `34`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xc2, 0x01, 0x0f, 0xb6, 0x04, 0x16, 0x84, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) (some 2) 1 0 8)] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 2 (.i 1),
  Op.ldzx 8 0 (some 6) (some 2) 1 0,
  Op.test 8 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 10

def j4 : List Byte := [0x74, 0x2a]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 42] 2) := by dec_rfl

/-- The stretch at `46`. -/
def p6 : List Byte := [
  0x8b, 0x0c, 0x97, 0x44, 0x0f, 0xb6, 0xc0, 0x41, 0x39, 0xc8]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) (some 2) 4 0 32)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .movzx 32 [gr 32 8, gr 8 0] 4) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 32 1 (some 7) (some 2) 4 0,
  Op.zxr 8 0,
  Op.cmp 32 8 (.r 1)]

theorem b6 (prof : Profile) : Blk prof p6 0 10 o6 :=
  .cons (p6_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.zxr) (by decide) <|
  .cons (p6_7 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .nil 10

def j5 : List Byte := [0x74, 0xe8]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551592] 2) := by dec_rfl

/-- The stretch at `58`. -/
def p7 : List Byte := [
  0x44, 0x8d, 0x51, 0xbf, 0x44, 0x8d, 0x48, 0xbf, 0x41, 0x83, 0xfa, 0x19]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 32 [gr 32 10, .mem (mg (some 1) none 1 18446744073709551551 0)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .lea 32 [gr 32 9, .mem (mg (some 0) none 1 18446744073709551551 0)] 4) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .cmp 32 [gr 32 10, Src.opd 32 (.i 25)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 32 10 (some 1) none 1 18446744073709551551,
  Op.lea 32 9 (some 0) none 1 18446744073709551551,
  Op.cmp 32 10 (.i 25)]

theorem b7 (prof : Profile) : Blk prof p7 0 12 o7 :=
  .cons (p7_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p7_8 _) (OpI.cmp (.i 25) (.inl rfl)) (by decide) <|
  .nil 12

def j6 : List Byte := [0x77, 0xc8]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551560] 2) := by dec_rfl

/-- The stretch at `72`. -/
def p8 : List Byte := [
  0x83, 0xc1, 0x20, 0x41, 0x80, 0xf9, 0x19]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 32)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .cmp 8 [gr 8 9, Src.opd 8 (.i 25)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 32 1 (.i 32),
  Op.cmp 8 9 (.i 25)]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.add (.i 32) (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.cmp8 (.i 25)) (by decide) <|
  .nil 7

def j7 : List Byte := [0x77, 0xcc]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551564] 2) := by dec_rfl

def j8 : List Byte := [0xeb, 0xc3]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551555] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p9 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 0 (.i 1)]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `96`. -/
def p10 : List Byte := [
  0x31, 0xc0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b10 (prof : Profile) : Blk prof p10 0 2 o10 :=
  .cons (p10_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Isp
