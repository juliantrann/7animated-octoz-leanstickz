import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `FindFile_KeepDots` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 13 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fkd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x54, 0x0f, 0xb6, 0xd2, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x8b, 0x36]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .movzx 32 [gr 32 2, gr 8 2] 3) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 12,
  Op.zxr 2 2,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.ld 64 6 (some 6) none 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.zxr) (by decide) <|
  .cons (p0_5 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 16

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc4, 0x84, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.test 8 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x74, 0x45]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 69] 2) := by dec_rfl

/-- The stretch at `28`. -/
def p2 : List Byte := [
  0x8b, 0x43, 0x08, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 0 (some 3) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x74, 0x3e]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 62] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x13, 0x48, 0x8d, 0x74, 0x02, 0xff, 0x80, 0x3e, 0x2e]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 2) (some 0) 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 0 8), .imm 8 46] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 2 (some 3) none 1 0,
  Op.lea 64 6 (some 2) (some 0) 1 18446744073709551615,
  Op.cmpmi 8 (some 6) none 1 0 46]

theorem b3 (prof : Profile) : Blk prof p3 0 11 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 11

def j2 : List Byte := [0x75, 0x31]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p4 : List Byte := [
  0x48, 0x39, 0xf2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 64 2 (.r 6)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x23]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `53`. -/
def p5 : List Byte := [
  0x0f, 0xb6, 0x46, 0xff, 0x3c, 0x2f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) none 1 18446744073709551615 8)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .cmp 8 [gr 8 0, Src.opd 8 (.i 47)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 8 0 (some 6) none 1 18446744073709551615,
  Op.cmp 8 0 (.i 47)]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.cmp8 (.i 47)) (by decide) <|
  .nil 6

def j4 : List Byte := [0x74, 0x1b]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `61`. -/
def p6 : List Byte := [
  0x3c, 0x2e]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 8 [gr 8 0, Src.opd 8 (.i 46)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 8 0 (.i 46)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.cmp8 (.i 46)) (by decide) <|
  .nil 2

def j5 : List Byte := [0x75, 0x20]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `65`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x46, 0xff, 0x48, 0x39, 0xc2]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 6) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 64 0 (some 6) none 1 18446744073709551615,
  Op.cmp 64 2 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 7 o7 :=
  .cons (p7_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x74, 0x26]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 38] 2) := by dec_rfl

/-- The stretch at `74`. -/
def p8 : List Byte := [
  0x80, 0x7e, 0xfe, 0x2f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 18446744073709551614 8), .imm 8 47] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmpmi 8 (some 6) none 1 18446744073709551614 47]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j7 : List Byte := [0x75, 0x11]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p9 : List Byte := [
  0x48, 0x89, 0xc6, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 6 (.r 0),
  Op.nop]

theorem b9 (prof : Profile) : Blk prof p9 0 8 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p9_3 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `88`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0x7d, 0x68]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) none 1 104 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.lea 64 7 (some 5) none 1 104]

theorem b10 (prof : Profile) : Blk prof p10 0 4 o10 :=
  .cons (p10_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `97`. -/
def p11 : List Byte := [
  0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.pop) (by decide) <|
  .cons (p11_4 _) (OpI.pop) (by decide) <|
  .cons (p11_5 _) (OpI.pop) (by decide) <|
  .nil 7

/-- The stretch at `112`. -/
def p12 : List Byte := [
  0x48, 0x89, 0xd6]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 6 (.r 2)]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

def j8 : List Byte := [0xeb, 0xe3]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551587] 2) := by dec_rfl

end FV7z.Fkd
