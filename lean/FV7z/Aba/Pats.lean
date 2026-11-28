import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AllocBstrFromAscii` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Aba
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x85, 0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 7 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x74, 0x57]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 87] 2) := by dec_rfl

/-- The stretch at `9`. -/
def p1 : List Byte := [
  0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_1 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `23`. -/
def p2 : List Byte := [
  0x31, 0xff, 0x48, 0x89, 0xc6, 0x89, 0xc5]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 7 (.r 7),
  Op.mov 64 6 (.r 0),
  Op.mov 32 5 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `35`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x74, 0x28]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p4 : List Byte := [
  0x31, 0xd2, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p4_2 : ∀ feat, Dec feat p4 2 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.nop]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p4_2 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `48`. -/
def p5 : List Byte := [
  0x89, 0xd1, 0x83, 0xc2, 0x01, 0x0f, 0xb6, 0x34, 0x0b, 0x89, 0x34, 0x88, 0x39, 0xd5]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .movzx 32 [gr 32 6, .mem (mg (some 3) (some 1) 1 0 8)] 4) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .mov 32 [.mem (mg (some 0) (some 1) 4 0 32), gr 32 6] 3) := by dec_rfl
theorem p5_12 : ∀ feat, Dec feat p5 12 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 1 (.r 2),
  Op.add 32 2 (.i 1),
  Op.ldzx 8 6 (some 3) (some 1) 1 0,
  Op.st 32 (some 0) (some 1) 4 0 6,
  Op.cmp 32 5 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 14 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_12 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x73, 0xf0]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551600] 2) := by dec_rfl

/-- The stretch at `64`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.pop) (by decide) <|
  .cons (p6_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `80`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x31, 0xc0, 0x5b, 0x5d]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 8),
  Op.xor 32 0 (.r 0),
  Op.pop 3,
  Op.pop 5]

theorem b7 (prof : Profile) : Blk prof p7 0 8 o7 :=
  .cons (p7_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.pop) (by decide) <|
  .cons (p7_7 _) (OpI.pop) (by decide) <|
  .nil 8

/-- The stretch at `96`. -/
def p8 : List Byte := [
  0x31, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Aba
