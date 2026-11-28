import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::operator+=(const char *)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Apc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x31, 0xdb,
  0x80, 0x3e, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.xor 32 3 (.r 3),
  Op.cmpmi 8 (some 6) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 19 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 19

def j0 : List Byte := [0x74, 0x10]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x0f, 0x1f, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.nop) (by decide) <|
  .nil 3

/-- The stretch at `24`. -/
def p2 : List Byte := [
  0x8d, 0x53, 0x01, 0x80, 0x7c, 0x15, 0x00, 0x00, 0x48, 0x89, 0xd3]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 3) none 1 1 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .cmp 8 [.mem (mg (some 5) (some 2) 1 0 8), .imm 8 0] 5) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 2 (some 3) none 1 1,
  Op.cmpmi 8 (some 5) (some 2) 1 0 0,
  Op.mov 64 3 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 11 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x75, 0xf3]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551603] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p3 : List Byte := [
  0x89, 0xde, 0x4c, 0x89, 0xe7]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 6 (.r 3),
  Op.mov 64 7 (.r 12)]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `47`. -/
def p4 : List Byte := [
  0x41, 0x8b, 0x74, 0x24, 0x08, 0x31, 0xd2, 0x49, 0x03, 0x34, 0x24, 0x66, 0x0f, 0x1f, 0x44, 0x00,
  0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 12) none 1 8 32)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .add 64 [gr 64 6, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 6 (some 12) none 1 8,
  Op.xor 32 2 (.r 2),
  Op.addm 64 6 (some 12) none 1 0,
  Op.nop]

theorem b4 (prof : Profile) : Blk prof p4 0 17 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.nop) (by decide) <|
  .nil 17

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0x0f, 0xb6, 0x4c, 0x15, 0x00, 0x88, 0x0c, 0x16, 0x48, 0x83, 0xc2, 0x01, 0x84, 0xc9]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 5) (some 2) 1 0 8)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 8 [.mem (mg (some 6) (some 2) 1 0 8), gr 8 1] 3) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_12 : ∀ feat, Dec feat p5 12 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 8 1 (some 5) (some 2) 1 0,
  Op.st 8 (some 6) (some 2) 1 0 1,
  Op.add 64 2 (.i 1),
  Op.test 8 1 (.r 1)]

theorem b5 (prof : Profile) : Blk prof p5 0 14 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_12 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x75, 0xf0]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551600] 2) := by dec_rfl

/-- The stretch at `85`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.pop) (by decide) <|
  .cons (p6_4 _) (OpI.pop) (by decide) <|
  .cons (p6_5 _) (OpI.pop) (by decide) <|
  .nil 7

end FV7z.Apc
