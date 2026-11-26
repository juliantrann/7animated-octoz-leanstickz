import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::AString (const char *)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Acc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08,
  0x80, 0x3e, 0x00, 0xbe, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.cmpmi 8 (some 6) none 1 0 0,
  Op.mov 32 6 (.i 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 24 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.mov (.i 0) (.inl rfl)) (by decide) <|
  .nil 24

def j0 : List Byte := [0x74, 0x12]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `26`. -/
def p1 : List Byte := [
  0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.nop) (by decide) <|
  .nil 6

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x8d, 0x46, 0x01, 0x80, 0x3c, 0x03, 0x00, 0x48, 0x89, 0xc6]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 6) none 1 1 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .cmp 8 [.mem (mg (some 3) (some 0) 1 0 8), .imm 8 0] 4) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 0 (some 6) none 1 1,
  Op.cmpmi 8 (some 3) (some 0) 1 0 0,
  Op.mov 64 6 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x75, 0xf4]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551604] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p3 : List Byte := [
  0x48, 0x89, 0xef]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `52`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x4d, 0x00, 0x31, 0xc0, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 1 (some 5) none 1 0,
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b4 (prof : Profile) : Blk prof p4 0 12 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.nop) (by decide) <|
  .nil 12

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0x0f, 0xb6, 0x14, 0x03, 0x88, 0x14, 0x01, 0x48, 0x83, 0xc0, 0x01, 0x84, 0xd2]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 3) (some 0) 1 0 8)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 8 [.mem (mg (some 1) (some 0) 1 0 8), gr 8 2] 3) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 8 2 (some 3) (some 0) 1 0,
  Op.st 8 (some 1) (some 0) 1 0 2,
  Op.add 64 0 (.i 1),
  Op.test 8 2 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 13 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p5_11 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 13

def j2 : List Byte := [0x75, 0xf1]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551601] 2) := by dec_rfl

/-- The stretch at `79`. -/
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

end FV7z.Acc
