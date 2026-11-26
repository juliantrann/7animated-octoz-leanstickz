import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::Replace` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rpl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83,
  0xec, 0x08, 0x44, 0x8b, 0x6e, 0x08, 0x45, 0x85, 0xed]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 6) none 1 8 32)] 4) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .test 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.ld 32 13 (some 6) none 1 8,
  Op.test 32 13 (.r 13)]

theorem b0 (prof : Profile) : Blk prof p0 0 25 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.test (.r 13) (.inl rfl)) (by decide) <|
  .nil 25

def j0 : List Byte := [0x74, 0x5b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 91] 2) := by dec_rfl

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x44, 0x8b, 0x72, 0x08, 0x49, 0x89, 0xff, 0x48, 0x89, 0xf5, 0x49, 0x89, 0xd4, 0x45, 0x39, 0xee]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 14, .mem (mg (some 2) none 1 8 32)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .cmp 32 [gr 32 14, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 14 (some 2) none 1 8,
  Op.mov 64 15 (.r 7),
  Op.mov 64 5 (.r 6),
  Op.mov 64 12 (.r 2),
  Op.cmp 32 14 (.r 13)]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.cmp (.r 13) (.inl rfl)) (by decide) <|
  .nil 16

/-- The stretch at `45`. -/
def p2 : List Byte := [
  0x41, 0x8b, 0x47, 0x08, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 15) none 1 8 32)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 0 (some 15) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x74, 0x41]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 65] 2) := by dec_rfl

/-- The stretch at `53`. -/
def p3 : List Byte := [
  0x31, 0xd2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 2 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0xeb, 0x2b]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `64`. -/
def p4 : List Byte := [
  0x89, 0xc6, 0x44, 0x89, 0xea, 0x4c, 0x89, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_2 : ∀ feat, Dec feat p4 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 6 (.r 0),
  Op.mov 32 2 (.r 13),
  Op.mov 64 7 (.r 15)]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_2 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `77`. -/
def p5 : List Byte := [
  0x4c, 0x89, 0xe2, 0x89, 0xde, 0x4c, 0x89, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 2 (.r 12),
  Op.mov 32 6 (.r 3),
  Op.mov 64 7 (.r 15)]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `90`. -/
def p6 : List Byte := [
  0x42, 0x8d, 0x14, 0x33, 0x41, 0x39, 0x57, 0x08]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 3) (some 14) 1 0 0)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 32 [.mem (mg (some 15) none 1 8 32), gr 32 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 32 2 (some 3) (some 14) 1 0,
  Op.cmpmr 32 (some 15) none 1 8 2]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x76, 0x12]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `100`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x75, 0x00, 0x4c, 0x89, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 6 (some 5) none 1 0,
  Op.mov 64 7 (.r 15)]

theorem b7 (prof : Profile) : Blk prof p7 0 7 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `112`. -/
def p8 : List Byte := [
  0x89, 0xc3, 0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_2 : ∀ feat, Dec feat p8 2 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 3 (.r 0),
  Op.test 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p8_2 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x79, 0xca]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551562] 2) := by dec_rfl

/-- The stretch at `118`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p9_12 : ∀ feat, Dec feat p9 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b9 (prof : Profile) : Blk prof p9 0 14 o9 :=
  .cons (p9_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.pop) (by decide) <|
  .cons (p9_5 _) (OpI.pop) (by decide) <|
  .cons (p9_6 _) (OpI.pop) (by decide) <|
  .cons (p9_8 _) (OpI.pop) (by decide) <|
  .cons (p9_10 _) (OpI.pop) (by decide) <|
  .cons (p9_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `136`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x32, 0x48, 0x8b, 0x7d, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 6 (some 2) none 1 0,
  Op.ld 64 7 (some 5) none 1 0]

theorem b10 (prof : Profile) : Blk prof p10 0 7 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `148`. -/
def p11 : List Byte := [
  0x85, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 2 o11 :=
  .cons (p11_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j5 : List Byte := [0x75, 0x95]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551509] 2) := by dec_rfl

end FV7z.Rpl
