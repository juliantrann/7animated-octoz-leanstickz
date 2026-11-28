import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `PrintString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pst
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x55, 0x45, 0x31, 0xed, 0x41, 0x54, 0x41, 0x89, 0xfc, 0x48, 0x89, 0xd7, 0x55, 0x48, 0x89,
  0xd5, 0x53, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 13,
  Op.xor 32 13 (.r 13),
  Op.push 12,
  Op.mov 32 12 (.r 7),
  Op.mov 64 7 (.r 2),
  Op.push 5,
  Op.mov 64 5 (.r 2),
  Op.push 3,
  Op.mov 32 3 (.r 6),
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 24 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.xor (.r 13) (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.push) (by decide) <|
  .cons (p0_18 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 24

/-- The stretch at `29`. -/
def p1 : List Byte := [
  0x39, 0xd8]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 0 (.r 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.cmp (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

def j0 : List Byte := [0x73, 0x11]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 3) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p2 : List Byte := [
  0x29, 0xc3, 0x41, 0x89, 0xdd, 0x41, 0x83, 0xfc, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 32 [gr 32 3, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 32 3 (.r 0),
  Op.mov 32 13 (.r 3),
  Op.cmp 32 12 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 9 o2 :=
  .cons (p2_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x74, 0x64]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 100] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p3 : List Byte := [
  0x41, 0x83, 0xfc, 0x02]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 12 (.i 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x74, 0x46]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 70] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p4 : List Byte := [
  0x48, 0xc7, 0xc0, 0x70, 0xed, 0x79, 0x00, 0x48, 0x89, 0xef, 0x48, 0x8b, 0x30]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7990640)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 0 (.i 7990640),
  Op.mov 64 7 (.r 5),
  Op.ld 64 6 (some 0) none 1 0]

theorem b4 (prof : Profile) : Blk prof p4 0 13 o4 :=
  .cons (p4_0 _) (OpI.mov (.i 7990640) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p4_10 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `68`. -/
def p5 : List Byte := [
  0x41, 0x8d, 0x45, 0xff, 0x83, 0xf8, 0x1f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 13) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 31)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lea 32 0 (some 13) none 1 18446744073709551615,
  Op.cmp 32 0 (.i 31)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.cmp (.i 31) (.inl rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x76, 0x13]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `77`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b6 (prof : Profile) : Blk prof p6 0 10 o6 :=
  .cons (p6_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.pop) (by decide) <|
  .cons (p6_5 _) (OpI.pop) (by decide) <|
  .cons (p6_6 _) (OpI.pop) (by decide) <|
  .cons (p6_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x44, 0x89, 0xef, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 32 7 (.r 13),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b7 (prof : Profile) : Blk prof p7 0 13 o7 :=
  .cons (p7_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.pop) (by decide) <|
  .cons (p7_8 _) (OpI.pop) (by decide) <|
  .cons (p7_9 _) (OpI.pop) (by decide) <|
  .cons (p7_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `120`. -/
def p8 : List Byte := [
  0x8d, 0x43, 0xff, 0x89, 0xdf, 0x45, 0x31, 0xed]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 3) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.lea 32 0 (some 3) none 1 18446744073709551615,
  Op.mov 32 7 (.r 3),
  Op.xor 32 13 (.r 13)]

theorem b8 (prof : Profile) : Blk prof p8 0 8 o8 :=
  .cons (p8_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p8_5 _) (OpI.xor (.r 13) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `128`. -/
def p9 : List Byte := [
  0x83, 0xf8, 0x1f]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 31)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmp 32 0 (.i 31)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.cmp (.i 31) (.inl rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x77, 0xad]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551533] 2) := by dec_rfl

def j5 : List Byte := [0xeb, 0xa6]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551526] 2) := by dec_rfl

/-- The stretch at `144`. -/
def p10 : List Byte := [
  0x89, 0xdf, 0xd1, 0xef, 0x41, 0x29, 0xfd, 0x8d, 0x47, 0xff]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .sub 32 [gr 32 13, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 7) none 1 18446744073709551615 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 7 (.r 3),
  Op.shr 7 (.i 1),
  Op.sub 32 13 (.r 7),
  Op.lea 32 0 (some 7) none 1 18446744073709551615]

theorem b10 (prof : Profile) : Blk prof p10 0 10 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p10_4 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 10

def j6 : List Byte := [0xeb, 0xe4]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551588] 2) := by dec_rfl

end FV7z.Pst
