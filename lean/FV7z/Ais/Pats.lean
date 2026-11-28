import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `NWildcard::CCensorNode::AddItemSimple` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 16 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ais
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x49, 0x89, 0xd4, 0x55,
  0x53, 0x48, 0x8d, 0x5f, 0x28, 0x48, 0x83, 0xc7, 0x38, 0x48, 0x83, 0xec, 0x18, 0x40, 0x84, 0xf6,
  0x48, 0x0f, 0x44, 0xdf, 0x8b, 0x43, 0x0c, 0x39, 0x43, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 7) none 1 40 0)] 4) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .test 8 [gr 8 6, Src.opd 8 (.r 6)] 3) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk (.cmovcc 4) 64 [gr 64 3, gr 64 7] 4) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 12 32)] 3) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .cmp 32 [.mem (mg (some 3) none 1 8 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.mov 64 12 (.r 2),
  Op.push 5,
  Op.push 3,
  Op.lea 64 3 (some 7) none 1 40,
  Op.add 64 7 (.i 56),
  Op.sub 64 4 (.i 24),
  Op.test 8 6 (.r 6),
  Op.cmov64 4 3 7,
  Op.ld 32 0 (some 3) none 1 12,
  Op.cmpmr 32 (some 3) none 1 8 0]

theorem b0 (prof : Profile) : Blk prof p0 0 42 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.push) (by decide) <|
  .cons (p0_17 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_21 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p0_29 _) (OpI.test8 (.r 6)) (by decide) <|
  .cons (p0_32 _) (OpI.cmov64) (by decide) <|
  .cons (p0_36 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_39 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 42

def j0 : List Byte := [0x75, 0x4f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 79] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p1 : List Byte := [
  0x3d, 0xfe, 0xff, 0xff, 0x7f]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 2147483646)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 0 (.i 2147483646)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 2147483646) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `55`. -/
def p2 : List Byte := [
  0x89, 0xc5, 0xc1, 0xed, 0x02, 0x8d, 0x55, 0x01, 0xbd, 0xff, 0xff, 0xff, 0x7f, 0x29, 0xc5, 0x39,
  0xd5, 0x0f, 0x47, 0xea, 0x8d, 0x7c, 0x05, 0x00, 0x48, 0x89, 0xfd, 0x48, 0xc1, 0xe7, 0x03]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .shr 32 [gr 32 5, Src.opd 8 (.i 2)] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 5) none 1 1 0)] 3) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 2147483647)] 5) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_15 : ∀ feat, Dec feat p2 15 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_17 : ∀ feat, Dec feat p2 17 (FV7z.mk (.cmovcc 7) 32 [gr 32 5, gr 32 2] 3) := by dec_rfl
theorem p2_20 : ∀ feat, Dec feat p2 20 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 5) (some 0) 1 0 0)] 4) := by dec_rfl
theorem p2_24 : ∀ feat, Dec feat p2 24 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_27 : ∀ feat, Dec feat p2 27 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 5 (.r 0),
  Op.shr 5 (.i 2),
  Op.lea 32 2 (some 5) none 1 1,
  Op.mov 32 5 (.i 2147483647),
  Op.sub 32 5 (.r 0),
  Op.cmp 32 5 (.r 2),
  Op.cmov32 7 5 2,
  Op.lea 32 7 (some 5) (some 0) 1 0,
  Op.mov 64 5 (.r 7),
  Op.shl64 7 (.i 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 31 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.shr (.i 2)) (by decide) <|
  .cons (p2_5 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.mov (.i 2147483647) (.inl rfl)) (by decide) <|
  .cons (p2_13 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_15 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_17 _) (OpI.cmov32) (by decide) <|
  .cons (p2_20 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_24 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_27 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 31

/-- The stretch at `91`. -/
def p3 : List Byte := [
  0x8b, 0x53, 0x08, 0x4c, 0x8b, 0x33, 0x49, 0x89, 0xc5, 0x85, 0xd2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 32 2 (some 3) none 1 8,
  Op.ld 64 14 (some 3) none 1 0,
  Op.mov 64 13 (.r 0),
  Op.test 32 2 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 11 o3 :=
  .cons (p3_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x0f, 0x85, 0xdc, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 220] 6) := by dec_rfl

/-- The stretch at `108`. -/
def p4 : List Byte := [
  0x4d, 0x85, 0xf6]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 64 [gr 64 14, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 64 14 (.r 14)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x0f, 0x85, 0xe2, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 226] 6) := by dec_rfl

/-- The stretch at `117`. -/
def p5 : List Byte := [
  0x4c, 0x89, 0x2b, 0x89, 0x6b, 0x0c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 13] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 12 32), gr 32 5] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 64 (some 3) none 1 0 13,
  Op.st 32 (some 3) none 1 12 5]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 6

/-- The stretch at `123`. -/
def p6 : List Byte := [
  0xbf, 0x18, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 24)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 7 (.i 24)]

theorem b6 (prof : Profile) : Blk prof p6 0 5 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 24) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `133`. -/
def p7 : List Byte := [
  0x45, 0x8b, 0x6c, 0x24, 0x08, 0x48, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xc5, 0x48,
  0xc7, 0x40, 0x08, 0x00, 0x00, 0x00, 0x00, 0x45, 0x85, 0xed]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 12) none 1 8 32)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p7_12 : ∀ feat, Dec feat p7 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_15 : ∀ feat, Dec feat p7 15 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), .imm 64 0] 8) := by dec_rfl
theorem p7_23 : ∀ feat, Dec feat p7 23 (FV7z.mk .test 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 32 13 (some 12) none 1 8,
  Op.sti 64 (some 0) none 1 0 0,
  Op.mov 64 5 (.r 0),
  Op.sti 64 (some 0) none 1 8 0,
  Op.test 32 13 (.r 13)]

theorem b7 (prof : Profile) : Blk prof p7 0 26 o7 :=
  .cons (p7_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_12 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_15 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_23 _) (OpI.test (.r 13) (.inl rfl)) (by decide) <|
  .nil 26

def j3 : List Byte := [0x75, 0x2f]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `161`. -/
def p8 : List Byte := [
  0x41, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x13, 0x89, 0x45, 0x10, 0x8b, 0x43, 0x08, 0x8d, 0x48,
  0x01, 0x89, 0x4b, 0x08, 0x48, 0x89, 0x2c, 0xc2, 0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d, 0x41, 0x5c,
  0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 16 32)] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 16 32), gr 32 0] 3) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl
theorem p8_14 : ∀ feat, Dec feat p8 14 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p8_17 : ∀ feat, Dec feat p8 17 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 8 32), gr 32 1] 3) := by dec_rfl
theorem p8_20 : ∀ feat, Dec feat p8 20 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 0) 8 0 64), gr 64 5] 4) := by dec_rfl
theorem p8_24 : ∀ feat, Dec feat p8 24 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p8_28 : ∀ feat, Dec feat p8 28 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p8_29 : ∀ feat, Dec feat p8 29 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_30 : ∀ feat, Dec feat p8 30 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p8_32 : ∀ feat, Dec feat p8 32 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p8_34 : ∀ feat, Dec feat p8 34 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p8_36 : ∀ feat, Dec feat p8 36 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 0 (some 12) none 1 16,
  Op.ld 64 2 (some 3) none 1 0,
  Op.st 32 (some 5) none 1 16 0,
  Op.ld 32 0 (some 3) none 1 8,
  Op.lea 32 1 (some 0) none 1 1,
  Op.st 32 (some 3) none 1 8 1,
  Op.st 64 (some 2) (some 0) 8 0 5,
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b8 (prof : Profile) : Blk prof p8 0 38 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_8 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_11 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_14 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p8_17 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_20 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_24 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p8_28 _) (OpI.pop) (by decide) <|
  .cons (p8_29 _) (OpI.pop) (by decide) <|
  .cons (p8_30 _) (OpI.pop) (by decide) <|
  .cons (p8_32 _) (OpI.pop) (by decide) <|
  .cons (p8_34 _) (OpI.pop) (by decide) <|
  .cons (p8_36 _) (OpI.pop) (by decide) <|
  .nil 38

/-- The stretch at `208`. -/
def p9 : List Byte := [
  0x44, 0x89, 0xef, 0x48, 0xc1, 0xe7, 0x03]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 7 (.r 13),
  Op.shl64 7 (.i 3)]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p9_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .nil 7

/-- The stretch at `220`. -/
def p10 : List Byte := [
  0x48, 0x89, 0x45, 0x00, 0x41, 0x8d, 0x45, 0xff, 0x45, 0x31, 0xf6, 0x48, 0x8d, 0x04, 0xc5, 0x08,
  0x00, 0x00, 0x00, 0x44, 0x89, 0x6d, 0x0c, 0x48, 0x89, 0x44, 0x24, 0x08, 0x0f, 0x1f, 0x84, 0x00,
  0x00, 0x00, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 0] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 13) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 0) 8 8 0)] 8) := by dec_rfl
theorem p10_19 : ∀ feat, Dec feat p10 19 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 12 32), gr 32 13] 4) := by dec_rfl
theorem p10_23 : ∀ feat, Dec feat p10 23 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p10_28 : ∀ feat, Dec feat p10 28 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.st 64 (some 5) none 1 0 0,
  Op.lea 32 0 (some 13) none 1 18446744073709551615,
  Op.xor 32 14 (.r 14),
  Op.lea 64 0 none (some 0) 8 8,
  Op.st 32 (some 5) none 1 12 13,
  Op.st 64 (some 4) none 1 8 0,
  Op.nop]

theorem b10 (prof : Profile) : Blk prof p10 0 36 o10 :=
  .cons (p10_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p10_8 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .cons (p10_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_19 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p10_23 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_28 _) (OpI.nop) (by decide) <|
  .nil 36

/-- The stretch at `256`. -/
def p11 : List Byte := [
  0x49, 0x8b, 0x04, 0x24, 0xbf, 0x10, 0x00, 0x00, 0x00, 0x4e, 0x8b, 0x3c, 0x30]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p11_9 : ∀ feat, Dec feat p11 9 (FV7z.mk .mov 64 [gr 64 15, .mem (mg (some 0) (some 14) 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 0 (some 12) none 1 0,
  Op.mov 32 7 (.i 16),
  Op.ld 64 15 (some 0) (some 14) 1 0]

theorem b11 (prof : Profile) : Blk prof p11 0 13 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p11_9 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `274`. -/
def p12 : List Byte := [
  0x4c, 0x89, 0xfe, 0x48, 0x89, 0xc7, 0x49, 0x89, 0xc5]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p12_6 : ∀ feat, Dec feat p12 6 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 6 (.r 15),
  Op.mov 64 7 (.r 0),
  Op.mov 64 13 (.r 0)]

theorem b12 (prof : Profile) : Blk prof p12 0 9 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p12_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p12_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `288`. -/
def p13 : List Byte := [
  0x8b, 0x45, 0x08, 0x48, 0x8b, 0x55, 0x00, 0x49, 0x83, 0xc6, 0x08, 0x8d, 0x48, 0x01, 0x89, 0x4d,
  0x08, 0x4c, 0x89, 0x2c, 0xc2, 0x4c, 0x39, 0x74, 0x24, 0x08]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 8 32)] 3) := by dec_rfl
theorem p13_3 : ∀ feat, Dec feat p13 3 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .add 64 [gr 64 14, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p13_14 : ∀ feat, Dec feat p13 14 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 1] 3) := by dec_rfl
theorem p13_17 : ∀ feat, Dec feat p13 17 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 0) 8 0 64), gr 64 13] 4) := by dec_rfl
theorem p13_21 : ∀ feat, Dec feat p13 21 (FV7z.mk .cmp 64 [.mem (mg (some 4) none 1 8 64), gr 64 14] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 32 0 (some 5) none 1 8,
  Op.ld 64 2 (some 5) none 1 0,
  Op.add 64 14 (.i 8),
  Op.lea 32 1 (some 0) none 1 1,
  Op.st 32 (some 5) none 1 8 1,
  Op.st 64 (some 2) (some 0) 8 0 13,
  Op.cmpmr 64 (some 4) none 1 8 14]

theorem b13 (prof : Profile) : Blk prof p13 0 26 o13 :=
  .cons (p13_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p13_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p13_7 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p13_11 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p13_14 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p13_17 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p13_21 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 26

def j4 : List Byte := [0x75, 0xc4]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551556] 2) := by dec_rfl

def j5 : List Byte := [0xe9, 0x60, 0xff, 0xff, 0xff]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551456] 5) := by dec_rfl

/-- The stretch at `328`. -/
def p14 : List Byte := [
  0x48, 0xc1, 0xe2, 0x03, 0x4c, 0x89, 0xf6, 0x48, 0x89, 0xc7]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.shl64 2 (.i 3),
  Op.mov 64 6 (.r 14),
  Op.mov 64 7 (.r 0)]

theorem b14 (prof : Profile) : Blk prof p14 0 10 o14 :=
  .cons (p14_0 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p14_4 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `343`. -/
def p15 : List Byte := [
  0x4c, 0x89, 0xf7]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 7 (.r 14)]

theorem b15 (prof : Profile) : Blk prof p15 0 3 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0xe9, 0x11, 0xff, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551377] 5) := by dec_rfl

end FV7z.Ais
