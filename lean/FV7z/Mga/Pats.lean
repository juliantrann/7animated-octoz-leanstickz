import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_int_memalign` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 21 of them) and each distinct jump (`j*`, 13) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mga
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x08, 0x48, 0x85,
  0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.test 64 2 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 17 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.push) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 17

def j0 : List Byte := [0x0f, 0x88, 0x59, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 8) 64 [.rel 345] 6) := by dec_rfl

/-- The stretch at `23`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xc2, 0x17, 0xb8, 0x20, 0x00, 0x00, 0x00, 0x48, 0x89, 0xf3, 0x48, 0x89, 0xfd, 0x49,
  0x89, 0xd7, 0x49, 0x83, 0xe7, 0xf0, 0x48, 0x83, 0xfa, 0x1f, 0x4c, 0x0f, 0x46, 0xf8, 0x49, 0x8d,
  0x74, 0x37, 0x20]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 23)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 32)] 5) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .and 64 [gr 64 15, Src.opd 64 (.i 18446744073709551600)] 4) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 31)] 4) := by dec_rfl
theorem p1_26 : ∀ feat, Dec feat p1 26 (FV7z.mk (.cmovcc 6) 64 [gr 64 15, gr 64 0] 4) := by dec_rfl
theorem p1_30 : ∀ feat, Dec feat p1 30 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 15) (some 6) 1 32 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 2 (.i 23),
  Op.mov 32 0 (.i 32),
  Op.mov 64 3 (.r 6),
  Op.mov 64 5 (.r 7),
  Op.mov 64 15 (.r 2),
  Op.and 64 15 (.i 18446744073709551600),
  Op.cmp 64 2 (.i 31),
  Op.cmov64 6 15 0,
  Op.lea 64 6 (some 15) (some 6) 1 32]

theorem b1 (prof : Profile) : Blk prof p1 0 35 o1 :=
  .cons (p1_0 _) (OpI.add (.i 23) (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.i 32) (.inl rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.and (.i 18446744073709551600) (.inr rfl)) (by decide) <|
  .cons (p1_22 _) (OpI.cmp (.i 31) (.inr rfl)) (by decide) <|
  .cons (p1_26 _) (OpI.cmov64) (by decide) <|
  .cons (p1_30 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 35

/-- The stretch at `63`. -/
def p2 : List Byte := [
  0x49, 0x89, 0xc4, 0x48, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 12 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x0f, 0x84, 0x0a, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 266] 6) := by dec_rfl

/-- The stretch at `75`. -/
def p3 : List Byte := [
  0x31, 0xd2, 0x48, 0x8d, 0x70, 0xf0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 0) none 1 18446744073709551600 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.lea 64 6 (some 0) none 1 18446744073709551600]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `84`. -/
def p4 : List Byte := [
  0x48, 0x85, 0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 64 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x0f, 0x84, 0xa1, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 161] 6) := by dec_rfl

/-- The stretch at `93`. -/
def p5 : List Byte := [
  0x48, 0x89, 0xd8, 0x4d, 0x8d, 0x6c, 0x1c, 0xff, 0x48, 0xf7, 0xd8, 0x49, 0x21, 0xc5, 0x49, 0x83,
  0xed, 0x10, 0x4c, 0x89, 0xe9, 0x48, 0x29, 0xf1, 0x48, 0x83, 0xf9, 0x1f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 12) (some 3) 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .neg 64 [gr 64 0] 3) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .and 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .sub 64 [gr 64 13, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p5_18 : ∀ feat, Dec feat p5 18 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p5_21 : ∀ feat, Dec feat p5 21 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p5_24 : ∀ feat, Dec feat p5 24 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 31)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 0 (.r 3),
  Op.lea 64 13 (some 12) (some 3) 1 18446744073709551615,
  Op.neg 64 0,
  Op.and 64 13 (.r 0),
  Op.sub 64 13 (.i 16),
  Op.mov 64 1 (.r 13),
  Op.sub 64 1 (.r 6),
  Op.cmp 64 1 (.i 31)]

theorem b5 (prof : Profile) : Blk prof p5 0 28 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.neg (.inr rfl)) (by decide) <|
  .cons (p5_11 _) (OpI.and (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_14 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
  .cons (p5_18 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p5_21 _) (OpI.sub (.r 6) (.inr rfl)) (by decide) <|
  .cons (p5_24 _) (OpI.cmp (.i 31) (.inr rfl)) (by decide) <|
  .nil 28

def j3 : List Byte := [0x0f, 0x86, 0x09, 0x01, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 265] 6) := by dec_rfl

/-- The stretch at `127`. -/
def p6 : List Byte := [
  0x49, 0x8b, 0x44, 0x24, 0xf8, 0x49, 0x89, 0xc6, 0x49, 0x83, 0xe6, 0xf8, 0x49, 0x29, 0xce, 0x83,
  0xe0, 0x02]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 12) none 1 18446744073709551608 64)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .and 64 [gr 64 14, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .sub 64 [gr 64 14, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p6_15 : ∀ feat, Dec feat p6 15 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 0 (some 12) none 1 18446744073709551608,
  Op.mov 64 14 (.r 0),
  Op.and 64 14 (.i 18446744073709551608),
  Op.sub 64 14 (.r 1),
  Op.and 32 0 (.i 2)]

theorem b6 (prof : Profile) : Blk prof p6 0 18 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p6_8 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p6_12 _) (OpI.sub (.r 1) (.inr rfl)) (by decide) <|
  .cons (p6_15 _) (OpI.and (.i 2) (.inl rfl)) (by decide) <|
  .nil 18

def j4 : List Byte := [0x0f, 0x85, 0x09, 0x01, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 265] 6) := by dec_rfl

/-- The stretch at `151`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x3d, 0xe2, 0x0d, 0x16, 0x00, 0x4c, 0x89, 0xf2, 0x48, 0x39, 0xfd]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1445346 0)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 7 (.i 7940672),
  Op.mov 64 2 (.r 14),
  Op.cmp 64 5 (.r 7)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x631c57 : Addr) 0 13 o7 :=
  .cons (p7_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_7 _) ((OpI.mov (.r 14) (.inr rfl)).at _) (by decide) <|
  .cons (p7_10 _) ((OpI.cmp (.r 7) (.inr rfl)).at _) (by decide) <|
  .nil 13

def j5 : List Byte := [0x74, 0x09]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `166`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xca, 0x04, 0xb8, 0x04, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.or 64 2 (.i 4),
  Op.mov 32 0 (.i 4)]

theorem b8 (prof : Profile) : Blk prof p8 0 9 o8 :=
  .cons (p8_0 _) (OpI.or (.i 4) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `175`. -/
def p9 : List Byte := [
  0x48, 0x83, 0xca, 0x01, 0x48, 0x89, 0xef, 0x49, 0x89, 0x55, 0x08]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [.mem (mg (some 13) none 1 8 64), gr 64 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.or 64 2 (.i 1),
  Op.mov 64 7 (.r 5),
  Op.st 64 (some 13) none 1 8 2]

theorem b9 (prof : Profile) : Blk prof p9 0 11 o9 :=
  .cons (p9_0 _) (OpI.or (.i 1) (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 11

/-- The stretch at `192`. -/
def p10 : List Byte := [
  0x49, 0x8b, 0x54, 0x24, 0xf8, 0x83, 0xe2, 0x07, 0x48, 0x09, 0xca, 0x48, 0x09, 0xd0, 0xba, 0x01,
  0x00, 0x00, 0x00, 0x49, 0x89, 0x44, 0x24, 0xf8]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 12) none 1 18446744073709551608 64)] 5) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 7)] 3) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p10_14 : ∀ feat, Dec feat p10 14 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p10_19 : ∀ feat, Dec feat p10 19 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 18446744073709551608 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 2 (some 12) none 1 18446744073709551608,
  Op.and 32 2 (.i 7),
  Op.or 64 2 (.r 1),
  Op.or 64 0 (.r 2),
  Op.mov 32 2 (.i 1),
  Op.st 64 (some 12) none 1 18446744073709551608 0]

theorem b10 (prof : Profile) : Blk prof p10 0 24 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_5 _) (OpI.and (.i 7) (.inl rfl)) (by decide) <|
  .cons (p10_8 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (p10_11 _) (OpI.or (.r 2) (.inr rfl)) (by decide) <|
  .cons (p10_14 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p10_19 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 24

/-- The stretch at `221`. -/
def p11 : List Byte := [
  0x4d, 0x39, 0xfe]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .cmp 64 [gr 64 14, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.cmp 64 14 (.r 15)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.cmp (.r 15) (.inr rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0x0f, 0x82, 0xd1, 0x00, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 2) 64 [.rel 209] 6) := by dec_rfl

/-- The stretch at `230`. -/
def p12 : List Byte := [
  0x4d, 0x8d, 0x65, 0x10, 0x31, 0xd2, 0x4c, 0x89, 0xe0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 13) none 1 16 0)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p12_6 : ∀ feat, Dec feat p12 6 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.lea 64 12 (some 13) none 1 16,
  Op.xor 32 2 (.r 2),
  Op.mov 64 0 (.r 12)]

theorem b12 (prof : Profile) : Blk prof p12 0 9 o12 :=
  .cons (p12_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p12_6 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 9

def j7 : List Byte := [0x0f, 0x85, 0xbc, 0x00, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 188] 6) := by dec_rfl

/-- The stretch at `251`. -/
def p13 : List Byte := [
  0x4c, 0x89, 0xee]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 64 6 (.r 13)]

theorem b13 (prof : Profile) : Blk prof p13 0 3 o13 :=
  .cons (p13_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `254`. -/
def p14 : List Byte := [
  0x48, 0x8b, 0x46, 0x08, 0xa8, 0x02]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 8 64)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 64 0 (some 6) none 1 8,
  Op.test 8 0 (.i 2)]

theorem b14 (prof : Profile) : Blk prof p14 0 6 o14 :=
  .cons (p14_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 6

def j8 : List Byte := [0x75, 0x4f]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 79] 2) := by dec_rfl

/-- The stretch at `262`. -/
def p15 : List Byte := [
  0x48, 0x83, 0xe0, 0xf8, 0x49, 0x8d, 0x57, 0x20, 0x48, 0x39, 0xc2]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 15) none 1 32 0)] 4) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.and 64 0 (.i 18446744073709551608),
  Op.lea 64 2 (some 15) none 1 32,
  Op.cmp 64 2 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 11 o15 :=
  .cons (p15_0 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p15_8 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 11

def j9 : List Byte := [0x73, 0x42]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 3) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `275`. -/
def p16 : List Byte := [
  0x4c, 0x29, 0xf8, 0x48, 0x8d, 0x0d, 0x63, 0x0d, 0x16, 0x00, 0x4e, 0x8d, 0x04, 0x3e, 0x48, 0x89,
  0xef, 0x48, 0x89, 0xc2, 0x48, 0x83, 0xca, 0x04, 0x48, 0x39, 0xcd, 0x48, 0x0f, 0x45, 0xc2, 0xba,
  0x01, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc8, 0x01, 0x49, 0x89, 0x40, 0x08, 0x48, 0x8b, 0x46, 0x08,
  0x83, 0xe0, 0x07, 0x49, 0x09, 0xc7, 0x4c, 0x89, 0x7e, 0x08, 0x4c, 0x89, 0xc6]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 1445219 0)] 7) := by dec_rfl
theorem p16_10 : ∀ feat, Dec feat p16 10 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 6) (some 15) 1 0 0)] 4) := by dec_rfl
theorem p16_14 : ∀ feat, Dec feat p16 14 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p16_17 : ∀ feat, Dec feat p16 17 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p16_20 : ∀ feat, Dec feat p16 20 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p16_24 : ∀ feat, Dec feat p16 24 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p16_27 : ∀ feat, Dec feat p16 27 (FV7z.mk (.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem p16_31 : ∀ feat, Dec feat p16 31 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p16_36 : ∀ feat, Dec feat p16 36 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p16_40 : ∀ feat, Dec feat p16 40 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p16_44 : ∀ feat, Dec feat p16 44 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 8 64)] 4) := by dec_rfl
theorem p16_48 : ∀ feat, Dec feat p16 48 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 7)] 3) := by dec_rfl
theorem p16_51 : ∀ feat, Dec feat p16 51 (FV7z.mk .or 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p16_54 : ∀ feat, Dec feat p16 54 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 8 64), gr 64 15] 4) := by dec_rfl
theorem p16_58 : ∀ feat, Dec feat p16 58 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.sub 64 0 (.r 15),
  Op.mov 64 1 (.i 7940672),
  Op.lea 64 8 (some 6) (some 15) 1 0,
  Op.mov 64 7 (.r 5),
  Op.mov 64 2 (.r 0),
  Op.or 64 2 (.i 4),
  Op.cmp 64 5 (.r 1),
  Op.cmov64 5 0 2,
  Op.mov 32 2 (.i 1),
  Op.or 64 0 (.i 1),
  Op.st 64 (some 8) none 1 8 0,
  Op.ld 64 0 (some 6) none 1 8,
  Op.and 32 0 (.i 7),
  Op.or 64 15 (.r 0),
  Op.st 64 (some 6) none 1 8 15,
  Op.mov 64 6 (.r 8)]

theorem b16 (prof : Profile) : BlkA prof p16 (0x631cd3 : Addr) 0 61 o16 :=
  .cons (p16_0 _) ((OpI.sub (.r 15) (.inr rfl)).at _) (by decide) <|
  .cons (p16_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p16_10 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p16_14 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p16_17 _) ((OpI.mov (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p16_20 _) ((OpI.or (.i 4) (.inr rfl)).at _) (by decide) <|
  .cons (p16_24 _) ((OpI.cmp (.r 1) (.inr rfl)).at _) (by decide) <|
  .cons (p16_27 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p16_31 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p16_36 _) ((OpI.or (.i 1) (.inr rfl)).at _) (by decide) <|
  .cons (p16_40 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p16_44 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p16_48 _) ((OpI.and (.i 7) (.inl rfl)).at _) (by decide) <|
  .cons (p16_51 _) ((OpI.or (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p16_54 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p16_58 _) ((OpI.mov (.r 8) (.inr rfl)).at _) (by decide) <|
  .nil 61

/-- The stretch at `341`. -/
def p17 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41,
  0x5f]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p17_7 : ∀ feat, Dec feat p17 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p17_8 : ∀ feat, Dec feat p17 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p17_9 : ∀ feat, Dec feat p17 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p17_11 : ∀ feat, Dec feat p17 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p17_13 : ∀ feat, Dec feat p17 13 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p17_15 : ∀ feat, Dec feat p17 15 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b17 (prof : Profile) : Blk prof p17 0 17 o17 :=
  .cons (p17_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p17_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p17_7 _) (OpI.pop) (by decide) <|
  .cons (p17_8 _) (OpI.pop) (by decide) <|
  .cons (p17_9 _) (OpI.pop) (by decide) <|
  .cons (p17_11 _) (OpI.pop) (by decide) <|
  .cons (p17_13 _) (OpI.pop) (by decide) <|
  .cons (p17_15 _) (OpI.pop) (by decide) <|
  .nil 17

/-- The stretch at `368`. -/
def p18 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x45, 0x31, 0xe4, 0x64, 0xc7, 0x00, 0x0c, 0x00, 0x00,
  0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p18_7 : ∀ feat, Dec feat p18 7 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p18_10 : ∀ feat, Dec feat p18 10 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 12] 7) := by dec_rfl

/-- What the stretch does. -/
def o18 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.xor 32 12 (.r 12),
  Op.stfi fb 32 (some 0) none 1 0 12]

theorem b18 (prof : Profile) (fb : Addr) : BlkF prof p18 (0x631d30 : Addr) fb 0 17 (o18 fb) :=
  .cons (p18_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p18_7 _) (((OpI.xor (.r 12) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p18_10 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 17

def j10 : List Byte := [0xeb, 0xd2]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `392`. -/
def p19 : List Byte := [
  0x49, 0x01, 0xdd, 0x4c, 0x89, 0xe9, 0x48, 0x29, 0xf1]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .add 64 [gr 64 13, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p19_3 : ∀ feat, Dec feat p19 3 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p19_6 : ∀ feat, Dec feat p19 6 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.add 64 13 (.r 3),
  Op.mov 64 1 (.r 13),
  Op.sub 64 1 (.r 6)]

theorem b19 (prof : Profile) : Blk prof p19 0 9 o19 :=
  .cons (p19_0 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .cons (p19_3 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p19_6 _) (OpI.sub (.r 6) (.inr rfl)) (by decide) <|
  .nil 9

def j11 : List Byte := [0xe9, 0xe9, 0xfe, 0xff, 0xff]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551337] 5) := by dec_rfl

/-- The stretch at `416`. -/
def p20 : List Byte := [
  0x49, 0x03, 0x4c, 0x24, 0xf0, 0x49, 0x83, 0xce, 0x02, 0x4d, 0x8d, 0x65, 0x10, 0x49, 0x89, 0x4d,
  0x00, 0x4d, 0x89, 0x75, 0x08]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .add 64 [gr 64 1, .mem (mg (some 12) none 1 18446744073709551600 64)] 5) := by dec_rfl
theorem p20_5 : ∀ feat, Dec feat p20 5 (FV7z.mk .or 64 [gr 64 14, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p20_9 : ∀ feat, Dec feat p20 9 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 13) none 1 16 0)] 4) := by dec_rfl
theorem p20_13 : ∀ feat, Dec feat p20 13 (FV7z.mk .mov 64 [.mem (mg (some 13) none 1 0 64), gr 64 1] 4) := by dec_rfl
theorem p20_17 : ∀ feat, Dec feat p20 17 (FV7z.mk .mov 64 [.mem (mg (some 13) none 1 8 64), gr 64 14] 4) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.addm 64 1 (some 12) none 1 18446744073709551600,
  Op.or 64 14 (.i 2),
  Op.lea 64 12 (some 13) none 1 16,
  Op.st 64 (some 13) none 1 0 1,
  Op.st 64 (some 13) none 1 8 14]

theorem b20 (prof : Profile) : Blk prof p20 0 21 o20 :=
  .cons (p20_0 _) (OpI.addm (.inr rfl)) (by decide) <|
  .cons (p20_5 _) (OpI.or (.i 2) (.inr rfl)) (by decide) <|
  .cons (p20_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p20_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p20_17 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 21

def j12 : List Byte := [0xeb, 0x9e]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk .jmp 64 [.rel 18446744073709551518] 2) := by dec_rfl

end FV7z.Mga
