import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaDec_TryDummy` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 77 of them) and each distinct jump (`j*`, 64) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tdm
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x56, 0xb8, 0xff, 0xff, 0xff, 0xff, 0x4c, 0x8b, 0x0a, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53,
  0x0f, 0xb6, 0x4f, 0x02, 0x8b, 0x5f, 0x40, 0x44, 0x8b, 0x57, 0x58, 0xd3, 0xe0, 0x4c, 0x8b, 0x5f,
  0x10, 0x8b, 0x6f, 0x38, 0x89, 0xc1, 0x44, 0x8b, 0x47, 0x3c, 0xf7, 0xd1, 0x21, 0xd9, 0xc1, 0xe1,
  0x04, 0x41, 0x8d, 0x04, 0x0a, 0x45, 0x0f, 0xb7, 0xb4, 0x43, 0x00, 0xfe, 0xff, 0xff, 0x4c, 0x8d,
  0x2c, 0x00, 0x81, 0xfd, 0xff, 0xff, 0xff, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 9, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 7) none 1 2 8)] 4) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 32 [gr 32 3, .mem (mg (some 7) none 1 64 32)] 3) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 32 [gr 32 10, .mem (mg (some 7) none 1 88 32)] 4) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 32 [gr 32 5, .mem (mg (some 7) none 1 56 32)] 3) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .mov 32 [gr 32 8, .mem (mg (some 7) none 1 60 32)] 4) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .not 32 [gr 32 1] 2) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p0_46 : ∀ feat, Dec feat p0 46 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 4)] 3) := by dec_rfl
theorem p0_49 : ∀ feat, Dec feat p0 49 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 10) (some 1) 1 0 0)] 4) := by dec_rfl
theorem p0_53 : ∀ feat, Dec feat p0 53 (FV7z.mk .movzx 32 [gr 32 14, .mem (mg (some 11) (some 0) 2 18446744073709551104 16)] 9) := by dec_rfl
theorem p0_62 : ∀ feat, Dec feat p0 62 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 0) (some 0) 1 0 0)] 4) := by dec_rfl
theorem p0_66 : ∀ feat, Dec feat p0 66 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 14,
  Op.mov 32 0 (.i 4294967295),
  Op.ld 64 9 (some 2) none 1 0,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.ldzx 8 1 (some 7) none 1 2,
  Op.ld 32 3 (some 7) none 1 64,
  Op.ld 32 10 (some 7) none 1 88,
  Op.shl 0 (.r 1),
  Op.ld 64 11 (some 7) none 1 16,
  Op.ld 32 5 (some 7) none 1 56,
  Op.mov 32 1 (.r 0),
  Op.ld 32 8 (some 7) none 1 60,
  Op.not32 1,
  Op.and 32 1 (.r 3),
  Op.shl 1 (.i 4),
  Op.lea 32 0 (some 10) (some 1) 1 0,
  Op.ldzx 16 14 (some 11) (some 0) 2 18446744073709551104,
  Op.lea 64 13 (some 0) (some 0) 1 0,
  Op.cmp 32 5 (.i 16777215)]

theorem b0 (prof : Profile) : Blk prof p0 0 72 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_27 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p0_29 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_33 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_36 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_38 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_42 _) (OpI.not32) (by decide) <|
  .cons (p0_44 _) (OpI.and (.r 3) (.inl rfl)) (by decide) <|
  .cons (p0_46 _) (OpI.shl (.i 4)) (by decide) <|
  .cons (p0_49 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p0_53 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p0_62 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_66 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 72

def j0 : List Byte := [0x77, 0x1d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `74`. -/
def p1 : List Byte := [
  0x45, 0x31, 0xe4, 0x49, 0x39, 0xf1]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 64 [gr 64 9, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 12 (.r 12),
  Op.cmp 64 9 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x0f, 0x86, 0x01, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 257] 6) := by dec_rfl

/-- The stretch at `86`. -/
def p2 : List Byte := [
  0x0f, 0xb6, 0x06, 0x41, 0xc1, 0xe0, 0x08, 0xc1, 0xe5, 0x08, 0x48, 0x83, 0xc6, 0x01, 0x41, 0x09,
  0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.i 8)] 4) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .shl 32 [gr 32 5, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ldzx 8 0 (some 6) none 1 0,
  Op.shl 8 (.i 8),
  Op.shl 5 (.i 8),
  Op.add 64 6 (.i 1),
  Op.or 32 8 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 17 o2 :=
  .cons (p2_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p2_7 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p2_10 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.or (.r 0) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `103`. -/
def p3 : List Byte := [
  0x89, 0xe8, 0xc1, 0xe8, 0x0b, 0x41, 0x0f, 0xaf, 0xc6, 0x41, 0x39, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 14] 4) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.r 5),
  Op.shr 0 (.i 11),
  Op.imul 0 14,
  Op.cmp 32 8 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p3_5 _) (OpI.imul) (by decide) <|
  .cons (p3_9 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 12

def j2 : List Byte := [0x0f, 0x83, 0xef, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 3) 64 [.rel 239] 6) := by dec_rfl

/-- The stretch at `121`. -/
def p4 : List Byte := [
  0x49, 0x81, 0xc3, 0x80, 0x02, 0x00, 0x00, 0x48, 0x83, 0x7f, 0x40, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 11, Src.opd 64 (.i 640)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 64 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 11 (.i 640),
  Op.cmpmi 64 (some 7) none 1 64 0]

theorem b4 (prof : Profile) : Blk prof p4 0 12 o4 :=
  .cons (p4_0 _) (OpI.add (.i 640) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.cmpmi64) (by decide) <|
  .nil 12

def j3 : List Byte := [0x74, 0x4b]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 75] 2) := by dec_rfl

/-- The stretch at `135`. -/
def p5 : List Byte := [
  0x0f, 0xb6, 0x4f, 0x01, 0xbd, 0xff, 0xff, 0xff, 0xff, 0x44, 0x0f, 0xb6, 0x27, 0x4c, 0x8b, 0x6f,
  0x18, 0xd3, 0xe5, 0x44, 0x89, 0xe1, 0xf7, 0xd5, 0x21, 0xeb, 0x48, 0x8b, 0x6f, 0x28, 0xd3, 0xe3,
  0x48, 0x8d, 0x4d, 0xff, 0x48, 0x85, 0xed]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 7) none 1 1 8)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .movzx 32 [gr 32 12, .mem (mg (some 7) none 1 0 8)] 4) := by dec_rfl
theorem p5_13 : ∀ feat, Dec feat p5 13 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 7) none 1 24 64)] 4) := by dec_rfl
theorem p5_17 : ∀ feat, Dec feat p5 17 (FV7z.mk .shl 32 [gr 32 5, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p5_19 : ∀ feat, Dec feat p5 19 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p5_22 : ∀ feat, Dec feat p5 22 (FV7z.mk .not 32 [gr 32 5] 2) := by dec_rfl
theorem p5_24 : ∀ feat, Dec feat p5 24 (FV7z.mk .and 32 [gr 32 3, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p5_26 : ∀ feat, Dec feat p5 26 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p5_30 : ∀ feat, Dec feat p5 30 (FV7z.mk .shl 32 [gr 32 3, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p5_32 : ∀ feat, Dec feat p5 32 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 5) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p5_36 : ∀ feat, Dec feat p5 36 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 8 1 (some 7) none 1 1,
  Op.mov 32 5 (.i 4294967295),
  Op.ldzx 8 12 (some 7) none 1 0,
  Op.ld 64 13 (some 7) none 1 24,
  Op.shl 5 (.r 1),
  Op.mov 32 1 (.r 12),
  Op.not32 5,
  Op.and 32 3 (.r 5),
  Op.ld 64 5 (some 7) none 1 40,
  Op.shl 3 (.r 1),
  Op.lea 64 1 (some 5) none 1 18446744073709551615,
  Op.test 64 5 (.r 5)]

theorem b5 (prof : Profile) : Blk prof p5 0 39 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_13 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_17 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p5_19 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p5_22 _) (OpI.not32) (by decide) <|
  .cons (p5_24 _) (OpI.and (.r 5) (.inl rfl)) (by decide) <|
  .cons (p5_26 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_30 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p5_32 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_36 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 39

def j4 : List Byte := [0x0f, 0x84, 0x6c, 0x03, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 876] 6) := by dec_rfl

/-- The stretch at `180`. -/
def p6 : List Byte := [
  0x45, 0x0f, 0xb6, 0x6c, 0x0d, 0x00, 0xb9, 0x08, 0x00, 0x00, 0x00, 0x44, 0x29, 0xe1, 0x41, 0xd3,
  0xed, 0x44, 0x01, 0xeb, 0x8d, 0x0c, 0x5b, 0xc1, 0xe1, 0x08, 0x4d, 0x8d, 0x1c, 0x4b]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .movzx 32 [gr 32 13, .mem (mg (some 13) (some 1) 1 0 8)] 6) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p6_14 : ∀ feat, Dec feat p6 14 (FV7z.mk .shr 32 [gr 32 13, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p6_17 : ∀ feat, Dec feat p6 17 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p6_20 : ∀ feat, Dec feat p6 20 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 3) (some 3) 2 0 0)] 3) := by dec_rfl
theorem p6_23 : ∀ feat, Dec feat p6 23 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p6_26 : ∀ feat, Dec feat p6 26 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 11) (some 1) 2 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ldzx 8 13 (some 13) (some 1) 1 0,
  Op.mov 32 1 (.i 8),
  Op.sub 32 1 (.r 12),
  Op.shr 13 (.r 1),
  Op.add 32 3 (.r 13),
  Op.lea 32 1 (some 3) (some 3) 2 0,
  Op.shl 1 (.i 8),
  Op.lea 64 11 (some 11) (some 1) 2 0]

theorem b6 (prof : Profile) : Blk prof p6 0 30 o6 :=
  .cons (p6_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p6_11 _) (OpI.sub (.r 12) (.inl rfl)) (by decide) <|
  .cons (p6_14 _) (OpI.shr (.r 1)) (by decide) <|
  .cons (p6_17 _) (OpI.add (.r 13) (.inl rfl)) (by decide) <|
  .cons (p6_20 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_23 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p6_26 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 30

/-- The stretch at `210`. -/
def p7 : List Byte := [
  0x41, 0x83, 0xfa, 0x06]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 32 [gr 32 10, Src.opd 32 (.i 6)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 32 10 (.i 6)]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.cmp (.i 6) (.inl rfl)) (by decide) <|
  .nil 4

def j5 : List Byte := [0x0f, 0x87, 0x24, 0x02, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 7) 64 [.rel 548] 6) := by dec_rfl

/-- The stretch at `220`. -/
def p8 : List Byte := [
  0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 7 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 5 o8 :=
  .cons (p8_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

def j6 : List Byte := [0xeb, 0x15]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `232`. -/
def p9 : List Byte := [
  0x83, 0xc7, 0x01, 0x29, 0xc8, 0x41, 0x29, 0xc8, 0x81, 0xff, 0xff, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 255)] 6) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 32 7 (.i 1),
  Op.sub 32 0 (.r 1),
  Op.sub 32 8 (.r 1),
  Op.cmp 32 7 (.i 255)]

theorem b9 (prof : Profile) : Blk prof p9 0 14 o9 :=
  .cons (p9_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p9_3 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p9_5 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p9_8 _) (OpI.cmp (.i 255) (.inl rfl)) (by decide) <|
  .nil 14

def j7 : List Byte := [0x77, 0x42]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 7) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `248`. -/
def p10 : List Byte := [
  0x89, 0xf9, 0x45, 0x0f, 0xb7, 0x14, 0x4b, 0x3d, 0xff, 0xff, 0xff, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .movzx 32 [gr 32 10, .mem (mg (some 11) (some 1) 2 0 16)] 5) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16777215)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 1 (.r 7),
  Op.ldzx 16 10 (some 11) (some 1) 2 0,
  Op.cmp 32 0 (.i 16777215)]

theorem b10 (prof : Profile) : Blk prof p10 0 12 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 12

def j8 : List Byte := [0x77, 0x1a]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 7) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `262`. -/
def p11 : List Byte := [
  0x4c, 0x39, 0xce]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.cmp 64 6 (.r 9)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
  .nil 3

def j9 : List Byte := [0x0f, 0x83, 0xe0, 0x01, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 3) 64 [.rel 480] 6) := by dec_rfl

/-- The stretch at `271`. -/
def p12 : List Byte := [
  0x0f, 0xb6, 0x0e, 0x41, 0xc1, 0xe0, 0x08, 0xc1, 0xe0, 0x08, 0x48, 0x83, 0xc6, 0x01, 0x41, 0x09,
  0xc8]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.i 8)] 4) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p12_10 : ∀ feat, Dec feat p12 10 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p12_14 : ∀ feat, Dec feat p12 14 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ldzx 8 1 (some 6) none 1 0,
  Op.shl 8 (.i 8),
  Op.shl 0 (.i 8),
  Op.add 64 6 (.i 1),
  Op.or 32 8 (.r 1)]

theorem b12 (prof : Profile) : Blk prof p12 0 17 o12 :=
  .cons (p12_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p12_3 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p12_7 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p12_10 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p12_14 _) (OpI.or (.r 1) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `288`. -/
def p13 : List Byte := [
  0x89, 0xc1, 0x01, 0xff, 0xc1, 0xe9, 0x0b, 0x41, 0x0f, 0xaf, 0xca, 0x41, 0x39, 0xc8]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .imul 32 [gr 32 1, gr 32 10] 4) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.add 32 7 (.r 7),
  Op.shr 1 (.i 11),
  Op.imul 1 10,
  Op.cmp 32 8 (.r 1)]

theorem b13 (prof : Profile) : Blk prof p13 0 14 o13 :=
  .cons (p13_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p13_2 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p13_7 _) (OpI.imul) (by decide) <|
  .cons (p13_11 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .nil 14

def j10 : List Byte := [0x73, 0xb8]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551544] 2) := by dec_rfl

/-- The stretch at `304`. -/
def p14 : List Byte := [
  0x89, 0xc8, 0x81, 0xff, 0xff, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p14_2 : ∀ feat, Dec feat p14 2 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 255)] 6) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 32 0 (.r 1),
  Op.cmp 32 7 (.i 255)]

theorem b14 (prof : Profile) : Blk prof p14 0 8 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p14_2 _) (OpI.cmp (.i 255) (.inl rfl)) (by decide) <|
  .nil 8

def j11 : List Byte := [0x76, 0xbe]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551550] 2) := by dec_rfl

/-- The stretch at `314`. -/
def p15 : List Byte := [
  0x41, 0xbc, 0x01, 0x00, 0x00, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 1)] 6) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 32 12 (.i 1)]

theorem b15 (prof : Profile) : Blk prof p15 0 6 o15 :=
  .cons (p15_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `320`. -/
def p16 : List Byte := [
  0x3d, 0xff, 0xff, 0xff, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16777215)] 5) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.cmp 32 0 (.i 16777215)]

theorem b16 (prof : Profile) : Blk prof p16 0 5 o16 :=
  .cons (p16_0 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 5

def j12 : List Byte := [0x77, 0x0d]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 7) 64 [.rel 13] 2) := by dec_rfl

def j13 : List Byte := [0x0f, 0x83, 0x9f, 0x01, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 3) 64 [.rel 415] 6) := by dec_rfl

/-- The stretch at `336`. -/
def p17 : List Byte := [
  0x48, 0x83, 0xc6, 0x01]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.add 64 6 (.i 1)]

theorem b17 (prof : Profile) : Blk prof p17 0 4 o17 :=
  .cons (p17_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `340`. -/
def p18 : List Byte := [
  0x48, 0x89, 0x32]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), gr 64 6] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.st 64 (some 2) none 1 0 6]

theorem b18 (prof : Profile) : Blk prof p18 0 3 o18 :=
  .cons (p18_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 3

/-- The stretch at `343`. -/
def p19 : List Byte := [
  0x5b, 0x44, 0x89, 0xe0, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p19_1 : ∀ feat, Dec feat p19 1 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p19_5 : ∀ feat, Dec feat p19 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p19_9 : ∀ feat, Dec feat p19 9 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.pop 3,
  Op.mov 32 0 (.r 12),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b19 (prof : Profile) : Blk prof p19 0 11 o19 :=
  .cons (p19_0 _) (OpI.pop) (by decide) <|
  .cons (p19_1 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.pop) (by decide) <|
  .cons (p19_5 _) (OpI.pop) (by decide) <|
  .cons (p19_7 _) (OpI.pop) (by decide) <|
  .cons (p19_9 _) (OpI.pop) (by decide) <|
  .nil 11

/-- The stretch at `360`. -/
def p20 : List Byte := [
  0x49, 0x83, 0xc2, 0x10, 0x29, 0xc5, 0x41, 0x29, 0xc0, 0x4b, 0x8d, 0x1c, 0x12, 0x43, 0x0f, 0xb7,
  0x04, 0x53, 0x81, 0xfd, 0xff, 0xff, 0xff, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p20_6 : ∀ feat, Dec feat p20 6 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p20_9 : ∀ feat, Dec feat p20 9 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 10) (some 10) 1 0 0)] 4) := by dec_rfl
theorem p20_13 : ∀ feat, Dec feat p20 13 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 11) (some 10) 2 0 16)] 5) := by dec_rfl
theorem p20_18 : ∀ feat, Dec feat p20 18 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.add 64 10 (.i 16),
  Op.sub 32 5 (.r 0),
  Op.sub 32 8 (.r 0),
  Op.lea 64 3 (some 10) (some 10) 1 0,
  Op.ldzx 16 0 (some 11) (some 10) 2 0,
  Op.cmp 32 5 (.i 16777215)]

theorem b20 (prof : Profile) : Blk prof p20 0 24 o20 :=
  .cons (p20_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p20_6 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p20_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p20_13 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p20_18 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 24

def j14 : List Byte := [0x77, 0x19]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 7) 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `386`. -/
def p21 : List Byte := [
  0x45, 0x31, 0xe4, 0x4c, 0x39, 0xce]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p21_3 : ∀ feat, Dec feat p21 3 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.xor 32 12 (.r 12),
  Op.cmp 64 6 (.r 9)]

theorem b21 (prof : Profile) : Blk prof p21 0 6 o21 :=
  .cons (p21_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p21_3 _) (OpI.cmp (.r 9) (.inr rfl)) (by decide) <|
  .nil 6

def j15 : List Byte := [0x73, 0xcd]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `394`. -/
def p22 : List Byte := [
  0x0f, 0xb6, 0x3e, 0x41, 0xc1, 0xe0, 0x08, 0xc1, 0xe5, 0x08, 0x48, 0x83, 0xc6, 0x01, 0x41, 0x09,
  0xf8]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p22_3 : ∀ feat, Dec feat p22 3 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.i 8)] 4) := by dec_rfl
theorem p22_7 : ∀ feat, Dec feat p22 7 (FV7z.mk .shl 32 [gr 32 5, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p22_10 : ∀ feat, Dec feat p22 10 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p22_14 : ∀ feat, Dec feat p22 14 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ldzx 8 7 (some 6) none 1 0,
  Op.shl 8 (.i 8),
  Op.shl 5 (.i 8),
  Op.add 64 6 (.i 1),
  Op.or 32 8 (.r 7)]

theorem b22 (prof : Profile) : Blk prof p22 0 17 o22 :=
  .cons (p22_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p22_3 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p22_7 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p22_10 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p22_14 _) (OpI.or (.r 7) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `411`. -/
def p23 : List Byte := [
  0x89, 0xef, 0xc1, 0xef, 0x0b, 0x0f, 0xaf, 0xf8, 0x41, 0x39, 0xf8]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p23_2 : ∀ feat, Dec feat p23 2 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .imul 32 [gr 32 7, gr 32 0] 3) := by dec_rfl
theorem p23_8 : ∀ feat, Dec feat p23 8 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 32 7 (.r 5),
  Op.shr 7 (.i 11),
  Op.imul 7 0,
  Op.cmp 32 8 (.r 7)]

theorem b23 (prof : Profile) : Blk prof p23 0 11 o23 :=
  .cons (p23_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p23_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p23_5 _) (OpI.imul) (by decide) <|
  .cons (p23_8 _) (OpI.cmp (.r 7) (.inl rfl)) (by decide) <|
  .nil 11

def j16 : List Byte := [0x0f, 0x83, 0xe4, 0x01, 0x00, 0x00]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 3) 64 [.rel 484] 6) := by dec_rfl

/-- The stretch at `428`. -/
def p24 : List Byte := [
  0x4d, 0x8d, 0x93, 0x00, 0xfa, 0xff, 0xff, 0x41, 0xbc, 0x02, 0x00, 0x00, 0x00, 0x31, 0xed]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 11) none 1 18446744073709550080 0)] 7) := by dec_rfl
theorem p24_7 : ∀ feat, Dec feat p24 7 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 2)] 6) := by dec_rfl
theorem p24_13 : ∀ feat, Dec feat p24 13 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.lea 64 10 (some 11) none 1 18446744073709550080,
  Op.mov 32 12 (.i 2),
  Op.xor 32 5 (.r 5)]

theorem b24 (prof : Profile) : Blk prof p24 0 15 o24 :=
  .cons (p24_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p24_7 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p24_13 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .nil 15

/-- The stretch at `443`. -/
def p25 : List Byte := [
  0x41, 0x0f, 0xb7, 0x02, 0x81, 0xff, 0xff, 0xff, 0xff, 0x00]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 10) none 1 0 16)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.ldzx 16 0 (some 10) none 1 0,
  Op.cmp 32 7 (.i 16777215)]

theorem b25 (prof : Profile) : Blk prof p25 0 10 o25 :=
  .cons (p25_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p25_4 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 10

def j17 : List Byte := [0x0f, 0x83, 0x1f, 0x01, 0x00, 0x00]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 3) 64 [.rel 287] 6) := by dec_rfl

/-- The stretch at `464`. -/
def p26 : List Byte := [
  0x0f, 0xb6, 0x1e, 0x41, 0xc1, 0xe0, 0x08, 0xc1, 0xe7, 0x08, 0x48, 0x83, 0xc6, 0x01, 0x41, 0x09,
  0xd8]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p26_3 : ∀ feat, Dec feat p26 3 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.i 8)] 4) := by dec_rfl
theorem p26_7 : ∀ feat, Dec feat p26 7 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p26_10 : ∀ feat, Dec feat p26 10 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p26_14 : ∀ feat, Dec feat p26 14 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.ldzx 8 3 (some 6) none 1 0,
  Op.shl 8 (.i 8),
  Op.shl 7 (.i 8),
  Op.add 64 6 (.i 1),
  Op.or 32 8 (.r 3)]

theorem b26 (prof : Profile) : Blk prof p26 0 17 o26 :=
  .cons (p26_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p26_3 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p26_7 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p26_10 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p26_14 _) (OpI.or (.r 3) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `481`. -/
def p27 : List Byte := [
  0x89, 0xfb, 0xc1, 0xeb, 0x0b, 0x0f, 0xaf, 0xc3, 0x41, 0x39, 0xc0]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p27_2 : ∀ feat, Dec feat p27 2 (FV7z.mk .shr 32 [gr 32 3, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p27_5 : ∀ feat, Dec feat p27 5 (FV7z.mk .imul 32 [gr 32 0, gr 32 3] 3) := by dec_rfl
theorem p27_8 : ∀ feat, Dec feat p27 8 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.mov 32 3 (.r 7),
  Op.shr 3 (.i 11),
  Op.imul 0 3,
  Op.cmp 32 8 (.r 0)]

theorem b27 (prof : Profile) : Blk prof p27 0 11 o27 :=
  .cons (p27_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p27_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p27_5 _) (OpI.imul) (by decide) <|
  .cons (p27_8 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 11

def j18 : List Byte := [0x0f, 0x83, 0xde, 0x00, 0x00, 0x00]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 3) 64 [.rel 222] 6) := by dec_rfl

/-- The stretch at `498`. -/
def p28 : List Byte := [
  0x4d, 0x8d, 0x14, 0x4a, 0x45, 0x31, 0xed, 0xbb, 0x08, 0x00, 0x00, 0x00]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 10) (some 1) 2 0 0)] 4) := by dec_rfl
theorem p28_4 : ∀ feat, Dec feat p28 4 (FV7z.mk .xor 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p28_7 : ∀ feat, Dec feat p28 7 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.lea 64 10 (some 10) (some 1) 2 0,
  Op.xor 32 13 (.r 13),
  Op.mov 32 3 (.i 8)]

theorem b28 (prof : Profile) : Blk prof p28 0 12 o28 :=
  .cons (p28_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p28_4 _) (OpI.xor (.r 13) (.inl rfl)) (by decide) <|
  .cons (p28_7 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .nil 12

def j19 : List Byte := [0xeb, 0x0f]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `520`. -/
def p29 : List Byte := [
  0x83, 0xc7, 0x01, 0x29, 0xc8, 0x41, 0x29, 0xc8, 0x39, 0xdf]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p29_3 : ∀ feat, Dec feat p29 3 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p29_5 : ∀ feat, Dec feat p29 5 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p29_8 : ∀ feat, Dec feat p29 8 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.add 32 7 (.i 1),
  Op.sub 32 0 (.r 1),
  Op.sub 32 8 (.r 1),
  Op.cmp 32 7 (.r 3)]

theorem b29 (prof : Profile) : Blk prof p29 0 10 o29 :=
  .cons (p29_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p29_3 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p29_5 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p29_8 _) (OpI.cmp (.r 3) (.inl rfl)) (by decide) <|
  .nil 10

def j20 : List Byte := [0x73, 0x3e]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 3) 64 [.rel 62] 2) := by dec_rfl

/-- The stretch at `532`. -/
def p30 : List Byte := [
  0x89, 0xf9, 0x45, 0x0f, 0xb7, 0x34, 0x4a, 0x3d, 0xff, 0xff, 0xff, 0x00]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p30_2 : ∀ feat, Dec feat p30 2 (FV7z.mk .movzx 32 [gr 32 14, .mem (mg (some 10) (some 1) 2 0 16)] 5) := by dec_rfl
theorem p30_7 : ∀ feat, Dec feat p30 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16777215)] 5) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.mov 32 1 (.r 7),
  Op.ldzx 16 14 (some 10) (some 1) 2 0,
  Op.cmp 32 0 (.i 16777215)]

theorem b30 (prof : Profile) : Blk prof p30 0 12 o30 :=
  .cons (p30_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p30_2 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p30_7 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 12

def j21 : List Byte := [0x0f, 0x83, 0xc4, 0x00, 0x00, 0x00]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 3) 64 [.rel 196] 6) := by dec_rfl

/-- The stretch at `572`. -/
def p31 : List Byte := [
  0x89, 0xc1, 0x01, 0xff, 0xc1, 0xe9, 0x0b, 0x41, 0x0f, 0xaf, 0xce, 0x41, 0x39, 0xc8]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p31_2 : ∀ feat, Dec feat p31 2 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p31_4 : ∀ feat, Dec feat p31 4 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p31_7 : ∀ feat, Dec feat p31 7 (FV7z.mk .imul 32 [gr 32 1, gr 32 14] 4) := by dec_rfl
theorem p31_11 : ∀ feat, Dec feat p31 11 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.add 32 7 (.r 7),
  Op.shr 1 (.i 11),
  Op.imul 1 14,
  Op.cmp 32 8 (.r 1)]

theorem b31 (prof : Profile) : Blk prof p31 0 14 o31 :=
  .cons (p31_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p31_2 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p31_4 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p31_7 _) (OpI.imul) (by decide) <|
  .cons (p31_11 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .nil 14

def j22 : List Byte := [0x73, 0xbc]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551548] 2) := by dec_rfl

/-- The stretch at `588`. -/
def p32 : List Byte := [
  0x89, 0xc8, 0x39, 0xdf]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p32_2 : ∀ feat, Dec feat p32 2 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.mov 32 0 (.r 1),
  Op.cmp 32 7 (.r 3)]

theorem b32 (prof : Profile) : Blk prof p32 0 4 o32 :=
  .cons (p32_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p32_2 _) (OpI.cmp (.r 3) (.inl rfl)) (by decide) <|
  .nil 4

def j23 : List Byte := [0x72, 0xc2]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551554] 2) := by dec_rfl

/-- The stretch at `594`. -/
def p33 : List Byte := [
  0x83, 0xfd, 0x03]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.cmp 32 5 (.i 3)]

theorem b33 (prof : Profile) : Blk prof p33 0 3 o33 :=
  .cons (p33_0 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 3

def j24 : List Byte := [0x0f, 0x87, 0xe5, 0xfe, 0xff, 0xff]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551333] 6) := by dec_rfl

/-- The stretch at `603`. -/
def p34 : List Byte := [
  0x41, 0x29, 0xdd, 0xb9, 0x03, 0x00, 0x00, 0x00, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x44, 0x01, 0xef,
  0x83, 0xff, 0x03, 0x0f, 0x47, 0xf9, 0xc1, 0xe7, 0x06, 0x48, 0x83, 0xc7, 0x40]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .sub 32 [gr 32 13, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p34_3 : ∀ feat, Dec feat p34 3 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 3)] 5) := by dec_rfl
theorem p34_8 : ∀ feat, Dec feat p34 8 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p34_13 : ∀ feat, Dec feat p34 13 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p34_16 : ∀ feat, Dec feat p34 16 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 3)] 3) := by dec_rfl
theorem p34_19 : ∀ feat, Dec feat p34 19 (FV7z.mk (.cmovcc 7) 32 [gr 32 7, gr 32 1] 3) := by dec_rfl
theorem p34_22 : ∀ feat, Dec feat p34 22 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.i 6)] 3) := by dec_rfl
theorem p34_25 : ∀ feat, Dec feat p34 25 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.sub 32 13 (.r 3),
  Op.mov 32 1 (.i 3),
  Op.mov 32 3 (.i 1),
  Op.add 32 7 (.r 13),
  Op.cmp 32 7 (.i 3),
  Op.cmov32 7 7 1,
  Op.shl 7 (.i 6),
  Op.add 64 7 (.i 64)]

theorem b34 (prof : Profile) : Blk prof p34 0 29 o34 :=
  .cons (p34_0 _) (OpI.sub (.r 3) (.inl rfl)) (by decide) <|
  .cons (p34_3 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .cons (p34_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p34_13 _) (OpI.add (.r 13) (.inl rfl)) (by decide) <|
  .cons (p34_16 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .cons (p34_19 _) (OpI.cmov32) (by decide) <|
  .cons (p34_22 _) (OpI.shl (.i 6)) (by decide) <|
  .cons (p34_25 _) (OpI.add (.i 64) (.inr rfl)) (by decide) <|
  .nil 29

def j25 : List Byte := [0xeb, 0x17]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk .jmp 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `640`. -/
def p35 : List Byte := [
  0x29, 0xc8, 0x41, 0x29, 0xc8, 0x83, 0xc3, 0x01]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p35_2 : ∀ feat, Dec feat p35 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p35_5 : ∀ feat, Dec feat p35 5 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.sub 32 0 (.r 1),
  Op.sub 32 8 (.r 1),
  Op.add 32 3 (.i 1)]

theorem b35 (prof : Profile) : Blk prof p35 0 8 o35 :=
  .cons (p35_0 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p35_2 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p35_5 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `648`. -/
def p36 : List Byte := [
  0x83, 0xfb, 0x3f]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.i 63)] 3) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.cmp 32 3 (.i 63)]

theorem b36 (prof : Profile) : Blk prof p36 0 3 o36 :=
  .cons (p36_0 _) (OpI.cmp (.i 63) (.inl rfl)) (by decide) <|
  .nil 3

def j26 : List Byte := [0x0f, 0x87, 0xbf, 0x02, 0x00, 0x00]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 7) 64 [.rel 703] 6) := by dec_rfl

/-- The stretch at `657`. -/
def p37 : List Byte := [
  0x89, 0xd9, 0x48, 0x01, 0xf9, 0x45, 0x0f, 0xb7, 0x14, 0x4b, 0x3d, 0xff, 0xff, 0xff, 0x00]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p37_2 : ∀ feat, Dec feat p37 2 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p37_5 : ∀ feat, Dec feat p37 5 (FV7z.mk .movzx 32 [gr 32 10, .mem (mg (some 11) (some 1) 2 0 16)] 5) := by dec_rfl
theorem p37_10 : ∀ feat, Dec feat p37 10 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16777215)] 5) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.mov 32 1 (.r 3),
  Op.add 64 1 (.r 7),
  Op.ldzx 16 10 (some 11) (some 1) 2 0,
  Op.cmp 32 0 (.i 16777215)]

theorem b37 (prof : Profile) : Blk prof p37 0 15 o37 :=
  .cons (p37_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p37_2 _) (OpI.add (.r 7) (.inr rfl)) (by decide) <|
  .cons (p37_5 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p37_10 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 15

def j27 : List Byte := [0x77, 0x16]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 7) 64 [.rel 22] 2) := by dec_rfl

def j28 : List Byte := [0x73, 0x48]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 3) 64 [.rel 72] 2) := by dec_rfl

/-- The stretch at `696`. -/
def p38 : List Byte := [
  0x89, 0xc1, 0x01, 0xdb, 0xc1, 0xe9, 0x0b, 0x41, 0x0f, 0xaf, 0xca, 0x41, 0x39, 0xc8]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p38_2 : ∀ feat, Dec feat p38 2 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p38_4 : ∀ feat, Dec feat p38 4 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p38_7 : ∀ feat, Dec feat p38 7 (FV7z.mk .imul 32 [gr 32 1, gr 32 10] 4) := by dec_rfl
theorem p38_11 : ∀ feat, Dec feat p38 11 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.add 32 3 (.r 3),
  Op.shr 1 (.i 11),
  Op.imul 1 10,
  Op.cmp 32 8 (.r 1)]

theorem b38 (prof : Profile) : Blk prof p38 0 14 o38 :=
  .cons (p38_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p38_2 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .cons (p38_4 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p38_7 _) (OpI.imul) (by decide) <|
  .cons (p38_11 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .nil 14

/-- The stretch at `712`. -/
def p39 : List Byte := [
  0x89, 0xc8]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.mov 32 0 (.r 1)]

theorem b39 (prof : Profile) : Blk prof p39 0 2 o39 :=
  .cons (p39_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .nil 2

def j29 : List Byte := [0xeb, 0xbc]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk .jmp 64 [.rel 18446744073709551548] 2) := by dec_rfl

/-- The stretch at `720`. -/
def p40 : List Byte := [
  0x29, 0xc7, 0x41, 0x29, 0xc0, 0x41, 0x0f, 0xb7, 0x42, 0x10, 0x81, 0xff, 0xff, 0xff, 0xff, 0x00]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p40_2 : ∀ feat, Dec feat p40 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p40_5 : ∀ feat, Dec feat p40 5 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 10) none 1 16 16)] 5) := by dec_rfl
theorem p40_10 : ∀ feat, Dec feat p40 10 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 8 (.r 0),
  Op.ldzx 16 0 (some 10) none 1 16,
  Op.cmp 32 7 (.i 16777215)]

theorem b40 (prof : Profile) : Blk prof p40 0 16 o40 :=
  .cons (p40_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p40_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p40_5 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p40_10 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 16

def j30 : List Byte := [0x0f, 0x87, 0x6b, 0x01, 0x00, 0x00]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 7) 64 [.rel 363] 6) := by dec_rfl

def j31 : List Byte := [0x0f, 0x82, 0x51, 0x01, 0x00, 0x00]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk (.jcc 2) 64 [.rel 337] 6) := by dec_rfl

/-- The stretch at `751`. -/
def p41 : List Byte := [
  0x45, 0x31, 0xe4, 0x5b, 0x5d, 0x44, 0x89, 0xe0, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p41_3 : ∀ feat, Dec feat p41 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p41_4 : ∀ feat, Dec feat p41 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p41_5 : ∀ feat, Dec feat p41 5 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p41_8 : ∀ feat, Dec feat p41 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p41_10 : ∀ feat, Dec feat p41 10 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p41_12 : ∀ feat, Dec feat p41 12 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.xor 32 12 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.mov 32 0 (.r 12),
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b41 (prof : Profile) : Blk prof p41 0 14 o41 :=
  .cons (p41_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p41_3 _) (OpI.pop) (by decide) <|
  .cons (p41_4 _) (OpI.pop) (by decide) <|
  .cons (p41_5 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p41_8 _) (OpI.pop) (by decide) <|
  .cons (p41_10 _) (OpI.pop) (by decide) <|
  .cons (p41_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `768`. -/
def p42 : List Byte := [
  0x4c, 0x8b, 0x57, 0x28, 0x8b, 0x4f, 0x48, 0x48, 0x8b, 0x6f, 0x18, 0x4c, 0x89, 0xd3, 0x48, 0x29,
  0xcb, 0x49, 0x39, 0xca]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .mov 64 [gr 64 10, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p42_4 : ∀ feat, Dec feat p42 4 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 72 32)] 3) := by dec_rfl
theorem p42_7 : ∀ feat, Dec feat p42 7 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 7) none 1 24 64)] 4) := by dec_rfl
theorem p42_11 : ∀ feat, Dec feat p42 11 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p42_14 : ∀ feat, Dec feat p42 14 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p42_17 : ∀ feat, Dec feat p42 17 (FV7z.mk .cmp 64 [gr 64 10, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.ld 64 10 (some 7) none 1 40,
  Op.ld 32 1 (some 7) none 1 72,
  Op.ld 64 5 (some 7) none 1 24,
  Op.mov 64 3 (.r 10),
  Op.sub 64 3 (.r 1),
  Op.cmp 64 10 (.r 1)]

theorem b42 (prof : Profile) : Blk prof p42 0 20 o42 :=
  .cons (p42_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p42_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p42_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p42_11 _) (OpI.mov (.r 10) (.inr rfl)) (by decide) <|
  .cons (p42_14 _) (OpI.sub (.r 1) (.inr rfl)) (by decide) <|
  .cons (p42_17 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 20

def j32 : List Byte := [0x0f, 0x82, 0x16, 0x01, 0x00, 0x00]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk (.jcc 2) 64 [.rel 278] 6) := by dec_rfl

/-- The stretch at `794`. -/
def p43 : List Byte := [
  0x0f, 0xb6, 0x5c, 0x1d, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x41, 0xba, 0x00, 0x01, 0x00, 0x00]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .movzx 32 [gr 32 3, .mem (mg (some 5) (some 3) 1 0 8)] 5) := by dec_rfl
theorem p43_5 : ∀ feat, Dec feat p43 5 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p43_10 : ∀ feat, Dec feat p43 10 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 256)] 6) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.ldzx 8 3 (some 5) (some 3) 1 0,
  Op.mov 32 7 (.i 1),
  Op.mov 32 10 (.i 256)]

theorem b43 (prof : Profile) : Blk prof p43 0 16 o43 :=
  .cons (p43_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p43_5 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p43_10 _) (OpI.mov (.i 256) (.inl rfl)) (by decide) <|
  .nil 16

/-- The stretch at `816`. -/
def p44 : List Byte := [
  0x41, 0x31, 0xea, 0x89, 0xc8]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .xor 32 [gr 32 10, Src.opd 32 (.r 5)] 3) := by dec_rfl
theorem p44_3 : ∀ feat, Dec feat p44 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.xor 32 10 (.r 5),
  Op.mov 32 0 (.r 1)]

theorem b44 (prof : Profile) : Blk prof p44 0 5 o44 :=
  .cons (p44_0 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p44_3 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `821`. -/
def p45 : List Byte := [
  0x81, 0xff, 0xff, 0x00, 0x00, 0x00]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 255)] 6) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.cmp 32 7 (.i 255)]

theorem b45 (prof : Profile) : Blk prof p45 0 6 o45 :=
  .cons (p45_0 _) (OpI.cmp (.i 255) (.inl rfl)) (by decide) <|
  .nil 6

def j33 : List Byte := [0x0f, 0x87, 0xf9, 0xfd, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551097] 6) := by dec_rfl

/-- The stretch at `833`. -/
def p46 : List Byte := [
  0x01, 0xdb, 0x44, 0x89, 0xd5, 0x41, 0x8d, 0x0c, 0x3a, 0x21, 0xdd, 0x01, 0xe9, 0x45, 0x0f, 0xb7,
  0x24, 0x4b, 0x3d, 0xff, 0xff, 0xff, 0x00]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p46_2 : ∀ feat, Dec feat p46 2 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p46_5 : ∀ feat, Dec feat p46 5 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 10) (some 7) 1 0 0)] 4) := by dec_rfl
theorem p46_9 : ∀ feat, Dec feat p46 9 (FV7z.mk .and 32 [gr 32 5, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p46_11 : ∀ feat, Dec feat p46 11 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p46_13 : ∀ feat, Dec feat p46 13 (FV7z.mk .movzx 32 [gr 32 12, .mem (mg (some 11) (some 1) 2 0 16)] 5) := by dec_rfl
theorem p46_18 : ∀ feat, Dec feat p46 18 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16777215)] 5) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.add 32 3 (.r 3),
  Op.mov 32 5 (.r 10),
  Op.lea 32 1 (some 10) (some 7) 1 0,
  Op.and 32 5 (.r 3),
  Op.add 32 1 (.r 5),
  Op.ldzx 16 12 (some 11) (some 1) 2 0,
  Op.cmp 32 0 (.i 16777215)]

theorem b46 (prof : Profile) : Blk prof p46 0 23 o46 :=
  .cons (p46_0 _) (OpI.add (.r 3) (.inl rfl)) (by decide) <|
  .cons (p46_2 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p46_5 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p46_9 _) (OpI.and (.r 3) (.inl rfl)) (by decide) <|
  .cons (p46_11 _) (OpI.add (.r 5) (.inl rfl)) (by decide) <|
  .cons (p46_13 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p46_18 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 23

def j34 : List Byte := [0x73, 0x90]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551504] 2) := by dec_rfl

/-- The stretch at `880`. -/
def p47 : List Byte := [
  0x89, 0xc1, 0x01, 0xff, 0xc1, 0xe9, 0x0b, 0x41, 0x0f, 0xaf, 0xcc, 0x41, 0x39, 0xc8]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p47_2 : ∀ feat, Dec feat p47 2 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p47_4 : ∀ feat, Dec feat p47 4 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p47_7 : ∀ feat, Dec feat p47 7 (FV7z.mk .imul 32 [gr 32 1, gr 32 12] 4) := by dec_rfl
theorem p47_11 : ∀ feat, Dec feat p47 11 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.add 32 7 (.r 7),
  Op.shr 1 (.i 11),
  Op.imul 1 12,
  Op.cmp 32 8 (.r 1)]

theorem b47 (prof : Profile) : Blk prof p47 0 14 o47 :=
  .cons (p47_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p47_2 _) (OpI.add (.r 7) (.inl rfl)) (by decide) <|
  .cons (p47_4 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p47_7 _) (OpI.imul) (by decide) <|
  .cons (p47_11 _) (OpI.cmp (.r 1) (.inl rfl)) (by decide) <|
  .nil 14

def j35 : List Byte := [0x72, 0xb0]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551536] 2) := by dec_rfl

/-- The stretch at `896`. -/
def p48 : List Byte := [
  0x29, 0xc8, 0x41, 0x29, 0xc8, 0x83, 0xc7, 0x01, 0x41, 0x89, 0xea]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p48_2 : ∀ feat, Dec feat p48 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p48_5 : ∀ feat, Dec feat p48 5 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p48_8 : ∀ feat, Dec feat p48 8 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.sub 32 0 (.r 1),
  Op.sub 32 8 (.r 1),
  Op.add 32 7 (.i 1),
  Op.mov 32 10 (.r 5)]

theorem b48 (prof : Profile) : Blk prof p48 0 11 o48 :=
  .cons (p48_0 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p48_2 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p48_5 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p48_8 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .nil 11

def j36 : List Byte := [0xeb, 0xa8]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk .jmp 64 [.rel 18446744073709551528] 2) := by dec_rfl

/-- The stretch at `912`. -/
def p49 : List Byte := [
  0x29, 0xfd, 0x41, 0x0f, 0xb7, 0x44, 0x1b, 0x18, 0x41, 0x29, 0xf8, 0x81, 0xfd, 0xff, 0xff, 0xff,
  0x00]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p49_2 : ∀ feat, Dec feat p49 2 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 11) (some 3) 1 24 16)] 6) := by dec_rfl
theorem p49_8 : ∀ feat, Dec feat p49 8 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p49_11 : ∀ feat, Dec feat p49 11 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.sub 32 5 (.r 7),
  Op.ldzx 16 0 (some 11) (some 3) 1 24,
  Op.sub 32 8 (.r 7),
  Op.cmp 32 5 (.i 16777215)]

theorem b49 (prof : Profile) : Blk prof p49 0 17 o49 :=
  .cons (p49_0 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p49_2 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p49_8 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p49_11 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 17

def j37 : List Byte := [0x0f, 0x83, 0xa8, 0xfd, 0xff, 0xff]
theorem j37_0 : ∀ feat, Dec feat j37 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551016] 6) := by dec_rfl

def j38 : List Byte := [0x0f, 0x83, 0xaf, 0x00, 0x00, 0x00]
theorem j38_0 : ∀ feat, Dec feat j38 0 (FV7z.mk (.jcc 3) 64 [.rel 175] 6) := by dec_rfl

/-- The stretch at `977`. -/
def p50 : List Byte := [
  0x43, 0x0f, 0xb7, 0x84, 0x2b, 0x00, 0xf4, 0xff, 0xff, 0x81, 0xff, 0xff, 0xff, 0xff, 0x00]

theorem p50_0 : ∀ feat, Dec feat p50 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 11) (some 13) 1 18446744073709548544 16)] 9) := by dec_rfl
theorem p50_9 : ∀ feat, Dec feat p50 9 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o50 : List Op := [
  Op.ldzx 16 0 (some 11) (some 13) 1 18446744073709548544,
  Op.cmp 32 7 (.i 16777215)]

theorem b50 (prof : Profile) : Blk prof p50 0 15 o50 :=
  .cons (p50_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p50_9 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 15

def j39 : List Byte := [0x77, 0x1e]
theorem j39_0 : ∀ feat, Dec feat j39 0 (FV7z.mk (.jcc 7) 64 [.rel 30] 2) := by dec_rfl

def j40 : List Byte := [0x0f, 0x83, 0x69, 0xfd, 0xff, 0xff]
theorem j40_0 : ∀ feat, Dec feat j40 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709550953] 6) := by dec_rfl

/-- The stretch at `1006`. -/
def p51 : List Byte := [
  0x44, 0x0f, 0xb6, 0x16, 0x41, 0xc1, 0xe0, 0x08, 0xc1, 0xe7, 0x08, 0x48, 0x83, 0xc6, 0x01, 0x45,
  0x09, 0xd0]

theorem p51_0 : ∀ feat, Dec feat p51 0 (FV7z.mk .movzx 32 [gr 32 10, .mem (mg (some 6) none 1 0 8)] 4) := by dec_rfl
theorem p51_4 : ∀ feat, Dec feat p51 4 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.i 8)] 4) := by dec_rfl
theorem p51_8 : ∀ feat, Dec feat p51 8 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p51_11 : ∀ feat, Dec feat p51 11 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p51_15 : ∀ feat, Dec feat p51 15 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o51 : List Op := [
  Op.ldzx 8 10 (some 6) none 1 0,
  Op.shl 8 (.i 8),
  Op.shl 7 (.i 8),
  Op.add 64 6 (.i 1),
  Op.or 32 8 (.r 10)]

theorem b51 (prof : Profile) : Blk prof p51 0 18 o51 :=
  .cons (p51_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p51_4 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p51_8 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p51_11 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p51_15 _) (OpI.or (.r 10) (.inl rfl)) (by decide) <|
  .nil 18

/-- The stretch at `1024`. -/
def p52 : List Byte := [
  0x41, 0x89, 0xfa, 0x41, 0xc1, 0xea, 0x0b, 0x41, 0x0f, 0xaf, 0xc2, 0x41, 0x39, 0xc0]

theorem p52_0 : ∀ feat, Dec feat p52 0 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p52_3 : ∀ feat, Dec feat p52 3 (FV7z.mk .shr 32 [gr 32 10, Src.opd 8 (.i 11)] 4) := by dec_rfl
theorem p52_7 : ∀ feat, Dec feat p52 7 (FV7z.mk .imul 32 [gr 32 0, gr 32 10] 4) := by dec_rfl
theorem p52_11 : ∀ feat, Dec feat p52 11 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o52 : List Op := [
  Op.mov 32 10 (.r 7),
  Op.shr 10 (.i 11),
  Op.imul 0 10,
  Op.cmp 32 8 (.r 0)]

theorem b52 (prof : Profile) : Blk prof p52 0 14 o52 :=
  .cons (p52_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p52_3 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p52_7 _) (OpI.imul) (by decide) <|
  .cons (p52_11 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 14

def j41 : List Byte := [0x0f, 0x83, 0x2c, 0x01, 0x00, 0x00]
theorem j41_0 : ∀ feat, Dec feat j41 0 (FV7z.mk (.jcc 3) 64 [.rel 300] 6) := by dec_rfl

/-- The stretch at `1044`. -/
def p53 : List Byte := [
  0x41, 0xbc, 0x03, 0x00, 0x00, 0x00]

theorem p53_0 : ∀ feat, Dec feat p53 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 3)] 6) := by dec_rfl

/-- What the stretch does. -/
def o53 : List Op := [
  Op.mov 32 12 (.i 3)]

theorem b53 (prof : Profile) : Blk prof p53 0 6 o53 :=
  .cons (p53_0 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .nil 6

def j42 : List Byte := [0xe9, 0x21, 0xfd, 0xff, 0xff]
theorem j42_0 : ∀ feat, Dec feat j42 0 (FV7z.mk .jmp 64 [.rel 18446744073709550881] 5) := by dec_rfl

/-- The stretch at `1056`. -/
def p54 : List Byte := [
  0x48, 0x8b, 0x4f, 0x20, 0x48, 0x83, 0xe9, 0x01]

theorem p54_0 : ∀ feat, Dec feat p54 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 7) none 1 32 64)] 4) := by dec_rfl
theorem p54_4 : ∀ feat, Dec feat p54 4 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o54 : List Op := [
  Op.ld 64 1 (some 7) none 1 32,
  Op.sub 64 1 (.i 1)]

theorem b54 (prof : Profile) : Blk prof p54 0 8 o54 :=
  .cons (p54_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p54_4 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 8

def j43 : List Byte := [0xe9, 0x87, 0xfc, 0xff, 0xff]
theorem j43_0 : ∀ feat, Dec feat j43 0 (FV7z.mk .jmp 64 [.rel 18446744073709550727] 5) := by dec_rfl

/-- The stretch at `1072`. -/
def p55 : List Byte := [
  0x48, 0x03, 0x5f, 0x20]

theorem p55_0 : ∀ feat, Dec feat p55 0 (FV7z.mk .add 64 [gr 64 3, .mem (mg (some 7) none 1 32 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o55 : List Op := [
  Op.addm 64 3 (some 7) none 1 32]

theorem b55 (prof : Profile) : Blk prof p55 0 4 o55 :=
  .cons (p55_0 _) (OpI.addm (.inr rfl)) (by decide) <|
  .nil 4

def j44 : List Byte := [0xe9, 0xe1, 0xfe, 0xff, 0xff]
theorem j44_0 : ∀ feat, Dec feat j44 0 (FV7z.mk .jmp 64 [.rel 18446744073709551329] 5) := by dec_rfl

def j45 : List Byte := [0x0f, 0x83, 0xbe, 0x00, 0x00, 0x00]
theorem j45_0 : ∀ feat, Dec feat j45 0 (FV7z.mk (.jcc 3) 64 [.rel 190] 6) := by dec_rfl

/-- The stretch at `1122`. -/
def p56 : List Byte := [
  0x4d, 0x8d, 0x54, 0x4a, 0x10, 0x41, 0xbd, 0x08, 0x00, 0x00, 0x00, 0xbb, 0x08, 0x00, 0x00, 0x00]

theorem p56_0 : ∀ feat, Dec feat p56 0 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 10) (some 1) 2 16 0)] 5) := by dec_rfl
theorem p56_5 : ∀ feat, Dec feat p56 5 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.i 8)] 6) := by dec_rfl
theorem p56_11 : ∀ feat, Dec feat p56 11 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o56 : List Op := [
  Op.lea 64 10 (some 10) (some 1) 2 16,
  Op.mov 32 13 (.i 8),
  Op.mov 32 3 (.i 8)]

theorem b56 (prof : Profile) : Blk prof p56 0 16 o56 :=
  .cons (p56_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p56_5 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p56_11 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .nil 16

def j46 : List Byte := [0xe9, 0x87, 0xfd, 0xff, 0xff]
theorem j46_0 : ∀ feat, Dec feat j46 0 (FV7z.mk .jmp 64 [.rel 18446744073709550983] 5) := by dec_rfl

/-- The stretch at `1152`. -/
def p57 : List Byte := [
  0x29, 0xfd, 0x41, 0x0f, 0xb7, 0x44, 0x1b, 0x30, 0x41, 0x29, 0xf8, 0x81, 0xfd, 0xff, 0xff, 0xff,
  0x00]

theorem p57_0 : ∀ feat, Dec feat p57 0 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p57_2 : ∀ feat, Dec feat p57 2 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 11) (some 3) 1 48 16)] 6) := by dec_rfl
theorem p57_8 : ∀ feat, Dec feat p57 8 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p57_11 : ∀ feat, Dec feat p57 11 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o57 : List Op := [
  Op.sub 32 5 (.r 7),
  Op.ldzx 16 0 (some 11) (some 3) 1 48,
  Op.sub 32 8 (.r 7),
  Op.cmp 32 5 (.i 16777215)]

theorem b57 (prof : Profile) : Blk prof p57 0 17 o57 :=
  .cons (p57_0 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p57_2 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p57_8 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p57_11 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 17

def j47 : List Byte := [0x0f, 0x83, 0xb8, 0xfc, 0xff, 0xff]
theorem j47_0 : ∀ feat, Dec feat j47 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709550776] 6) := by dec_rfl

def j48 : List Byte := [0x72, 0x4b]
theorem j48_0 : ∀ feat, Dec feat j48 0 (FV7z.mk (.jcc 2) 64 [.rel 75] 2) := by dec_rfl

/-- The stretch at `1213`. -/
def p58 : List Byte := [
  0x29, 0xfd, 0x41, 0x0f, 0xb7, 0x44, 0x1b, 0x48, 0x41, 0x29, 0xf8, 0x81, 0xfd, 0xff, 0xff, 0xff,
  0x00]

theorem p58_0 : ∀ feat, Dec feat p58 0 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p58_2 : ∀ feat, Dec feat p58 2 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 11) (some 3) 1 72 16)] 6) := by dec_rfl
theorem p58_8 : ∀ feat, Dec feat p58 8 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p58_11 : ∀ feat, Dec feat p58 11 (FV7z.mk .cmp 32 [gr 32 5, Src.opd 32 (.i 16777215)] 6) := by dec_rfl

/-- What the stretch does. -/
def o58 : List Op := [
  Op.sub 32 5 (.r 7),
  Op.ldzx 16 0 (some 11) (some 3) 1 72,
  Op.sub 32 8 (.r 7),
  Op.cmp 32 5 (.i 16777215)]

theorem b58 (prof : Profile) : Blk prof p58 0 17 o58 :=
  .cons (p58_0 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p58_2 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p58_8 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p58_11 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 17

def j49 : List Byte := [0x0f, 0x83, 0x7b, 0xfc, 0xff, 0xff]
theorem j49_0 : ∀ feat, Dec feat j49 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709550715] 6) := by dec_rfl

def j50 : List Byte := [0x72, 0x0e]
theorem j50_0 : ∀ feat, Dec feat j50 0 (FV7z.mk (.jcc 2) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `1274`. -/
def p59 : List Byte := [
  0x29, 0xfd, 0x41, 0x29, 0xf8, 0x89, 0xef, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p59_0 : ∀ feat, Dec feat p59 0 (FV7z.mk .sub 32 [gr 32 5, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p59_2 : ∀ feat, Dec feat p59 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p59_5 : ∀ feat, Dec feat p59 5 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p59_7 : ∀ feat, Dec feat p59 7 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o59 : List Op := [
  Op.sub 32 5 (.r 7),
  Op.sub 32 8 (.r 7),
  Op.mov 32 7 (.r 5),
  Op.nop]

theorem b59 (prof : Profile) : Blk prof p59 0 14 o59 :=
  .cons (p59_0 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p59_2 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p59_5 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p59_7 _) (OpI.nop) (by decide) <|
  .nil 14

/-- The stretch at `1288`. -/
def p60 : List Byte := [
  0x4d, 0x8d, 0x93, 0x00, 0xf6, 0xff, 0xff, 0x41, 0xbc, 0x03, 0x00, 0x00, 0x00, 0xbd, 0x0c, 0x00,
  0x00, 0x00]

theorem p60_0 : ∀ feat, Dec feat p60 0 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 11) none 1 18446744073709549056 0)] 7) := by dec_rfl
theorem p60_7 : ∀ feat, Dec feat p60 7 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 3)] 6) := by dec_rfl
theorem p60_13 : ∀ feat, Dec feat p60 13 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 12)] 5) := by dec_rfl

/-- What the stretch does. -/
def o60 : List Op := [
  Op.lea 64 10 (some 11) none 1 18446744073709549056,
  Op.mov 32 12 (.i 3),
  Op.mov 32 5 (.i 12)]

theorem b60 (prof : Profile) : Blk prof p60 0 18 o60 :=
  .cons (p60_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p60_7 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .cons (p60_13 _) (OpI.mov (.i 12) (.inl rfl)) (by decide) <|
  .nil 18

def j51 : List Byte := [0xe9, 0x9c, 0xfc, 0xff, 0xff]
theorem j51_0 : ∀ feat, Dec feat j51 0 (FV7z.mk .jmp 64 [.rel 18446744073709550748] 5) := by dec_rfl

/-- The stretch at `1312`. -/
def p61 : List Byte := [
  0x29, 0xc7, 0x41, 0x29, 0xc0, 0x41, 0xbd, 0x10, 0x00, 0x00, 0x00, 0xbb, 0x00, 0x01, 0x00, 0x00,
  0x49, 0x81, 0xc2, 0x00, 0x02, 0x00, 0x00, 0x89, 0xf8]

theorem p61_0 : ∀ feat, Dec feat p61 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p61_2 : ∀ feat, Dec feat p61 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p61_5 : ∀ feat, Dec feat p61 5 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.i 16)] 6) := by dec_rfl
theorem p61_11 : ∀ feat, Dec feat p61 11 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 256)] 5) := by dec_rfl
theorem p61_16 : ∀ feat, Dec feat p61 16 (FV7z.mk .add 64 [gr 64 10, Src.opd 64 (.i 512)] 7) := by dec_rfl
theorem p61_23 : ∀ feat, Dec feat p61 23 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o61 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 8 (.r 0),
  Op.mov 32 13 (.i 16),
  Op.mov 32 3 (.i 256),
  Op.add 64 10 (.i 512),
  Op.mov 32 0 (.r 7)]

theorem b61 (prof : Profile) : Blk prof p61 0 25 o61 :=
  .cons (p61_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p61_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p61_5 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p61_11 _) (OpI.mov (.i 256) (.inl rfl)) (by decide) <|
  .cons (p61_16 _) (OpI.add (.i 512) (.inr rfl)) (by decide) <|
  .cons (p61_23 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .nil 25

def j52 : List Byte := [0xe9, 0xc0, 0xfc, 0xff, 0xff]
theorem j52_0 : ∀ feat, Dec feat j52 0 (FV7z.mk .jmp 64 [.rel 18446744073709550784] 5) := by dec_rfl

/-- The stretch at `1344`. -/
def p62 : List Byte := [
  0x29, 0xc7, 0x41, 0x29, 0xc0]

theorem p62_0 : ∀ feat, Dec feat p62 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p62_2 : ∀ feat, Dec feat p62 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o62 : List Op := [
  Op.sub 32 7 (.r 0),
  Op.sub 32 8 (.r 0)]

theorem b62 (prof : Profile) : Blk prof p62 0 5 o62 :=
  .cons (p62_0 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p62_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j53 : List Byte := [0xeb, 0xc1]
theorem j53_0 : ∀ feat, Dec feat j53 0 (FV7z.mk .jmp 64 [.rel 18446744073709551553] 2) := by dec_rfl

/-- The stretch at `1360`. -/
def p63 : List Byte := [
  0x8d, 0x7b, 0xc0, 0x83, 0xff, 0x03]

theorem p63_0 : ∀ feat, Dec feat p63 0 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 3) none 1 18446744073709551552 0)] 3) := by dec_rfl
theorem p63_3 : ∀ feat, Dec feat p63 3 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o63 : List Op := [
  Op.lea 32 7 (some 3) none 1 18446744073709551552,
  Op.cmp 32 7 (.i 3)]

theorem b63 (prof : Profile) : Blk prof p63 0 6 o63 :=
  .cons (p63_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p63_3 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 6

def j54 : List Byte := [0x0f, 0x86, 0xe4, 0xfb, 0xff, 0xff]
theorem j54_0 : ∀ feat, Dec feat j54 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709550564] 6) := by dec_rfl

/-- The stretch at `1372`. -/
def p64 : List Byte := [
  0x89, 0xf9, 0xd1, 0xe9, 0x83, 0xff, 0x0d]

theorem p64_0 : ∀ feat, Dec feat p64 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p64_2 : ∀ feat, Dec feat p64 2 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p64_4 : ∀ feat, Dec feat p64 4 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o64 : List Op := [
  Op.mov 32 1 (.r 7),
  Op.shr 1 (.i 1),
  Op.cmp 32 7 (.i 13)]

theorem b64 (prof : Profile) : Blk prof p64 0 7 o64 :=
  .cons (p64_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p64_2 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p64_4 _) (OpI.cmp (.i 13) (.inl rfl)) (by decide) <|
  .nil 7

def j55 : List Byte := [0x77, 0x78]
theorem j55_0 : ∀ feat, Dec feat j55 0 (FV7z.mk (.jcc 7) 64 [.rel 120] 2) := by dec_rfl

/-- The stretch at `1381`. -/
def p65 : List Byte := [
  0x83, 0xe7, 0x01, 0x83, 0xe9, 0x01, 0x83, 0xcf, 0x02, 0xd3, 0xe7, 0x4d, 0x8d, 0x9c, 0x7b, 0x00,
  0xf3, 0xff, 0xff]

theorem p65_0 : ∀ feat, Dec feat p65 0 (FV7z.mk .and 32 [gr 32 7, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p65_3 : ∀ feat, Dec feat p65 3 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p65_6 : ∀ feat, Dec feat p65 6 (FV7z.mk .or 32 [gr 32 7, Src.opd 32 (.i 2)] 3) := by dec_rfl
theorem p65_9 : ∀ feat, Dec feat p65 9 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p65_11 : ∀ feat, Dec feat p65 11 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 11) (some 7) 2 18446744073709548288 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o65 : List Op := [
  Op.and 32 7 (.i 1),
  Op.sub 32 1 (.i 1),
  Op.or 32 7 (.i 2),
  Op.shl 7 (.r 1),
  Op.lea 64 11 (some 11) (some 7) 2 18446744073709548288]

theorem b65 (prof : Profile) : Blk prof p65 0 19 o65 :=
  .cons (p65_0 _) (OpI.and (.i 1) (.inl rfl)) (by decide) <|
  .cons (p65_3 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p65_6 _) (OpI.or (.i 2) (.inl rfl)) (by decide) <|
  .cons (p65_9 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p65_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 19

/-- The stretch at `1400`. -/
def p66 : List Byte := [
  0xbd, 0x01, 0x00, 0x00, 0x00, 0xbb, 0x01, 0x00, 0x00, 0x00]

theorem p66_0 : ∀ feat, Dec feat p66 0 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p66_5 : ∀ feat, Dec feat p66 5 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o66 : List Op := [
  Op.mov 32 5 (.i 1),
  Op.mov 32 3 (.i 1)]

theorem b66 (prof : Profile) : Blk prof p66 0 10 o66 :=
  .cons (p66_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p66_5 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 10

def j56 : List Byte := [0xeb, 0x14]
theorem j56_0 : ∀ feat, Dec feat j56 0 (FV7z.mk .jmp 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `1416`. -/
def p67 : List Byte := [
  0x01, 0xeb, 0x89, 0xf8]

theorem p67_0 : ∀ feat, Dec feat p67 0 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p67_2 : ∀ feat, Dec feat p67 2 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o67 : List Op := [
  Op.add 32 3 (.r 5),
  Op.mov 32 0 (.r 7)]

theorem b67 (prof : Profile) : Blk prof p67 0 4 o67 :=
  .cons (p67_0 _) (OpI.add (.r 5) (.inl rfl)) (by decide) <|
  .cons (p67_2 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `1420`. -/
def p68 : List Byte := [
  0x83, 0xe9, 0x01]

theorem p68_0 : ∀ feat, Dec feat p68 0 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o68 : List Op := [
  Op.sub 32 1 (.i 1)]

theorem b68 (prof : Profile) : Blk prof p68 0 3 o68 :=
  .cons (p68_0 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j57 : List Byte := [0x0f, 0x84, 0xab, 0xfb, 0xff, 0xff]
theorem j57_0 : ∀ feat, Dec feat j57 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709550507] 6) := by dec_rfl

/-- The stretch at `1429`. -/
def p69 : List Byte := [
  0x44, 0x89, 0xd5]

theorem p69_0 : ∀ feat, Dec feat p69 0 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o69 : List Op := [
  Op.mov 32 5 (.r 10)]

theorem b69 (prof : Profile) : Blk prof p69 0 3 o69 :=
  .cons (p69_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `1432`. -/
def p70 : List Byte := [
  0x89, 0xdf, 0x45, 0x0f, 0xb7, 0x14, 0x7b, 0x3d, 0xff, 0xff, 0xff, 0x00]

theorem p70_0 : ∀ feat, Dec feat p70 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p70_2 : ∀ feat, Dec feat p70 2 (FV7z.mk .movzx 32 [gr 32 10, .mem (mg (some 11) (some 7) 2 0 16)] 5) := by dec_rfl
theorem p70_7 : ∀ feat, Dec feat p70 7 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16777215)] 5) := by dec_rfl

/-- What the stretch does. -/
def o70 : List Op := [
  Op.mov 32 7 (.r 3),
  Op.ldzx 16 10 (some 11) (some 7) 2 0,
  Op.cmp 32 0 (.i 16777215)]

theorem b70 (prof : Profile) : Blk prof p70 0 12 o70 :=
  .cons (p70_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p70_2 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p70_7 _) (OpI.cmp (.i 16777215) (.inl rfl)) (by decide) <|
  .nil 12

def j58 : List Byte := [0x0f, 0x83, 0x40, 0xfd, 0xff, 0xff]
theorem j58_0 : ∀ feat, Dec feat j58 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709550912] 6) := by dec_rfl

/-- The stretch at `1455`. -/
def p71 : List Byte := [
  0x0f, 0xb6, 0x3e, 0x41, 0xc1, 0xe0, 0x08, 0xc1, 0xe0, 0x08, 0x48, 0x83, 0xc6, 0x01, 0x41, 0x09,
  0xf8]

theorem p71_0 : ∀ feat, Dec feat p71 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p71_3 : ∀ feat, Dec feat p71 3 (FV7z.mk .shl 32 [gr 32 8, Src.opd 8 (.i 8)] 4) := by dec_rfl
theorem p71_7 : ∀ feat, Dec feat p71 7 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p71_10 : ∀ feat, Dec feat p71 10 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p71_14 : ∀ feat, Dec feat p71 14 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o71 : List Op := [
  Op.ldzx 8 7 (some 6) none 1 0,
  Op.shl 8 (.i 8),
  Op.shl 0 (.i 8),
  Op.add 64 6 (.i 1),
  Op.or 32 8 (.r 7)]

theorem b71 (prof : Profile) : Blk prof p71 0 17 o71 :=
  .cons (p71_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p71_3 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p71_7 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p71_10 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p71_14 _) (OpI.or (.r 7) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `1472`. -/
def p72 : List Byte := [
  0x89, 0xc7, 0xc1, 0xef, 0x0b, 0x41, 0x0f, 0xaf, 0xfa, 0x44, 0x8d, 0x54, 0x2d, 0x00, 0x41, 0x39,
  0xf8]

theorem p72_0 : ∀ feat, Dec feat p72 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p72_2 : ∀ feat, Dec feat p72 2 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 11)] 3) := by dec_rfl
theorem p72_5 : ∀ feat, Dec feat p72 5 (FV7z.mk .imul 32 [gr 32 7, gr 32 10] 4) := by dec_rfl
theorem p72_9 : ∀ feat, Dec feat p72 9 (FV7z.mk .lea 32 [gr 32 10, .mem (mg (some 5) (some 5) 1 0 0)] 5) := by dec_rfl
theorem p72_14 : ∀ feat, Dec feat p72 14 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o72 : List Op := [
  Op.mov 32 7 (.r 0),
  Op.shr 7 (.i 11),
  Op.imul 7 10,
  Op.lea 32 10 (some 5) (some 5) 1 0,
  Op.cmp 32 8 (.r 7)]

theorem b72 (prof : Profile) : Blk prof p72 0 17 o72 :=
  .cons (p72_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p72_2 _) (OpI.shr (.i 11)) (by decide) <|
  .cons (p72_5 _) (OpI.imul) (by decide) <|
  .cons (p72_9 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p72_14 _) (OpI.cmp (.r 7) (.inl rfl)) (by decide) <|
  .nil 17

def j59 : List Byte := [0x72, 0xb5]
theorem j59_0 : ∀ feat, Dec feat j59 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551541] 2) := by dec_rfl

/-- The stretch at `1491`. -/
def p73 : List Byte := [
  0x29, 0xf8, 0x41, 0x29, 0xf8, 0x44, 0x01, 0xd3]

theorem p73_0 : ∀ feat, Dec feat p73 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p73_2 : ∀ feat, Dec feat p73 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p73_5 : ∀ feat, Dec feat p73 5 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o73 : List Op := [
  Op.sub 32 0 (.r 7),
  Op.sub 32 8 (.r 7),
  Op.add 32 3 (.r 10)]

theorem b73 (prof : Profile) : Blk prof p73 0 8 o73 :=
  .cons (p73_0 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p73_2 _) (OpI.sub (.r 7) (.inl rfl)) (by decide) <|
  .cons (p73_5 _) (OpI.add (.r 10) (.inl rfl)) (by decide) <|
  .nil 8

def j60 : List Byte := [0xeb, 0xaf]
theorem j60_0 : ∀ feat, Dec feat j60 0 (FV7z.mk .jmp 64 [.rel 18446744073709551535] 2) := by dec_rfl

/-- The stretch at `1501`. -/
def p74 : List Byte := [
  0x8d, 0x79, 0xfb]

theorem p74_0 : ∀ feat, Dec feat p74 0 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 1) none 1 18446744073709551611 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o74 : List Op := [
  Op.lea 32 7 (some 1) none 1 18446744073709551611]

theorem b74 (prof : Profile) : Blk prof p74 0 3 o74 :=
  .cons (p74_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 3

def j61 : List Byte := [0x0f, 0x83, 0xff, 0xfc, 0xff, 0xff]
theorem j61_0 : ∀ feat, Dec feat j61 0 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709550847] 6) := by dec_rfl

/-- The stretch at `1537`. -/
def p75 : List Byte := [
  0xd1, 0xe8, 0x44, 0x89, 0xc1, 0x29, 0xc1, 0xc1, 0xe9, 0x1f, 0x83, 0xe9, 0x01, 0x21, 0xc1, 0x41,
  0x29, 0xc8, 0x83, 0xef, 0x01]

theorem p75_0 : ∀ feat, Dec feat p75 0 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p75_2 : ∀ feat, Dec feat p75 2 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p75_5 : ∀ feat, Dec feat p75 5 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p75_7 : ∀ feat, Dec feat p75 7 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 31)] 3) := by dec_rfl
theorem p75_10 : ∀ feat, Dec feat p75 10 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p75_13 : ∀ feat, Dec feat p75 13 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p75_15 : ∀ feat, Dec feat p75 15 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p75_18 : ∀ feat, Dec feat p75 18 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o75 : List Op := [
  Op.shr 0 (.i 1),
  Op.mov 32 1 (.r 8),
  Op.sub 32 1 (.r 0),
  Op.shr 1 (.i 31),
  Op.sub 32 1 (.i 1),
  Op.and 32 1 (.r 0),
  Op.sub 32 8 (.r 1),
  Op.sub 32 7 (.i 1)]

theorem b75 (prof : Profile) : Blk prof p75 0 21 o75 :=
  .cons (p75_0 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p75_2 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p75_5 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p75_7 _) (OpI.shr (.i 31)) (by decide) <|
  .cons (p75_10 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p75_13 _) (OpI.and (.r 0) (.inl rfl)) (by decide) <|
  .cons (p75_15 _) (OpI.sub (.r 1) (.inl rfl)) (by decide) <|
  .cons (p75_18 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 21

def j62 : List Byte := [0x75, 0xc8]
theorem j62_0 : ∀ feat, Dec feat j62 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551560] 2) := by dec_rfl

/-- The stretch at `1560`. -/
def p76 : List Byte := [
  0xb9, 0x04, 0x00, 0x00, 0x00]

theorem p76_0 : ∀ feat, Dec feat p76 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 4)] 5) := by dec_rfl

/-- What the stretch does. -/
def o76 : List Op := [
  Op.mov 32 1 (.i 4)]

theorem b76 (prof : Profile) : Blk prof p76 0 5 o76 :=
  .cons (p76_0 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 5

def j63 : List Byte := [0xe9, 0x56, 0xff, 0xff, 0xff]
theorem j63_0 : ∀ feat, Dec feat j63 0 (FV7z.mk .jmp 64 [.rel 18446744073709551446] 5) := by dec_rfl

end FV7z.Tdm
