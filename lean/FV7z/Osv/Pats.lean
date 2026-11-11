import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps5
/-!
# The stretches of straight-line code of `_dl_discover_osversion` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Osv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x48, 0x81, 0xec, 0xd0, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x7c, 0x24, 0x40]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 464)] 7) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 4) none 1 64 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 464),
  Op.lea 64 7 (some 4) none 1 64]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.sub (.i 464) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 20

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0xbc, 0x24, 0xc2, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 4) none 1 194 0)] 8) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 7 (some 4) none 1 194,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x0f, 0x85, 0x87, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 135] 6) := by dec_rfl

/-- The stretch at `41`. -/
def p2 : List Byte := [
  0x45, 0x31, 0xc0, 0x31, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 8 (.r 8),
  Op.xor 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 8) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `46`. -/
def p3 : List Byte := [
  0x0f, 0xbe, 0x0f, 0x8d, 0x51, 0xd0, 0x80, 0xfa, 0x09]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movsx 32 [gr 32 1, .mem (mg (some 7) none 1 0 8)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 1) none 1 18446744073709551568 0)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldsxb 1 (some 7) none 1 0,
  Op.lea 32 2 (some 1) none 1 18446744073709551568,
  Op.cmp 8 2 (.i 9)]

theorem b3 (prof : Profile) : Blk prof p3 0 9 o3 :=
  .cons (p3_0 _) (OpI.ldsxb) (by decide) <|
  .cons (p3_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.cmp8 (.i 9)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x77, 0x58]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 88] 2) := by dec_rfl

/-- The stretch at `57`. -/
def p4 : List Byte := [
  0x0f, 0xbe, 0x57, 0x01, 0x48, 0x8d, 0x77, 0x01, 0x83, 0xe9, 0x30, 0x8d, 0x7a, 0xd0, 0x40, 0x80,
  0xff, 0x09]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movsx 32 [gr 32 2, .mem (mg (some 7) none 1 1 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 7) none 1 1 0)] 4) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 48)] 3) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 2) none 1 18446744073709551568 0)] 3) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .cmp 8 [gr 8 7, Src.opd 8 (.i 9)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldsxb 2 (some 7) none 1 1,
  Op.lea 64 6 (some 7) none 1 1,
  Op.sub 32 1 (.i 48),
  Op.lea 32 7 (some 2) none 1 18446744073709551568,
  Op.cmp 8 7 (.i 9)]

theorem b4 (prof : Profile) : Blk prof p4 0 18 o4 :=
  .cons (p4_0 _) (OpI.ldsxb) (by decide) <|
  .cons (p4_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_8 _) (OpI.sub (.i 48) (.inl rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p4_14 _) (OpI.cmp8 (.i 9)) (by decide) <|
  .nil 18

def j2 : List Byte := [0x77, 0x1a]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `77`. -/
def p5 : List Byte := [
  0x0f, 0x1f, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.nop]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.nop) (by decide) <|
  .nil 3

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x8d, 0x0c, 0x89, 0x48, 0x83, 0xc6, 0x01, 0x8d, 0x4c, 0x4a, 0xd0, 0x0f, 0xbe, 0x16, 0x8d, 0x7a,
  0xd0, 0x40, 0x80, 0xff, 0x09]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 1) (some 1) 4 0 0)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 2) (some 1) 2 18446744073709551568 0)] 4) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .movsx 32 [gr 32 2, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p6_14 : ∀ feat, Dec feat p6 14 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 2) none 1 18446744073709551568 0)] 3) := by dec_rfl
theorem p6_17 : ∀ feat, Dec feat p6 17 (FV7z.mk .cmp 8 [gr 8 7, Src.opd 8 (.i 9)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 32 1 (some 1) (some 1) 4 0,
  Op.add 64 6 (.i 1),
  Op.lea 32 1 (some 2) (some 1) 2 18446744073709551568,
  Op.ldsxb 2 (some 6) none 1 0,
  Op.lea 32 7 (some 2) none 1 18446744073709551568,
  Op.cmp 8 7 (.i 9)]

theorem b6 (prof : Profile) : Blk prof p6 0 21 o6 :=
  .cons (p6_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_11 _) (OpI.ldsxb) (by decide) <|
  .cons (p6_14 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_17 _) (OpI.cmp8 (.i 9)) (by decide) <|
  .nil 21

def j3 : List Byte := [0x76, 0xe9]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551593] 2) := by dec_rfl

/-- The stretch at `103`. -/
def p7 : List Byte := [
  0xc1, 0xe0, 0x08, 0x41, 0x83, 0xc0, 0x01, 0x48, 0x8d, 0x7e, 0x01, 0x09, 0xc8, 0x80, 0xfa, 0x2e]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .add 32 [gr 32 8, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 6) none 1 1 0)] 4) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p7_13 : ∀ feat, Dec feat p7 13 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 46)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.shl 0 (.i 8),
  Op.add 32 8 (.i 1),
  Op.lea 64 7 (some 6) none 1 1,
  Op.or 32 0 (.r 1),
  Op.cmp 8 2 (.i 46)]

theorem b7 (prof : Profile) : Blk prof p7 0 16 o7 :=
  .cons (p7_0 _) (OpI.shl (.i 8)) (by decide) <|
  .cons (p7_3 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_11 _) (OpI.or (.r 1) (.inl rfl)) (by decide) <|
  .cons (p7_13 _) (OpI.cmp8 (.i 46)) (by decide) <|
  .nil 16

def j4 : List Byte := [0x75, 0x12]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `121`. -/
def p8 : List Byte := [
  0x41, 0x83, 0xf8, 0x03]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 32 [gr 32 8, Src.opd 32 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmp 32 8 (.i 3)]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 4

def j5 : List Byte := [0x75, 0xaf]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551535] 2) := by dec_rfl

/-- The stretch at `127`. -/
def p9 : List Byte := [
  0x48, 0x81, 0xc4, 0xd0, 0x01, 0x00, 0x00, 0x5b, 0x5d, 0x41, 0x5c]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 464)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_9 : ∀ feat, Dec feat p9 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.add 64 4 (.i 464),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b9 (prof : Profile) : Blk prof p9 0 11 o9 :=
  .cons (p9_0 _) (OpI.add (.i 464) (.inr rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.pop) (by decide) <|
  .cons (p9_8 _) (OpI.pop) (by decide) <|
  .cons (p9_9 _) (OpI.pop) (by decide) <|
  .nil 11

def j6 : List Byte := [0x74, 0xee]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `145`. -/
def p10 : List Byte := [
  0xb9, 0x03, 0x00, 0x00, 0x00, 0x48, 0x81, 0xc4, 0xd0, 0x01, 0x00, 0x00, 0x44, 0x29, 0xc1, 0x5b,
  0x5d, 0xc1, 0xe1, 0x03, 0x41, 0x5c, 0xd3, 0xe0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 3)] 5) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 464)] 7) := by dec_rfl
theorem p10_12 : ∀ feat, Dec feat p10 12 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p10_15 : ∀ feat, Dec feat p10 15 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p10_16 : ∀ feat, Dec feat p10 16 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p10_17 : ∀ feat, Dec feat p10 17 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 3)] 3) := by dec_rfl
theorem p10_20 : ∀ feat, Dec feat p10 20 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p10_22 : ∀ feat, Dec feat p10 22 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 1 (.i 3),
  Op.add 64 4 (.i 464),
  Op.sub 32 1 (.r 8),
  Op.pop 3,
  Op.pop 5,
  Op.shl 1 (.i 3),
  Op.pop 12,
  Op.shl 0 (.r 1)]

theorem b10 (prof : Profile) : Blk prof p10 0 24 o10 :=
  .cons (p10_0 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .cons (p10_5 _) (OpI.add (.i 464) (.inr rfl)) (by decide) <|
  .cons (p10_12 _) (OpI.sub (.r 8) (.inl rfl)) (by decide) <|
  .cons (p10_15 _) (OpI.pop) (by decide) <|
  .cons (p10_16 _) (OpI.pop) (by decide) <|
  .cons (p10_17 _) (OpI.shl (.i 3)) (by decide) <|
  .cons (p10_20 _) (OpI.pop) (by decide) <|
  .cons (p10_22 _) (OpI.shl (.r 1)) (by decide) <|
  .nil 24

end FV7z.Osv
