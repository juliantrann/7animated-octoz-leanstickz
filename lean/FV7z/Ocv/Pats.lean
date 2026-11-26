import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `CObjectVector<CRecordVector<unsigned>>::~CObjectVector` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ocv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x53, 0x8b, 0x47, 0x08, 0x48, 0x8b,
  0x3f, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.push 3,
  Op.ld 32 0 (some 7) none 1 8,
  Op.ld 64 7 (some 7) none 1 0,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 19 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 19

def j0 : List Byte := [0x74, 0x3d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x8d, 0x58, 0xff, 0x48, 0xc1, 0xe3, 0x03, 0x0f, 0x1f, 0x40, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .shl 64 [gr 64 3, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 3 (some 0) none 1 18446744073709551615,
  Op.shl64 3 (.i 3),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.shl64 (.i 3)) (by decide) <|
  .cons (p1_7 _) (OpI.nop) (by decide) <|
  .nil 11

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x2c, 0x1f, 0x48, 0x85, 0xed]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 7) (some 3) 1 0 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 5 (some 7) (some 3) 1 0,
  Op.test 64 5 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x74, 0x1f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x7d, 0x00, 0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 7 (some 5) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `55`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xef, 0xbe, 0x10, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.r 5),
  Op.mov 32 6 (.i 16)]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `68`. -/
def p5 : List Byte := [
  0x49, 0x8b, 0x3c, 0x24]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 12) none 1 0]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `72`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xeb, 0x08, 0x48, 0x83, 0xfb, 0xf8]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.sub 64 3 (.i 8),
  Op.cmp 64 3 (.i 18446744073709551608)]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmp (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x75, 0xce]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551566] 2) := by dec_rfl

/-- The stretch at `82`. -/
def p7 : List Byte := [
  0x48, 0x85, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0x09]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `87`. -/
def p8 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p8_1 : ∀ feat, Dec feat p8 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_2 : ∀ feat, Dec feat p8 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.pop) (by decide) <|
  .cons (p8_1 _) (OpI.pop) (by decide) <|
  .cons (p8_2 _) (OpI.pop) (by decide) <|
  .nil 4

end FV7z.Ocv
