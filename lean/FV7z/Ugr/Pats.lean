import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::Grow` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ugr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x57, 0x08, 0x8b, 0x47, 0x0c, 0x29, 0xd0, 0x39, 0xf0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 12 32)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 2 (some 7) none 1 8,
  Op.ld 32 0 (some 7) none 1 12,
  Op.sub 32 0 (.r 2),
  Op.cmp 32 0 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x73, 0x48]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 3) 64 [.rel 72] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x8d, 0x04, 0x32, 0x48, 0x83, 0xec, 0x08, 0x89, 0xc1, 0xd1, 0xe9, 0x8d, 0x44, 0x01, 0x10, 0x83,
  0xe0, 0xf0, 0x83, 0xe8, 0x01, 0x39, 0xc2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 2) (some 6) 1 0 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 1) (some 0) 1 16 0)] 4) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4294967280)] 3) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p1_21 : ∀ feat, Dec feat p1 21 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 0 (some 2) (some 6) 1 0,
  Op.sub 64 4 (.i 8),
  Op.mov 32 1 (.r 0),
  Op.shr 1 (.i 1),
  Op.lea 32 0 (some 1) (some 0) 1 16,
  Op.and 32 0 (.i 4294967280),
  Op.sub 32 0 (.i 1),
  Op.cmp 32 2 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 23 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p1_11 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.and (.i 4294967280) (.inl rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_21 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 23

def j1 : List Byte := [0x77, 0x07]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p2 : List Byte := [
  0x3d, 0xfe, 0xff, 0xff, 0x3f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1073741822)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 32 0 (.i 1073741822)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 5

def j2 : List Byte := [0x76, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0xb8, 0xfe, 0xff, 0xff, 0x3f]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1073741822)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.i 1073741822)]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `53`. -/
def p4 : List Byte := [
  0x39, 0xc2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 32 2 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `61`. -/
def p5 : List Byte := [
  0x89, 0xc1, 0x29, 0xd1, 0x39, 0xf1]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.sub 32 1 (.r 2),
  Op.cmp 32 1 (.r 6)]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `73`. -/
def p6 : List Byte := [
  0x8d, 0x70, 0xff, 0x48, 0x83, 0xc4, 0x08]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 0) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 32 6 (some 0) none 1 18446744073709551615,
  Op.add 64 4 (.i 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 7

end FV7z.Ugr
