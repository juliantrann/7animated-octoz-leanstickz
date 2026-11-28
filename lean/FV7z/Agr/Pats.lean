import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::Grow` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Agr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x57, 0x08, 0x8b, 0x4f, 0x0c, 0x29, 0xd1, 0x39, 0xf1]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 12 32)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 2 (some 7) none 1 8,
  Op.ld 32 1 (some 7) none 1 12,
  Op.sub 32 1 (.r 2),
  Op.cmp 32 1 (.r 6)]

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
  0x8d, 0x0c, 0x32, 0x89, 0xf0, 0x48, 0x83, 0xec, 0x08, 0x89, 0xce, 0xd1, 0xee, 0x8d, 0x74, 0x0e,
  0x10, 0x83, 0xe6, 0xf0, 0x83, 0xee, 0x01, 0x39, 0xf2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 2) (some 6) 1 0 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 6) (some 1) 1 16 0)] 4) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 4294967280)] 3) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk .sub 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p1_23 : ∀ feat, Dec feat p1 23 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 1 (some 2) (some 6) 1 0,
  Op.mov 32 0 (.r 6),
  Op.sub 64 4 (.i 8),
  Op.mov 32 6 (.r 1),
  Op.shr 6 (.i 1),
  Op.lea 32 6 (some 6) (some 1) 1 16,
  Op.and 32 6 (.i 4294967280),
  Op.sub 32 6 (.i 1),
  Op.cmp 32 2 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 25 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p1_11 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p1_13 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_17 _) (OpI.and (.i 4294967280) (.inl rfl)) (by decide) <|
  .cons (p1_20 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_23 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 25

def j1 : List Byte := [0x77, 0x08]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `43`. -/
def p2 : List Byte := [
  0x81, 0xfe, 0xfe, 0xff, 0xff, 0x3f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 1073741822)] 6) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 32 6 (.i 1073741822)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x76, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `51`. -/
def p3 : List Byte := [
  0xbe, 0xfe, 0xff, 0xff, 0x3f]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1073741822)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 6 (.i 1073741822)]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x39, 0xf2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 32 2 (.r 6)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0x89, 0xf1, 0x29, 0xd1, 0x39, 0xc1]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 1 (.r 6),
  Op.sub 32 1 (.r 2),
  Op.cmp 32 1 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `76`. -/
def p6 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 4 o6 :=
  .cons (p6_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Agr
