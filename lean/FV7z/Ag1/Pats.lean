import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::Grow_1` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ag1
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x8b, 0x47, 0x08, 0x89, 0xc2, 0xd1, 0xea, 0x8d,
  0x74, 0x02, 0x10, 0x83, 0xe6, 0xf0, 0x83, 0xee, 0x01, 0x81, 0xfe, 0xfe, 0xff, 0xff, 0x3f]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 2) (some 0) 1 16 0)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 4294967280)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .sub 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 1073741822)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8),
  Op.ld 32 0 (some 7) none 1 8,
  Op.mov 32 2 (.r 0),
  Op.shr 2 (.i 1),
  Op.lea 32 6 (some 2) (some 0) 1 16,
  Op.and 32 6 (.i 4294967280),
  Op.sub 32 6 (.i 1),
  Op.cmp 32 6 (.i 1073741822)]

theorem b0 (prof : Profile) : Blk prof p0 0 31 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p0_15 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.and (.i 4294967280) (.inl rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p0_25 _) (OpI.cmp (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 31

def j0 : List Byte := [0x77, 0x04]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p1 : List Byte := [
  0x39, 0xf0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 0 (.r 6)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.cmp (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x76, 0x05]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p2 : List Byte := [
  0xbe, 0xfe, 0xff, 0xff, 0x3f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1073741822)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 6 (.i 1073741822)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `42`. -/
def p3 : List Byte := [
  0x39, 0xc6]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 6 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `50`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Ag1
