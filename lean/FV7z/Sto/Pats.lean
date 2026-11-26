import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `COpenCallbackImp::SetTotal` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sto
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x4c, 0x8b, 0x47, 0x60, 0x4d, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 7) none 1 96 64)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 64 8 (some 7) none 1 96,
  Op.test 64 8 (.r 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x74, 0x13]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x49, 0x8b, 0x00, 0x4c, 0x89, 0xc7, 0x48, 0x8b, 0x40, 0x18]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 8) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 24 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 8) none 1 0,
  Op.mov 64 7 (.r 8),
  Op.ld 64 0 (some 0) none 1 24]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x7f, 0x68, 0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 104 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 7) none 1 104,
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x74, 0x17]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xec, 0x08, 0x48, 0x8b, 0x07]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sub 64 4 (.i 8),
  Op.ld 64 0 (some 7) none 1 0]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `51`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0x31, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Sto
