import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CDirPathSortPair::SetNumSlashes` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sns
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x0f, 0xb6, 0x06, 0x48, 0x8d, 0x56, 0x01, 0x31, 0xc9, 0x84, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 6) none 1 1 0)] 4) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ldzx 8 0 (some 6) none 1 0,
  Op.lea 64 2 (some 6) none 1 1,
  Op.xor 32 1 (.r 1),
  Op.test 8 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 15 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 15

def j0 : List Byte := [0x74, 0x1d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.nop) (by decide) <|
  .nil 7

/-- The stretch at `24`. -/
def p2 : List Byte := [
  0x3c, 0x2f, 0x0f, 0x94, 0xc0, 0x48, 0x83, 0xc2, 0x01, 0x0f, 0xb6, 0xc0, 0x01, 0xc1, 0x0f, 0xb6,
  0x42, 0xff, 0x84, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [gr 8 0, Src.opd 8 (.i 47)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .movzx 32 [gr 32 0, gr 8 0] 3) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 2) none 1 18446744073709551615 8)] 4) := by dec_rfl
theorem p2_18 : ∀ feat, Dec feat p2 18 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 8 0 (.i 47),
  Op.setcc 4 0,
  Op.add 64 2 (.i 1),
  Op.zxr 0 0,
  Op.add 32 1 (.r 0),
  Op.ldzx 8 0 (some 2) none 1 18446744073709551615,
  Op.test 8 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 20 o2 :=
  .cons (p2_0 _) (OpI.cmp8 (.i 47)) (by decide) <|
  .cons (p2_2 _) (OpI.setcc) (by decide) <|
  .cons (p2_5 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.zxr) (by decide) <|
  .cons (p2_12 _) (OpI.add (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p2_18 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 20

def j1 : List Byte := [0x75, 0xea]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551594] 2) := by dec_rfl

/-- The stretch at `46`. -/
def p3 : List Byte := [
  0x89, 0x0f]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 0 32), gr 32 1] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 7) none 1 0 1]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 2

end FV7z.Sns
