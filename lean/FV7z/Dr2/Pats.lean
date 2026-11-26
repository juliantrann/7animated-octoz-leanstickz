import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaDec_DecodeReal2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dr2
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x53, 0x8b, 0x4f, 0x44, 0x48, 0x89, 0xfb, 0x85, 0xc9]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_1 : ∀ feat, Dec feat p0 1 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 68 32)] 3) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 3,
  Op.ld 32 1 (some 7) none 1 68,
  Op.mov 64 3 (.r 7),
  Op.test 32 1 (.r 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_1 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x75, 0x1a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x47, 0x28, 0x8b, 0x4f, 0x04, 0x2b, 0x4f, 0x40, 0x48, 0x89, 0xf7, 0x48, 0x29, 0xc7,
  0x48, 0x01, 0xc8, 0x48, 0x39, 0xcf, 0x48, 0x0f, 0x47, 0xf0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 40 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 7) none 1 4 32)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .sub 32 [gr 32 1, .mem (mg (some 7) none 1 64 32)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p1_19 : ∀ feat, Dec feat p1 19 (FV7z.mk .cmp 64 [gr 64 7, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk (.cmovcc 7) 64 [gr 64 6, gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 40,
  Op.ld 32 1 (some 7) none 1 4,
  Op.subm 32 1 (some 7) none 1 64,
  Op.mov 64 7 (.r 6),
  Op.sub 64 7 (.r 0),
  Op.add 64 0 (.r 1),
  Op.cmp 64 7 (.r 1),
  Op.cmov64 7 6 0]

theorem b1 (prof : Profile) : Blk prof p1 0 26 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.subm (.inl rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_13 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .cons (p1_16 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p1_19 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .cons (p1_22 _) (OpI.cmov64) (by decide) <|
  .nil 26

/-- The stretch at `37`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xdf]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x8b, 0x53, 0x44, 0x85, 0xd2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 68 32)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 32 2 (some 3) none 1 68,
  Op.test 32 2 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 5 o3 :=
  .cons (p3_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x75, 0x0b]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `52`. -/
def p4 : List Byte := [
  0x8b, 0x53, 0x04, 0x39, 0x53, 0x40]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 4 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .cmp 32 [.mem (mg (some 3) none 1 64 32), gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 2 (some 3) none 1 4,
  Op.cmpmr 32 (some 3) none 1 64 2]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x72, 0x03]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 2) 64 [.rel 3] 2) := by dec_rfl

/-- The stretch at `60`. -/
def p5 : List Byte := [
  0x89, 0x53, 0x44]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 68 32), gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 32 (some 3) none 1 68 2]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 3

/-- The stretch at `63`. -/
def p6 : List Byte := [
  0x5b]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.pop 3]

theorem b6 (prof : Profile) : Blk prof p6 0 1 o6 :=
  .cons (p6_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.Dr2
