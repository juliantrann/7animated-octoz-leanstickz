import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__strdup` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sdp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x48, 0x89, 0xfd, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `19`. -/
def p1 : List Byte := [
  0x4c, 0x8d, 0x60, 0x01, 0x4c, 0x89, 0xe7]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 12 (some 0) none 1 1,
  Op.mov 64 7 (.r 12)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `31`. -/
def p2 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j0 : List Byte := [0x74, 0x15]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `36`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe2, 0x48, 0x89, 0xee, 0x48, 0x89, 0xc7, 0x5d, 0x41, 0x5c]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 2 (.r 12),
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 0),
  Op.pop 5,
  Op.pop 12]

theorem b3 (prof : Profile) : Blk prof p3 0 16 o3 :=
  .cons (p3_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_13 _) (OpI.pop) (by decide) <|
  .cons (p3_14 _) (OpI.pop) (by decide) <|
  .nil 16

/-- The stretch at `57`. -/
def p4 : List Byte := [
  0x5a, 0x31, 0xc0, 0x5d, 0x41, 0x5c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .pop 64 [gr 64 2] 1) := by dec_rfl
theorem p4_1 : ∀ feat, Dec feat p4 1 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.pop 2,
  Op.xor 32 0 (.r 0),
  Op.pop 5,
  Op.pop 12]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.pop) (by decide) <|
  .cons (p4_1 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.pop) (by decide) <|
  .cons (p4_4 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Sdp
