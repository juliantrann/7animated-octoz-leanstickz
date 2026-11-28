import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::Insert` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ain
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x10, 0x44, 0x8b, 0x62, 0x08,
  0x89, 0x74, 0x24, 0x0c, 0x45, 0x85, 0xe4]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 2) none 1 8 32)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 6] 4) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 16),
  Op.ld 32 12 (some 2) none 1 8,
  Op.st 32 (some 4) none 1 12 6,
  Op.test 32 12 (.r 12)]

theorem b0 (prof : Profile) : Blk prof p0 0 23 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.sub (.i 16) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_20 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .nil 23

def j0 : List Byte := [0x75, 0x0f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x5b, 0x5d, 0x41, 0x5c]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 4 (.i 16),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.pop) (by decide) <|
  .cons (p1_5 _) (OpI.pop) (by decide) <|
  .cons (p1_6 _) (OpI.pop) (by decide) <|
  .nil 8

/-- The stretch at `40`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xd3, 0x48, 0x8d, 0x74, 0x24, 0x0c, 0x44, 0x89, 0xe2, 0x48, 0x89, 0xfd]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 4) none 1 12 0)] 5) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 3 (.r 2),
  Op.lea 64 6 (some 4) none 1 12,
  Op.mov 32 2 (.r 12),
  Op.mov 64 5 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `59`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x33, 0x8b, 0x7c, 0x24, 0x0c, 0x44, 0x89, 0xe2, 0x48, 0x03, 0x7d, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .add 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 6 (some 3) none 1 0,
  Op.ld 32 7 (some 4) none 1 12,
  Op.mov 32 2 (.r 12),
  Op.addm 64 7 (some 5) none 1 0]

theorem b3 (prof : Profile) : Blk prof p3 0 14 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.addm (.inr rfl)) (by decide) <|
  .nil 14

end FV7z.Ain
