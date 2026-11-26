import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmovLd
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::UString(unsigned, const UString&)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ucu
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x49, 0x89, 0xd4, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x89, 0xf3,
  0x39, 0x72, 0x08, 0x0f, 0x46, 0x5a, 0x08, 0x89, 0xde, 0x89, 0xdb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .cmp 32 [.mem (mg (some 2) none 1 8 32), gr 32 6] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk (.cmovcc 6) 32 [gr 32 3, .mem (mg (some 2) none 1 8 32)] 4) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 12 (.r 2),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 32 3 (.r 6),
  Op.cmpmr 32 (some 2) none 1 8 6,
  Op.cmovld32 6 3 (some 2) none 1 8,
  Op.mov 32 6 (.r 3),
  Op.mov 32 3 (.r 3)]

theorem b0 (prof : Profile) : Blk prof p0 0 27 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.cmovld32) (by decide) <|
  .cons (p0_23 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p0_25 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .nil 27

/-- The stretch at `32`. -/
def p1 : List Byte := [
  0x49, 0x8b, 0x34, 0x24, 0x48, 0x8b, 0x7d, 0x00, 0x48, 0x89, 0xda]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 6 (some 12) none 1 0,
  Op.ld 64 7 (some 5) none 1 0,
  Op.mov 64 2 (.r 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x45, 0x00, 0xc7, 0x04, 0x98, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x5d, 0x41, 0x5c]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 32 [.mem (mg (some 0) (some 3) 4 0 32), .imm 32 0] 7) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 0 (some 5) none 1 0,
  Op.sti 32 (some 0) (some 3) 4 0 0,
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b2 (prof : Profile) : Blk prof p2 0 15 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_11 _) (OpI.pop) (by decide) <|
  .cons (p2_12 _) (OpI.pop) (by decide) <|
  .cons (p2_13 _) (OpI.pop) (by decide) <|
  .nil 15

end FV7z.Ucu
