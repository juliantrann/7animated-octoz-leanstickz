import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::ReAlloc2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ur2
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x81, 0xfe, 0xfe, 0xff, 0xff, 0x3f]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 1073741822)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.cmp 32 6 (.i 1073741822)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.cmp (.i 1073741822) (.inl rfl)) (by decide) <|
  .nil 14

/-- The stretch at `20`. -/
def p1 : List Byte := [
  0x89, 0xf0, 0x48, 0x89, 0xfb, 0x89, 0xf5, 0x48, 0x8d, 0x3c, 0x85, 0x04, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mg none (some 0) 4 4 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.r 6),
  Op.mov 64 3 (.r 7),
  Op.mov 32 5 (.r 6),
  Op.lea 64 7 none (some 0) 4 4]

theorem b1 (prof : Profile) : Blk prof p1 0 15 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 15

/-- The stretch at `40`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x3b, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00, 0x49, 0x89, 0xc4, 0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 0] 6) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 3) none 1 0,
  Op.sti 32 (some 0) none 1 0 0,
  Op.mov 64 12 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 15 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_9 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 15

def j0 : List Byte := [0x74, 0x05]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `62`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0x23, 0x89, 0x6b, 0x0c, 0xc7, 0x43, 0x08, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x5d, 0x41,
  0x5c]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 12] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 12 32), gr 32 5] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 64 (some 3) none 1 0 12,
  Op.st 32 (some 3) none 1 12 5,
  Op.sti 32 (some 3) none 1 8 0,
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b3 (prof : Profile) : Blk prof p3 0 17 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_6 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_13 _) (OpI.pop) (by decide) <|
  .cons (p3_14 _) (OpI.pop) (by decide) <|
  .cons (p3_15 _) (OpI.pop) (by decide) <|
  .nil 17

end FV7z.Ur2
