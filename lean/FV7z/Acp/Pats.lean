import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::AString (const AString &)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Acp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x08,
  0x8b, 0x76, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 32 [gr 32 6, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8),
  Op.ld 32 6 (some 6) none 1 8]

theorem b0 (prof : Profile) : Blk prof p0 0 19 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 19

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x75, 0x00, 0x48, 0x8b, 0x0b, 0x31, 0xc0, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 6 (some 5) none 1 0,
  Op.ld 64 1 (some 3) none 1 0,
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `40`. -/
def p2 : List Byte := [
  0x0f, 0xb6, 0x14, 0x06, 0x88, 0x14, 0x01, 0x48, 0x83, 0xc0, 0x01, 0x84, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) (some 0) 1 0 8)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 8 [.mem (mg (some 1) (some 0) 1 0 8), gr 8 2] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ldzx 8 2 (some 6) (some 0) 1 0,
  Op.st 8 (some 1) (some 0) 1 0 2,
  Op.add 64 0 (.i 1),
  Op.test 8 2 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 13 o2 :=
  .cons (p2_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 13

def j0 : List Byte := [0x75, 0xf1]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551601] 2) := by dec_rfl

/-- The stretch at `55`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.pop) (by decide) <|
  .cons (p3_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Acp
