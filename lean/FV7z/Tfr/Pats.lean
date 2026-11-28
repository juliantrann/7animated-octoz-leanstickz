import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NDir::CTempFile::Remove()` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tfr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0x3f, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 8 (some 7) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 7 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x75, 0x07]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `9`. -/
def p1 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `16`. -/
def p2 : List Byte := [
  0x53, 0x48, 0x89, 0xfb, 0x48, 0x8b, 0x7f, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p2_1 : ∀ feat, Dec feat p2 1 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.ld 64 7 (some 7) none 1 8]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.push) (by decide) <|
  .cons (p2_1 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `29`. -/
def p3 : List Byte := [
  0x89, 0xc2, 0x83, 0xf2, 0x01, 0x88, 0x13, 0x5b]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 8 [.mem (mg (some 3) none 1 0 8), gr 8 2] 2) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 2 (.r 0),
  Op.xor 32 2 (.i 1),
  Op.st 8 (some 3) none 1 0 2,
  Op.pop 3]

theorem b3 (prof : Profile) : Blk prof p3 0 8 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.xor (.i 1) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.pop) (by decide) <|
  .nil 8

end FV7z.Tfr
