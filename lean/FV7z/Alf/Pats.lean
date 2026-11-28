import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::Add_LF` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Alf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x8b, 0x47, 0x08, 0x48, 0x89, 0xfb, 0x39, 0x47, 0x0c]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .cmp 32 [.mem (mg (some 7) none 1 12 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.ld 32 0 (some 7) none 1 8,
  Op.mov 64 3 (.r 7),
  Op.cmpmr 32 (some 7) none 1 12 0]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x20]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x0b, 0x8d, 0x50, 0x01, 0xc7, 0x04, 0x81, 0x0a, 0x00, 0x00, 0x00, 0x89, 0xd0, 0xc7,
  0x04, 0x81, 0x00, 0x00, 0x00, 0x00, 0x89, 0x53, 0x08, 0x5b]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 32 [.mem (mg (some 1) (some 0) 4 0 32), .imm 32 10] 7) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 32 [.mem (mg (some 1) (some 0) 4 0 32), .imm 32 0] 7) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 8 32), gr 32 2] 3) := by dec_rfl
theorem p1_25 : ∀ feat, Dec feat p1 25 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 1 (some 3) none 1 0,
  Op.lea 32 2 (some 0) none 1 1,
  Op.sti 32 (some 1) (some 0) 4 0 10,
  Op.mov 32 0 (.r 2),
  Op.sti 32 (some 1) (some 0) 4 0 0,
  Op.st 32 (some 3) none 1 8 2,
  Op.pop 3]

theorem b1 (prof : Profile) : Blk prof p1 0 26 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_13 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_22 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_25 _) (OpI.pop) (by decide) <|
  .nil 26

/-- The stretch at `53`. -/
def p2 : List Byte := [
  0x8b, 0x43, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 8 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 0 (some 3) none 1 8]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0xeb, 0xd6]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 18446744073709551574] 2) := by dec_rfl

end FV7z.Alf
