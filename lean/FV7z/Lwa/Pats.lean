import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `MyStringLower_Ascii(char *)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lwa
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop]

theorem b0 (prof : Profile) : Blk prof p0 0 4 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .nil 4

def j0 : List Byte := [0xeb, 0x1d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk .jmp 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x8d, 0x48, 0xbf, 0x48, 0x83, 0xc7, 0x01, 0x8d, 0x50, 0x20, 0x80, 0xf9, 0x1a, 0x0f, 0x42, 0xc2,
  0x88, 0x47, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 18446744073709551551 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 0) none 1 32 0)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .cmp 8 [gr 8 1, Src.opd 8 (.i 26)] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk (.cmovcc 2) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 18446744073709551615 8), gr 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 1 (some 0) none 1 18446744073709551551,
  Op.add 64 7 (.i 1),
  Op.lea 32 2 (some 0) none 1 32,
  Op.cmp 8 1 (.i 26),
  Op.cmov32 2 0 2,
  Op.st 8 (some 7) none 1 18446744073709551615 0]

theorem b1 (prof : Profile) : Blk prof p1 0 19 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.cmp8 (.i 26)) (by decide) <|
  .cons (p1_13 _) (OpI.cmov32) (by decide) <|
  .cons (p1_16 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 19

/-- The stretch at `35`. -/
def p2 : List Byte := [
  0x0f, 0xb6, 0x07, 0x84, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 8)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ldzx 8 0 (some 7) none 1 0,
  Op.test 8 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x75, 0xe6]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551590] 2) := by dec_rfl

end FV7z.Lwa
