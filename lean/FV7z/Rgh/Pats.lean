import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `RegisterHasher` (PLAN.md §M, constructors)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rgh
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc2, 0xe0, 0xc8, 0x79, 0x00, 0x8b, 0x02, 0x83, 0xf8, 0x1f]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 7981280)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 2) none 1 0 32)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 31)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 2 (.i 7981280),
  Op.ld 32 0 (some 2) none 1 0,
  Op.cmp 32 0 (.i 31)]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7981280) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.cmp (.i 31) (.inl rfl)) (by decide) <|
  .nil 16

def j0 : List Byte := [0x77, 0x10]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `18`. -/
def p1 : List Byte := [
  0x8d, 0x48, 0x01, 0x89, 0x0a, 0x48, 0xc7, 0xc2, 0xe0, 0xc7, 0x79, 0x00, 0x48, 0x89, 0x3c, 0xc2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 0) none 1 1 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 0 32), gr 32 1] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 7981024)] 7) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 0) 8 0 64), gr 64 7] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 1 (some 0) none 1 1,
  Op.st 32 (some 2) none 1 0 1,
  Op.mov 64 2 (.i 7981024),
  Op.st 64 (some 2) (some 0) 8 0 7]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_5 _) (OpI.mov (.i 7981024) (.inr rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 16

end FV7z.Rgh
