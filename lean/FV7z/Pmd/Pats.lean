import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__pthread_mutex_destroy` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pmd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x90, 0x8b, 0x47, 0x10, 0xa8, 0x10]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 16 32)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 16)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.nop,
  Op.ld 32 0 (some 7) none 1 16,
  Op.test 8 0 (.i 16)]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.nop) (by decide) <|
  .cons (p0_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.test8 (.i 16)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x75, 0x0c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `12`. -/
def p1 : List Byte := [
  0x8b, 0x57, 0x0c, 0xb8, 0x10, 0x00, 0x00, 0x00, 0x85, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 12 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 2 (some 7) none 1 12,
  Op.mov 32 0 (.i 16),
  Op.test 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x75, 0x09]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `24`. -/
def p2 : List Byte := [
  0xc7, 0x47, 0x10, 0xff, 0xff, 0xff, 0xff, 0x31, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 16 32), .imm 32 4294967295] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 32 (some 7) none 1 16 4294967295,
  Op.xor 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 9 o2 :=
  .cons (p2_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p2_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

end FV7z.Pmd
