import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_pthread_cleanup_pop` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pco
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x47, 0x18, 0x64, 0x48, 0x89, 0x04, 0x25, 0xf8, 0x02, 0x00,
  0x00, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 24 64)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [.mem (mf none none 1 760 64), gr 64 0] 9) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.ld 64 0 (some 7) none 1 24,
  Op.stf fb 64 none none 1 760 0,
  Op.test 32 6 (.r 6)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5ff010 : Addr) fb 0 19 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (((OpI.test (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 19

def j0 : List Byte := [0x74, 0x13]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `21`. -/
def p1 : List Byte := [
  0x4c, 0x8b, 0x47, 0x08, 0x48, 0x8b, 0x07, 0x4c, 0x89, 0xc7]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 8 (some 7) none 1 8,
  Op.ld 64 0 (some 7) none 1 0,
  Op.mov 64 7 (.r 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .nil 10

end FV7z.Pco
