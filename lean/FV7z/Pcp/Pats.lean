import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_pthread_cleanup_push` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pcp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0x37, 0x48, 0x89, 0x57, 0x08, 0x64, 0x48, 0x8b, 0x04, 0x25,
  0xf8, 0x02, 0x00, 0x00, 0x48, 0x89, 0x47, 0x18, 0x64, 0x48, 0x89, 0x3c, 0x25, 0xf8, 0x02, 0x00,
  0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 6] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 8 64), gr 64 2] 4) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 760 64)] 9) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 24 64), gr 64 0] 4) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 64 [.mem (mf none none 1 760 64), gr 64 7] 9) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.st 64 (some 7) none 1 0 6,
  Op.st 64 (some 7) none 1 8 2,
  Op.ldf fb 64 0 none none 1 760,
  Op.st 64 (some 7) none 1 24 0,
  Op.stf fb 64 none none 1 760 7]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5fefe0 : Addr) fb 0 33 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_7 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_11 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_24 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .nil 33

end FV7z.Pcp
