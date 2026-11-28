import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__mbsrtowcs` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mbr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x05, 0x85, 0x72, 0x14, 0x00, 0x48, 0x85, 0xc9, 0x48, 0x0f,
  0x44, 0xc8, 0x48, 0xc7, 0xc0, 0x80, 0xff, 0xff, 0xff, 0x64, 0x4c, 0x8b, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1340037 0)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .test 64 [gr 64 1, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk (.cmovcc 4) 64 [gr 64 1, gr 64 0] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551488)] 7) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [gr 64 8, .mem (mf (some 0) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 8013232),
  Op.test 64 1 (.r 1),
  Op.cmov64 4 1 0,
  Op.mov 64 0 (.i 18446744073709551488),
  Op.ldf fb 64 8 (some 0) none 1 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x65d320 : Addr) fb 0 29 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) ((OpIA.lea_rip (by decide)).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.test (.r 1) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.cmov64).at _).fs _) (by decide) <|
  .cons (p0_18 _) (((OpI.mov (.i 18446744073709551488) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_25 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .nil 29

end FV7z.Mbr
