import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `exit` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Exi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x50, 0x58, 0xb9, 0x01, 0x00, 0x00, 0x00, 0xba, 0x01, 0x00, 0x00, 0x00,
  0x48, 0x8d, 0x35, 0x89, 0xef, 0x16, 0x00, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 0] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .pop 64 [gr 64 0] 1) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1503113 0)] 7) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 0,
  Op.pop 0,
  Op.mov 32 1 (.i 1),
  Op.mov 32 2 (.i 1),
  Op.mov 64 6 (.i 7938992),
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x623410 : Addr) 0 27 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_5 _) ((OpI.pop).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p0_11 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p0_16 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_23 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 27

end FV7z.Exi
