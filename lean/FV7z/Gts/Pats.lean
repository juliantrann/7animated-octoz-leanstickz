import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_dl_get_tls_static_info` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gts
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x05, 0xe5, 0x3b, 0x12, 0x00, 0x48, 0x89, 0x07, 0x48, 0x8b,
  0x05, 0xfb, 0x97, 0x13, 0x00, 0x48, 0x89, 0x06]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1194981 64)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1284091 64)] 7) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lda 64 0 7938736,
  Op.st 64 (some 7) none 1 0 0,
  Op.lda 64 0 8027856,
  Op.st 64 (some 6) none 1 0 0]

theorem b0 (prof : Profile) : BlkA prof p0 (0x66e6c0 : Addr) 0 24 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_11 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p0_14 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_21 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 24

end FV7z.Gts
