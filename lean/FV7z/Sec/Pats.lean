import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_init_secure` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 1 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sec
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x05, 0x1a, 0x7f, 0x13, 0x00, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1277722 32)] 6) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lda 32 0 8029636,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x6706a0 : Addr) 0 12 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p0_10 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 12

def j0 : List Byte := [0x74, 0x02]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 2] 2) := by dec_rfl

end FV7z.Sec
