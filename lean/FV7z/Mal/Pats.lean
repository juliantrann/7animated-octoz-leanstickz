import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_malloc` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mal
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x48, 0x8b, 0x05, 0xc3, 0xf8, 0x15, 0x00, 0x55, 0x48, 0x89,
  0xfd, 0x53, 0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1439939 64)] 7) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.lda 64 0 7940656,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x633160 : Addr) 0 21 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_14 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_17 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_18 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 21

def j0 : List Byte := [0x0f, 0x85, 0x55, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 341] 6) := by dec_rfl

/-- The stretch at `368`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x18, 0x5b, 0x5d, 0x41, 0x5c]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 6 (some 4) none 1 24,
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.pop) (by decide) <|
  .cons (p1_6 _) (OpI.pop) (by decide) <|
  .cons (p1_7 _) (OpI.pop) (by decide) <|
  .nil 9

end FV7z.Mal
