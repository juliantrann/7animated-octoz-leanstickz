import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__sigjmp_save` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sjs
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xfb, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.test 32 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x75, 0x0c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `12`. -/
def p1 : List Byte := [
  0x89, 0x73, 0x40, 0x31, 0xc0, 0x5b]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 64 32), gr 32 6] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.st 32 (some 3) none 1 64 6,
  Op.xor 32 0 (.r 0),
  Op.pop 3]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p1_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Sjs
