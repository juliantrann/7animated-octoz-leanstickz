import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `frame_dummy` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fdm
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xb8, 0xe0, 0x27, 0x61, 0x00, 0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 6367200)] 5) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 32 0 (.i 6367200),
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 12 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 6367200) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 12

def j0 : List Byte := [0x74, 0x22]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `14`. -/
def p1 : List Byte := [
  0x55, 0xbe, 0x20, 0x46, 0x79, 0x00, 0xbf, 0x60, 0xbb, 0x70, 0x00, 0x48, 0x89, 0xe5]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 7947808)] 5) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 7388000)] 5) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 5,
  Op.mov 32 6 (.i 7947808),
  Op.mov 32 7 (.i 7388000),
  Op.mov 64 5 (.r 4)]

theorem b1 (prof : Profile) : Blk prof p1 0 14 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_1 _) (OpI.mov (.i 7947808) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.i 7388000) (.inl rfl)) (by decide) <|
  .cons (p1_11 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .nil 14

/-- The stretch at `33`. -/
def p2 : List Byte := [
  0x5d]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.pop 5]

theorem b2 (prof : Profile) : Blk prof p2 0 1 o2 :=
  .cons (p2_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.Fdm
