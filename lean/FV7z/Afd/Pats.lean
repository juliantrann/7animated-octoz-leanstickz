import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::Find` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Afd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x8b, 0x1f, 0x89, 0xd7, 0x48, 0x01, 0xdf]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.ld 64 3 (some 7) none 1 0,
  Op.mov 32 7 (.r 2),
  Op.add 64 7 (.r 3)]

theorem b0 (prof : Profile) : Blk prof p0 0 13 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .nil 13

/-- The stretch at `18`. -/
def p1 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j0 : List Byte := [0x74, 0x04]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `23`. -/
def p2 : List Byte := [
  0x29, 0xd8, 0x5b]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 32 0 (.r 3),
  Op.pop 3]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.sub (.r 3) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.pop) (by decide) <|
  .nil 3

/-- The stretch at `27`. -/
def p3 : List Byte := [
  0xb8, 0xff, 0xff, 0xff, 0xff, 0x5b]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.i 4294967295),
  Op.pop 3]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.pop) (by decide) <|
  .nil 6

end FV7z.Afd
