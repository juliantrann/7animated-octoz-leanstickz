import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `deregister_tm_clones` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dtc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xb8, 0x10, 0x3d, 0x79, 0x00, 0x48, 0x3d, 0x10, 0x3d, 0x79, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 7945488)] 5) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 7945488)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.mov 32 0 (.i 7945488),
  Op.cmp 64 0 (.i 7945488)]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.mov (.i 7945488) (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.cmp (.i 7945488) (.inr rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x74, 0x13]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0xb8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 0)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.i 0),
  Op.test 64 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 0) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x74, 0x09]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `23`. -/
def p2 : List Byte := [
  0xbf, 0x10, 0x3d, 0x79, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 7945488)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 7 (.i 7945488)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 7945488) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Dtc
