import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `register_tm_clones` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rtc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xbe, 0x10, 0x3d, 0x79, 0x00, 0x48, 0x81, 0xee, 0x10, 0x3d, 0x79, 0x00, 0x48, 0x89, 0xf0, 0x48,
  0xc1, 0xee, 0x3f, 0x48, 0xc1, 0xf8, 0x03, 0x48, 0x01, 0xc6, 0x48, 0xd1, 0xfe]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 7945488)] 5) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .sub 64 [gr 64 6, Src.opd 64 (.i 7945488)] 7) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .shr 64 [gr 64 6, Src.opd 8 (.i 63)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .sar 64 [gr 64 0, Src.opd 8 (.i 3)] 4) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .sar 64 [gr 64 6, Src.opd 8 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.mov 32 6 (.i 7945488),
  Op.sub 64 6 (.i 7945488),
  Op.mov 64 0 (.r 6),
  Op.shr64 6 (.i 63),
  Op.sar64 0 (.i 3),
  Op.add 64 6 (.r 0),
  Op.sar64 6 (.i 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 29 o0 :=
  .cons (p0_0 _) (OpI.mov (.i 7945488) (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.sub (.i 7945488) (.inr rfl)) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.shr64 (.i 63)) (by decide) <|
  .cons (p0_19 _) (OpI.sar64 (.i 3)) (by decide) <|
  .cons (p0_23 _) (OpI.add (.r 0) (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.sar64 (.i 1)) (by decide) <|
  .nil 29

def j0 : List Byte := [0x74, 0x11]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `31`. -/
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

def j1 : List Byte := [0x74, 0x07]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p2 : List Byte := [
  0xbf, 0x10, 0x3d, 0x79, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 7945488)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 7 (.i 7945488)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 7945488) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Rtc
