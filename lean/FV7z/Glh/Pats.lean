import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps18
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `GetLastError_noZero_HRESULT()` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Glh
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 8 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j0 : List Byte := [0x74, 0x17]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p2 : List Byte := [
  0x0f, 0xb7, 0xd0, 0x81, 0xca, 0x00, 0x00, 0x00, 0x88, 0x85, 0xc0, 0x0f, 0x4f, 0xc2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 2, gr 16 0] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .or 32 [gr 32 2, Src.opd 32 (.i 2281701376)] 6) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk (.cmovcc 15) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.zxr16 2 0,
  Op.or 32 2 (.i 2281701376),
  Op.test 32 0 (.r 0),
  Op.cmov32 15 0 2]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.zxr16) (by decide) <|
  .cons (p2_3 _) (OpI.or (.i 2281701376) (.inl rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.cmov32) (by decide) <|
  .nil 14

/-- The stretch at `31`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `40`. -/
def p4 : List Byte := [
  0xb8, 0x05, 0x40, 0x00, 0x80]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147500037)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 0 (.i 2147500037)]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.mov (.i 2147500037) (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0xeb, 0xf0]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 18446744073709551600] 2) := by dec_rfl

end FV7z.Glh
