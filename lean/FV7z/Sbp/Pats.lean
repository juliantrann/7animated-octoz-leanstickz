import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `z7_SwapBytesPrepare` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 4 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sbp
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
  0x41, 0x89, 0xc0, 0xb8, 0x03, 0x00, 0x00, 0x00, 0x45, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 3)] 5) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 8 (.r 0),
  Op.mov 32 0 (.i 3),
  Op.test 32 8 (.r 8)]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x74, 0x0e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `26`. -/
def p2 : List Byte := [
  0x89, 0x05, 0xc8, 0x93, 0x35, 0x00, 0x48, 0x83, 0xc4, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mrip 3511240 32), gr 32 0] 6) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sta 32 7956408 0,
  Op.add 64 4 (.i 8)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x43d3ea : Addr) 0 10 o2 :=
  .cons (p2_0 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p2_6 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 10

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x85, 0xc0, 0x0f, 0x95, 0xc0, 0x0f, 0xb6, 0xc0, 0x83, 0xc0, 0x01, 0x89, 0x05, 0xaa, 0x93, 0x35,
  0x00, 0x48, 0x83, 0xc4, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk (.setcc 5) 8 [gr 8 0] 3) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .movzx 32 [gr 32 0, gr 8 0] 3) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .mov 32 [.mem (mrip 3511210 32), gr 32 0] 6) := by dec_rfl
theorem p3_17 : ∀ feat, Dec feat p3 17 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 32 0 (.r 0),
  Op.setcc 5 0,
  Op.zxr 0 0,
  Op.add 32 0 (.i 1),
  Op.sta 32 7956408 0,
  Op.add 64 4 (.i 8)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x43d3fd : Addr) 0 21 o3 :=
  .cons (p3_0 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p3_2 _) ((OpI.setcc).at _) (by decide) <|
  .cons (p3_5 _) ((OpI.zxr).at _) (by decide) <|
  .cons (p3_8 _) ((OpI.add (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p3_11 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p3_17 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .nil 21

end FV7z.Sbp
