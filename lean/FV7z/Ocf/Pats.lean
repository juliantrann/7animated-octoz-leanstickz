import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `COpenCallbackConsole::Open_Finished` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ocf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0x7f, 0x40, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 64 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 64 (some 7) none 1 64 0]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi64) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x25]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x80, 0x7f, 0x48, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 72 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmi 8 (some 7) none 1 72 0]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x75, 0x1f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xec, 0x08, 0x48, 0x83, 0xc7, 0x08, 0xbe, 0x01, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 64 4 (.i 8),
  Op.add 64 7 (.i 8),
  Op.mov 32 6 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 13 o2 :=
  .cons (p2_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `35`. -/
def p3 : List Byte := [
  0x31, 0xc0, 0x48, 0x83, 0xc4, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.add 64 4 (.i 8)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `48`. -/
def p4 : List Byte := [
  0x31, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Ocf
