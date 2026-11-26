import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `VariantClear` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Vcl
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x66, 0x83, 0x3f, 0x08, 0x48, 0x89, 0xfb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .cmp 16 [.mem (mg (some 7) none 1 0 16), .imm 16 8] 4) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 3,
  Op.cmpmi 16 (some 7) none 1 0 8,
  Op.mov 64 3 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 12 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.cmpmi16) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 12

def j0 : List Byte := [0x74, 0x12]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `14`. -/
def p1 : List Byte := [
  0x31, 0xc0, 0x66, 0x89, 0x03, 0x31, 0xc0, 0x5b]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 16 [.mem (mg (some 3) none 1 0 16), gr 16 0] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.st 16 (some 3) none 1 0 0,
  Op.xor 32 0 (.r 0),
  Op.pop 3]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p1_5 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.pop) (by decide) <|
  .nil 8

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x7f, 0x08]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 7) none 1 8]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Vcl
