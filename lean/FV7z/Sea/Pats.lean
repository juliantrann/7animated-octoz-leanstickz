import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `StringsAreEqual_Ascii` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sea
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x0f, 0xb6, 0x06, 0x89, 0xc2, 0x3b, 0x07]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .cmp 32 [gr 32 0, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ldzx 8 0 (some 6) none 1 0,
  Op.mov 32 2 (.r 0),
  Op.cmpm 32 0 (some 7) none 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x75, 0x2b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x31, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0xeb, 0x17]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `24`. -/
def p2 : List Byte := [
  0x0f, 0xb6, 0x4c, 0x06, 0x01, 0x48, 0x83, 0xc0, 0x01, 0x89, 0xca, 0x3b, 0x0c, 0x87]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 6) (some 0) 1 1 8)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .cmp 32 [gr 32 1, .mem (mg (some 7) (some 0) 4 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ldzx 8 1 (some 6) (some 0) 1 1,
  Op.add 64 0 (.i 1),
  Op.mov 32 2 (.r 1),
  Op.cmpm 32 1 (some 7) (some 0) 4 0]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x75, 0x10]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x84, 0xd2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 8 2 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x75, 0xec]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551596] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p4 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 0 (.i 1)]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Sea
