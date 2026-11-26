import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps23
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `DoesNameContainWildcard` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dnw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x08, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x36]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 54] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x17, 0x83, 0xe8, 0x01, 0x48, 0x8d, 0x74, 0x82, 0x04]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 2) (some 0) 4 4 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 7) none 1 0,
  Op.sub 32 0 (.i 1),
  Op.lea 64 6 (some 2) (some 0) 4 4]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0xeb, 0x11]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc2, 0x04, 0x48, 0x39, 0xf2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 2 (.i 4),
  Op.cmp 64 2 (.r 6)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x17]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0x8b, 0x0a, 0x83, 0xf9, 0x2a, 0x0f, 0x94, 0xc0, 0x83, 0xf9, 0x3f, 0x0f, 0x94, 0xc1, 0x08, 0xc8]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 2) none 1 0 32)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 42)] 3) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk (.setcc 4) 8 [gr 8 1] 3) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .or 8 [gr 8 0, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 32 1 (some 2) none 1 0,
  Op.cmp 32 1 (.i 42),
  Op.setcc 4 0,
  Op.cmp 32 1 (.i 63),
  Op.setcc 4 1,
  Op.or8 0 (.r 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 16 o3 :=
  .cons (p3_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.cmp (.i 42) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.setcc) (by decide) <|
  .cons (p3_8 _) (OpI.cmp (.i 63) (.inl rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.setcc) (by decide) <|
  .cons (p3_14 _) (OpI.or8 (.r 1)) (by decide) <|
  .nil 16

def j3 : List Byte := [0x74, 0xe5]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551589] 2) := by dec_rfl

/-- The stretch at `65`. -/
def p4 : List Byte := [
  0x31, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Dnw
