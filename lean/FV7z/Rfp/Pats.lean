import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::ReverseFind_PathSepar` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rfp
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

def j0 : List Byte := [0x74, 0x23]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x17, 0x48, 0x8d, 0x44, 0x02, 0xff, 0x80, 0x38, 0x2f]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) (some 0) 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 47] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 7) none 1 0,
  Op.lea 64 0 (some 2) (some 0) 1 18446744073709551615,
  Op.cmpmi 8 (some 0) none 1 0 47]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x75, 0x11]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl

def j2 : List Byte := [0xeb, 0x1e]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xe8, 0x01, 0x80, 0x38, 0x2f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 47] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 64 0 (.i 1),
  Op.cmpmi 8 (some 0) none 1 0 47]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x74, 0x0f]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0x48, 0x39, 0xc2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 64 2 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x75, 0xf2]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551602] 2) := by dec_rfl

/-- The stretch at `46`. -/
def p4 : List Byte := [
  0xb8, 0xff, 0xff, 0xff, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 0 (.i 4294967295)]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `56`. -/
def p5 : List Byte := [
  0x29, 0xd0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sub 32 0 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.sub (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Rfp
