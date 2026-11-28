import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArcInfoEx::FindExtension` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fex
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x47, 0x30, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 48 32)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ld 32 0 (some 7) none 1 48,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x4f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 79] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x41, 0x54, 0x49, 0x89, 0xf4, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x31, 0xdb]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.xor 32 3 (.r 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.push) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.push) (by decide) <|
  .cons (p1_10 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0xeb, 0x0f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x83, 0xc3, 0x01, 0x39, 0x5d, 0x30]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .cmp 32 [.mem (mg (some 5) none 1 48 32), gr 32 3] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 32 3 (.i 1),
  Op.cmpmr 32 (some 5) none 1 48 3]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x76, 0x28]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x55, 0x28, 0x89, 0xd8, 0x49, 0x8b, 0x3c, 0x24, 0x48, 0x8b, 0x04, 0xc2, 0x48, 0x8b,
  0x30]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 5) none 1 40 64)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 2 (some 5) none 1 40,
  Op.mov 32 0 (.r 3),
  Op.ld 64 7 (some 12) none 1 0,
  Op.ld 64 0 (some 2) (some 0) 8 0,
  Op.ld 64 6 (some 0) none 1 0]

theorem b3 (prof : Profile) : Blk prof p3 0 17 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 17

/-- The stretch at `62`. -/
def p4 : List Byte := [
  0x84, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 8 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0xde]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551582] 2) := by dec_rfl

/-- The stretch at `66`. -/
def p5 : List Byte := [
  0x89, 0xd8, 0x5b, 0x5d, 0x41, 0x5c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 0 (.r 3),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.pop) (by decide) <|
  .cons (p5_3 _) (OpI.pop) (by decide) <|
  .cons (p5_4 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x5b, 0xb8, 0xff, 0xff, 0xff, 0xff, 0x5d, 0x41, 0x5c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_1 : ∀ feat, Dec feat p6 1 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.pop 3,
  Op.mov 32 0 (.i 4294967295),
  Op.pop 5,
  Op.pop 12]

theorem b6 (prof : Profile) : Blk prof p6 0 9 o6 :=
  .cons (p6_0 _) (OpI.pop) (by decide) <|
  .cons (p6_1 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.pop) (by decide) <|
  .cons (p6_7 _) (OpI.pop) (by decide) <|
  .nil 9

/-- The stretch at `90`. -/
def p7 : List Byte := [
  0xb8, 0xff, 0xff, 0xff, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 32 0 (.i 4294967295)]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Fex
