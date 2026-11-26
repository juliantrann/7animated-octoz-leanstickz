import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `SysAllocStringLen` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sas
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x89, 0xf3, 0x81, 0xfb, 0xfc, 0xff, 0xff, 0x3f]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .cmp 32 [gr 32 3, Src.opd 32 (.i 1073741820)] 6) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 32 3 (.r 6),
  Op.cmp 32 3 (.i 1073741820)]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.cmp (.i 1073741820) (.inl rfl)) (by decide) <|
  .nil 16

def j0 : List Byte := [0x77, 0x4e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 78] 2) := by dec_rfl

/-- The stretch at `18`. -/
def p1 : List Byte := [
  0x44, 0x8d, 0x24, 0x9d, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xfd, 0x41, 0x8d, 0x7c, 0x24, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 12, .mem (mg none (some 3) 4 0 0)] 8) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .lea 32 [gr 32 7, .mem (mg (some 12) none 1 8 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 12 none (some 3) 4 0,
  Op.mov 64 5 (.r 7),
  Op.lea 32 7 (some 12) none 1 8]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_11 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 16

/-- The stretch at `39`. -/
def p2 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x74, 0x34]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 52] 2) := by dec_rfl

/-- The stretch at `44`. -/
def p3 : List Byte := [
  0x44, 0x89, 0x20, 0x4c, 0x8d, 0x40, 0x04, 0x48, 0x85, 0xed]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), gr 32 12] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 0) none 1 4 0)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 0) none 1 0 12,
  Op.lea 64 8 (some 0) none 1 4,
  Op.test 64 5 (.r 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x74, 0x11]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x4c, 0x89, 0xc7, 0x44, 0x89, 0xe2, 0x48, 0x89, 0xee]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.r 8),
  Op.mov 32 2 (.r 12),
  Op.mov 64 6 (.r 5)]

theorem b4 (prof : Profile) : Blk prof p4 0 9 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `70`. -/
def p5 : List Byte := [
  0x49, 0x89, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 8 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `73`. -/
def p6 : List Byte := [
  0x41, 0xc7, 0x04, 0x98, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xc0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [.mem (mg (some 8) (some 3) 4 0 32), .imm 32 0] 8) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_13 : ∀ feat, Dec feat p6 13 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.sti 32 (some 8) (some 3) 4 0 0,
  Op.mov 64 0 (.r 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b6 (prof : Profile) : Blk prof p6 0 15 o6 :=
  .cons (p6_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_8 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p6_11 _) (OpI.pop) (by decide) <|
  .cons (p6_12 _) (OpI.pop) (by decide) <|
  .cons (p6_13 _) (OpI.pop) (by decide) <|
  .nil 15

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x45, 0x31, 0xc0, 0x5b, 0x5d, 0x4c, 0x89, 0xc0, 0x41, 0x5c]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 8 (.r 8),
  Op.pop 3,
  Op.pop 5,
  Op.mov 64 0 (.r 8),
  Op.pop 12]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.xor (.r 8) (.inl rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.pop) (by decide) <|
  .cons (p7_4 _) (OpI.pop) (by decide) <|
  .cons (p7_5 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p7_8 _) (OpI.pop) (by decide) <|
  .nil 10

end FV7z.Sas
