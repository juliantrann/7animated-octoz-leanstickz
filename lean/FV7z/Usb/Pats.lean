import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::SetFromBstr` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Usb
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x49, 0x89, 0xf4, 0x55, 0x48, 0x89, 0xfd, 0x48,
  0x89, 0xf7, 0x53, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.mov 64 12 (.r 6),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.mov 64 7 (.r 6),
  Op.push 3,
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 23 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.push) (by decide) <|
  .cons (p0_19 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 23

/-- The stretch at `28`. -/
def p1 : List Byte := [
  0x89, 0xc3, 0x39, 0x45, 0x0c]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .cmp 32 [.mem (mg (some 5) none 1 12 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 3 (.r 0),
  Op.cmpmr 32 (some 5) none 1 12 0]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x72, 0x25]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 2) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p2 : List Byte := [
  0x4c, 0x8b, 0x6d, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 13 (some 5) none 1 0]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `39`. -/
def p3 : List Byte := [
  0x89, 0x5d, 0x08, 0x48, 0x83, 0xc4, 0x08, 0x8d, 0x53, 0x01, 0x4c, 0x89, 0xe6, 0x5b, 0x4c, 0x89,
  0xef, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 3] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 3) none 1 1 0)] 3) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p3_17 : ∀ feat, Dec feat p3 17 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_18 : ∀ feat, Dec feat p3 18 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p3_20 : ∀ feat, Dec feat p3 20 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 5) none 1 8 3,
  Op.add 64 4 (.i 8),
  Op.lea 32 2 (some 3) none 1 1,
  Op.mov 64 6 (.r 12),
  Op.pop 3,
  Op.mov 64 7 (.r 13),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b3 (prof : Profile) : Blk prof p3 0 22 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_3 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p3_10 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_13 _) (OpI.pop) (by decide) <|
  .cons (p3_14 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p3_17 _) (OpI.pop) (by decide) <|
  .cons (p3_18 _) (OpI.pop) (by decide) <|
  .cons (p3_20 _) (OpI.pop) (by decide) <|
  .nil 22

/-- The stretch at `72`. -/
def p4 : List Byte := [
  0x89, 0xc0, 0x48, 0x8d, 0x3c, 0x85, 0x04, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_2 : ∀ feat, Dec feat p4 2 (FV7z.mk .lea 64 [gr 64 7, .mem (mg none (some 0) 4 4 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 32 0 (.r 0),
  Op.lea 64 7 none (some 0) 4 4]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `87`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x7d, 0x00, 0x49, 0x89, 0xc5, 0x48, 0x85, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 5) none 1 0,
  Op.mov 64 13 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x74, 0x05]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `104`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0x6d, 0x00, 0x89, 0x5d, 0x0c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 13] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 12 32), gr 32 3] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.st 64 (some 5) none 1 0 13,
  Op.st 32 (some 5) none 1 12 3]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p6_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

def j2 : List Byte := [0xeb, 0xb6]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551542] 2) := by dec_rfl

end FV7z.Usb
