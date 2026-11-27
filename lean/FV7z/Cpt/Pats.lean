import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWildcard::CCensorNode::CheckPathCurrent` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cpt
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x4c, 0x8d, 0x6f, 0x28, 0x48, 0x83, 0xc7, 0x38, 0x41, 0x54,
  0x55, 0x48, 0x89, 0xd5, 0x53, 0x0f, 0xb6, 0xd9, 0x48, 0x83, 0xec, 0x08, 0x40, 0x84, 0xf6, 0x4c,
  0x0f, 0x44, 0xef, 0x45, 0x31, 0xe4, 0x41, 0x8b, 0x45, 0x08, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 7) none 1 40 0)] 4) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .movzx 32 [gr 32 3, gr 8 1] 3) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .test 8 [gr 8 6, Src.opd 8 (.r 6)] 3) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk (.cmovcc 4) 64 [gr 64 13, gr 64 7] 4) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p0_38 : ∀ feat, Dec feat p0 38 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 13) none 1 8 32)] 4) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.lea 64 13 (some 7) none 1 40,
  Op.add 64 7 (.i 56),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 2),
  Op.push 3,
  Op.zxr 3 1,
  Op.sub 64 4 (.i 8),
  Op.test 8 6 (.r 6),
  Op.cmov64 4 13 7,
  Op.xor 32 12 (.r 12),
  Op.ld 32 0 (some 13) none 1 8,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 44 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.push) (by decide) <|
  .cons (p0_17 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.push) (by decide) <|
  .cons (p0_21 _) (OpI.zxr) (by decide) <|
  .cons (p0_24 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_28 _) (OpI.test8 (.r 6)) (by decide) <|
  .cons (p0_31 _) (OpI.cmov64) (by decide) <|
  .cons (p0_35 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p0_38 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_42 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 44

def j0 : List Byte := [0x75, 0x0c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 12] 2) := by dec_rfl

def j1 : List Byte := [0xeb, 0x30]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 48] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p1 : List Byte := [
  0x41, 0x83, 0xc4, 0x01, 0x45, 0x39, 0x65, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 32 [gr 32 12, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .cmp 32 [.mem (mg (some 13) none 1 8 32), gr 32 12] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 32 12 (.i 1),
  Op.cmpmr 32 (some 13) none 1 8 12]

theorem b1 (prof : Profile) : Blk prof p1 0 8 o1 :=
  .cons (p1_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 8

def j2 : List Byte := [0x76, 0x26]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 38] 2) := by dec_rfl

/-- The stretch at `58`. -/
def p2 : List Byte := [
  0x49, 0x8b, 0x55, 0x00, 0x44, 0x89, 0xe0, 0x48, 0x89, 0xee, 0x48, 0x8b, 0x3c, 0xc2, 0x89, 0xda]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 13) none 1 0 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 2) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 2 (some 13) none 1 0,
  Op.mov 32 0 (.r 12),
  Op.mov 64 6 (.r 5),
  Op.ld 64 7 (some 2) (some 0) 8 0,
  Op.mov 32 2 (.r 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 16 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .nil 16

/-- The stretch at `79`. -/
def p3 : List Byte := [
  0x84, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 8 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0xdd]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551581] 2) := by dec_rfl

/-- The stretch at `83`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.pop) (by decide) <|
  .cons (p4_5 _) (OpI.pop) (by decide) <|
  .cons (p4_6 _) (OpI.pop) (by decide) <|
  .cons (p4_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `96`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x31, 0xc0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 4 (.i 8),
  Op.xor 32 0 (.r 0),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.pop) (by decide) <|
  .cons (p5_7 _) (OpI.pop) (by decide) <|
  .cons (p5_8 _) (OpI.pop) (by decide) <|
  .cons (p5_10 _) (OpI.pop) (by decide) <|
  .nil 12

end FV7z.Cpt
