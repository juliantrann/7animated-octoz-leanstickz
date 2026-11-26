import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `LzmaDec_AllocateProbs2` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lap
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x54, 0x49, 0x89, 0xcc, 0x8d, 0x0c, 0x32, 0x55, 0xbd, 0x00, 0x03, 0x00, 0x00, 0xd3, 0xe5,
  0x53, 0x48, 0x89, 0xfb, 0x81, 0xc5, 0xc0, 0x07, 0x00, 0x00, 0x48, 0x83, 0x7f, 0x08, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 2) (some 6) 1 0 0)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 768)] 5) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .shl 32 [gr 32 5, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .add 32 [gr 32 5, Src.opd 32 (.i 1984)] 6) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 8 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 12,
  Op.mov 64 12 (.r 1),
  Op.lea 32 1 (some 2) (some 6) 1 0,
  Op.push 5,
  Op.mov 32 5 (.i 768),
  Op.shl 5 (.r 1),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.add 32 5 (.i 1984),
  Op.cmpmi 64 (some 7) none 1 8 0]

theorem b0 (prof : Profile) : Blk prof p0 0 31 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_2 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.mov (.i 768) (.inl rfl)) (by decide) <|
  .cons (p0_14 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p0_16 _) (OpI.push) (by decide) <|
  .cons (p0_17 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.add (.i 1984) (.inl rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.cmpmi64) (by decide) <|
  .nil 31

def j0 : List Byte := [0x74, 0x07]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p1 : List Byte := [
  0x31, 0xc0, 0x3b, 0x6f, 0x60]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .cmp 32 [gr 32 5, .mem (mg (some 7) none 1 96 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.cmpm 32 5 (some 7) none 1 96]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.cmpm (.inl rfl)) (by decide) <|
  .nil 5

def j1 : List Byte := [0x74, 0x2f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xe6, 0x48, 0x89, 0xdf]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `51`. -/
def p3 : List Byte := [
  0x89, 0xee, 0x4c, 0x89, 0xe7, 0x48, 0x01, 0xf6]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 6 (.r 5),
  Op.mov 64 7 (.r 12),
  Op.add 64 6 (.r 6)]

theorem b3 (prof : Profile) : Blk prof p3 0 8 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.add (.r 6) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `63`. -/
def p4 : List Byte := [
  0x48, 0x89, 0x43, 0x08, 0x48, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 64 (some 3) none 1 8 0,
  Op.test 64 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_4 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x18]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `72`. -/
def p5 : List Byte := [
  0x89, 0x6b, 0x60, 0x48, 0x05, 0x00, 0x0d, 0x00, 0x00, 0x48, 0x89, 0x43, 0x10, 0x31, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 96 32), gr 32 5] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 3328)] 6) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 16 64), gr 64 0] 4) := by dec_rfl
theorem p5_13 : ∀ feat, Dec feat p5 13 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 32 (some 3) none 1 96 5,
  Op.add 64 0 (.i 3328),
  Op.st 64 (some 3) none 1 16 0,
  Op.xor 32 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 15 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_3 _) (OpI.add (.i 3328) (.inr rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_13 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 15

/-- The stretch at `87`. -/
def p6 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_1 : ∀ feat, Dec feat p6 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_2 : ∀ feat, Dec feat p6 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b6 (prof : Profile) : Blk prof p6 0 4 o6 :=
  .cons (p6_0 _) (OpI.pop) (by decide) <|
  .cons (p6_1 _) (OpI.pop) (by decide) <|
  .cons (p6_2 _) (OpI.pop) (by decide) <|
  .nil 4

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0xb8, 0x02, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 32 0 (.i 2)]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 5

def j3 : List Byte := [0xeb, 0xf0]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551600] 2) := by dec_rfl

end FV7z.Lap
