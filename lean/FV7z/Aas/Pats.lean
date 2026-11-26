import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `AString::operator= (const AString &)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Aas
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x53, 0x48, 0x83, 0xec,
  0x08, 0x48, 0x39, 0xfe]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.cmp 64 6 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.cmp (.r 7) (.inr rfl)) (by decide) <|
  .nil 20

def j0 : List Byte := [0x74, 0x31]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p1 : List Byte := [
  0x44, 0x8b, 0x6e, 0x08, 0x48, 0x89, 0xf5, 0x44, 0x39, 0x6f, 0x0c]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 13, .mem (mg (some 6) none 1 8 32)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .cmp 32 [.mem (mg (some 7) none 1 12 32), gr 32 13] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 13 (some 6) none 1 8,
  Op.mov 64 5 (.r 6),
  Op.cmpmr 32 (some 7) none 1 12 13]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x72, 0x35]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 2) 64 [.rel 53] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x1f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 3 (some 7) none 1 0]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `38`. -/
def p3 : List Byte := [
  0x45, 0x89, 0x6c, 0x24, 0x08, 0x48, 0x8b, 0x45, 0x00, 0x31, 0xd2, 0x0f, 0x1f, 0x80, 0x00, 0x00,
  0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 8 32), gr 32 13] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 12) none 1 8 13,
  Op.ld 64 0 (some 5) none 1 0,
  Op.xor 32 2 (.r 2),
  Op.nop]

theorem b3 (prof : Profile) : Blk prof p3 0 18 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.nop) (by decide) <|
  .nil 18

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x0f, 0xb6, 0x0c, 0x10, 0x88, 0x0c, 0x13, 0x48, 0x83, 0xc2, 0x01, 0x84, 0xc9]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 0) (some 2) 1 0 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 8 [.mem (mg (some 3) (some 2) 1 0 8), gr 8 1] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 1 (some 0) (some 2) 1 0,
  Op.st 8 (some 3) (some 2) 1 0 1,
  Op.add 64 2 (.i 1),
  Op.test 8 1 (.r 1)]

theorem b4 (prof : Profile) : Blk prof p4 0 13 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 13

def j2 : List Byte := [0x75, 0xf1]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551601] 2) := by dec_rfl

/-- The stretch at `71`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b5 (prof : Profile) : Blk prof p5 0 13 o5 :=
  .cons (p5_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.pop) (by decide) <|
  .cons (p5_8 _) (OpI.pop) (by decide) <|
  .cons (p5_9 _) (OpI.pop) (by decide) <|
  .cons (p5_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `88`. -/
def p6 : List Byte := [
  0x44, 0x89, 0xef, 0x48, 0x83, 0xc7, 0x01]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 7 (.r 13),
  Op.add 64 7 (.i 1)]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `100`. -/
def p7 : List Byte := [
  0x49, 0x8b, 0x3c, 0x24, 0x48, 0x89, 0xc3, 0x48, 0x85, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 7 (some 12) none 1 0,
  Op.mov 64 3 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j3 : List Byte := [0x74, 0x05]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `117`. -/
def p8 : List Byte := [
  0x49, 0x89, 0x1c, 0x24, 0x45, 0x89, 0x6c, 0x24, 0x0c]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 0 64), gr 64 3] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 12 32), gr 32 13] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 64 (some 12) none 1 0 3,
  Op.st 32 (some 12) none 1 12 13]

theorem b8 (prof : Profile) : Blk prof p8 0 9 o8 :=
  .cons (p8_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 9

def j4 : List Byte := [0xeb, 0xa6]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551526] 2) := by dec_rfl

end FV7z.Aas
