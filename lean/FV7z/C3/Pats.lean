import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CrcGenerateTable` (PLAN.md G3, constructors)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C3
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc7, 0x00, 0x4e, 0x7a, 0x00, 0x31, 0xf6, 0x0f, 0x1f, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 8015360)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 7 (.i 8015360),
  Op.xor 32 6 (.r 6),
  Op.nop]

theorem b0 (prof : Profile) : Blk prof p0 0 16 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 8015360) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x89, 0xf0, 0xba, 0x08, 0x00, 0x00, 0x00, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 8)] 5) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 9) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 0 (.r 6),
  Op.mov 32 2 (.i 8),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 16 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x89, 0xc1, 0x83, 0xe0, 0x01, 0xf7, 0xd8, 0xd1, 0xe9, 0x25, 0x20, 0x83, 0xb8, 0xed, 0x31, 0xc8,
  0x83, 0xea, 0x01]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .neg 32 [gr 32 0] 2) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 3988292384)] 5) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.and 32 0 (.i 1),
  Op.neg 32 0,
  Op.shr 1 (.i 1),
  Op.and 32 0 (.i 3988292384),
  Op.xor 32 0 (.r 1),
  Op.sub 32 2 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 19 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.and (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.neg (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p2_9 _) (OpI.and (.i 3988292384) (.inl rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_16 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .nil 19

def j0 : List Byte := [0x75, 0xeb]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `53`. -/
def p3 : List Byte := [
  0x89, 0x04, 0xb7, 0x48, 0x83, 0xc6, 0x01, 0x48, 0x81, 0xfe, 0x00, 0x01, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 7) (some 6) 4 0 32), gr 32 0] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.i 256)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.st 32 (some 7) (some 6) 4 0 0,
  Op.add 64 6 (.i 1),
  Op.cmp 64 6 (.i 256)]

theorem b3 (prof : Profile) : Blk prof p3 0 14 o3 :=
  .cons (p3_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.cmp (.i 256) (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0xcb]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551563] 2) := by dec_rfl

/-- The stretch at `69`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xfa, 0x48, 0x8d, 0xb7, 0x00, 0x2c, 0x00, 0x00, 0x90]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 7) none 1 11264 0)] 7) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 2 (.r 7),
  Op.lea 64 6 (some 7) none 1 11264,
  Op.nop]

theorem b4 (prof : Profile) : Blk prof p4 0 11 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_10 _) (OpI.nop) (by decide) <|
  .nil 11

/-- The stretch at `80`. -/
def p5 : List Byte := [
  0x8b, 0x02, 0x48, 0x83, 0xc2, 0x04, 0x0f, 0xb6, 0xc8, 0xc1, 0xe8, 0x08, 0x33, 0x04, 0x8f, 0x89,
  0x82, 0xfc, 0x03, 0x00, 0x00, 0x48, 0x39, 0xd6]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 2) none 1 0 32)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .movzx 32 [gr 32 1, gr 8 0] 3) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem p5_12 : ∀ feat, Dec feat p5 12 (FV7z.mk .xor 32 [gr 32 0, .mem (mg (some 7) (some 1) 4 0 32)] 3) := by dec_rfl
theorem p5_15 : ∀ feat, Dec feat p5 15 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 1020 32), gr 32 0] 6) := by dec_rfl
theorem p5_21 : ∀ feat, Dec feat p5 21 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 32 0 (some 2) none 1 0,
  Op.add 64 2 (.i 4),
  Op.zxr 1 0,
  Op.shr 0 (.i 8),
  Op.xorm 32 0 (some 7) (some 1) 4 0,
  Op.st 32 (some 2) none 1 1020 0,
  Op.cmp 64 6 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 24 o5 :=
  .cons (p5_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.zxr) (by decide) <|
  .cons (p5_9 _) (OpI.shr (.i 8)) (by decide) <|
  .cons (p5_12 _) (OpI.xorm (.inl rfl)) (by decide) <|
  .cons (p5_15 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_21 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 24

def j2 : List Byte := [0x75, 0xe6]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551590] 2) := by dec_rfl

end FV7z.C3
