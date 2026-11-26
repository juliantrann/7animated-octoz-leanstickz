import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `__hash_string` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Hsh
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x0f, 0xb6, 0x07, 0x84, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 8)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ldzx 8 0 (some 7) none 1 0,
  Op.test 8 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x4d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 77] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x0f, 0xb6, 0x57, 0x01, 0x48, 0x8d, 0x4f, 0x01, 0x48, 0xbe, 0xff, 0xff, 0xff, 0x0f, 0xff, 0xff,
  0xff, 0xff, 0x84, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 7) none 1 1 8)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 7) none 1 1 0)] 4) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 18446744069683019775)] 10) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ldzx 8 2 (some 7) none 1 1,
  Op.lea 64 1 (some 7) none 1 1,
  Op.mov 64 6 (.i 18446744069683019775),
  Op.test 8 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 20 o1 :=
  .cons (p1_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.mov (.i 18446744069683019775) (.inr rfl)) (by decide) <|
  .cons (p1_18 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 20

def j1 : List Byte := [0x74, 0x2f]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `33`. -/
def p2 : List Byte := [
  0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.nop]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.nop) (by decide) <|
  .nil 7

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x48, 0xc1, 0xe0, 0x04, 0x48, 0x83, 0xc1, 0x01, 0x48, 0x01, 0xd0, 0x48, 0x89, 0xc2, 0x81, 0xe2,
  0x00, 0x00, 0x00, 0xf0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 4026531840)] 6) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.shl64 0 (.i 4),
  Op.add 64 1 (.i 1),
  Op.add 64 0 (.r 2),
  Op.mov 64 2 (.r 0),
  Op.and 32 2 (.i 4026531840)]

theorem b3 (prof : Profile) : Blk prof p3 0 20 o3 :=
  .cons (p3_0 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p3_4 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p3_14 _) (OpI.and (.i 4026531840) (.inl rfl)) (by decide) <|
  .nil 20

def j2 : List Byte := [0x74, 0x0a]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `62`. -/
def p4 : List Byte := [
  0x48, 0x21, 0xf0, 0x48, 0xc1, 0xea, 0x18, 0x48, 0x31, 0xd0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .shr 64 [gr 64 2, Src.opd 8 (.i 24)] 4) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .xor 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.and 64 0 (.r 6),
  Op.shr64 2 (.i 24),
  Op.xor 64 0 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.and (.r 6) (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.shr64 (.i 24)) (by decide) <|
  .cons (p4_7 _) (OpI.xor (.r 2) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `72`. -/
def p5 : List Byte := [
  0x0f, 0xb6, 0x11, 0x84, 0xd2]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 1) none 1 0 8)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 8 2 (some 1) none 1 0,
  Op.test 8 2 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 5 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 5

def j3 : List Byte := [0x75, 0xd9]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551577] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p6 : List Byte := [
  0x31, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

end FV7z.Hsh
