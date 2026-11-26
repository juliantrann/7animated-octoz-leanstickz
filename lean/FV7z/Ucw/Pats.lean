import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::UString(const wchar_t*)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ucw
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x8b, 0x16, 0x48, 0x89, 0xfb,
  0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 6) none 1 0 32)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.ld 32 2 (some 6) none 1 0,
  Op.mov 64 3 (.r 7),
  Op.test 32 2 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_10 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_16 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 18

def j0 : List Byte := [0x74, 0x3c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 60] 2) := by dec_rfl

/-- The stretch at `20`. -/
def p1 : List Byte := [
  0x31, 0xf6, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.xor 32 6 (.r 6),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.nop) (by decide) <|
  .nil 12

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x8d, 0x46, 0x01, 0x89, 0xf2, 0x48, 0x89, 0xc6, 0x8b, 0x44, 0x85, 0x00, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 6) none 1 1 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) (some 0) 4 0 32)] 4) := by dec_rfl
theorem p2_12 : ∀ feat, Dec feat p2 12 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 0 (some 6) none 1 1,
  Op.mov 32 2 (.r 6),
  Op.mov 64 6 (.r 0),
  Op.ld 32 0 (some 5) (some 0) 4 0,
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_12 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0xf0]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551600] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0x44, 0x8d, 0x62, 0x02]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 32 [gr 32 12, .mem (mg (some 2) none 1 2 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 32 12 (some 2) none 1 2]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `52`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xdf]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.r 3)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `60`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x3b, 0x4c, 0x89, 0xe2, 0x5b, 0x48, 0x89, 0xee, 0x5d, 0x41, 0x5c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 3) none 1 0,
  Op.mov 64 2 (.r 12),
  Op.pop 3,
  Op.mov 64 6 (.r 5),
  Op.pop 5,
  Op.pop 12]

theorem b5 (prof : Profile) : Blk prof p5 0 13 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p5_6 _) (OpI.pop) (by decide) <|
  .cons (p5_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p5_10 _) (OpI.pop) (by decide) <|
  .cons (p5_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x41, 0xbc, 0x01, 0x00, 0x00, 0x00, 0x31, 0xf6]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 12 (.i 1),
  Op.xor 32 6 (.r 6)]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 8

def j2 : List Byte := [0xeb, 0xda]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551578] 2) := by dec_rfl

end FV7z.Ucw
