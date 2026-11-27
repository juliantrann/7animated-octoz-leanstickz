import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `UString::UString(const char*)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 11 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Uca
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x49, 0x89, 0xfe, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x80,
  0x3e, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.mov 64 14 (.r 7),
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.cmpmi 8 (some 6) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 18 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 18

def j0 : List Byte := [0x74, 0x6c]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 108] 2) := by dec_rfl

/-- The stretch at `20`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xf5, 0x31, 0xdb, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 5 (.r 6),
  Op.xor 32 3 (.r 3),
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 12 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.nop) (by decide) <|
  .nil 12

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x44, 0x8d, 0x63, 0x01, 0x41, 0x89, 0xdd, 0x42, 0x80, 0x7c, 0x25, 0x00, 0x00, 0x4c, 0x89, 0xe3]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 12, .mem (mg (some 3) none 1 1 0)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .cmp 8 [.mem (mg (some 5) (some 12) 1 0 8), .imm 8 0] 6) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 12 (some 3) none 1 1,
  Op.mov 32 13 (.r 3),
  Op.cmpmi 8 (some 5) (some 12) 1 0 0,
  Op.mov 64 3 (.r 12)]

theorem b2 (prof : Profile) : Blk prof p2 0 16 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p2_13 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 16

def j1 : List Byte := [0x75, 0xee]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p3 : List Byte := [
  0x44, 0x89, 0xe6, 0x4c, 0x89, 0xf7, 0x49, 0xc1, 0xe4, 0x02]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .shl 64 [gr 64 12, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 6 (.r 12),
  Op.mov 64 7 (.r 14),
  Op.shl64 12 (.i 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.shl64 (.i 2)) (by decide) <|
  .nil 10

/-- The stretch at `65`. -/
def p4 : List Byte := [
  0x49, 0x8b, 0x0e, 0x85, 0xdb]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .test 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 1 (some 14) none 1 0,
  Op.test 32 3 (.r 3)]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.test (.r 3) (.inl rfl)) (by decide) <|
  .nil 5

def j2 : List Byte := [0x74, 0x1c]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `72`. -/
def p5 : List Byte := [
  0x31, 0xc0, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x0f, 0xb6, 0x54, 0x05, 0x00, 0x89, 0x14, 0x81, 0x48, 0x89, 0xc2, 0x48, 0x83, 0xc0, 0x01, 0x49,
  0x39, 0xd5]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 5) (some 0) 1 0 8)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .mov 32 [.mem (mg (some 1) (some 0) 4 0 32), gr 32 2] 3) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p6_15 : ∀ feat, Dec feat p6 15 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ldzx 8 2 (some 5) (some 0) 1 0,
  Op.st 32 (some 1) (some 0) 4 0 2,
  Op.mov 64 2 (.r 0),
  Op.add 64 0 (.i 1),
  Op.cmp 64 13 (.r 2)]

theorem b6 (prof : Profile) : Blk prof p6 0 18 o6 :=
  .cons (p6_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p6_8 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p6_11 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p6_15 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 18

def j3 : List Byte := [0x75, 0xec]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551596] 2) := by dec_rfl

/-- The stretch at `100`. -/
def p7 : List Byte := [
  0x49, 0x01, 0xcc]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 12, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 12 (.r 1)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `103`. -/
def p8 : List Byte := [
  0x41, 0xc7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 0 32), .imm 32 0] 8) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p8_9 : ∀ feat, Dec feat p8 9 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p8_14 : ∀ feat, Dec feat p8 14 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.sti 32 (some 12) none 1 0 0,
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b8 (prof : Profile) : Blk prof p8 0 16 o8 :=
  .cons (p8_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_8 _) (OpI.pop) (by decide) <|
  .cons (p8_9 _) (OpI.pop) (by decide) <|
  .cons (p8_10 _) (OpI.pop) (by decide) <|
  .cons (p8_12 _) (OpI.pop) (by decide) <|
  .cons (p8_14 _) (OpI.pop) (by decide) <|
  .nil 16

/-- The stretch at `128`. -/
def p9 : List Byte := [
  0x31, 0xf6]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.xor 32 6 (.r 6)]

theorem b9 (prof : Profile) : Blk prof p9 0 2 o9 :=
  .cons (p9_0 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `135`. -/
def p10 : List Byte := [
  0x4d, 0x8b, 0x26]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 12 (some 14) none 1 0]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0xeb, 0xdb]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551579] 2) := by dec_rfl

end FV7z.Uca
