import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `UString::operator= (const char *)` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 13 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Uac
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x49, 0x89, 0xff, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55,
  0x48, 0x89, 0xf5, 0x53, 0x31, 0xdb, 0x48, 0x83, 0xec, 0x08, 0x80, 0x3e, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .cmp 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.mov 64 15 (.r 7),
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.xor 32 3 (.r 3),
  Op.sub 64 4 (.i 8),
  Op.cmpmi 8 (some 6) none 1 0 0]

theorem b0 (prof : Profile) : Blk prof p0 0 29 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.push) (by decide) <|
  .cons (p0_20 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 29

def j0 : List Byte := [0x0f, 0x84, 0x8d, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 141] 6) := by dec_rfl

/-- The stretch at `35`. -/
def p1 : List Byte := [
  0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.nop) (by decide) <|
  .nil 5

/-- The stretch at `40`. -/
def p2 : List Byte := [
  0x8d, 0x43, 0x01, 0x41, 0x89, 0xdd, 0x80, 0x7c, 0x05, 0x00, 0x00, 0x48, 0x89, 0xc3]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 3) none 1 1 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.r 3)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .cmp 8 [.mem (mg (some 5) (some 0) 1 0 8), .imm 8 0] 5) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 0 (some 3) none 1 1,
  Op.mov 32 13 (.r 3),
  Op.cmpmi 8 (some 5) (some 0) 1 0 0,
  Op.mov 64 3 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p2_11 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x75, 0xf0]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551600] 2) := by dec_rfl

/-- The stretch at `56`. -/
def p3 : List Byte := [
  0x4c, 0x8d, 0x24, 0x85, 0x00, 0x00, 0x00, 0x00, 0x41, 0x39, 0x47, 0x0c]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 12, .mem (mg none (some 0) 4 0 0)] 8) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .cmp 32 [.mem (mg (some 15) none 1 12 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 12 none (some 0) 4 0,
  Op.cmpmr 32 (some 15) none 1 12 0]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 12

def j2 : List Byte := [0x72, 0x42]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 2) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `70`. -/
def p4 : List Byte := [
  0x4d, 0x8b, 0x37]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 15) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 14 (some 15) none 1 0]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `73`. -/
def p5 : List Byte := [
  0x31, 0xd2, 0x85, 0xdb]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .test 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.test 32 3 (.r 3)]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p5_2 _) (OpI.test (.r 3) (.inl rfl)) (by decide) <|
  .nil 4

def j3 : List Byte := [0x74, 0x16]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `79`. -/
def p6 : List Byte := [
  0x90]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.nop]

theorem b6 (prof : Profile) : Blk prof p6 0 1 o6 :=
  .cons (p6_0 _) (OpI.nop) (by decide) <|
  .nil 1

/-- The stretch at `80`. -/
def p7 : List Byte := [
  0x0f, 0xb6, 0x4c, 0x15, 0x00, 0x41, 0x89, 0x0c, 0x96, 0x48, 0x89, 0xd1, 0x48, 0x83, 0xc2, 0x01,
  0x49, 0x39, 0xcd]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 5) (some 2) 1 0 8)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .mov 32 [.mem (mg (some 14) (some 2) 4 0 32), gr 32 1] 4) := by dec_rfl
theorem p7_9 : ∀ feat, Dec feat p7 9 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p7_12 : ∀ feat, Dec feat p7 12 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p7_16 : ∀ feat, Dec feat p7 16 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldzx 8 1 (some 5) (some 2) 1 0,
  Op.st 32 (some 14) (some 2) 4 0 1,
  Op.mov 64 1 (.r 2),
  Op.add 64 2 (.i 1),
  Op.cmp 64 13 (.r 1)]

theorem b7 (prof : Profile) : Blk prof p7 0 19 o7 :=
  .cons (p7_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p7_9 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p7_12 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p7_16 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 19

def j4 : List Byte := [0x75, 0xeb]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `101`. -/
def p8 : List Byte := [
  0x43, 0xc7, 0x04, 0x26, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xf8, 0x41, 0x89, 0x5f, 0x08, 0x48,
  0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [.mem (mg (some 14) (some 12) 1 0 32), .imm 32 0] 8) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .mov 32 [.mem (mg (some 15) none 1 8 32), gr 32 3] 4) := by dec_rfl
theorem p8_15 : ∀ feat, Dec feat p8 15 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p8_19 : ∀ feat, Dec feat p8 19 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p8_20 : ∀ feat, Dec feat p8 20 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_21 : ∀ feat, Dec feat p8 21 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p8_23 : ∀ feat, Dec feat p8 23 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p8_25 : ∀ feat, Dec feat p8 25 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p8_27 : ∀ feat, Dec feat p8 27 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.sti 32 (some 14) (some 12) 1 0 0,
  Op.mov 64 0 (.r 15),
  Op.st 32 (some 15) none 1 8 3,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b8 (prof : Profile) : Blk prof p8 0 29 o8 :=
  .cons (p8_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_8 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p8_11 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_15 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p8_19 _) (OpI.pop) (by decide) <|
  .cons (p8_20 _) (OpI.pop) (by decide) <|
  .cons (p8_21 _) (OpI.pop) (by decide) <|
  .cons (p8_23 _) (OpI.pop) (by decide) <|
  .cons (p8_25 _) (OpI.pop) (by decide) <|
  .cons (p8_27 _) (OpI.pop) (by decide) <|
  .nil 29

/-- The stretch at `136`. -/
def p9 : List Byte := [
  0x49, 0x8d, 0x7c, 0x24, 0x04]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 12) none 1 4 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lea 64 7 (some 12) none 1 4]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `146`. -/
def p10 : List Byte := [
  0x49, 0x8b, 0x3f, 0x49, 0x89, 0xc6, 0x48, 0x85, 0xff]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 15) none 1 0 64)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p10_6 : ∀ feat, Dec feat p10 6 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 7 (some 15) none 1 0,
  Op.mov 64 14 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b10 (prof : Profile) : Blk prof p10 0 9 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p10_6 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 9

def j5 : List Byte := [0x74, 0x05]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `162`. -/
def p11 : List Byte := [
  0x4d, 0x89, 0x37, 0x41, 0x89, 0x5f, 0x0c]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 0 64), gr 64 14] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .mov 32 [.mem (mg (some 15) none 1 12 32), gr 32 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.st 64 (some 15) none 1 0 14,
  Op.st 32 (some 15) none 1 12 3]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 7

def j6 : List Byte := [0xeb, 0x9e]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551518] 2) := by dec_rfl

/-- The stretch at `176`. -/
def p12 : List Byte := [
  0x4c, 0x8b, 0x37, 0x45, 0x31, 0xe4]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 14, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 14 (some 7) none 1 0,
  Op.xor 32 12 (.r 12)]

theorem b12 (prof : Profile) : Blk prof p12 0 6 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_3 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0xeb, 0xad]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551533] 2) := by dec_rfl

end FV7z.Uac
