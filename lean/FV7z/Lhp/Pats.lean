import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CHeader_Parse` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 15 of them) and each distinct jump (`j*`, 11) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Lhp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xc6, 0x47, 0x08, 0x00, 0x84, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 8 8), .imm 8 0] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sti 8 (some 7) none 1 8 0,
  Op.test 8 2 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x74, 0x0a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `12`. -/
def p1 : List Byte := [
  0x0f, 0xb6, 0x06, 0x48, 0x83, 0xc6, 0x01, 0x88, 0x47, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 6) none 1 0 8)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 8 8), gr 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ldzx 8 0 (some 6) none 1 0,
  Op.add 64 6 (.i 1),
  Op.st 8 (some 7) none 1 8 0]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `22`. -/
def p2 : List Byte := [
  0x31, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `24`. -/
def p3 : List Byte := [
  0x0f, 0xb6, 0x14, 0x06, 0x88, 0x54, 0x07, 0x09, 0x48, 0x83, 0xc0, 0x01, 0x48, 0x83, 0xf8, 0x05]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 6) (some 0) 1 0 8)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 8 [.mem (mg (some 7) (some 0) 1 9 8), gr 8 2] 4) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 5)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldzx 8 2 (some 6) (some 0) 1 0,
  Op.st 8 (some 7) (some 0) 1 9 2,
  Op.add 64 0 (.i 1),
  Op.cmp 64 0 (.i 5)]

theorem b3 (prof : Profile) : Blk prof p3 0 16 o3 :=
  .cons (p3_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p3_12 _) (OpI.cmp (.i 5) (.inr rfl)) (by decide) <|
  .nil 16

def j1 : List Byte := [0x75, 0xee]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `42`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x46, 0x05, 0x45, 0x31, 0xc0, 0x80, 0x7f, 0x09, 0xe0, 0x48, 0x89, 0x07]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 5 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 9 8), .imm 8 224] 4) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 0 (some 6) none 1 5,
  Op.xor 32 8 (.r 8),
  Op.cmpmi 8 (some 7) none 1 9 224,
  Op.st 64 (some 7) none 1 0 0]

theorem b4 (prof : Profile) : Blk prof p4 0 14 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.xor (.r 8) (.inl rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 14

def j2 : List Byte := [0x77, 0x06]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `58`. -/
def p5 : List Byte := [
  0x80, 0x7f, 0x08, 0x01]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 8 8), .imm 8 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmpmi 8 (some 7) none 1 8 1]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j3 : List Byte := [0x76, 0x08]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `64`. -/
def p6 : List Byte := [
  0x44, 0x89, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 0 (.r 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `72`. -/
def p7 : List Byte := [
  0x48, 0xba, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xff, 0x48, 0x01, 0xd0, 0x48, 0x83, 0xea,
  0x02, 0x48, 0x39, 0xd0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18374686479671623680)] 10) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p7_13 : ∀ feat, Dec feat p7 13 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p7_17 : ∀ feat, Dec feat p7 17 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 2 (.i 18374686479671623680),
  Op.add 64 0 (.r 2),
  Op.sub 64 2 (.i 2),
  Op.cmp 64 0 (.r 2)]

theorem b7 (prof : Profile) : Blk prof p7 0 20 o7 :=
  .cons (p7_0 _) (OpI.mov (.i 18374686479671623680) (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p7_13 _) (OpI.sub (.i 2) (.inr rfl)) (by decide) <|
  .cons (p7_17 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 20

def j4 : List Byte := [0x76, 0xe2]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551586] 2) := by dec_rfl

/-- The stretch at `94`. -/
def p8 : List Byte := [
  0x8b, 0x47, 0x0a, 0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x83, 0xf8, 0x01]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 10 32)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p8_9 : ∀ feat, Dec feat p8 9 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 0 (some 7) none 1 10,
  Op.mov 32 8 (.i 1),
  Op.cmp 32 0 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 12 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p8_9 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 12

def j5 : List Byte := [0x74, 0xd4]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551572] 2) := by dec_rfl

/-- The stretch at `108`. -/
def p9 : List Byte := [
  0x31, 0xc9, 0xbe, 0x02, 0x00, 0x00, 0x00, 0xbf, 0x03, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 3)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.mov 32 6 (.i 2),
  Op.mov 32 7 (.i 3)]

theorem b9 (prof : Profile) : Blk prof p9 0 12 o9 :=
  .cons (p9_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p9_2 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .nil 12

def j6 : List Byte := [0xeb, 0x16]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `128`. -/
def p10 : List Byte := [
  0x89, 0xfa, 0xd3, 0xe2, 0x39, 0xd0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .shl 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 2 (.r 7),
  Op.shl 2 (.r 1),
  Op.cmp 32 0 (.r 2)]

theorem b10 (prof : Profile) : Blk prof p10 0 6 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p10_4 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0x74, 0x10]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `136`. -/
def p11 : List Byte := [
  0x83, 0xc1, 0x01, 0x83, 0xf9, 0x1f]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 31)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.add 32 1 (.i 1),
  Op.cmp 32 1 (.i 31)]

theorem b11 (prof : Profile) : Blk prof p11 0 6 o11 :=
  .cons (p11_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.cmp (.i 31) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `144`. -/
def p12 : List Byte := [
  0x89, 0xf2, 0xd3, 0xe2, 0x39, 0xd0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p12_2 : ∀ feat, Dec feat p12 2 (FV7z.mk .shl 32 [gr 32 2, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 32 2 (.r 6),
  Op.shl 2 (.r 1),
  Op.cmp 32 0 (.r 2)]

theorem b12 (prof : Profile) : Blk prof p12 0 6 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .cons (p12_2 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p12_4 _) (OpI.cmp (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

def j8 : List Byte := [0x75, 0xe8]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551592] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p13 : List Byte := [
  0x41, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 32 8 (.i 1)]

theorem b13 (prof : Profile) : Blk prof p13 0 6 o13 :=
  .cons (p13_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 6

def j9 : List Byte := [0xeb, 0xa0]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551520] 2) := by dec_rfl

/-- The stretch at `160`. -/
def p14 : List Byte := [
  0x83, 0xf8, 0xff, 0x41, 0x0f, 0x94, 0xc0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk (.setcc 4) 8 [gr 8 8] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 32 0 (.i 4294967295),
  Op.setcc 4 8]

theorem b14 (prof : Profile) : Blk prof p14 0 7 o14 :=
  .cons (p14_0 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.setcc) (by decide) <|
  .nil 7

def j10 : List Byte := [0xeb, 0x97]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551511] 2) := by dec_rfl

end FV7z.Lhp
