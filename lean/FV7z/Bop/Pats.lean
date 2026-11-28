import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CExtractCallbackConsole::BeforeOpen` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 17 of them) and each distinct jump (`j*`, 12) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Bop
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x41, 0x89, 0xd4, 0x55, 0x48, 0x89, 0xf5, 0x53,
  0x48, 0x89, 0xfb, 0x48, 0x81, 0xc7, 0x60, 0x01, 0x00, 0x00, 0x48, 0x83, 0xec, 0x08]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 352)] 7) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.mov 32 12 (.r 2),
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.add 64 7 (.i 352),
  Op.sub 64 4 (.i 8)]

theorem b0 (prof : Profile) : Blk prof p0 0 30 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.push) (by decide) <|
  .cons (p0_16 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.add (.i 352) (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 30

/-- The stretch at `35`. -/
def p1 : List Byte := [
  0x48, 0xc7, 0xc0, 0x88, 0xf0, 0x79, 0x00, 0xc6, 0x83, 0x3c, 0x01, 0x00, 0x00, 0x01, 0x8b, 0x10,
  0x85, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7991432)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 8 [.mem (mg (some 3) none 1 316 8), .imm 8 1] 7) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 0) none 1 0 32)] 2) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 0 (.i 7991432),
  Op.sti 8 (some 3) none 1 316 1,
  Op.ld 32 2 (some 0) none 1 0,
  Op.test 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 18 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 7991432) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p1_14 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_16 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 18

def j0 : List Byte := [0x0f, 0x85, 0xe5, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 229] 6) := by dec_rfl

/-- The stretch at `59`. -/
def p2 : List Byte := [
  0x31, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `69`. -/
def p3 : List Byte := [
  0x4c, 0x8b, 0xab, 0x08, 0x01, 0x00, 0x00, 0x66, 0x89, 0x83, 0x3d, 0x01, 0x00, 0x00, 0x48, 0x8b,
  0x43, 0x68, 0x48, 0xc7, 0x83, 0xc0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 16 [.mem (mg (some 3) none 1 317 16), gr 16 0] 7) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 104 64)] 4) := by dec_rfl
theorem p3_18 : ∀ feat, Dec feat p3 18 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 448 64), .imm 64 0] 11) := by dec_rfl
theorem p3_29 : ∀ feat, Dec feat p3 29 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 13 (some 3) none 1 264,
  Op.st 16 (some 3) none 1 317 0,
  Op.ld 64 0 (some 3) none 1 104,
  Op.sti 64 (some 3) none 1 448 0,
  Op.test 64 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 32 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p3_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_18 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_29 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 32

def j1 : List Byte := [0x0f, 0x84, 0x85, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 133] 6) := by dec_rfl

/-- The stretch at `107`. -/
def p4 : List Byte := [
  0x80, 0x7b, 0x70, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 8 [.mem (mg (some 3) none 1 112 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmpmi 8 (some 3) none 1 112 0]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x75, 0x7f]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 127] 2) := by dec_rfl

/-- The stretch at `113`. -/
def p5 : List Byte := [
  0x49, 0x39, 0xc5]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 64 13 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x0f, 0x84, 0x86, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 134] 6) := by dec_rfl

/-- The stretch at `122`. -/
def p6 : List Byte := [
  0x4d, 0x85, 0xed]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.test 64 13 (.r 13)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.test (.r 13) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0x4e]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 78] 2) := by dec_rfl

/-- The stretch at `127`. -/
def p7 : List Byte := [
  0x4c, 0x89, 0xef]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 7 (.r 13)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `135`. -/
def p8 : List Byte := [
  0x45, 0x84, 0xe4, 0x48, 0x8d, 0x3d, 0x03, 0x1f, 0x10, 0x00, 0x48, 0x8d, 0x05, 0x0e, 0x1f, 0x10,
  0x00, 0x48, 0x0f, 0x44, 0xf8, 0x49, 0x8b, 0x75, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 8 [gr 8 12, Src.opd 8 (.r 12)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1056515 0)] 7) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1056526 0)] 7) := by dec_rfl
theorem p8_17 : ∀ feat, Dec feat p8 17 (FV7z.mk (.cmovcc 4) 64 [gr 64 7, gr 64 0] 4) := by dec_rfl
theorem p8_21 : ∀ feat, Dec feat p8 21 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 13) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 8 12 (.r 12),
  Op.mov 64 7 (.i 7248644),
  Op.mov 64 0 (.i 7248662),
  Op.cmov64 4 7 0,
  Op.ld 64 6 (some 13) none 1 0]

theorem b8 (prof : Profile) : BlkA prof p8 (0x5e7bf7 : Addr) 0 25 o8 :=
  .cons (p8_0 _) ((OpI.test8 (.r 12)).at _) (by decide) <|
  .cons (p8_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p8_10 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p8_17 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p8_21 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .nil 25

/-- The stretch at `165`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0xbb, 0x08, 0x01, 0x00, 0x00, 0x48, 0x89, 0xee]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 7 (some 3) none 1 264,
  Op.mov 64 6 (.r 5)]

theorem b9 (prof : Profile) : Blk prof p9 0 10 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `180`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0xbb, 0x08, 0x01, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 7 (some 3) none 1 264]

theorem b10 (prof : Profile) : Blk prof p10 0 7 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `192`. -/
def p11 : List Byte := [
  0x48, 0x83, 0x7b, 0x68, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .cmp 64 [.mem (mg (some 3) none 1 104 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.cmpmi 64 (some 3) none 1 104 0]

theorem b11 (prof : Profile) : Blk prof p11 0 5 o11 :=
  .cons (p11_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 5

def j5 : List Byte := [0x74, 0x16]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 22] 2) := by dec_rfl

def j6 : List Byte := [0x75, 0x10]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `205`. -/
def p12 : List Byte := [
  0x48, 0x8d, 0x7b, 0x48, 0x48, 0x8d, 0x35, 0xe3, 0x1e, 0x10, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 72 0)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1056483 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.lea 64 7 (some 3) none 1 72,
  Op.mov 64 6 (.i 7248683)]

theorem b12 (prof : Profile) : BlkA prof p12 (0x5e7c3d : Addr) 0 11 o12 :=
  .cons (p12_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p12_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 11

/-- The stretch at `223`. -/
def p13 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p13_5 : ∀ feat, Dec feat p13 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p13_6 : ∀ feat, Dec feat p13 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p13_8 : ∀ feat, Dec feat p13 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b13 (prof : Profile) : Blk prof p13 0 10 o13 :=
  .cons (p13_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.pop) (by decide) <|
  .cons (p13_5 _) (OpI.pop) (by decide) <|
  .cons (p13_6 _) (OpI.pop) (by decide) <|
  .cons (p13_8 _) (OpI.pop) (by decide) <|
  .nil 10

def j7 : List Byte := [0x75, 0x8a]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551498] 2) := by dec_rfl

def j8 : List Byte := [0xeb, 0xe6]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551590] 2) := by dec_rfl

/-- The stretch at `256`. -/
def p14 : List Byte := [
  0x48, 0x8d, 0x7b, 0x30, 0x31, 0xf6]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 48 0)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.lea 64 7 (some 3) none 1 48,
  Op.xor 32 6 (.r 6)]

theorem b14 (prof : Profile) : Blk prof p14 0 6 o14 :=
  .cons (p14_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `267`. -/
def p15 : List Byte := [
  0x4c, 0x8b, 0xab, 0x08, 0x01, 0x00, 0x00, 0x4d, 0x85, 0xed]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 13 (some 3) none 1 264,
  Op.test 64 13 (.r 13)]

theorem b15 (prof : Profile) : Blk prof p15 0 10 o15 :=
  .cons (p15_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p15_7 _) (OpI.test (.r 13) (.inr rfl)) (by decide) <|
  .nil 10

def j9 : List Byte := [0x0f, 0x85, 0x64, 0xff, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551460] 6) := by dec_rfl

def j10 : List Byte := [0xeb, 0xa3]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551523] 2) := by dec_rfl

/-- The stretch at `288`. -/
def p16 : List Byte := [
  0xb8, 0x04, 0x40, 0x00, 0x80]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147500036)] 5) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 32 0 (.i 2147500036)]

theorem b16 (prof : Profile) : Blk prof p16 0 5 o16 :=
  .cons (p16_0 _) (OpI.mov (.i 2147500036) (.inl rfl)) (by decide) <|
  .nil 5

def j11 : List Byte := [0xeb, 0xb8]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551544] 2) := by dec_rfl

end FV7z.Bop
