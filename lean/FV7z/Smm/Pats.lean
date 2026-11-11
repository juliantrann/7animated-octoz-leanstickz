import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `sysmalloc` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 30 of them) and each distinct jump (`j*`, 24) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Smm
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x48, 0x89, 0xfd, 0x53, 0x48, 0x83, 0xec,
  0x38, 0x4c, 0x8b, 0x35, 0x60, 0x30, 0x16, 0x00, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 14, .mem (mrip 1454176 64)] 7) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.sub 64 4 (.i 56),
  Op.lda 64 14 7943128,
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x630360 : Addr) 0 27 o0 :=
  .cons (p0_0 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_2 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_8 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_9 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_12 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_13 _) ((OpI.sub (.i 56) (.inr rfl)).at _) (by decide) <|
  .cons (p0_17 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_24 _) ((OpI.test (.r 6) (.inr rfl)).at _) (by decide) <|
  .nil 27

def j0 : List Byte := [0x0f, 0x84, 0x6f, 0x02, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 623] 6) := by dec_rfl

/-- The stretch at `33`. -/
def p1 : List Byte := [
  0x48, 0x39, 0x3d, 0x28, 0x26, 0x16, 0x00, 0x48, 0x89, 0xf3]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [.mem (mrip 1451560 64), gr 64 7] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmra 64 7940528 7,
  Op.mov 64 3 (.r 6)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x630381 : Addr) 0 10 o1 :=
  .cons (p1_0 _) (OpIA.cmpmr_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_7 _) ((OpI.mov (.r 6) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j1 : List Byte := [0x0f, 0x86, 0x5f, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 351] 6) := by dec_rfl

/-- The stretch at `49`. -/
def p2 : List Byte := [
  0xc6, 0x04, 0x24, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 8 [.mem (mg (some 4) none 1 0 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sti 8 (some 4) none 1 0 0]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `53`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0xf2, 0x49, 0x8d, 0x44, 0x2e, 0x07, 0x4c, 0x8d, 0x53, 0x60, 0x48, 0xf7, 0xda, 0x4d,
  0x89, 0xd7, 0x48, 0x21, 0xd0, 0x48, 0x89, 0x44, 0x24, 0x10]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 14) (some 5) 1 7 0)] 5) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 3) none 1 96 0)] 4) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .neg 64 [gr 64 2] 3) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p3_18 : ∀ feat, Dec feat p3 18 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p3_21 : ∀ feat, Dec feat p3 21 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 2 (.r 14),
  Op.lea 64 0 (some 14) (some 5) 1 7,
  Op.lea 64 10 (some 3) none 1 96,
  Op.neg 64 2,
  Op.mov 64 15 (.r 10),
  Op.and 64 0 (.r 2),
  Op.st 64 (some 4) none 1 16 0]

theorem b3 (prof : Profile) : Blk prof p3 0 26 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_12 _) (OpI.neg (.inr rfl)) (by decide) <|
  .cons (p3_15 _) (OpI.mov (.r 10) (.inr rfl)) (by decide) <|
  .cons (p3_18 _) (OpI.and (.r 2) (.inr rfl)) (by decide) <|
  .cons (p3_21 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 26

/-- The stretch at `79`. -/
def p4 : List Byte := [
  0x4c, 0x8b, 0x6b, 0x60, 0x49, 0x8b, 0x45, 0x08, 0x49, 0x89, 0xc4, 0x49, 0x83, 0xe4, 0xf8, 0x4f,
  0x8d, 0x5c, 0x25, 0x00, 0x4d, 0x39, 0xfd]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 13, .mem (mg (some 3) none 1 96 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 13) none 1 8 64)] 4) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .and 64 [gr 64 12, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p4_15 : ∀ feat, Dec feat p4 15 (FV7z.mk .lea 64 [gr 64 11, .mem (mg (some 13) (some 12) 1 0 0)] 5) := by dec_rfl
theorem p4_20 : ∀ feat, Dec feat p4 20 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 13 (some 3) none 1 96,
  Op.ld 64 0 (some 13) none 1 8,
  Op.mov 64 12 (.r 0),
  Op.and 64 12 (.i 18446744073709551608),
  Op.lea 64 11 (some 13) (some 12) 1 0,
  Op.cmp 64 13 (.r 15)]

theorem b4 (prof : Profile) : Blk prof p4 0 23 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_8 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p4_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_20 _) (OpI.cmp (.r 15) (.inr rfl)) (by decide) <|
  .nil 23

def j2 : List Byte := [0x75, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `104`. -/
def p5 : List Byte := [
  0x4d, 0x85, 0xe4]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 64 12 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x1f]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `140`. -/
def p6 : List Byte := [
  0x4c, 0x8d, 0x55, 0x20, 0x4d, 0x39, 0xe2]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 10, .mem (mg (some 5) none 1 32 0)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .cmp 64 [gr 64 10, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 10 (some 5) none 1 32,
  Op.cmp 64 10 (.r 12)]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.cmp (.r 12) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x0f, 0x86, 0xbc, 0x06, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 6) 64 [.rel 1724] 6) := by dec_rfl

/-- The stretch at `153`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x05, 0x40, 0x26, 0x16, 0x00, 0x48, 0x39, 0xc3]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1451584 0)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 0 (.i 7940672),
  Op.cmp 64 3 (.r 0)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x6303f9 : Addr) 0 10 o7 :=
  .cons (p7_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_7 _) ((OpI.cmp (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j5 : List Byte := [0x0f, 0x84, 0x8f, 0x02, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 655] 6) := by dec_rfl

/-- The stretch at `296`. -/
def p8 : List Byte := [
  0x48, 0x39, 0x8b, 0x90, 0x08, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 64 [.mem (mg (some 3) none 1 2192 64), gr 64 1] 7) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmpmr 64 (some 3) none 1 2192 1]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.cmpmr (.inr rfl)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x73, 0x07]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 3) 64 [.rel 7] 2) := by dec_rfl

/-- The stretch at `305`. -/
def p9 : List Byte := [
  0x48, 0x89, 0x8b, 0x90, 0x08, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 2192 64), gr 64 1] 7) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.st 64 (some 3) none 1 2192 1]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `312`. -/
def p10 : List Byte := [
  0x49, 0x8b, 0x40, 0x08, 0x48, 0x83, 0xe0, 0xf8, 0x49, 0x39, 0xc7]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 8) none 1 8 64)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .cmp 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 0 (some 8) none 1 8,
  Op.and 64 0 (.i 18446744073709551608),
  Op.cmp 64 15 (.r 0)]

theorem b10 (prof : Profile) : Blk prof p10 0 11 o10 :=
  .cons (p10_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p10_8 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 11

def j7 : List Byte := [0x0f, 0x87, 0x27, 0x01, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 7) 64 [.rel 295] 6) := by dec_rfl

/-- The stretch at `329`. -/
def p11 : List Byte := [
  0x48, 0x89, 0xee, 0x48, 0x8d, 0x3d, 0x8d, 0x25, 0x16, 0x00, 0x49, 0x8d, 0x0c, 0x28, 0x48, 0x29,
  0xe8, 0x48, 0x83, 0xce, 0x04, 0x48, 0x39, 0xfb, 0x48, 0x89, 0x4b, 0x60, 0x48, 0x0f, 0x45, 0xee,
  0x48, 0x83, 0xc8, 0x01, 0x49, 0x83, 0xc0, 0x10, 0x48, 0x83, 0xcd, 0x01, 0x49, 0x89, 0x68, 0xf8,
  0x48, 0x89, 0x41, 0x08]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1451405 0)] 7) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 8) (some 5) 1 0 0)] 4) := by dec_rfl
theorem p11_14 : ∀ feat, Dec feat p11 14 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p11_17 : ∀ feat, Dec feat p11 17 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p11_21 : ∀ feat, Dec feat p11 21 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p11_24 : ∀ feat, Dec feat p11 24 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 96 64), gr 64 1] 4) := by dec_rfl
theorem p11_28 : ∀ feat, Dec feat p11 28 (FV7z.mk (.cmovcc 5) 64 [gr 64 5, gr 64 6] 4) := by dec_rfl
theorem p11_32 : ∀ feat, Dec feat p11 32 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_36 : ∀ feat, Dec feat p11 36 (FV7z.mk .add 64 [gr 64 8, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p11_40 : ∀ feat, Dec feat p11 40 (FV7z.mk .or 64 [gr 64 5, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_44 : ∀ feat, Dec feat p11 44 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 18446744073709551608 64), gr 64 5] 4) := by dec_rfl
theorem p11_48 : ∀ feat, Dec feat p11 48 (FV7z.mk .mov 64 [.mem (mg (some 1) none 1 8 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.i 7940672),
  Op.lea 64 1 (some 8) (some 5) 1 0,
  Op.sub 64 0 (.r 5),
  Op.or 64 6 (.i 4),
  Op.cmp 64 3 (.r 7),
  Op.st 64 (some 3) none 1 96 1,
  Op.cmov64 5 5 6,
  Op.or 64 0 (.i 1),
  Op.add 64 8 (.i 16),
  Op.or 64 5 (.i 1),
  Op.st 64 (some 8) none 1 18446744073709551608 5,
  Op.st 64 (some 1) none 1 8 0]

theorem b11 (prof : Profile) : BlkA prof p11 (0x6304a9 : Addr) 0 52 o11 :=
  .cons (p11_0 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p11_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p11_10 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p11_14 _) ((OpI.sub (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p11_17 _) ((OpI.or (.i 4) (.inr rfl)).at _) (by decide) <|
  .cons (p11_21 _) ((OpI.cmp (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p11_24 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p11_28 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p11_32 _) ((OpI.or (.i 1) (.inr rfl)).at _) (by decide) <|
  .cons (p11_36 _) ((OpI.add (.i 16) (.inr rfl)).at _) (by decide) <|
  .cons (p11_40 _) ((OpI.or (.i 1) (.inr rfl)).at _) (by decide) <|
  .cons (p11_44 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p11_48 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 52

/-- The stretch at `381`. -/
def p12 : List Byte := [
  0x48, 0x83, 0xc4, 0x38, 0x4c, 0x89, 0xc0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41,
  0x5f]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p12_9 : ∀ feat, Dec feat p12 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p12_11 : ∀ feat, Dec feat p12 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p12_13 : ∀ feat, Dec feat p12 13 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p12_15 : ∀ feat, Dec feat p12 15 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.add 64 4 (.i 56),
  Op.mov 64 0 (.r 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b12 (prof : Profile) : Blk prof p12 0 17 o12 :=
  .cons (p12_0 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p12_7 _) (OpI.pop) (by decide) <|
  .cons (p12_8 _) (OpI.pop) (by decide) <|
  .cons (p12_9 _) (OpI.pop) (by decide) <|
  .cons (p12_11 _) (OpI.pop) (by decide) <|
  .cons (p12_13 _) (OpI.pop) (by decide) <|
  .cons (p12_15 _) (OpI.pop) (by decide) <|
  .nil 17

/-- The stretch at `824`. -/
def p13 : List Byte := [
  0x49, 0x8d, 0x46, 0xff, 0x4d, 0x89, 0xd7, 0x4d, 0x89, 0xf2, 0x48, 0x89, 0x04, 0x24, 0x48, 0x8b,
  0x05, 0xfb, 0x22, 0x16, 0x00, 0x49, 0xf7, 0xda, 0x49, 0x8d, 0x74, 0x06, 0x1f, 0x48, 0x01, 0xee,
  0xf6, 0x43, 0x04, 0x02]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 14) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .mov 64 [gr 64 10, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p13_10 : ∀ feat, Dec feat p13 10 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 0] 4) := by dec_rfl
theorem p13_14 : ∀ feat, Dec feat p13 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1450747 64)] 7) := by dec_rfl
theorem p13_21 : ∀ feat, Dec feat p13 21 (FV7z.mk .neg 64 [gr 64 10] 3) := by dec_rfl
theorem p13_24 : ∀ feat, Dec feat p13 24 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 14) (some 0) 1 31 0)] 5) := by dec_rfl
theorem p13_29 : ∀ feat, Dec feat p13 29 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p13_32 : ∀ feat, Dec feat p13 32 (FV7z.mk .test 8 [.mem (mg (some 3) none 1 4 8), .imm 8 2] 4) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.lea 64 0 (some 14) none 1 18446744073709551615,
  Op.mov 64 15 (.r 10),
  Op.mov 64 10 (.r 14),
  Op.st 64 (some 4) none 1 0 0,
  Op.lda 64 0 7940520,
  Op.neg 64 10,
  Op.lea 64 6 (some 14) (some 0) 1 31,
  Op.add 64 6 (.r 5),
  Op.testmi 8 (some 3) none 1 4 2]

theorem b13 (prof : Profile) : BlkA prof p13 (0x630698 : Addr) 0 36 o13 :=
  .cons (p13_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p13_4 _) ((OpI.mov (.r 10) (.inr rfl)).at _) (by decide) <|
  .cons (p13_7 _) ((OpI.mov (.r 14) (.inr rfl)).at _) (by decide) <|
  .cons (p13_10 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p13_14 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p13_21 _) ((OpI.neg (.inr rfl)).at _) (by decide) <|
  .cons (p13_24 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p13_29 _) ((OpI.add (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p13_32 _) ((OpI.testmi8).at _) (by decide) <|
  .nil 36

def j8 : List Byte := [0x0f, 0x85, 0x9e, 0x00, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 158] 6) := by dec_rfl

/-- The stretch at `866`. -/
def p14 : List Byte := [
  0x4c, 0x29, 0xe6, 0x4c, 0x21, 0xd6, 0x49, 0x89, 0xf6]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .sub 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .and 64 [gr 64 6, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p14_6 : ∀ feat, Dec feat p14 6 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.sub 64 6 (.r 12),
  Op.and 64 6 (.r 10),
  Op.mov 64 14 (.r 6)]

theorem b14 (prof : Profile) : Blk prof p14 0 9 o14 :=
  .cons (p14_0 _) (OpI.sub (.r 12) (.inr rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.and (.r 10) (.inr rfl)) (by decide) <|
  .cons (p14_6 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 9

def j9 : List Byte := [0x0f, 0x8e, 0x8c, 0x01, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 14) 64 [.rel 396] 6) := by dec_rfl

/-- The stretch at `881`. -/
def p15 : List Byte := [
  0x4c, 0x89, 0x54, 0x24, 0x10, 0x4c, 0x89, 0xf7, 0x4c, 0x89, 0x5c, 0x24, 0x08]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 10] 5) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 11] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.st 64 (some 4) none 1 16 10,
  Op.mov 64 7 (.r 14),
  Op.st 64 (some 4) none 1 8 11]

theorem b15 (prof : Profile) : Blk prof p15 0 13 o15 :=
  .cons (p15_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p15_5 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p15_8 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 13

/-- The stretch at `900`. -/
def p16 : List Byte := [
  0x49, 0x89, 0xc0, 0x90, 0x48, 0x85, 0xc0, 0x4c, 0x8b, 0x5c, 0x24, 0x08, 0x4c, 0x8b, 0x54, 0x24,
  0x10]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p16_7 : ∀ feat, Dec feat p16 7 (FV7z.mk .mov 64 [gr 64 11, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p16_12 : ∀ feat, Dec feat p16 12 (FV7z.mk .mov 64 [gr 64 10, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 64 8 (.r 0),
  Op.nop,
  Op.test 64 0 (.r 0),
  Op.ld 64 11 (some 4) none 1 8,
  Op.ld 64 10 (some 4) none 1 16]

theorem b16 (prof : Profile) : Blk prof p16 0 17 o16 :=
  .cons (p16_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.nop) (by decide) <|
  .cons (p16_4 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .cons (p16_7 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_12 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 17

def j10 : List Byte := [0x0f, 0x84, 0x55, 0x01, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 341] 6) := by dec_rfl

/-- The stretch at `923`. -/
def p17 : List Byte := [
  0x48, 0x8b, 0x05, 0x5e, 0x3e, 0x17, 0x00, 0x48, 0x85, 0xc0]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1523294 64)] 7) := by dec_rfl
theorem p17_7 : ∀ feat, Dec feat p17 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.lda 64 0 8013152,
  Op.test 64 0 (.r 0)]

theorem b17 (prof : Profile) : BlkA prof p17 (0x6306fb : Addr) 0 10 o17 :=
  .cons (p17_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p17_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j11 : List Byte := [0x0f, 0x85, 0x4d, 0x03, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 5) 64 [.rel 845] 6) := by dec_rfl

/-- The stretch at `939`. -/
def p18 : List Byte := [
  0x48, 0x8b, 0x0d, 0xb6, 0x2b, 0x16, 0x00, 0x48, 0x8b, 0x05, 0xcf, 0x22, 0x16, 0x00, 0xbf, 0x01,
  0x00, 0x00, 0x00, 0x4c, 0x01, 0xf1, 0x48, 0x85, 0xc0]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mrip 1452982 64)] 7) := by dec_rfl
theorem p18_7 : ∀ feat, Dec feat p18 7 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1450703 64)] 7) := by dec_rfl
theorem p18_14 : ∀ feat, Dec feat p18 14 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p18_19 : ∀ feat, Dec feat p18 19 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p18_22 : ∀ feat, Dec feat p18 22 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.lda 64 1 7942856,
  Op.lda 64 0 7940584,
  Op.mov 32 7 (.i 1),
  Op.add 64 1 (.r 14),
  Op.test 64 0 (.r 0)]

theorem b18 (prof : Profile) : BlkA prof p18 (0x63070b : Addr) 0 25 o18 :=
  .cons (p18_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p18_7 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p18_14 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p18_19 _) ((OpI.add (.r 14) (.inr rfl)).at _) (by decide) <|
  .cons (p18_22 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 25

def j12 : List Byte := [0x0f, 0x84, 0x50, 0x01, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 336] 6) := by dec_rfl

/-- The stretch at `972`. -/
def p19 : List Byte := [
  0x48, 0x89, 0x0d, 0x95, 0x2b, 0x16, 0x00, 0x4d, 0x39, 0xc3]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [.mem (mrip 1452949 64), gr 64 1] 7) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .cmp 64 [gr 64 11, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.sta 64 7942856 1,
  Op.cmp 64 11 (.r 8)]

theorem b19 (prof : Profile) : BlkA prof p19 (0x63072c : Addr) 0 10 o19 :=
  .cons (p19_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p19_7 _) ((OpI.cmp (.r 8) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j13 : List Byte := [0x0f, 0x85, 0x44, 0x02, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 5) 64 [.rel 580] 6) := by dec_rfl

/-- The stretch at `1306`. -/
def p20 : List Byte := [
  0x4c, 0x89, 0x05, 0x67, 0x21, 0x16, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [.mem (mrip 1450343 64), gr 64 8] 7) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.sta 64 7940584 8]

theorem b20 (prof : Profile) : BlkA prof p20 (0x63087a : Addr) 0 7 o20 :=
  .cons (p20_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 7

def j14 : List Byte := [0xe9, 0xa6, 0xfe, 0xff, 0xff]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk .jmp 64 [.rel 18446744073709551270] 5) := by dec_rfl

/-- The stretch at `1450`. -/
def p21 : List Byte := [
  0x4c, 0x29, 0xc0, 0x4c, 0x89, 0x05, 0x8c, 0x21, 0x16, 0x00, 0x4c, 0x01, 0xf0, 0x48, 0x83, 0xc8,
  0x01, 0x49, 0x89, 0x40, 0x08, 0x48, 0x89, 0x0d, 0xa2, 0x29, 0x16, 0x00, 0x4d, 0x85, 0xe4]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p21_3 : ∀ feat, Dec feat p21 3 (FV7z.mk .mov 64 [.mem (mrip 1450380 64), gr 64 8] 7) := by dec_rfl
theorem p21_10 : ∀ feat, Dec feat p21 10 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p21_13 : ∀ feat, Dec feat p21 13 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p21_17 : ∀ feat, Dec feat p21 17 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p21_21 : ∀ feat, Dec feat p21 21 (FV7z.mk .mov 64 [.mem (mrip 1452450 64), gr 64 1] 7) := by dec_rfl
theorem p21_28 : ∀ feat, Dec feat p21 28 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.sub 64 0 (.r 8),
  Op.sta 64 7940768 8,
  Op.add 64 0 (.r 14),
  Op.or 64 0 (.i 1),
  Op.st 64 (some 8) none 1 8 0,
  Op.sta 64 7942856 1,
  Op.test 64 12 (.r 12)]

theorem b21 (prof : Profile) : BlkA prof p21 (0x63090a : Addr) 0 31 o21 :=
  .cons (p21_0 _) ((OpI.sub (.r 8) (.inr rfl)).at _) (by decide) <|
  .cons (p21_3 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p21_10 _) ((OpI.add (.r 14) (.inr rfl)).at _) (by decide) <|
  .cons (p21_13 _) ((OpI.or (.i 1) (.inr rfl)).at _) (by decide) <|
  .cons (p21_17 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p21_21 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p21_28 _) ((OpI.test (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 31

def j15 : List Byte := [0x0f, 0x84, 0x59, 0xfb, 0xff, 0xff]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709550425] 6) := by dec_rfl

/-- The stretch at `1568`. -/
def p22 : List Byte := [
  0xf6, 0x05, 0xbd, 0x20, 0x16, 0x00, 0x02]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .test 8 [.mem (mrip 1450173 8), .imm 8 2] 7) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.testmia 8 7940676 2]

theorem b22 (prof : Profile) : BlkA prof p22 (0x630980 : Addr) 0 7 o22 :=
  .cons (p22_0 _) (OpIA.testmi8_rip (by decide)) (by decide) <|
  .nil 7

def j16 : List Byte := [0x0f, 0x85, 0xa6, 0x01, 0x00, 0x00]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 5) 64 [.rel 422] 6) := by dec_rfl

def j17 : List Byte := [0x74, 0x1e]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 4) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `1616`. -/
def p23 : List Byte := [
  0x4c, 0x89, 0xc0, 0x83, 0xe0, 0x0f]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p23_3 : ∀ feat, Dec feat p23 3 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.mov 64 0 (.r 8),
  Op.and 32 0 (.i 15)]

theorem b23 (prof : Profile) : Blk prof p23 0 6 o23 :=
  .cons (p23_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p23_3 _) (OpI.and (.i 15) (.inl rfl)) (by decide) <|
  .nil 6

def j18 : List Byte := [0x74, 0x68]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 4) 64 [.rel 104] 2) := by dec_rfl

/-- The stretch at `1624`. -/
def p24 : List Byte := [
  0xb9, 0x10, 0x00, 0x00, 0x00, 0x48, 0x29, 0xc1, 0x49, 0x8d, 0x04, 0x08, 0x4c, 0x01, 0xe1, 0x48,
  0x89, 0x44, 0x24, 0x08]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p24_5 : ∀ feat, Dec feat p24 5 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p24_8 : ∀ feat, Dec feat p24 8 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 8) (some 1) 1 0 0)] 4) := by dec_rfl
theorem p24_12 : ∀ feat, Dec feat p24 12 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p24_15 : ∀ feat, Dec feat p24 15 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.mov 32 1 (.i 16),
  Op.sub 64 1 (.r 0),
  Op.lea 64 0 (some 8) (some 1) 1 0,
  Op.add 64 1 (.r 12),
  Op.st 64 (some 4) none 1 8 0]

theorem b24 (prof : Profile) : Blk prof p24 0 20 o24 :=
  .cons (p24_0 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .cons (p24_5 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .cons (p24_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p24_12 _) (OpI.add (.r 12) (.inr rfl)) (by decide) <|
  .cons (p24_15 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 20

/-- The stretch at `1644`. -/
def p25 : List Byte := [
  0x4a, 0x8d, 0x34, 0x31, 0x48, 0x8b, 0x3c, 0x24, 0x49, 0x8d, 0x14, 0x30, 0x48, 0x01, 0xd7, 0x48,
  0x29, 0xd1, 0x48, 0x89, 0xf8, 0x4c, 0x21, 0xd0, 0x48, 0x8d, 0x3c, 0x08, 0x49, 0x89, 0xfe, 0x48,
  0x85, 0xff]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 1) (some 14) 1 0 0)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p25_8 : ∀ feat, Dec feat p25 8 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 8) (some 6) 1 0 0)] 4) := by dec_rfl
theorem p25_12 : ∀ feat, Dec feat p25 12 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p25_15 : ∀ feat, Dec feat p25 15 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p25_18 : ∀ feat, Dec feat p25 18 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p25_21 : ∀ feat, Dec feat p25 21 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem p25_24 : ∀ feat, Dec feat p25 24 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 0) (some 1) 1 0 0)] 4) := by dec_rfl
theorem p25_28 : ∀ feat, Dec feat p25 28 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p25_31 : ∀ feat, Dec feat p25 31 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.lea 64 6 (some 1) (some 14) 1 0,
  Op.ld 64 7 (some 4) none 1 0,
  Op.lea 64 2 (some 8) (some 6) 1 0,
  Op.add 64 7 (.r 2),
  Op.sub 64 1 (.r 2),
  Op.mov 64 0 (.r 7),
  Op.and 64 0 (.r 10),
  Op.lea 64 7 (some 0) (some 1) 1 0,
  Op.mov 64 14 (.r 7),
  Op.test 64 7 (.r 7)]

theorem b25 (prof : Profile) : Blk prof p25 0 34 o25 :=
  .cons (p25_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p25_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p25_12 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p25_15 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p25_18 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p25_21 _) (OpI.and (.r 10) (.inr rfl)) (by decide) <|
  .cons (p25_24 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p25_28 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p25_31 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 34

def j19 : List Byte := [0x0f, 0x88, 0x68, 0x01, 0x00, 0x00]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 8) 64 [.rel 360] 6) := by dec_rfl

/-- The stretch at `1690`. -/
def p26 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b26 (prof : Profile) : Blk prof p26 0 3 o26 :=
  .cons (p26_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j20 : List Byte := [0x74, 0x31]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 4) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `1695`. -/
def p27 : List Byte := [
  0x48, 0x8b, 0x15, 0x5a, 0x3b, 0x17, 0x00, 0x48, 0x85, 0xd2]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip 1522522 64)] 7) := by dec_rfl
theorem p27_7 : ∀ feat, Dec feat p27 7 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.lda 64 2 8013152,
  Op.test 64 2 (.r 2)]

theorem b27 (prof : Profile) : BlkA prof p27 (0x6309ff : Addr) 0 10 o27 :=
  .cons (p27_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p27_7 _) ((OpI.test (.r 2) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j21 : List Byte := [0x75, 0x6d]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 5) 64 [.rel 109] 2) := by dec_rfl

/-- The stretch at `1707`. -/
def p28 : List Byte := [
  0x48, 0x8b, 0x0d, 0xb6, 0x28, 0x16, 0x00, 0x4c, 0x8b, 0x44, 0x24, 0x08, 0x4c, 0x01, 0xf1]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mrip 1452214 64)] 7) := by dec_rfl
theorem p28_7 : ∀ feat, Dec feat p28 7 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p28_12 : ∀ feat, Dec feat p28 12 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.lda 64 1 7942856,
  Op.ld 64 8 (some 4) none 1 8,
  Op.add 64 1 (.r 14)]

theorem b28 (prof : Profile) : BlkA prof p28 (0x630a0b : Addr) 0 15 o28 :=
  .cons (p28_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p28_7 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p28_12 _) ((OpI.add (.r 14) (.inr rfl)).at _) (by decide) <|
  .nil 15

def j22 : List Byte := [0xe9, 0xeb, 0xfe, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 18446744073709551339] 5) := by dec_rfl

/-- The stretch at `1728`. -/
def p29 : List Byte := [
  0x4c, 0x89, 0x44, 0x24, 0x08, 0x4c, 0x89, 0xe1]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 8] 5) := by dec_rfl
theorem p29_5 : ∀ feat, Dec feat p29 5 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.st 64 (some 4) none 1 8 8,
  Op.mov 64 1 (.r 12)]

theorem b29 (prof : Profile) : Blk prof p29 0 8 o29 :=
  .cons (p29_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p29_5 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 8

def j23 : List Byte := [0xeb, 0xa2]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk .jmp 64 [.rel 18446744073709551522] 2) := by dec_rfl

end FV7z.Smm
