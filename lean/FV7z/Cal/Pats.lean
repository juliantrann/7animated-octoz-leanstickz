import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps17
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps13
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_calloc` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 27 of them) and each distinct jump (`j*`, 23) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cal
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x48, 0x89, 0xf8, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec,
  0x08, 0x48, 0xf7, 0xe6, 0x49, 0x89, 0xc4, 0x0f, 0x90, 0xc0, 0x4d, 0x85, 0xe4]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mul 64 [gr 64 6] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk (.setcc 0) 8 [gr 8 0] 3) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 64 0 (.r 7),
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.mul64 6,
  Op.mov 64 12 (.r 0),
  Op.setcc 0 0,
  Op.test 64 12 (.r 12)]

theorem b0 (prof : Profile) : Blk prof p0 0 29 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_12 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_17 _) (OpI.mul64) (by decide) <|
  .cons (p0_20 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p0_23 _) (OpI.setcc) (by decide) <|
  .cons (p0_26 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 29

def j0 : List Byte := [0x0f, 0x88, 0x6d, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 8) 64 [.rel 365] 6) := by dec_rfl

/-- The stretch at `35`. -/
def p1 : List Byte := [
  0x0f, 0xb6, 0xc0, 0x48, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .movzx 32 [gr 32 0, gr 8 0] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.zxr 0 0,
  Op.test 64 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.zxr) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x0f, 0x85, 0x61, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 353] 6) := by dec_rfl

/-- The stretch at `47`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x05, 0x9a, 0xdf, 0x15, 0x00, 0x48, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1433498 64)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lda 64 0 7940656,
  Op.test 64 0 (.r 0)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x634a8f : Addr) 0 10 o2 :=
  .cons (p2_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j2 : List Byte := [0x0f, 0x85, 0x81, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 385] 6) := by dec_rfl

/-- The stretch at `63`. -/
def p3 : List Byte := [
  0x64, 0x48, 0x83, 0x3c, 0x25, 0xd8, 0xff, 0xff, 0xff, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [.mem (mf none none 1 18446744073709551576 64), .imm 64 0] 10) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.cmpmif fb 64 none none 1 18446744073709551576 0]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x634a9f : Addr) fb 0 10 (o3 fb) :=
  .cons (p3_0 _) (OpIF.cmpmif (.inr rfl)) (by decide) <|
  .nil 10

def j3 : List Byte := [0x0f, 0x84, 0xf1, 0x01, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 497] 6) := by dec_rfl

/-- The stretch at `79`. -/
def p4 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x634aaf : Addr) fb 0 10 (o4 fb) :=
  .cons (p4_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p4_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 10

def j4 : List Byte := [0x0f, 0x85, 0x01, 0x02, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 513] 6) := by dec_rfl

/-- The stretch at `95`. -/
def p5 : List Byte := [
  0x4c, 0x8b, 0x2d, 0xda, 0xdf, 0x15, 0x00, 0x48, 0x8d, 0x2d, 0x73, 0xdf, 0x15, 0x00, 0x49, 0x8b,
  0x5d, 0x08, 0x48, 0x83, 0xe3, 0xf8]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 13, .mem (mrip 1433562 64)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .lea 64 [gr 64 5, .mem (mrip 1433459 0)] 7) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 13) none 1 8 64)] 4) := by dec_rfl
theorem p5_18 : ∀ feat, Dec feat p5 18 (FV7z.mk .and 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lda 64 13 7940768,
  Op.mov 64 5 (.i 7940672),
  Op.ld 64 3 (some 13) none 1 8,
  Op.and 64 3 (.i 18446744073709551608)]

theorem b5 (prof : Profile) : BlkA prof p5 (0x634abf : Addr) 0 22 o5 :=
  .cons (p5_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p5_7 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_14 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p5_18 _) ((OpI.and (.i 18446744073709551608) (.inr rfl)).at _) (by decide) <|
  .nil 22

/-- The stretch at `117`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xe6, 0x48, 0x89, 0xef]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 6 (.r 12),
  Op.mov 64 7 (.r 5)]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `128`. -/
def p7 : List Byte := [
  0x49, 0x89, 0xc0, 0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 8 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j5 : List Byte := [0x74, 0x0c]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `136`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x40, 0xf8, 0xa8, 0x02]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 18446744073709551608 64)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 0 (some 0) none 1 18446744073709551608,
  Op.test 8 0 (.i 2)]

theorem b8 (prof : Profile) : Blk prof p8 0 6 o8 :=
  .cons (p8_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x0f, 0x84, 0x9c, 0x00, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 156] 6) := by dec_rfl

/-- The stretch at `148`. -/
def p9 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b9 (prof : Profile) (fb : Addr) : BlkF prof p9 (0x634af4 : Addr) fb 0 10 (o9 fb) :=
  .cons (p9_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p9_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 10

def j7 : List Byte := [0x0f, 0x85, 0x4c, 0x01, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 332] 6) := by dec_rfl

/-- The stretch at `164`. -/
def p10 : List Byte := [
  0x4d, 0x85, 0xc0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.test 64 8 (.r 8)]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.test (.r 8) (.inr rfl)) (by decide) <|
  .nil 3

def j8 : List Byte := [0x0f, 0x84, 0x03, 0x01, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 259] 6) := by dec_rfl

/-- The stretch at `173`. -/
def p11 : List Byte := [
  0x49, 0x8b, 0x50, 0xf8, 0x8b, 0x05, 0x8d, 0xfa, 0x16, 0x00, 0xf6, 0xc2, 0x02]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 8) none 1 18446744073709551608 64)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1505933 32)] 6) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 2 (some 8) none 1 18446744073709551608,
  Op.lda 32 0 8013220,
  Op.test 8 2 (.i 2)]

theorem b11 (prof : Profile) : BlkA prof p11 (0x634b0d : Addr) 0 13 o11 :=
  .cons (p11_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p11_4 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p11_10 _) ((OpI.test8 (.i 2)).at _) (by decide) <|
  .nil 13

def j9 : List Byte := [0x74, 0x1c]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `188`. -/
def p12 : List Byte := [
  0x85, 0xc0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b12 (prof : Profile) : Blk prof p12 0 2 o12 :=
  .cons (p12_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j10 : List Byte := [0x0f, 0x85, 0x1c, 0x02, 0x00, 0x00]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 540] 6) := by dec_rfl

/-- The stretch at `196`. -/
def p13 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xc0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p13_8 : ∀ feat, Dec feat p13 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p13_9 : ∀ feat, Dec feat p13 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b13 (prof : Profile) : Blk prof p13 0 13 o13 :=
  .cons (p13_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p13_7 _) (OpI.pop) (by decide) <|
  .cons (p13_8 _) (OpI.pop) (by decide) <|
  .cons (p13_9 _) (OpI.pop) (by decide) <|
  .cons (p13_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `216`. -/
def p14 : List Byte := [
  0x48, 0x83, 0xe2, 0xf8, 0x85, 0xc0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.and 64 2 (.i 18446744073709551608),
  Op.test 32 0 (.r 0)]

theorem b14 (prof : Profile) : Blk prof p14 0 6 o14 :=
  .cons (p14_0 _) (OpI.and (.i 18446744073709551608) (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

def j11 : List Byte := [0x0f, 0x84, 0x8c, 0x00, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 140] 6) := by dec_rfl

/-- The stretch at `228`. -/
def p15 : List Byte := [
  0x48, 0x83, 0xea, 0x08, 0x48, 0x83, 0xfa, 0x17]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 23)] 4) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.sub 64 2 (.i 8),
  Op.cmp 64 2 (.i 23)]

theorem b15 (prof : Profile) : Blk prof p15 0 8 o15 :=
  .cons (p15_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.cmp (.i 23) (.inr rfl)) (by decide) <|
  .nil 8

def j12 : List Byte := [0x0f, 0x86, 0x74, 0x02, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 6) 64 [.rel 628] 6) := by dec_rfl

/-- The stretch at `242`. -/
def p16 : List Byte := [
  0x48, 0x83, 0xfa, 0x4f]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 79)] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.cmp 64 2 (.i 79)]

theorem b16 (prof : Profile) : Blk prof p16 0 4 o16 :=
  .cons (p16_0 _) (OpI.cmp (.i 79) (.inr rfl)) (by decide) <|
  .nil 4

def j13 : List Byte := [0x0f, 0x87, 0xcc, 0x01, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 7) 64 [.rel 460] 6) := by dec_rfl

/-- The stretch at `256`. -/
def p17 : List Byte := [
  0x49, 0xc7, 0x40, 0x10, 0x00, 0x00, 0x00, 0x00]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 16 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.sti 64 (some 8) none 1 16 0]

theorem b17 (prof : Profile) : Blk prof p17 0 8 o17 :=
  .cons (p17_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `268`. -/
def p18 : List Byte := [
  0x48, 0x83, 0xfa, 0x27]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 39)] 4) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmp 64 2 (.i 39)]

theorem b18 (prof : Profile) : Blk prof p18 0 4 o18 :=
  .cons (p18_0 _) (OpI.cmp (.i 39) (.inr rfl)) (by decide) <|
  .nil 4

def j14 : List Byte := [0x76, 0xb2]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551538] 2) := by dec_rfl

/-- The stretch at `279`. -/
def p19 : List Byte := [
  0x48, 0x83, 0xfa, 0x37]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 55)] 4) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmp 64 2 (.i 55)]

theorem b19 (prof : Profile) : Blk prof p19 0 4 o19 :=
  .cons (p19_0 _) (OpI.cmp (.i 55) (.inr rfl)) (by decide) <|
  .nil 4

def j15 : List Byte := [0x76, 0xa7]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551527] 2) := by dec_rfl

/-- The stretch at `290`. -/
def p20 : List Byte := [
  0x48, 0x83, 0xfa, 0x47]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 71)] 4) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.cmp 64 2 (.i 71)]

theorem b20 (prof : Profile) : Blk prof p20 0 4 o20 :=
  .cons (p20_0 _) (OpI.cmp (.i 71) (.inr rfl)) (by decide) <|
  .nil 4

def j16 : List Byte := [0x76, 0x9c]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551516] 2) := by dec_rfl

def j17 : List Byte := [0xeb, 0x95]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551509] 2) := by dec_rfl

/-- The stretch at `304`. -/
def p21 : List Byte := [
  0x48, 0x8d, 0x15, 0xa9, 0xde, 0x15, 0x00, 0xa8, 0x04]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1433257 0)] 7) := by dec_rfl
theorem p21_7 : ∀ feat, Dec feat p21 7 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 4)] 2) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.mov 64 2 (.i 7940672),
  Op.test 8 0 (.i 4)]

theorem b21 (prof : Profile) : BlkA prof p21 (0x634b90 : Addr) 0 9 o21 :=
  .cons (p21_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p21_7 _) ((OpI.test8 (.i 4)).at _) (by decide) <|
  .nil 9

def j18 : List Byte := [0x74, 0x0d]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 4) 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `328`. -/
def p22 : List Byte := [
  0x48, 0x39, 0xea]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.cmp 64 2 (.r 5)]

theorem b22 (prof : Profile) : Blk prof p22 0 3 o22 :=
  .cons (p22_0 _) (OpI.cmp (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j19 : List Byte := [0x0f, 0x84, 0x43, 0xff, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551427] 6) := by dec_rfl

/-- The stretch at `368`. -/
def p23 : List Byte := [
  0x49, 0x8d, 0x40, 0xf0, 0x49, 0x39, 0xc5]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 8) none 1 18446744073709551600 0)] 4) := by dec_rfl
theorem p23_4 : ∀ feat, Dec feat p23 4 (FV7z.mk .cmp 64 [gr 64 13, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.lea 64 0 (some 8) none 1 18446744073709551600,
  Op.cmp 64 13 (.r 0)]

theorem b23 (prof : Profile) : Blk prof p23 0 7 o23 :=
  .cons (p23_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p23_4 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

def j20 : List Byte := [0x0f, 0x85, 0x67, 0xff, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551463] 6) := by dec_rfl

/-- The stretch at `381`. -/
def p24 : List Byte := [
  0x48, 0x39, 0xd3, 0x48, 0x0f, 0x42, 0xd3]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p24_3 : ∀ feat, Dec feat p24 3 (FV7z.mk (.cmovcc 2) 64 [gr 64 2, gr 64 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.cmp 64 3 (.r 2),
  Op.cmov64 2 2 3]

theorem b24 (prof : Profile) : Blk prof p24 0 7 o24 :=
  .cons (p24_0 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .cons (p24_3 _) (OpI.cmov64) (by decide) <|
  .nil 7

def j21 : List Byte := [0xe9, 0x5b, 0xff, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk .jmp 64 [.rel 18446744073709551451] 5) := by dec_rfl

/-- The stretch at `712`. -/
def p25 : List Byte := [
  0x4c, 0x89, 0xc7, 0x31, 0xf6]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p25_3 : ∀ feat, Dec feat p25 3 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 64 7 (.r 8),
  Op.xor 32 6 (.r 6)]

theorem b25 (prof : Profile) : Blk prof p25 0 5 o25 :=
  .cons (p25_0 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p25_3 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `722`. -/
def p26 : List Byte := [
  0x49, 0x89, 0xc0]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.mov 64 8 (.r 0)]

theorem b26 (prof : Profile) : Blk prof p26 0 3 o26 :=
  .cons (p26_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j22 : List Byte := [0xe9, 0xea, 0xfd, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 18446744073709551082] 5) := by dec_rfl

end FV7z.Cal
