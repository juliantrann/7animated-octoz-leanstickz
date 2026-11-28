import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CExtractCallbackConsole::ExtractResult` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 34 of them) and each distinct jump (`j*`, 23) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Exr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x41, 0x89, 0xf4, 0x55, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x8d,
  0x3d, 0xcb, 0x6d, 0x1b, 0x00, 0x48, 0x83, 0xec, 0x20, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00,
  0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 6)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1797579 0)] 7) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 32 12 (.r 6),
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.mov 64 7 (.i 7991456),
  Op.sub 64 4 (.i 32),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5e82c0 : Addr) fb 0 41 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) ((OpIA.lea_rip (by decide)).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.sub (.i 32) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_25 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_34 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_39 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 41

/-- The stretch at `46`. -/
def p1 : List Byte := [
  0x48, 0x83, 0x7b, 0x68, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [.mem (mg (some 3) none 1 104 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmi 64 (some 3) none 1 104 0]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 5

def j0 : List Byte := [0x74, 0x0a]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `53`. -/
def p2 : List Byte := [
  0x80, 0x7b, 0x70, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [.mem (mg (some 3) none 1 112 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 8 (some 3) none 1 112 0]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x0f, 0x84, 0x51, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 337] 6) := by dec_rfl

/-- The stretch at `63`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0xbb, 0x08, 0x01, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 7 (some 3) none 1 264,
  Op.test 64 7 (.r 7)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p4 : List Byte := [
  0x45, 0x85, 0xe4]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 12 (.r 12)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x0f, 0x85, 0x97, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 151] 6) := by dec_rfl

/-- The stretch at `89`. -/
def p5 : List Byte := [
  0x48, 0x83, 0xbb, 0xc0, 0x01, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 64 [.mem (mg (some 3) none 1 448 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmpmi 64 (some 3) none 1 448 0]

theorem b5 (prof : Profile) : Blk prof p5 0 8 o5 :=
  .cons (p5_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 8

def j4 : List Byte := [0x0f, 0x84, 0x61, 0x01, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 353] 6) := by dec_rfl

/-- The stretch at `103`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0xbb, 0x08, 0x01, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 7 (some 3) none 1 264]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `118`. -/
def p7 : List Byte := [
  0x48, 0x85, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x74, 0x2c]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 44] 2) := by dec_rfl

def j6 : List Byte := [0x0f, 0x85, 0x9a, 0x01, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 410] 6) := by dec_rfl

def j7 : List Byte := [0x74, 0x0d]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `154`. -/
def p8 : List Byte := [
  0x80, 0xbb, 0x3f, 0x01, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 8 [.mem (mg (some 3) none 1 319 8), .imm 8 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmpmi 8 (some 3) none 1 319 0]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j8 : List Byte := [0x0f, 0x85, 0xdd, 0x00, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 221] 6) := by dec_rfl

/-- The stretch at `167`. -/
def p9 : List Byte := [
  0x48, 0xc7, 0xc0, 0x88, 0xf0, 0x79, 0x00, 0x83, 0x38, 0x01, 0x45, 0x19, 0xe4, 0x41, 0xf7, 0xd4,
  0x41, 0x81, 0xe4, 0x04, 0x40, 0x00, 0x80]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7991432)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .cmp 32 [.mem (mg (some 0) none 1 0 32), .imm 32 1] 3) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .sbb 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p9_13 : ∀ feat, Dec feat p9 13 (FV7z.mk .not 32 [gr 32 12] 3) := by dec_rfl
theorem p9_16 : ∀ feat, Dec feat p9 16 (FV7z.mk .and 32 [gr 32 12, Src.opd 32 (.i 2147500036)] 7) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 0 (.i 7991432),
  Op.cmpmi 32 (some 0) none 1 0 1,
  Op.sbb 32 12 (.r 12),
  Op.not32 12,
  Op.and 32 12 (.i 2147500036)]

theorem b9 (prof : Profile) : Blk prof p9 0 23 o9 :=
  .cons (p9_0 _) (OpI.mov (.i 7991432) (.inr rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .cons (p9_10 _) (OpI.sbb (.r 12) (.inl rfl)) (by decide) <|
  .cons (p9_13 _) (OpI.not32) (by decide) <|
  .cons (p9_16 _) (OpI.and (.i 2147500036) (.inl rfl)) (by decide) <|
  .nil 23

/-- The stretch at `190`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0x3d, 0x1b, 0x6d, 0x1b, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1797403 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 7 (.i 7991456)]

theorem b10 (prof : Profile) : BlkA prof p10 (0x5e837e : Addr) 0 7 o10 :=
  .cons (p10_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `202`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o11 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b11 (prof : Profile) (fb : Addr) : BlkF prof p11 (0x5e838a : Addr) fb 0 14 (o11 fb) :=
  .cons (p11_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p11_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j9 : List Byte := [0x0f, 0x85, 0xb9, 0x01, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 441] 6) := by dec_rfl

/-- The stretch at `222`. -/
def p12 : List Byte := [
  0x48, 0x83, 0xc4, 0x20, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p12_9 : ∀ feat, Dec feat p12 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.add 64 4 (.i 32),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b12 (prof : Profile) : Blk prof p12 0 11 o12 :=
  .cons (p12_0 _) (OpI.add (.i 32) (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p12_7 _) (OpI.pop) (by decide) <|
  .cons (p12_8 _) (OpI.pop) (by decide) <|
  .cons (p12_9 _) (OpI.pop) (by decide) <|
  .nil 11

/-- The stretch at `240`. -/
def p13 : List Byte := [
  0x41, 0x81, 0xfc, 0x04, 0x40, 0x00, 0x80]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 2147500036)] 7) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmp 32 12 (.i 2147500036)]

theorem b13 (prof : Profile) : Blk prof p13 0 7 o13 :=
  .cons (p13_0 _) (OpI.cmp (.i 2147500036) (.inl rfl)) (by decide) <|
  .nil 7

def j10 : List Byte := [0x74, 0xc5]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551557] 2) := by dec_rfl

/-- The stretch at `249`. -/
def p14 : List Byte := [
  0x41, 0x81, 0xfc, 0x1c, 0x00, 0x00, 0x88]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 2281701404)] 7) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 32 12 (.i 2281701404)]

theorem b14 (prof : Profile) : Blk prof p14 0 7 o14 :=
  .cons (p14_0 _) (OpI.cmp (.i 2281701404) (.inl rfl)) (by decide) <|
  .nil 7

def j11 : List Byte := [0x74, 0xbc]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551548] 2) := by dec_rfl

/-- The stretch at `258`. -/
def p15 : List Byte := [
  0x48, 0x8b, 0xab, 0x10, 0x01, 0x00, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 272 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.ld 64 5 (some 3) none 1 272]

theorem b15 (prof : Profile) : Blk prof p15 0 7 o15 :=
  .cons (p15_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `273`. -/
def p16 : List Byte := [
  0x48, 0x85, 0xed]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b16 (prof : Profile) : Blk prof p16 0 3 o16 :=
  .cons (p16_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j12 : List Byte := [0x74, 0x91]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551505] 2) := by dec_rfl

/-- The stretch at `278`. -/
def p17 : List Byte := [
  0x48, 0x89, 0xef]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b17 (prof : Profile) : Blk prof p17 0 3 o17 :=
  .cons (p17_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `286`. -/
def p18 : List Byte := [
  0x48, 0x8b, 0x4d, 0x00, 0xba, 0x07, 0x00, 0x00, 0x00, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d,
  0x3d, 0x3d, 0x17, 0x10, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 7)] 5) := by dec_rfl
theorem p18_9 : ∀ feat, Dec feat p18 9 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p18_14 : ∀ feat, Dec feat p18 14 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1054525 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.ld 64 1 (some 5) none 1 0,
  Op.mov 32 2 (.i 7),
  Op.mov 32 6 (.i 1),
  Op.mov 64 7 (.i 7248688)]

theorem b18 (prof : Profile) : BlkA prof p18 (0x5e83de : Addr) 0 21 o18 :=
  .cons (p18_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p18_4 _) ((OpI.mov (.i 7) (.inl rfl)).at _) (by decide) <|
  .cons (p18_9 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p18_14 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 21

/-- The stretch at `312`. -/
def p19 : List Byte := [
  0x48, 0x8b, 0xab, 0x10, 0x01, 0x00, 0x00, 0x41, 0x81, 0xfc, 0x0e, 0x00, 0x07, 0x80]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 272 64)] 7) := by dec_rfl
theorem p19_7 : ∀ feat, Dec feat p19 7 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 2147942414)] 7) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 64 5 (some 3) none 1 272,
  Op.cmp 32 12 (.i 2147942414)]

theorem b19 (prof : Profile) : Blk prof p19 0 14 o19 :=
  .cons (p19_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p19_7 _) (OpI.cmp (.i 2147942414) (.inl rfl)) (by decide) <|
  .nil 14

def j13 : List Byte := [0x0f, 0x84, 0x2c, 0x01, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 300] 6) := by dec_rfl

/-- The stretch at `332`. -/
def p20 : List Byte := [
  0x48, 0x89, 0xe7, 0x44, 0x89, 0xe6]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 64 7 (.r 4),
  Op.mov 32 6 (.r 12)]

theorem b20 (prof : Profile) : Blk prof p20 0 6 o20 :=
  .cons (p20_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `343`. -/
def p21 : List Byte := [
  0x48, 0x8b, 0x34, 0x24, 0x48, 0x89, 0xef]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p21_4 : ∀ feat, Dec feat p21 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.ld 64 6 (some 4) none 1 0,
  Op.mov 64 7 (.r 5)]

theorem b21 (prof : Profile) : Blk prof p21 0 7 o21 :=
  .cons (p21_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p21_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `355`. -/
def p22 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x48, 0x85, 0xff]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p22_4 : ∀ feat, Dec feat p22 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b22 (prof : Profile) : Blk prof p22 0 7 o22 :=
  .cons (p22_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p22_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `369`. -/
def p23 : List Byte := [
  0x48, 0x8b, 0xbb, 0x10, 0x01, 0x00, 0x00]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 272 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.ld 64 7 (some 3) none 1 272]

theorem b23 (prof : Profile) : Blk prof p23 0 7 o23 :=
  .cons (p23_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 7

def j14 : List Byte := [0xe9, 0x19, 0xff, 0xff, 0xff]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk .jmp 64 [.rel 18446744073709551385] 5) := by dec_rfl

/-- The stretch at `400`. -/
def p24 : List Byte := [
  0x48, 0x8d, 0x7b, 0x30, 0xbe, 0x01, 0x00, 0x00, 0x00]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 48 0)] 4) := by dec_rfl
theorem p24_4 : ∀ feat, Dec feat p24 4 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.lea 64 7 (some 3) none 1 48,
  Op.mov 32 6 (.i 1)]

theorem b24 (prof : Profile) : Blk prof p24 0 9 o24 :=
  .cons (p24_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p24_4 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `414`. -/
def p25 : List Byte := [
  0x48, 0x8b, 0x43, 0x48, 0xc7, 0x43, 0x50, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x00, 0x00, 0x48, 0x8b,
  0x43, 0x58, 0xc7, 0x43, 0x60, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 72 64)] 4) := by dec_rfl
theorem p25_4 : ∀ feat, Dec feat p25 4 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 80 32), .imm 32 0] 7) := by dec_rfl
theorem p25_11 : ∀ feat, Dec feat p25 11 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p25_14 : ∀ feat, Dec feat p25 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 88 64)] 4) := by dec_rfl
theorem p25_18 : ∀ feat, Dec feat p25 18 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 96 32), .imm 32 0] 7) := by dec_rfl
theorem p25_25 : ∀ feat, Dec feat p25 25 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.ld 64 0 (some 3) none 1 72,
  Op.sti 32 (some 3) none 1 80 0,
  Op.sti 8 (some 0) none 1 0 0,
  Op.ld 64 0 (some 3) none 1 88,
  Op.sti 32 (some 3) none 1 96 0,
  Op.sti 32 (some 0) none 1 0 0]

theorem b25 (prof : Profile) : Blk prof p25 0 31 o25 :=
  .cons (p25_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_4 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p25_11 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p25_14 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p25_18 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p25_25 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 31

def j15 : List Byte := [0xe9, 0x7d, 0xfe, 0xff, 0xff]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 18446744073709551229] 5) := by dec_rfl

/-- The stretch at `456`. -/
def p26 : List Byte := [
  0x80, 0xbb, 0x3d, 0x01, 0x00, 0x00, 0x00]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .cmp 8 [.mem (mg (some 3) none 1 317 8), .imm 8 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.cmpmi 8 (some 3) none 1 317 0]

theorem b26 (prof : Profile) : Blk prof p26 0 7 o26 :=
  .cons (p26_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j16 : List Byte := [0x0f, 0x85, 0x92, 0xfe, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551250] 6) := by dec_rfl

/-- The stretch at `469`. -/
def p27 : List Byte := [
  0x80, 0xbb, 0x3e, 0x01, 0x00, 0x00, 0x00]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .cmp 8 [.mem (mg (some 3) none 1 318 8), .imm 8 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.cmpmi 8 (some 3) none 1 318 0]

theorem b27 (prof : Profile) : Blk prof p27 0 7 o27 :=
  .cons (p27_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j17 : List Byte := [0x0f, 0x84, 0x86, 0x00, 0x00, 0x00]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 4) 64 [.rel 134] 6) := by dec_rfl

/-- The stretch at `490`. -/
def p28 : List Byte := [
  0x48, 0x8b, 0xab, 0x08, 0x01, 0x00, 0x00, 0x48, 0x85, 0xed]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl
theorem p28_7 : ∀ feat, Dec feat p28 7 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.ld 64 5 (some 3) none 1 264,
  Op.test 64 5 (.r 5)]

theorem b28 (prof : Profile) : Blk prof p28 0 10 o28 :=
  .cons (p28_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p28_7 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 10

def j18 : List Byte := [0x0f, 0x84, 0xad, 0xfe, 0xff, 0xff]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551277] 6) := by dec_rfl

/-- The stretch at `506`. -/
def p29 : List Byte := [
  0x48, 0x8b, 0x4d, 0x00, 0xba, 0x10, 0x00, 0x00, 0x00, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d,
  0x3d, 0x70, 0x16, 0x10, 0x00]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p29_4 : ∀ feat, Dec feat p29 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p29_9 : ∀ feat, Dec feat p29 9 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p29_14 : ∀ feat, Dec feat p29 14 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1054320 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.ld 64 1 (some 5) none 1 0,
  Op.mov 32 2 (.i 16),
  Op.mov 32 6 (.i 1),
  Op.mov 64 7 (.i 7248703)]

theorem b29 (prof : Profile) : BlkA prof p29 (0x5e84ba : Addr) 0 21 o29 :=
  .cons (p29_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p29_4 _) ((OpI.mov (.i 16) (.inl rfl)).at _) (by decide) <|
  .cons (p29_9 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p29_14 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 21

def j19 : List Byte := [0xe9, 0x6d, 0xfe, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551213] 5) := by dec_rfl

/-- The stretch at `552`. -/
def p30 : List Byte := [
  0x48, 0x8b, 0xab, 0x08, 0x01, 0x00, 0x00, 0xba, 0x12, 0x00, 0x00, 0x00, 0xbe, 0x01, 0x00, 0x00,
  0x00, 0x48, 0x8d, 0x3d, 0x50, 0x16, 0x10, 0x00, 0x48, 0x8b, 0x4d, 0x00]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 264 64)] 7) := by dec_rfl
theorem p30_7 : ∀ feat, Dec feat p30 7 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 18)] 5) := by dec_rfl
theorem p30_12 : ∀ feat, Dec feat p30 12 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p30_17 : ∀ feat, Dec feat p30 17 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1054288 0)] 7) := by dec_rfl
theorem p30_24 : ∀ feat, Dec feat p30 24 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.ld 64 5 (some 3) none 1 264,
  Op.mov 32 2 (.i 18),
  Op.mov 32 6 (.i 1),
  Op.mov 64 7 (.i 7248720),
  Op.ld 64 1 (some 5) none 1 0]

theorem b30 (prof : Profile) : BlkA prof p30 (0x5e84e8 : Addr) 0 28 o30 :=
  .cons (p30_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p30_7 _) ((OpI.mov (.i 18) (.inl rfl)).at _) (by decide) <|
  .cons (p30_12 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p30_17 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p30_24 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .nil 28

/-- The stretch at `585`. -/
def p31 : List Byte := [
  0x48, 0x8b, 0xb3, 0xc0, 0x01, 0x00, 0x00, 0x48, 0x89, 0xef]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 3) none 1 448 64)] 7) := by dec_rfl
theorem p31_7 : ∀ feat, Dec feat p31 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.ld 64 6 (some 3) none 1 448,
  Op.mov 64 7 (.r 5)]

theorem b31 (prof : Profile) : Blk prof p31 0 10 o31 :=
  .cons (p31_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `600`. -/
def p32 : List Byte := [
  0x48, 0x89, 0xc7]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.mov 64 7 (.r 0)]

theorem b32 (prof : Profile) : Blk prof p32 0 3 o32 :=
  .cons (p32_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j20 : List Byte := [0xe9, 0x29, 0xfe, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk .jmp 64 [.rel 18446744073709551145] 5) := by dec_rfl

def j21 : List Byte := [0xe9, 0x75, 0xff, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk .jmp 64 [.rel 18446744073709551477] 5) := by dec_rfl

/-- The stretch at `632`. -/
def p33 : List Byte := [
  0x48, 0x8b, 0x4d, 0x00, 0xba, 0x1f, 0x00, 0x00, 0x00, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d,
  0x3d, 0x0b, 0x18, 0x10, 0x00]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p33_4 : ∀ feat, Dec feat p33 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 31)] 5) := by dec_rfl
theorem p33_9 : ∀ feat, Dec feat p33 9 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p33_14 : ∀ feat, Dec feat p33 14 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1054731 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.ld 64 1 (some 5) none 1 0,
  Op.mov 32 2 (.i 31),
  Op.mov 32 6 (.i 1),
  Op.mov 64 7 (.i 7249240)]

theorem b33 (prof : Profile) : BlkA prof p33 (0x5e8538 : Addr) 0 21 o33 :=
  .cons (p33_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p33_4 _) ((OpI.mov (.i 31) (.inl rfl)).at _) (by decide) <|
  .cons (p33_9 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p33_14 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 21

def j22 : List Byte := [0xe9, 0xda, 0xfe, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 18446744073709551322] 5) := by dec_rfl

end FV7z.Exr
