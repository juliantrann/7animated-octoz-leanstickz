import FV7z.Lemmas.SpFs
import FV7z.Lemmas.CmovLd
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__opendir` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 18 of them) and each distinct jump (`j*`, 11) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Opd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x81, 0xec, 0xa8, 0x00, 0x00,
  0x00, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x98, 0x00,
  0x00, 0x00, 0x31, 0xc0, 0x80, 0x3f, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 168)] 7) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 152 64), gr 64 0] 8) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 168),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 152 0,
  Op.xor 32 0 (.r 0),
  Op.cmpmi 8 (some 7) none 1 0 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x6635d0 : Addr) fb 0 39 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.sub (.i 168) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_36 _) (((OpI.cmpmi (.inl rfl)).at _).fs _) (by decide) <|
  .nil 39

def j0 : List Byte := [0x0f, 0x84, 0xf3, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 243] 6) := by dec_rfl

/-- The stretch at `45`. -/
def p1 : List Byte := [
  0xbe, 0x00, 0x08, 0x09, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 591872)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 6 (.i 591872)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 591872) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `55`. -/
def p2 : List Byte := [
  0x89, 0xc5, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 5 (.r 0),
  Op.test 32 0 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x0f, 0x88, 0xf7, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 8) 64 [.rel 247] 6) := by dec_rfl

/-- The stretch at `65`. -/
def p3 : List Byte := [
  0x48, 0x89, 0xe2, 0x89, 0xc6, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 2 (.r 4),
  Op.mov 32 6 (.r 0),
  Op.mov 32 7 (.i 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `80`. -/
def p4 : List Byte := [
  0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0x0f, 0x88, 0xb6, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 8) 64 [.rel 182] 6) := by dec_rfl

/-- The stretch at `88`. -/
def p5 : List Byte := [
  0x8b, 0x44, 0x24, 0x18, 0x25, 0x00, 0xf0, 0x00, 0x00, 0x3d, 0x00, 0x40, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 24 32)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 61440)] 5) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 16384)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 32 0 (some 4) none 1 24,
  Op.and 32 0 (.i 61440),
  Op.cmp 32 0 (.i 16384)]

theorem b5 (prof : Profile) : Blk prof p5 0 14 o5 :=
  .cons (p5_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.and (.i 61440) (.inl rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.cmp (.i 16384) (.inl rfl)) (by decide) <|
  .nil 14

def j3 : List Byte := [0x0f, 0x85, 0x94, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 148] 6) := by dec_rfl

/-- The stretch at `108`. -/
def p6 : List Byte := [
  0x48, 0x81, 0x7c, 0x24, 0x38, 0x00, 0x80, 0x00, 0x00, 0xbb, 0x00, 0x80, 0x00, 0x00, 0x48, 0x0f,
  0x43, 0x5c, 0x24, 0x38, 0xb8, 0x00, 0x00, 0x10, 0x00, 0x48, 0x81, 0xfb, 0x00, 0x00, 0x10, 0x00,
  0x48, 0x0f, 0x47, 0xd8, 0x48, 0x8d, 0x7b, 0x30]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 64 [.mem (mg (some 4) none 1 56 64), .imm 64 32768] 9) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 32768)] 5) := by dec_rfl
theorem p6_14 : ∀ feat, Dec feat p6 14 (FV7z.mk (.cmovcc 3) 64 [gr 64 3, .mem (mg (some 4) none 1 56 64)] 6) := by dec_rfl
theorem p6_20 : ∀ feat, Dec feat p6 20 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1048576)] 5) := by dec_rfl
theorem p6_25 : ∀ feat, Dec feat p6 25 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.i 1048576)] 7) := by dec_rfl
theorem p6_32 : ∀ feat, Dec feat p6 32 (FV7z.mk (.cmovcc 7) 64 [gr 64 3, gr 64 0] 4) := by dec_rfl
theorem p6_36 : ∀ feat, Dec feat p6 36 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 48 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmpmi 64 (some 4) none 1 56 32768,
  Op.mov 32 3 (.i 32768),
  Op.cmovld64 3 3 (some 4) none 1 56,
  Op.mov 32 0 (.i 1048576),
  Op.cmp 64 3 (.i 1048576),
  Op.cmov64 7 3 0,
  Op.lea 64 7 (some 3) none 1 48]

theorem b6 (prof : Profile) : Blk prof p6 0 40 o6 :=
  .cons (p6_0 _) (OpI.cmpmi64) (by decide) <|
  .cons (p6_9 _) (OpI.mov (.i 32768) (.inl rfl)) (by decide) <|
  .cons (p6_14 _) (OpI.cmovld64) (by decide) <|
  .cons (p6_20 _) (OpI.mov (.i 1048576) (.inl rfl)) (by decide) <|
  .cons (p6_25 _) (OpI.cmp (.i 1048576) (.inr rfl)) (by decide) <|
  .cons (p6_32 _) (OpI.cmov64) (by decide) <|
  .cons (p6_36 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 40

/-- The stretch at `153`. -/
def p7 : List Byte := [
  0x49, 0x89, 0xc4, 0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 12 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j4 : List Byte := [0x0f, 0x84, 0x9d, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 157] 6) := by dec_rfl

/-- The stretch at `165`. -/
def p8 : List Byte := [
  0x41, 0x89, 0x2c, 0x24, 0x41, 0xc7, 0x44, 0x24, 0x04, 0x00, 0x00, 0x00, 0x00, 0x49, 0x89, 0x5c,
  0x24, 0x08, 0x49, 0xc7, 0x44, 0x24, 0x10, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x44, 0x24, 0x18,
  0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, 0x41, 0xc7, 0x44,
  0x24, 0x28, 0x00, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 0 32), gr 32 5] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 4 32), .imm 32 0] 9) := by dec_rfl
theorem p8_13 : ∀ feat, Dec feat p8 13 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 8 64), gr 64 3] 5) := by dec_rfl
theorem p8_18 : ∀ feat, Dec feat p8 18 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 16 64), .imm 64 0] 9) := by dec_rfl
theorem p8_27 : ∀ feat, Dec feat p8 27 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 24 64), .imm 64 0] 9) := by dec_rfl
theorem p8_36 : ∀ feat, Dec feat p8 36 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 32 64), .imm 64 0] 9) := by dec_rfl
theorem p8_45 : ∀ feat, Dec feat p8 45 (FV7z.mk .mov 32 [.mem (mg (some 12) none 1 40 32), .imm 32 0] 9) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 32 (some 12) none 1 0 5,
  Op.sti 32 (some 12) none 1 4 0,
  Op.st 64 (some 12) none 1 8 3,
  Op.sti 64 (some 12) none 1 16 0,
  Op.sti 64 (some 12) none 1 24 0,
  Op.sti 64 (some 12) none 1 32 0,
  Op.sti 32 (some 12) none 1 40 0]

theorem b8 (prof : Profile) : Blk prof p8 0 54 o8 :=
  .cons (p8_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_4 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_13 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_18 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_27 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_36 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_45 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 54

/-- The stretch at `219`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x84, 0x24, 0x98, 0x00, 0x00, 0x00, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00,
  0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 152 64)] 8) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o9 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 152,
  Op.xormf fb 64 0 none none 1 40]

theorem b9 (prof : Profile) (fb : Addr) : BlkF prof p9 (0x6636ab : Addr) fb 0 17 (o9 fb) :=
  .cons (p9_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p9_8 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 17

def j5 : List Byte := [0x75, 0x4f]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 79] 2) := by dec_rfl

/-- The stretch at `238`. -/
def p10 : List Byte := [
  0x48, 0x81, 0xc4, 0xa8, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 168)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p10_12 : ∀ feat, Dec feat p10 12 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p10_14 : ∀ feat, Dec feat p10 14 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.add 64 4 (.i 168),
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b10 (prof : Profile) : Blk prof p10 0 16 o10 :=
  .cons (p10_0 _) (OpI.add (.i 168) (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p10_10 _) (OpI.pop) (by decide) <|
  .cons (p10_11 _) (OpI.pop) (by decide) <|
  .cons (p10_12 _) (OpI.pop) (by decide) <|
  .cons (p10_14 _) (OpI.pop) (by decide) <|
  .nil 16

/-- The stretch at `256`. -/
def p11 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0xc7, 0x00, 0x14, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 20] 7) := by dec_rfl

/-- What the stretch does. -/
def o11 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.stfi fb 32 (some 0) none 1 0 20]

theorem b11 (prof : Profile) (fb : Addr) : BlkF prof p11 (0x6636d0 : Addr) fb 0 14 (o11 fb) :=
  .cons (p11_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p11_7 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 14

/-- The stretch at `270`. -/
def p12 : List Byte := [
  0x89, 0xef, 0x45, 0x31, 0xe4]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p12_2 : ∀ feat, Dec feat p12 2 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 32 7 (.r 5),
  Op.xor 32 12 (.r 12)]

theorem b12 (prof : Profile) : Blk prof p12 0 5 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p12_2 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .nil 5

def j6 : List Byte := [0xeb, 0xc1]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551553] 2) := by dec_rfl

/-- The stretch at `288`. -/
def p13 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x45, 0x31, 0xe4, 0x64, 0xc7, 0x00, 0x02, 0x00, 0x00,
  0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p13_10 : ∀ feat, Dec feat p13 10 (FV7z.mk .mov 32 [.mem (mf (some 0) none 1 0 32), .imm 32 2] 7) := by dec_rfl

/-- What the stretch does. -/
def o13 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.xor 32 12 (.r 12),
  Op.stfi fb 32 (some 0) none 1 0 2]

theorem b13 (prof : Profile) (fb : Addr) : BlkF prof p13 (0x6636f0 : Addr) fb 0 17 (o13 fb) :=
  .cons (p13_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p13_7 _) (((OpI.xor (.r 12) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p13_10 _) (OpIF.stfi (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 17

def j7 : List Byte := [0xeb, 0xa8]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551528] 2) := by dec_rfl

/-- The stretch at `312`. -/
def p14 : List Byte := [
  0x45, 0x31, 0xe4]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.xor 32 12 (.r 12)]

theorem b14 (prof : Profile) : Blk prof p14 0 3 o14 :=
  .cons (p14_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

def j8 : List Byte := [0xeb, 0x9e]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551518] 2) := by dec_rfl

/-- The stretch at `322`. -/
def p15 : List Byte := [
  0xbf, 0x30, 0x20, 0x00, 0x00, 0xbb, 0x00, 0x20, 0x00, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 8240)] 5) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 8192)] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 32 7 (.i 8240),
  Op.mov 32 3 (.i 8192)]

theorem b15 (prof : Profile) : Blk prof p15 0 10 o15 :=
  .cons (p15_0 _) (OpI.mov (.i 8240) (.inl rfl)) (by decide) <|
  .cons (p15_5 _) (OpI.mov (.i 8192) (.inl rfl)) (by decide) <|
  .nil 10

def j9 : List Byte := [0x0f, 0x85, 0x48, 0xff, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551432] 6) := by dec_rfl

/-- The stretch at `349`. -/
def p16 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc3, 0xb8, 0xff, 0xff, 0xff, 0x89, 0xef, 0x64, 0x44, 0x8b,
  0x2b]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p16_11 : ∀ feat, Dec feat p16 11 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p16_13 : ∀ feat, Dec feat p16 13 (FV7z.mk .mov 32 [gr 32 13, .mem (mf (some 3) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 (fb : Addr) : List Op := [
  Op.nop,
  Op.mov 64 3 (.i 18446744073709551544),
  Op.mov 32 7 (.r 5),
  Op.ldf fb 32 13 (some 3) none 1 0]

theorem b16 (prof : Profile) (fb : Addr) : BlkF prof p16 (0x66372d : Addr) fb 0 17 (o16 fb) :=
  .cons (p16_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p16_4 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p16_11 _) (((OpI.mov (.r 5) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p16_13 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `371`. -/
def p17 : List Byte := [
  0x64, 0x44, 0x89, 0x2b]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [.mem (mf (some 3) none 1 0 32), gr 32 13] 4) := by dec_rfl

/-- What the stretch does. -/
def o17 (fb : Addr) : List Op := [
  Op.stf fb 32 (some 3) none 1 0 13]

theorem b17 (prof : Profile) (fb : Addr) : BlkF prof p17 (0x663743 : Addr) fb 0 4 (o17 fb) :=
  .cons (p17_0 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .nil 4

def j10 : List Byte := [0xe9, 0x5f, 0xff, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551455] 5) := by dec_rfl

end FV7z.Opd
