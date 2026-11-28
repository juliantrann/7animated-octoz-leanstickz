import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Print_ErrorFormatIndex_Warning` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 16 of them) and each distinct jump (`j*`, 5) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pew
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x49, 0x89, 0xf5, 0xbe, 0x01, 0x00, 0x00, 0x00, 0x41, 0x54,
  0x55, 0x48, 0x89, 0xfd, 0x53, 0x48, 0x89, 0xd3, 0xba, 0x09, 0x00, 0x00, 0x00, 0x48, 0x83, 0xec,
  0x28, 0x48, 0x8b, 0x0f, 0x48, 0x8d, 0x3d, 0x86, 0x05, 0x10, 0x00, 0x64, 0x48, 0x8b, 0x04, 0x25,
  0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 9)] 5) := by dec_rfl
theorem p0_29 : ∀ feat, Dec feat p0 29 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_36 : ∀ feat, Dec feat p0 36 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1049990 0)] 7) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_52 : ∀ feat, Dec feat p0 52 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_57 : ∀ feat, Dec feat p0 57 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 13,
  Op.mov 64 13 (.r 6),
  Op.mov 32 6 (.i 1),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 2),
  Op.mov 32 2 (.i 9),
  Op.sub 64 4 (.i 40),
  Op.ld 64 1 (some 7) none 1 0,
  Op.mov 64 7 (.i 7249041),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5e96e0 : Addr) fb 0 59 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.mov (.i 1) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_16 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_20 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_24 _) (((OpI.mov (.i 9) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_29 _) (((OpI.sub (.i 40) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_33 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_36 _) ((OpIA.lea_rip (by decide)).fs _) (by decide) <|
  .cons (p0_43 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_52 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_57 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 59

/-- The stretch at `64`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x73, 0x28, 0x48, 0x89, 0xef, 0x49, 0x89, 0xe4]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 3) none 1 40 0)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 6 (some 3) none 1 40,
  Op.mov 64 7 (.r 5),
  Op.mov 64 12 (.r 4)]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `79`. -/
def p2 : List Byte := [
  0x4c, 0x89, 0xe7]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 12)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `87`. -/
def p3 : List Byte := [
  0x48, 0x63, 0x83, 0xa4, 0x00, 0x00, 0x00, 0x39, 0x43, 0x58]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 3) none 1 164 32)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .cmp 32 [.mem (mg (some 3) none 1 88 32), gr 32 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldsx 0 (some 3) none 1 164,
  Op.cmpmr 32 (some 3) none 1 88 0]

theorem b3 (prof : Profile) : Blk prof p3 0 10 o3 :=
  .cons (p3_0 _) (OpI.ldsx) (by decide) <|
  .cons (p3_7 _) (OpI.cmpmr (.inl rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x0f, 0x84, 0x99, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 153] 6) := by dec_rfl

/-- The stretch at `103`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x15, 0xde, 0x08, 0x10, 0x00, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1050846 0)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 2 (.i 7249964),
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x5e9747 : Addr) 0 9 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_7 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 9

def j1 : List Byte := [0x78, 0x0c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 8) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `114`. -/
def p5 : List Byte := [
  0x49, 0x8b, 0x55, 0x10, 0x48, 0x8b, 0x04, 0xc2, 0x48, 0x8b, 0x50, 0x18]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 13) none 1 16 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) (some 0) 8 0 64)] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 0) none 1 24 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 2 (some 13) none 1 16,
  Op.ld 64 0 (some 2) (some 0) 8 0,
  Op.ld 64 2 (some 0) none 1 24]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `126`. -/
def p6 : List Byte := [
  0x48, 0x8d, 0x35, 0x36, 0x05, 0x10, 0x00, 0x4c, 0x89, 0xe7]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1049910 0)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 6 (.i 7249051),
  Op.mov 64 7 (.r 12)]

theorem b6 (prof : Profile) : BlkA prof p6 (0x5e975e : Addr) 0 10 o6 :=
  .cons (p6_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_7 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 10

/-- The stretch at `141`. -/
def p7 : List Byte := [
  0x48, 0x63, 0x43, 0x58, 0x48, 0x8d, 0x15, 0xb4, 0x08, 0x10, 0x00, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 3) none 1 88 32)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1050804 0)] 7) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldsx 0 (some 3) none 1 88,
  Op.mov 64 2 (.i 7249964),
  Op.test 32 0 (.r 0)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x5e976d : Addr) 0 13 o7 :=
  .cons (p7_0 _) ((OpI.ldsx).at _) (by decide) <|
  .cons (p7_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_11 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 13

/-- The stretch at `168`. -/
def p8 : List Byte := [
  0x48, 0x8d, 0x35, 0x21, 0x05, 0x10, 0x00, 0x4c, 0x89, 0xe7]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1049889 0)] 7) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 6 (.i 7249072),
  Op.mov 64 7 (.r 12)]

theorem b8 (prof : Profile) : BlkA prof p8 (0x5e9788 : Addr) 0 10 o8 :=
  .cons (p8_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p8_7 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 10

/-- The stretch at `183`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x34, 0x24, 0x48, 0x89, 0xef]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 6 (some 4) none 1 0,
  Op.mov 64 7 (.r 5)]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `195`. -/
def p10 : List Byte := [
  0x48, 0x89, 0xc5, 0x48, 0x89, 0xc7]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 5 (.r 0),
  Op.mov 64 7 (.r 0)]

theorem b10 (prof : Profile) : Blk prof p10 0 6 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `206`. -/
def p11 : List Byte := [
  0x48, 0x89, 0xef]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b11 (prof : Profile) : Blk prof p11 0 3 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `214`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x3c, 0x24, 0x48, 0x85, 0xff]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 7 (some 4) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `228`. -/
def p13 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p13_5 : ∀ feat, Dec feat p13 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o13 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b13 (prof : Profile) (fb : Addr) : BlkF prof p13 (0x5e97c4 : Addr) fb 0 14 (o13 fb) :=
  .cons (p13_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p13_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j3 : List Byte := [0x75, 0x25]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `244`. -/
def p14 : List Byte := [
  0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p14_5 : ∀ feat, Dec feat p14 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p14_6 : ∀ feat, Dec feat p14 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p14_8 : ∀ feat, Dec feat p14 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b14 (prof : Profile) : Blk prof p14 0 10 o14 :=
  .cons (p14_0 _) (OpI.add (.i 40) (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.pop) (by decide) <|
  .cons (p14_5 _) (OpI.pop) (by decide) <|
  .cons (p14_6 _) (OpI.pop) (by decide) <|
  .cons (p14_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `264`. -/
def p15 : List Byte := [
  0x48, 0x8d, 0x35, 0x79, 0x07, 0x10, 0x00, 0x4c, 0x89, 0xe7]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1050489 0)] 7) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 6 (.i 7249768),
  Op.mov 64 7 (.r 12)]

theorem b15 (prof : Profile) : BlkA prof p15 (0x5e97e8 : Addr) 0 10 o15 :=
  .cons (p15_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p15_7 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j4 : List Byte := [0xeb, 0x9e]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551518] 2) := by dec_rfl

end FV7z.Pew
