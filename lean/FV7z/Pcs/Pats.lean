import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `ParseComplexSize` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 16 of them) and each distinct jump (`j*`, 12) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pcs
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x18,
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31, 0xc0,
  0x48, 0xc7, 0x06, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xe6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 4)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 24),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.sti 64 (some 6) none 1 0 0,
  Op.mov 64 6 (.r 4)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5d38f0 : Addr) fb 0 42 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_5 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.sub (.i 24) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_39 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 42

/-- The stretch at `47`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x0c, 0x24, 0x48, 0x39, 0xd9]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 0 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 1 (some 4) none 1 0,
  Op.cmp 64 1 (.r 3)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.cmp (.r 3) (.inr rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x74, 0x78]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 120] 2) := by dec_rfl

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x8b, 0x11, 0x48, 0x89, 0xc6, 0x85, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 1) none 1 0 32)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 2 (some 1) none 1 0,
  Op.mov 64 6 (.r 0),
  Op.test 32 2 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x74, 0x77]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 119] 2) := by dec_rfl

/-- The stretch at `65`. -/
def p3 : List Byte := [
  0x8b, 0x49, 0x04, 0x31, 0xc0, 0x85, 0xc9]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 1) none 1 4 32)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 32 1 (some 1) none 1 4,
  Op.xor 32 0 (.r 0),
  Op.test 32 1 (.r 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x75, 0x46]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 70] 2) := by dec_rfl

/-- The stretch at `74`. -/
def p4 : List Byte := [
  0x8d, 0x4a, 0xbf, 0x8d, 0x42, 0x20, 0x83, 0xf9, 0x1a, 0x0f, 0x42, 0xd0, 0x83, 0xea, 0x62, 0x83,
  0xfa, 0x12]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 2) none 1 18446744073709551551 0)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 2) none 1 32 0)] 3) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 26)] 3) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk (.cmovcc 2) 32 [gr 32 2, gr 32 0] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 98)] 3) := by dec_rfl
theorem p4_15 : ∀ feat, Dec feat p4 15 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 18)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lea 32 1 (some 2) none 1 18446744073709551551,
  Op.lea 32 0 (some 2) none 1 32,
  Op.cmp 32 1 (.i 26),
  Op.cmov32 2 2 0,
  Op.sub 32 2 (.i 98),
  Op.cmp 32 2 (.i 18)]

theorem b4 (prof : Profile) : Blk prof p4 0 18 o4 :=
  .cons (p4_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.cmp (.i 26) (.inl rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.cmov32) (by decide) <|
  .cons (p4_12 _) (OpI.sub (.i 98) (.inl rfl)) (by decide) <|
  .cons (p4_15 _) (OpI.cmp (.i 18) (.inl rfl)) (by decide) <|
  .nil 18

def j3 : List Byte := [0x77, 0x52]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 7) 64 [.rel 82] 2) := by dec_rfl

/-- The stretch at `94`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x0d, 0x37, 0x55, 0x11, 0x00, 0x48, 0x63, 0x04, 0x91, 0x48, 0x01, 0xc8]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 1135927 0)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 1) (some 2) 4 0 32)] 4) := by dec_rfl
theorem p5_11 : ∀ feat, Dec feat p5 11 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 1 (.i 7245452),
  Op.ldsx 0 (some 1) (some 2) 4 0,
  Op.add 64 0 (.r 1)]

theorem b5 (prof : Profile) : BlkA prof p5 (0x5d394e : Addr) 0 14 o5 :=
  .cons (p5_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_7 _) ((OpI.ldsx).at _) (by decide) <|
  .cons (p5_11 _) ((OpI.add (.r 1) (.inr rfl)).at _) (by decide) <|
  .nil 14

def j4 : List Byte := [0x3e, 0xff, 0xe0]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [gr 64 0] 3) := by dec_rfl

/-- The stretch at `112`. -/
def p6 : List Byte := [
  0xba, 0x00, 0x00, 0x00, 0x01, 0xb9, 0x28, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 16777216)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 40)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 2 (.i 16777216),
  Op.mov 32 1 (.i 40)]

theorem b6 (prof : Profile) : Blk prof p6 0 10 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 16777216) (.inl rfl)) (by decide) <|
  .cons (p6_5 _) (OpI.mov (.i 40) (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `122`. -/
def p7 : List Byte := [
  0x31, 0xc0, 0x48, 0x39, 0xd6]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_2 : ∀ feat, Dec feat p7 2 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.cmp 64 6 (.r 2)]

theorem b7 (prof : Profile) : Blk prof p7 0 5 o7 :=
  .cons (p7_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p7_2 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 5

def j5 : List Byte := [0x73, 0x0f]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 3) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `129`. -/
def p8 : List Byte := [
  0x48, 0x89, 0xf0, 0x48, 0xd3, 0xe0, 0x48, 0x89, 0x45, 0x00, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p8_6 : ∀ feat, Dec feat p8 6 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 0] 4) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 0 (.r 6),
  Op.shl64 0 (.r 1),
  Op.st 64 (some 5) none 1 0 0,
  Op.mov 32 0 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 15 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.shl64 (.r 1)) (by decide) <|
  .cons (p8_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_10 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 15

/-- The stretch at `144`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x5c, 0x24, 0x08, 0x64, 0x48, 0x33, 0x1c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .xor 64 [gr 64 3, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o9 (fb : Addr) : List Op := [
  Op.ld 64 3 (some 4) none 1 8,
  Op.xormf fb 64 3 none none 1 40]

theorem b9 (prof : Profile) (fb : Addr) : BlkF prof p9 (0x5d3980 : Addr) fb 0 14 (o9 fb) :=
  .cons (p9_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p9_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j6 : List Byte := [0x75, 0x6c]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 108] 2) := by dec_rfl

/-- The stretch at `160`. -/
def p10 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5]

theorem b10 (prof : Profile) : Blk prof p10 0 6 o10 :=
  .cons (p10_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.pop) (by decide) <|
  .cons (p10_5 _) (OpI.pop) (by decide) <|
  .nil 6

/-- The stretch at `176`. -/
def p11 : List Byte := [
  0x31, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 2 o11 :=
  .cons (p11_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j7 : List Byte := [0xeb, 0xdc]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551580] 2) := by dec_rfl

/-- The stretch at `184`. -/
def p12 : List Byte := [
  0x48, 0x89, 0x75, 0x00, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 6] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.st 64 (some 5) none 1 0 6,
  Op.mov 32 0 (.i 1)]

theorem b12 (prof : Profile) : Blk prof p12 0 9 o12 :=
  .cons (p12_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p12_4 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 9

def j8 : List Byte := [0xeb, 0xcd]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `200`. -/
def p13 : List Byte := [
  0x48, 0xba, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0xb9, 0x1e, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 17179869184)] 10) := by dec_rfl
theorem p13_10 : ∀ feat, Dec feat p13 10 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 30)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 64 2 (.i 17179869184),
  Op.mov 32 1 (.i 30)]

theorem b13 (prof : Profile) : Blk prof p13 0 15 o13 :=
  .cons (p13_0 _) (OpI.mov (.i 17179869184) (.inr rfl)) (by decide) <|
  .cons (p13_10 _) (OpI.mov (.i 30) (.inl rfl)) (by decide) <|
  .nil 15

def j9 : List Byte := [0xeb, 0xa1]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551521] 2) := by dec_rfl

/-- The stretch at `224`. -/
def p14 : List Byte := [
  0x48, 0xba, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0xb9, 0x0a, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18014398509481984)] 10) := by dec_rfl
theorem p14_10 : ∀ feat, Dec feat p14 10 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 10)] 5) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 2 (.i 18014398509481984),
  Op.mov 32 1 (.i 10)]

theorem b14 (prof : Profile) : Blk prof p14 0 15 o14 :=
  .cons (p14_0 _) (OpI.mov (.i 18014398509481984) (.inr rfl)) (by decide) <|
  .cons (p14_10 _) (OpI.mov (.i 10) (.inl rfl)) (by decide) <|
  .nil 15

def j10 : List Byte := [0xeb, 0x89]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551497] 2) := by dec_rfl

/-- The stretch at `248`. -/
def p15 : List Byte := [
  0x48, 0xba, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x00, 0xb9, 0x14, 0x00, 0x00, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 17592186044416)] 10) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 20)] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 2 (.i 17592186044416),
  Op.mov 32 1 (.i 20)]

theorem b15 (prof : Profile) : Blk prof p15 0 15 o15 :=
  .cons (p15_0 _) (OpI.mov (.i 17592186044416) (.inr rfl)) (by decide) <|
  .cons (p15_10 _) (OpI.mov (.i 20) (.inl rfl)) (by decide) <|
  .nil 15

def j11 : List Byte := [0xe9, 0x6e, 0xff, 0xff, 0xff]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551470] 5) := by dec_rfl

end FV7z.Pcs
