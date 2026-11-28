import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `FindCharset` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 16 of them) and each distinct jump (`j*`, 11) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fch
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x55, 0x89, 0xf6, 0x41, 0x54, 0x41, 0x89, 0xcc, 0x55, 0x53, 0x89, 0xd3, 0x48, 0x8d, 0x14,
  0x76, 0x48, 0x83, 0xec, 0x38, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x44, 0x24, 0x28, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 6) (some 6) 2 0 0)] 4) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), gr 64 0] 5) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 13,
  Op.mov 32 6 (.r 6),
  Op.push 12,
  Op.mov 32 12 (.r 1),
  Op.push 5,
  Op.push 3,
  Op.mov 32 3 (.r 2),
  Op.lea 64 2 (some 6) (some 6) 2 0,
  Op.sub 64 4 (.i 56),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 40 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5a67b0 : Addr) fb 0 37 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_2 _) (((OpI.mov (.r 6) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 1) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.mov (.r 2) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.sub (.i 56) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_30 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_35 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 37

/-- The stretch at `37`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x07, 0x48, 0x8d, 0x04, 0xd0, 0x80, 0x38, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 2) 8 0 0)] 4) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 7) none 1 0,
  Op.lea 64 0 (some 0) (some 2) 8 0,
  Op.cmpmi 8 (some 0) none 1 0 0]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x75, 0x27]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x28, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 40,
  Op.xormf fb 64 0 none none 1 40]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x5a67e1 : Addr) fb 0 14 (o2 fb) :=
  .cons (p2_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x0f, 0x85, 0xd2, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 210] 6) := by dec_rfl

/-- The stretch at `69`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x38, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 56),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b3 (prof : Profile) : Blk prof p3 0 13 o3 :=
  .cons (p3_0 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.pop) (by decide) <|
  .cons (p3_8 _) (OpI.pop) (by decide) <|
  .cons (p3_9 _) (OpI.pop) (by decide) <|
  .cons (p3_11 _) (OpI.pop) (by decide) <|
  .nil 13

/-- The stretch at `88`. -/
def p4 : List Byte := [
  0x8b, 0x50, 0x10, 0x48, 0x8b, 0x40, 0x08, 0x48, 0x8d, 0x7c, 0x24, 0x10, 0x48, 0x8b, 0x74, 0xd0,
  0xf8]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 0) none 1 16 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 4) none 1 16 0)] 5) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 0) (some 2) 8 18446744073709551608 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 2 (some 0) none 1 16,
  Op.ld 64 0 (some 0) none 1 8,
  Op.lea 64 7 (some 4) none 1 16,
  Op.ld 64 6 (some 0) (some 2) 8 18446744073709551608]

theorem b4 (prof : Profile) : Blk prof p4 0 17 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 17

/-- The stretch at `110`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x10, 0x8b, 0x07, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 4) none 1 16,
  Op.ld 32 0 (some 7) none 1 0,
  Op.test 32 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 9 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

def j2 : List Byte := [0x74, 0x27]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `121`. -/
def p6 : List Byte := [
  0x48, 0x8d, 0x74, 0x24, 0x0c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 4) none 1 12 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 6 (some 4) none 1 12]

theorem b6 (prof : Profile) : Blk prof p6 0 5 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `131`. -/
def p7 : List Byte := [
  0x84, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 8 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 2 o7 :=
  .cons (p7_0 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x0f, 0x84, 0x85, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 133] 6) := by dec_rfl

/-- The stretch at `139`. -/
def p8 : List Byte := [
  0x44, 0x8b, 0x64, 0x24, 0x0c, 0x48, 0x8b, 0x7c, 0x24, 0x10, 0x41, 0x81, 0xfc, 0xff, 0xff, 0x00,
  0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 4) none 1 12 32)] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .cmp 32 [gr 32 12, Src.opd 32 (.i 65535)] 7) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 12 (some 4) none 1 12,
  Op.ld 64 7 (some 4) none 1 16,
  Op.cmp 32 12 (.i 65535)]

theorem b8 (prof : Profile) : Blk prof p8 0 17 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_10 _) (OpI.cmp (.i 65535) (.inl rfl)) (by decide) <|
  .nil 17

def j4 : List Byte := [0x76, 0x5e]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 6) 64 [.rel 94] 2) := by dec_rfl

/-- The stretch at `158`. -/
def p9 : List Byte := [
  0x66, 0x90]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .nop 16 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.nop]

theorem b9 (prof : Profile) : Blk prof p9 0 2 o9 :=
  .cons (p9_0 _) (OpI.nop) (by decide) <|
  .nil 2

/-- The stretch at `165`. -/
def p10 : List Byte := [
  0x80, 0xfb, 0x01, 0x4c, 0x8d, 0x25, 0xa1, 0x7b, 0x1d, 0x00, 0x48, 0x8d, 0x35, 0x7c, 0x10, 0x14,
  0x00, 0x45, 0x19, 0xed, 0x4c, 0x89, 0xe5, 0x31, 0xdb, 0x41, 0x83, 0xe5, 0x02, 0x41, 0x83, 0xc5,
  0x03]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 8 [gr 8 3, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .lea 64 [gr 64 12, .mem (mrip 1932193 0)] 7) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1314940 0)] 7) := by dec_rfl
theorem p10_17 : ∀ feat, Dec feat p10 17 (FV7z.mk .sbb 32 [gr 32 13, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p10_20 : ∀ feat, Dec feat p10 20 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p10_23 : ∀ feat, Dec feat p10 23 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p10_25 : ∀ feat, Dec feat p10 25 (FV7z.mk .and 32 [gr 32 13, Src.opd 32 (.i 2)] 4) := by dec_rfl
theorem p10_29 : ∀ feat, Dec feat p10 29 (FV7z.mk .add 32 [gr 32 13, Src.opd 32 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmp 8 3 (.i 1),
  Op.mov 64 12 (.i 7857152),
  Op.mov 64 6 (.i 7239906),
  Op.sbb 32 13 (.r 13),
  Op.mov 64 5 (.r 12),
  Op.xor 32 3 (.r 3),
  Op.and 32 13 (.i 2),
  Op.add 32 13 (.i 3)]

theorem b10 (prof : Profile) : BlkA prof p10 (0x5a6855 : Addr) 0 33 o10 :=
  .cons (p10_0 _) ((OpI.cmp8 (.i 1)).at _) (by decide) <|
  .cons (p10_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_10 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_17 _) ((OpI.sbb (.r 13) (.inl rfl)).at _) (by decide) <|
  .cons (p10_20 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p10_23 _) ((OpI.xor (.r 3) (.inl rfl)).at _) (by decide) <|
  .cons (p10_25 _) ((OpI.and (.i 2) (.inl rfl)).at _) (by decide) <|
  .cons (p10_29 _) ((OpI.add (.i 3) (.inl rfl)).at _) (by decide) <|
  .nil 33

def j5 : List Byte := [0xeb, 0x18]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `208`. -/
def p11 : List Byte := [
  0x83, 0xc3, 0x01, 0x48, 0x83, 0xc5, 0x10, 0x41, 0x39, 0xdd]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .add 32 [gr 32 3, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.add 32 3 (.i 1),
  Op.add 64 5 (.i 16),
  Op.cmp 32 13 (.r 3)]

theorem b11 (prof : Profile) : Blk prof p11 0 10 o11 :=
  .cons (p11_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p11_7 _) (OpI.cmp (.r 3) (.inl rfl)) (by decide) <|
  .nil 10

def j6 : List Byte := [0x74, 0x40]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 64] 2) := by dec_rfl

/-- The stretch at `220`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x75, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 6 (some 5) none 1 0]

theorem b12 (prof : Profile) : Blk prof p12 0 4 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `224`. -/
def p13 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x10]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.ld 64 7 (some 4) none 1 16]

theorem b13 (prof : Profile) : Blk prof p13 0 5 o13 :=
  .cons (p13_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 5

def j7 : List Byte := [0x74, 0xe2]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551586] 2) := by dec_rfl

/-- The stretch at `238`. -/
def p14 : List Byte := [
  0x48, 0xc1, 0xe3, 0x04, 0x48, 0x8b, 0x7c, 0x24, 0x10, 0x45, 0x8b, 0x64, 0x1c, 0x08]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .shl 64 [gr 64 3, Src.opd 8 (.i 4)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p14_9 : ∀ feat, Dec feat p14 9 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 12) (some 3) 1 8 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.shl64 3 (.i 4),
  Op.ld 64 7 (some 4) none 1 16,
  Op.ld 32 12 (some 12) (some 3) 1 8]

theorem b14 (prof : Profile) : Blk prof p14 0 14 o14 :=
  .cons (p14_0 _) (OpI.shl64 (.i 4)) (by decide) <|
  .cons (p14_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p14_9 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 14

/-- The stretch at `252`. -/
def p15 : List Byte := [
  0x48, 0x85, 0xff]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b15 (prof : Profile) : Blk prof p15 0 3 o15 :=
  .cons (p15_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j8 : List Byte := [0x0f, 0x84, 0x2c, 0xff, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551404] 6) := by dec_rfl

def j9 : List Byte := [0xe9, 0x22, 0xff, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551394] 5) := by dec_rfl

def j10 : List Byte := [0xeb, 0x89]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551497] 2) := by dec_rfl

end FV7z.Fch
