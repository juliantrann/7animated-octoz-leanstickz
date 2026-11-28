import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CDirItems::SetLinkInfo` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 15 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sli
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x30,
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x31, 0xc0,
  0x80, 0x7f, 0x40, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), gr 64 0] 5) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 64 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 48),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 40 0,
  Op.xor 32 0 (.r 0),
  Op.cmpmi 8 (some 7) none 1 64 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5c0e20 : Addr) fb 0 36 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.sub (.i 48) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.cmpmi (.inl rfl)).at _).fs _) (by decide) <|
  .nil 36

def j0 : List Byte := [0x0f, 0x84, 0x86, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 134] 6) := by dec_rfl

/-- The stretch at `42`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xd3, 0x8b, 0x52, 0x48, 0x81, 0xe2, 0x00, 0xf0, 0x00, 0x00, 0x81, 0xfa, 0x00, 0xa0,
  0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 2) none 1 72 32)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 61440)] 6) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 40960)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 3 (.r 2),
  Op.ld 32 2 (some 2) none 1 72,
  Op.and 32 2 (.i 61440),
  Op.cmp 32 2 (.i 40960)]

theorem b1 (prof : Profile) : Blk prof p1 0 18 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.and (.i 61440) (.inl rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.cmp (.i 40960) (.inl rfl)) (by decide) <|
  .nil 18

def j1 : List Byte := [0x74, 0x22]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `62`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x5c, 0x24, 0x28, 0x64, 0x48, 0x33, 0x1c, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .xor 64 [gr 64 3, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.ld 64 3 (some 4) none 1 40,
  Op.xormf fb 64 3 none none 1 40]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x5c0e5e : Addr) fb 0 14 (o2 fb) :=
  .cons (p2_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j2 : List Byte := [0x0f, 0x85, 0xa2, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 162] 6) := by dec_rfl

/-- The stretch at `82`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xc4, 0x30, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 4 (.i 48),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.add (.i 48) (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.pop) (by decide) <|
  .cons (p3_5 _) (OpI.pop) (by decide) <|
  .cons (p3_6 _) (OpI.pop) (by decide) <|
  .cons (p3_8 _) (OpI.pop) (by decide) <|
  .cons (p3_10 _) (OpI.pop) (by decide) <|
  .nil 12

/-- The stretch at `96`. -/
def p4 : List Byte := [
  0x4c, 0x8d, 0x6c, 0x24, 0x10, 0x49, 0x89, 0xf4, 0x48, 0x89, 0xfd, 0x48, 0x89, 0xce, 0x4c, 0x89,
  0xef, 0x48, 0x8d, 0x53, 0x68]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 4) none 1 16 0)] 5) := by dec_rfl
theorem p4_5 : ∀ feat, Dec feat p4 5 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p4_17 : ∀ feat, Dec feat p4 17 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 3) none 1 104 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lea 64 13 (some 4) none 1 16,
  Op.mov 64 12 (.r 6),
  Op.mov 64 5 (.r 7),
  Op.mov 64 6 (.r 1),
  Op.mov 64 7 (.r 13),
  Op.lea 64 2 (some 3) none 1 104]

theorem b4 (prof : Profile) : Blk prof p4 0 21 o4 :=
  .cons (p4_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_5 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p4_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p4_11 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p4_14 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p4_17 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 21

/-- The stretch at `122`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x10, 0x49, 0x8d, 0x74, 0x24, 0x78]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 12) none 1 120 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 7 (some 4) none 1 16,
  Op.lea 64 6 (some 12) none 1 120]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `137`. -/
def p6 : List Byte := [
  0x84, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.test 8 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0x2b]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `141`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x03]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 3) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 0 (some 3) none 1 0]

theorem b7 (prof : Profile) : Blk prof p7 0 3 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `148`. -/
def p8 : List Byte := [
  0x31, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `150`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x10, 0x48, 0x85, 0xff]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 7 (some 4) none 1 16,
  Op.test 64 7 (.r 7)]

theorem b9 (prof : Profile) : Blk prof p9 0 8 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_5 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 8

def j4 : List Byte := [0x74, 0x9e]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551518] 2) := by dec_rfl

/-- The stretch at `160`. -/
def p10 : List Byte := [
  0x89, 0x44, 0x24, 0x0c]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.st 32 (some 4) none 1 12 0]

theorem b10 (prof : Profile) : Blk prof p10 0 4 o10 :=
  .cons (p10_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 4

/-- The stretch at `169`. -/
def p11 : List Byte := [
  0x8b, 0x44, 0x24, 0x0c]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 32 0 (some 4) none 1 12]

theorem b11 (prof : Profile) : Blk prof p11 0 4 o11 :=
  .cons (p11_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 4

def j5 : List Byte := [0xeb, 0x8f]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551503] 2) := by dec_rfl

def j6 : List Byte := [0xeb, 0x8a]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551498] 2) := by dec_rfl

/-- The stretch at `189`. -/
def p12 : List Byte := [
  0x49, 0x8b, 0x7c, 0x24, 0x78, 0x41, 0x89, 0xc6, 0x48, 0x85, 0xff]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 12) none 1 120 64)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .mov 32 [gr 32 14, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 7 (some 12) none 1 120,
  Op.mov 32 14 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b12 (prof : Profile) : Blk prof p12 0 11 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_5 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p12_8 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 11

def j7 : List Byte := [0x74, 0x0e]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `207`. -/
def p13 : List Byte := [
  0x49, 0xc7, 0x44, 0x24, 0x78, 0x00, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 120 64), .imm 64 0] 9) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sti 64 (some 12) none 1 120 0]

theorem b13 (prof : Profile) : Blk prof p13 0 9 o13 :=
  .cons (p13_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 9

/-- The stretch at `216`. -/
def p14 : List Byte := [
  0x44, 0x89, 0xf2, 0x4c, 0x89, 0xee, 0x48, 0x89, 0xef, 0x49, 0xc7, 0x84, 0x24, 0x80, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p14_6 : ∀ feat, Dec feat p14 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p14_9 : ∀ feat, Dec feat p14 9 (FV7z.mk .mov 64 [.mem (mg (some 12) none 1 128 64), .imm 64 0] 12) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 32 2 (.r 14),
  Op.mov 64 6 (.r 13),
  Op.mov 64 7 (.r 5),
  Op.sti 64 (some 12) none 1 128 0]

theorem b14 (prof : Profile) : Blk prof p14 0 21 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 14) (.inl rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p14_6 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p14_9 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 21

def j8 : List Byte := [0xeb, 0xa2]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551522] 2) := by dec_rfl

end FV7z.Sli
