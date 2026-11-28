import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `WriteStream` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Wst
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83, 0xec, 0x10,
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31, 0xc0,
  0x48, 0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 16),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.test 64 2 (.r 2)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x463420 : Addr) fb 0 35 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.sub (.i 16) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.test (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 35

def j0 : List Byte := [0x74, 0x6b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 107] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p1 : List Byte := [
  0x49, 0x89, 0xfe, 0x48, 0x89, 0xf5, 0x48, 0x89, 0xd3, 0x41, 0xbc, 0x00, 0x00, 0x00, 0x80, 0x4c,
  0x8d, 0x6c, 0x24, 0x04]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 2147483648)] 6) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .lea 64 [gr 64 13, .mem (mg (some 4) none 1 4 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 14 (.r 7),
  Op.mov 64 5 (.r 6),
  Op.mov 64 3 (.r 2),
  Op.mov 32 12 (.i 2147483648),
  Op.lea 64 13 (some 4) none 1 4]

theorem b1 (prof : Profile) : Blk prof p1 0 20 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.mov (.i 2147483648) (.inl rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 20

def j1 : List Byte := [0xeb, 0x0e]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `64`. -/
def p2 : List Byte := [
  0x85, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 32 2 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0x74, 0x54]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 84] 2) := by dec_rfl

/-- The stretch at `68`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xdb]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 3 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x47]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 71] 2) := by dec_rfl

/-- The stretch at `73`. -/
def p4 : List Byte := [
  0x49, 0x8b, 0x06, 0x4c, 0x39, 0xe3, 0x4c, 0x89, 0xe2, 0x48, 0x89, 0xee, 0x48, 0x0f, 0x42, 0xd3,
  0x4c, 0x89, 0xe9, 0x4c, 0x89, 0xf7]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk (.cmovcc 2) 64 [gr 64 2, gr 64 3] 4) := by dec_rfl
theorem p4_16 : ∀ feat, Dec feat p4 16 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p4_19 : ∀ feat, Dec feat p4 19 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 0 (some 14) none 1 0,
  Op.cmp 64 3 (.r 12),
  Op.mov 64 2 (.r 12),
  Op.mov 64 6 (.r 5),
  Op.cmov64 2 2 3,
  Op.mov 64 1 (.r 13),
  Op.mov 64 7 (.r 14)]

theorem b4 (prof : Profile) : Blk prof p4 0 22 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.cmp (.r 12) (.inr rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.cmov64) (by decide) <|
  .cons (p4_16 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p4_19 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .nil 22

/-- The stretch at `98`. -/
def p5 : List Byte := [
  0x8b, 0x54, 0x24, 0x04, 0x48, 0x01, 0xd5, 0x48, 0x29, 0xd3, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 4 32)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 32 2 (some 4) none 1 4,
  Op.add 64 5 (.r 2),
  Op.sub 64 3 (.r 2),
  Op.test 32 0 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p5_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 12

def j4 : List Byte := [0x74, 0xd0]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551568] 2) := by dec_rfl

/-- The stretch at `112`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x08, 0x64, 0x48, 0x33, 0x34, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p6_5 : ∀ feat, Dec feat p6 5 (FV7z.mk .xor 64 [gr 64 6, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.ld 64 6 (some 4) none 1 8,
  Op.xormf fb 64 6 none none 1 40]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x463490 : Addr) fb 0 14 (o6 fb) :=
  .cons (p6_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p6_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j5 : List Byte := [0x75, 0x1f]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `128`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.add 64 4 (.i 16),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b7 (prof : Profile) : Blk prof p7 0 12 o7 :=
  .cons (p7_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.pop) (by decide) <|
  .cons (p7_5 _) (OpI.pop) (by decide) <|
  .cons (p7_6 _) (OpI.pop) (by decide) <|
  .cons (p7_8 _) (OpI.pop) (by decide) <|
  .cons (p7_10 _) (OpI.pop) (by decide) <|
  .nil 12

/-- The stretch at `144`. -/
def p8 : List Byte := [
  0x31, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j6 : List Byte := [0xeb, 0xdc]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551580] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p9 : List Byte := [
  0xb8, 0x05, 0x40, 0x00, 0x80]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147500037)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 0 (.i 2147500037)]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.mov (.i 2147500037) (.inl rfl)) (by decide) <|
  .nil 5

def j7 : List Byte := [0xeb, 0xd1]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551569] 2) := by dec_rfl

end FV7z.Wst
