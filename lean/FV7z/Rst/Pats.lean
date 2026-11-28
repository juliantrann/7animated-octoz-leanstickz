import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `ReadStream` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rst
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83,
  0xec, 0x18, 0x48, 0x8b, 0x1a, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x44, 0x24, 0x08, 0x31, 0xc0, 0x48, 0xc7, 0x02, 0x00, 0x00, 0x00, 0x00, 0x48, 0x85, 0xdb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 24),
  Op.ld 64 3 (some 2) none 1 0,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.sti 64 (some 2) none 1 0 0,
  Op.test 64 3 (.r 3)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x4632b0 : Addr) fb 0 47 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.sub (.i 24) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_18 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_30 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_35 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_37 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_44 _) (((OpI.test (.r 3) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 47

def j0 : List Byte := [0x74, 0x77]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 119] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p1 : List Byte := [
  0x49, 0x89, 0xff, 0x49, 0x89, 0xf5, 0x49, 0x89, 0xd6, 0xbd, 0x00, 0x00, 0x00, 0x80, 0x4c, 0x8d,
  0x64, 0x24, 0x04]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 2147483648)] 5) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 4) none 1 4 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 15 (.r 7),
  Op.mov 64 13 (.r 6),
  Op.mov 64 14 (.r 2),
  Op.mov 32 5 (.i 2147483648),
  Op.lea 64 12 (some 4) none 1 4]

theorem b1 (prof : Profile) : Blk prof p1 0 19 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.mov (.i 2147483648) (.inl rfl)) (by decide) <|
  .cons (p1_14 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 19

def j1 : List Byte := [0xeb, 0x13]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p2 : List Byte := [
  0x85, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 32 2 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0x74, 0x2f]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `84`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xdb]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 3 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x4f]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 79] 2) := by dec_rfl

/-- The stretch at `89`. -/
def p4 : List Byte := [
  0x49, 0x8b, 0x07, 0x48, 0x39, 0xeb, 0x48, 0x89, 0xea, 0x4c, 0x89, 0xee, 0x48, 0x0f, 0x42, 0xd3,
  0x4c, 0x89, 0xe1, 0x4c, 0x89, 0xff]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 15) none 1 0 64)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .cmp 64 [gr 64 3, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk (.cmovcc 2) 64 [gr 64 2, gr 64 3] 4) := by dec_rfl
theorem p4_16 : ∀ feat, Dec feat p4 16 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p4_19 : ∀ feat, Dec feat p4 19 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 0 (some 15) none 1 0,
  Op.cmp 64 3 (.r 5),
  Op.mov 64 2 (.r 5),
  Op.mov 64 6 (.r 13),
  Op.cmov64 2 2 3,
  Op.mov 64 1 (.r 12),
  Op.mov 64 7 (.r 15)]

theorem b4 (prof : Profile) : Blk prof p4 0 22 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.cmp (.r 5) (.inr rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p4_9 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p4_12 _) (OpI.cmov64) (by decide) <|
  .cons (p4_16 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p4_19 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 22

/-- The stretch at `114`. -/
def p5 : List Byte := [
  0x8b, 0x54, 0x24, 0x04]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 4 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 32 2 (some 4) none 1 4]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `121`. -/
def p6 : List Byte := [
  0x49, 0x01, 0xd5, 0x48, 0x29, 0xd3, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .add 64 [gr 64 13, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.add 64 13 (.r 2),
  Op.sub 64 3 (.r 2),
  Op.test 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 8 o6 :=
  .cons (p6_0 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 8

def j4 : List Byte := [0x74, 0xcd]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `131`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x08, 0x64, 0x48, 0x33, 0x34, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .xor 64 [gr 64 6, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o7 (fb : Addr) : List Op := [
  Op.ld 64 6 (some 4) none 1 8,
  Op.xormf fb 64 6 none none 1 40]

theorem b7 (prof : Profile) (fb : Addr) : BlkF prof p7 (0x463333 : Addr) fb 0 14 (o7 fb) :=
  .cons (p7_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p7_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j5 : List Byte := [0x75, 0x19]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `147`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p8_6 : ∀ feat, Dec feat p8 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b8 (prof : Profile) : Blk prof p8 0 14 o8 :=
  .cons (p8_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.pop) (by decide) <|
  .cons (p8_5 _) (OpI.pop) (by decide) <|
  .cons (p8_6 _) (OpI.pop) (by decide) <|
  .cons (p8_8 _) (OpI.pop) (by decide) <|
  .cons (p8_10 _) (OpI.pop) (by decide) <|
  .cons (p8_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `168`. -/
def p9 : List Byte := [
  0x31, 0xc0]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b9 (prof : Profile) : Blk prof p9 0 2 o9 :=
  .cons (p9_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j6 : List Byte := [0xeb, 0xd7]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551575] 2) := by dec_rfl

end FV7z.Rst
