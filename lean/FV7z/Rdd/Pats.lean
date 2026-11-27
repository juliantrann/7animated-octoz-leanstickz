import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps13
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__readdir` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rdd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x49, 0x89, 0xfe, 0x41, 0x55, 0x41, 0x54, 0x55, 0x48, 0xc7,
  0xc5, 0xb8, 0xff, 0xff, 0xff, 0x53, 0x64, 0x44, 0x8b, 0x6d, 0x00, 0x64, 0x8b, 0x04, 0x25, 0x18,
  0x00, 0x00, 0x00, 0x4c, 0x8d, 0x67, 0x04, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 32 [gr 32 13, .mem (mf (some 5) none 1 0 32)] 5) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 7) none 1 4 0)] 4) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 14,
  Op.mov 64 14 (.r 7),
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.i 18446744073709551544),
  Op.push 3,
  Op.ldf fb 32 13 (some 5) none 1 0,
  Op.ldf fb 32 0 none none 1 24,
  Op.lea 64 12 (some 7) none 1 4,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x6638a0 : Addr) fb 0 41 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_9 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_11 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_22 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p0_27 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p0_35 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_39 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 41

def j0 : List Byte := [0x0f, 0x85, 0xce, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 206] 6) := by dec_rfl

/-- The stretch at `47`. -/
def p1 : List Byte := [
  0xba, 0x01, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 2 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0x49, 0x8b, 0x56, 0x18, 0x49, 0x8b, 0x46, 0x10, 0x49, 0x8d, 0x5e, 0x30]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 14) none 1 24 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 14) none 1 16 64)] 4) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 14) none 1 48 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 2 (some 14) none 1 24,
  Op.ld 64 0 (some 14) none 1 16,
  Op.lea 64 3 (some 14) none 1 48]

theorem b2 (prof : Profile) : Blk prof p2 0 12 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0xeb, 0x27]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p3 : List Byte := [
  0x4d, 0x01, 0xf0, 0x41, 0x0f, 0xb7, 0x48, 0x10, 0x48, 0x01, 0xca, 0x49, 0x8b, 0x48, 0x08, 0x49,
  0x83, 0x38, 0x00, 0x49, 0x89, 0x56, 0x18, 0x49, 0x89, 0x4e, 0x20]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 8, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 8) none 1 16 16)] 5) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 8) none 1 8 64)] 4) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .cmp 64 [.mem (mg (some 8) none 1 0 64), .imm 64 0] 4) := by dec_rfl
theorem p3_19 : ∀ feat, Dec feat p3 19 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 24 64), gr 64 2] 4) := by dec_rfl
theorem p3_23 : ∀ feat, Dec feat p3 23 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 32 64), gr 64 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 8 (.r 14),
  Op.ldzx 16 1 (some 8) none 1 16,
  Op.add 64 2 (.r 1),
  Op.ld 64 1 (some 8) none 1 8,
  Op.cmpmi 64 (some 8) none 1 0 0,
  Op.st 64 (some 14) none 1 24 2,
  Op.st 64 (some 14) none 1 32 1]

theorem b3 (prof : Profile) : Blk prof p3 0 27 o3 :=
  .cons (p3_0 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.add (.r 1) (.inr rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_15 _) (OpI.cmpmi64) (by decide) <|
  .cons (p3_19 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_23 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 27

def j2 : List Byte := [0x75, 0x43]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 67] 2) := by dec_rfl

/-- The stretch at `109`. -/
def p4 : List Byte := [
  0x4c, 0x8d, 0x42, 0x30, 0x48, 0x39, 0xc2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 2) none 1 48 0)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lea 64 8 (some 2) none 1 48,
  Op.cmp 64 2 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.cmp (.r 0) (.inr rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x72, 0xda]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551578] 2) := by dec_rfl

/-- The stretch at `118`. -/
def p5 : List Byte := [
  0x49, 0x8b, 0x56, 0x08, 0x41, 0x8b, 0x3e, 0x48, 0x89, 0xde]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 14) none 1 8 64)] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 14) none 1 0 32)] 3) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 2 (some 14) none 1 8,
  Op.ld 32 7 (some 14) none 1 0,
  Op.mov 64 6 (.r 3)]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `133`. -/
def p6 : List Byte := [
  0x48, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.test 64 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x7e, 0x16]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 14) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `138`. -/
def p7 : List Byte := [
  0x49, 0x89, 0x46, 0x10, 0x31, 0xd2, 0x41, 0xb8, 0x30, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 16 64), gr 64 0] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 48)] 6) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.st 64 (some 14) none 1 16 0,
  Op.xor 32 2 (.r 2),
  Op.mov 32 8 (.i 48)]

theorem b7 (prof : Profile) : Blk prof p7 0 12 o7 :=
  .cons (p7_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_4 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.mov (.i 48) (.inl rfl)) (by decide) <|
  .nil 12

def j5 : List Byte := [0xeb, 0xb8]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551544] 2) := by dec_rfl

def j6 : List Byte := [0x75, 0x2b]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `162`. -/
def p8 : List Byte := [
  0x64, 0x44, 0x89, 0x6d, 0x00, 0x45, 0x31, 0xc0, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [.mem (mf (some 5) none 1 0 32), gr 32 13] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o8 (fb : Addr) : List Op := [
  Op.stf fb 32 (some 5) none 1 0 13,
  Op.xor 32 8 (.r 8),
  Op.nop]

theorem b8 (prof : Profile) (fb : Addr) : BlkF prof p8 (0x663942 : Addr) fb 0 14 (o8 fb) :=
  .cons (p8_0 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .cons (p8_5 _) (((OpI.xor (.r 8) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p8_8 _) (((OpI.nop).at _).fs _) (by decide) <|
  .nil 14

/-- The stretch at `176`. -/
def p9 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b9 (prof : Profile) (fb : Addr) : BlkF prof p9 (0x663950 : Addr) fb 0 10 (o9 fb) :=
  .cons (p9_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p9_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 10

def j7 : List Byte := [0x75, 0x1d]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `193`. -/
def p10 : List Byte := [
  0x5b, 0x4c, 0x89, 0xc0, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p10_1 : ∀ feat, Dec feat p10 1 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p10_9 : ∀ feat, Dec feat p10 9 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.pop 3,
  Op.mov 64 0 (.r 8),
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b10 (prof : Profile) : Blk prof p10 0 11 o10 :=
  .cons (p10_0 _) (OpI.pop) (by decide) <|
  .cons (p10_1 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.pop) (by decide) <|
  .cons (p10_5 _) (OpI.pop) (by decide) <|
  .cons (p10_7 _) (OpI.pop) (by decide) <|
  .cons (p10_9 _) (OpI.pop) (by decide) <|
  .nil 11

/-- The stretch at `205`. -/
def p11 : List Byte := [
  0x45, 0x31, 0xc0, 0x64, 0x83, 0x7d, 0x00, 0x02]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .cmp 32 [.mem (mf (some 5) none 1 0 32), .imm 32 2] 5) := by dec_rfl

/-- What the stretch does. -/
def o11 (fb : Addr) : List Op := [
  Op.xor 32 8 (.r 8),
  Op.cmpmif fb 32 (some 5) none 1 0 2]

theorem b11 (prof : Profile) (fb : Addr) : BlkF prof p11 (0x66396d : Addr) fb 0 8 (o11 fb) :=
  .cons (p11_0 _) (((OpI.xor (.r 8) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p11_3 _) (OpIF.cmpmif (.inl rfl)) (by decide) <|
  .nil 8

def j8 : List Byte := [0x75, 0xd9]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551577] 2) := by dec_rfl

def j9 : List Byte := [0xeb, 0xc9]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551561] 2) := by dec_rfl

end FV7z.Rdd
