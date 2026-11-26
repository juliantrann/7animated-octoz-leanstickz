import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `SortFileNames` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 36 of them) and each distinct jump (`j*`, 19) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sfn
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x49, 0x89, 0xfd, 0x41, 0x54, 0x55,
  0x48, 0x89, 0xf5, 0x53, 0x48, 0x83, 0xec, 0x48, 0x44, 0x8b, 0x67, 0x08, 0x64, 0x48, 0x8b, 0x04,
  0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x38, 0x31, 0xc0, 0xc7, 0x46, 0x08, 0x00,
  0x00, 0x00, 0x00, 0x44, 0x3b, 0x66, 0x0c]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 32 [gr 32 12, .mem (mg (some 7) none 1 8 32)] 4) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_37 : ∀ feat, Dec feat p0 37 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 56 64), gr 64 0] 5) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 32 [.mem (mg (some 6) none 1 8 32), .imm 32 0] 7) := by dec_rfl
theorem p0_51 : ∀ feat, Dec feat p0 51 (FV7z.mk .cmp 32 [gr 32 12, .mem (mg (some 6) none 1 12 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.mov 64 13 (.r 7),
  Op.push 12,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.sub 64 4 (.i 72),
  Op.ld 32 12 (some 7) none 1 8,
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 56 0,
  Op.xor 32 0 (.r 0),
  Op.sti 32 (some 6) none 1 8 0,
  Op.cmpm 32 12 (some 6) none 1 12]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5dca70 : Addr) fb 0 55 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_6 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_13 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_15 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_16 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_19 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_20 _) (((OpI.sub (.i 72) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_24 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_28 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_37 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_42 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_44 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p0_51 _) (((OpI.cmpm (.inl rfl)).at _).fs _) (by decide) <|
  .nil 55

def j0 : List Byte := [0x76, 0x39]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 57] 2) := by dec_rfl

/-- The stretch at `57`. -/
def p1 : List Byte := [
  0x45, 0x85, 0xe4]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 32 12 (.r 12)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `66`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x3e, 0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 6) none 1 0,
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 6 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x74, 0x05]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `79`. -/
def p3 : List Byte := [
  0x48, 0xc7, 0x45, 0x00, 0x00, 0x00, 0x00, 0x00, 0x44, 0x89, 0xe7, 0xc7, 0x45, 0x0c, 0x00, 0x00,
  0x00, 0x00, 0x48, 0xc1, 0xe7, 0x02]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), .imm 64 0] 8) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 12 32), .imm 32 0] 7) := by dec_rfl
theorem p3_18 : ∀ feat, Dec feat p3 18 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sti 64 (some 5) none 1 0 0,
  Op.mov 32 7 (.r 12),
  Op.sti 32 (some 5) none 1 12 0,
  Op.shl64 7 (.i 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 22 o3 :=
  .cons (p3_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_8 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p3_18 _) (OpI.shl64 (.i 2)) (by decide) <|
  .nil 22

/-- The stretch at `106`. -/
def p4 : List Byte := [
  0x44, 0x89, 0x65, 0x0c, 0x48, 0x89, 0x45, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 12 32), gr 32 12] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 0 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 32 (some 5) none 1 12 12,
  Op.st 64 (some 5) none 1 0 0]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 8

/-- The stretch at `114`. -/
def p5 : List Byte := [
  0x44, 0x89, 0x65, 0x08, 0x45, 0x85, 0xe4]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 8 32), gr 32 12] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .test 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 32 (some 5) none 1 8 12,
  Op.test 32 12 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p5_4 _) (OpI.test (.r 12) (.inl rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x0f, 0x84, 0x11, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 273] 6) := by dec_rfl

/-- The stretch at `127`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x5d, 0x00, 0x41, 0x8d, 0x4c, 0x24, 0xff, 0x31, 0xc0, 0x66, 0x0f, 0x1f, 0x44, 0x00,
  0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 5) none 1 0 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 12) none 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p6_9 : ∀ feat, Dec feat p6 9 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 3 (some 5) none 1 0,
  Op.lea 32 1 (some 12) none 1 18446744073709551615,
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b6 (prof : Profile) : Blk prof p6 0 17 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p6_9 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p6_11 _) (OpI.nop) (by decide) <|
  .nil 17

/-- The stretch at `144`. -/
def p7 : List Byte := [
  0x48, 0x89, 0xc2, 0x89, 0x04, 0x83, 0x48, 0x83, 0xc0, 0x01, 0x48, 0x39, 0xd1]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 0) 4 0 32), gr 32 0] 3) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 2 (.r 0),
  Op.st 32 (some 3) (some 0) 4 0 0,
  Op.add 64 0 (.i 1),
  Op.cmp 64 1 (.r 2)]

theorem b7 (prof : Profile) : Blk prof p7 0 13 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p7_6 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 13

def j3 : List Byte := [0x75, 0xf1]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551601] 2) := by dec_rfl

/-- The stretch at `159`. -/
def p8 : List Byte := [
  0x8b, 0x45, 0x08, 0x48, 0x83, 0xf8, 0x01]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 8 32)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 0 (some 5) none 1 8,
  Op.cmp 64 0 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.cmp (.i 1) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x0f, 0x86, 0xe4, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 6) 64 [.rel 228] 6) := by dec_rfl

/-- The stretch at `172`. -/
def p9 : List Byte := [
  0x48, 0x8d, 0x68, 0xff, 0x48, 0xd1, 0xe8, 0x4c, 0x8d, 0x78, 0xff, 0x48, 0x8d, 0x44, 0x00, 0xff,
  0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8d, 0x44, 0x24, 0x34, 0x48, 0x89, 0x44, 0x24, 0x28, 0x0f,
  0x1f, 0x44, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .shr 64 [gr 64 0, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .lea 64 [gr 64 15, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 0) 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p9_16 : ∀ feat, Dec feat p9 16 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 32 64), gr 64 0] 5) := by dec_rfl
theorem p9_21 : ∀ feat, Dec feat p9 21 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 4) none 1 52 0)] 5) := by dec_rfl
theorem p9_26 : ∀ feat, Dec feat p9 26 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), gr 64 0] 5) := by dec_rfl
theorem p9_31 : ∀ feat, Dec feat p9 31 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lea 64 5 (some 0) none 1 18446744073709551615,
  Op.shr64 0 (.i 1),
  Op.lea 64 15 (some 0) none 1 18446744073709551615,
  Op.lea 64 0 (some 0) (some 0) 1 18446744073709551615,
  Op.st 64 (some 4) none 1 32 0,
  Op.lea 64 0 (some 4) none 1 52,
  Op.st 64 (some 4) none 1 40 0,
  Op.nop]

theorem b9 (prof : Profile) : Blk prof p9 0 36 o9 :=
  .cons (p9_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.shr64 (.i 1)) (by decide) <|
  .cons (p9_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_16 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p9_21 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p9_26 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p9_31 _) (OpI.nop) (by decide) <|
  .nil 36

/-- The stretch at `208`. -/
def p10 : List Byte := [
  0x42, 0x8b, 0x0c, 0xbb, 0x48, 0x8b, 0x74, 0x24, 0x20, 0x4a, 0x8d, 0x14, 0xbb, 0x4b, 0x8d, 0x04,
  0x3f, 0x89, 0x4c, 0x24, 0x34, 0x48, 0x39, 0xf5]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 3) (some 15) 4 0 32)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 32 64)] 5) := by dec_rfl
theorem p10_9 : ∀ feat, Dec feat p10 9 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 3) (some 15) 4 0 0)] 4) := by dec_rfl
theorem p10_13 : ∀ feat, Dec feat p10 13 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 15) (some 15) 1 0 0)] 4) := by dec_rfl
theorem p10_17 : ∀ feat, Dec feat p10 17 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 52 32), gr 32 1] 4) := by dec_rfl
theorem p10_21 : ∀ feat, Dec feat p10 21 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 32 1 (some 3) (some 15) 4 0,
  Op.ld 64 6 (some 4) none 1 32,
  Op.lea 64 2 (some 3) (some 15) 4 0,
  Op.lea 64 0 (some 15) (some 15) 1 0,
  Op.st 32 (some 4) none 1 52 1,
  Op.cmp 64 5 (.r 6)]

theorem b10 (prof : Profile) : Blk prof p10 0 24 o10 :=
  .cons (p10_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p10_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_17 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p10_21 _) (OpI.cmp (.r 6) (.inr rfl)) (by decide) <|
  .nil 24

def j5 : List Byte := [0x0f, 0x82, 0x8c, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 2) 64 [.rel 140] 6) := by dec_rfl

/-- The stretch at `238`. -/
def p11 : List Byte := [
  0x4c, 0x89, 0x7c, 0x24, 0x08, 0x49, 0x89, 0xf6]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 15] 5) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.st 64 (some 4) none 1 8 15,
  Op.mov 64 14 (.r 6)]

theorem b11 (prof : Profile) : Blk prof p11 0 8 o11 :=
  .cons (p11_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_5 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .nil 8

def j6 : List Byte := [0xeb, 0x27]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `256`. -/
def p12 : List Byte := [
  0x41, 0x8b, 0x04, 0x24, 0x89, 0x02, 0x4b, 0x8d, 0x04, 0x36, 0x48, 0x8d, 0x50, 0x01, 0x48, 0x39,
  0xd5]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 12) none 1 0 32)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p12_6 : ∀ feat, Dec feat p12 6 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 14) (some 14) 1 0 0)] 4) := by dec_rfl
theorem p12_10 : ∀ feat, Dec feat p12 10 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p12_14 : ∀ feat, Dec feat p12 14 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 32 0 (some 12) none 1 0,
  Op.st 32 (some 2) none 1 0 0,
  Op.lea 64 0 (some 14) (some 14) 1 0,
  Op.lea 64 2 (some 0) none 1 1,
  Op.cmp 64 5 (.r 2)]

theorem b12 (prof : Profile) : Blk prof p12 0 17 o12 :=
  .cons (p12_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p12_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_14 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 17

def j7 : List Byte := [0x0f, 0x82, 0x59, 0x01, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 2) 64 [.rel 345] 6) := by dec_rfl

/-- The stretch at `279`. -/
def p13 : List Byte := [
  0x4c, 0x89, 0x74, 0x24, 0x08, 0x49, 0x89, 0xd6]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 14] 5) := by dec_rfl
theorem p13_5 : ∀ feat, Dec feat p13 5 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.st 64 (some 4) none 1 8 14,
  Op.mov 64 14 (.r 2)]

theorem b13 (prof : Profile) : Blk prof p13 0 8 o13 :=
  .cons (p13_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p13_5 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `287`. -/
def p14 : List Byte := [
  0x4e, 0x8d, 0x24, 0xb3, 0x4c, 0x39, 0xf5]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 3) (some 14) 4 0 0)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.lea 64 12 (some 3) (some 14) 4 0,
  Op.cmp 64 5 (.r 14)]

theorem b14 (prof : Profile) : Blk prof p14 0 7 o14 :=
  .cons (p14_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.cmp (.r 14) (.inr rfl)) (by decide) <|
  .nil 7

def j8 : List Byte := [0x76, 0x31]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 6) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `296`. -/
def p15 : List Byte := [
  0x4c, 0x8d, 0x40, 0x02, 0x4c, 0x89, 0xe6, 0x4c, 0x89, 0xea, 0x4a, 0x8d, 0x3c, 0x83, 0x4c, 0x89,
  0x44, 0x24, 0x18, 0x48, 0x89, 0x7c, 0x24, 0x10]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 0) none 1 2 0)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) (some 8) 4 0 0)] 4) := by dec_rfl
theorem p15_14 : ∀ feat, Dec feat p15 14 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 8] 5) := by dec_rfl
theorem p15_19 : ∀ feat, Dec feat p15 19 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 7] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.lea 64 8 (some 0) none 1 2,
  Op.mov 64 6 (.r 12),
  Op.mov 64 2 (.r 13),
  Op.lea 64 7 (some 3) (some 8) 4 0,
  Op.st 64 (some 4) none 1 24 8,
  Op.st 64 (some 4) none 1 16 7]

theorem b15 (prof : Profile) : Blk prof p15 0 24 o15 :=
  .cons (p15_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p15_7 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p15_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p15_14 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p15_19 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 24

/-- The stretch at `325`. -/
def p16 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x10, 0x4c, 0x8b, 0x44, 0x24, 0x18, 0x85, 0xc0, 0x4c, 0x0f, 0x4f, 0xe7,
  0x4d, 0x0f, 0x4f, 0xf0]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p16_5 : ∀ feat, Dec feat p16 5 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p16_10 : ∀ feat, Dec feat p16 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_12 : ∀ feat, Dec feat p16 12 (FV7z.mk (.cmovcc 15) 64 [gr 64 12, gr 64 7] 4) := by dec_rfl
theorem p16_16 : ∀ feat, Dec feat p16 16 (FV7z.mk (.cmovcc 15) 64 [gr 64 14, gr 64 8] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.ld 64 7 (some 4) none 1 16,
  Op.ld 64 8 (some 4) none 1 24,
  Op.test 32 0 (.r 0),
  Op.cmov64 15 12 7,
  Op.cmov64 15 14 8]

theorem b16 (prof : Profile) : Blk prof p16 0 20 o16 :=
  .cons (p16_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_12 _) (OpI.cmov64) (by decide) <|
  .cons (p16_16 _) (OpI.cmov64) (by decide) <|
  .nil 20

/-- The stretch at `345`. -/
def p17 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x28, 0x4c, 0x89, 0xea, 0x4c, 0x89, 0xe6]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p17_5 : ∀ feat, Dec feat p17 5 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p17_8 : ∀ feat, Dec feat p17 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.ld 64 7 (some 4) none 1 40,
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 12)]

theorem b17 (prof : Profile) : Blk prof p17 0 11 o17 :=
  .cons (p17_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p17_5 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p17_8 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `361`. -/
def p18 : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x08, 0x48, 0x8d, 0x14, 0xb3, 0x85, 0xc0]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p18_5 : ∀ feat, Dec feat p18 5 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 3) (some 6) 4 0 0)] 4) := by dec_rfl
theorem p18_9 : ∀ feat, Dec feat p18 9 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.ld 64 6 (some 4) none 1 8,
  Op.lea 64 2 (some 3) (some 6) 4 0,
  Op.test 32 0 (.r 0)]

theorem b18 (prof : Profile) : Blk prof p18 0 11 o18 :=
  .cons (p18_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p18_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p18_9 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 11

def j9 : List Byte := [0x78, 0x8a]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 8) 64 [.rel 18446744073709551498] 2) := by dec_rfl

/-- The stretch at `374`. -/
def p19 : List Byte := [
  0x8b, 0x4c, 0x24, 0x34]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 52 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 32 1 (some 4) none 1 52]

theorem b19 (prof : Profile) : Blk prof p19 0 4 o19 :=
  .cons (p19_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `384`. -/
def p20 : List Byte := [
  0x89, 0x0a, 0x4d, 0x85, 0xff]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 0 32), gr 32 1] 2) := by dec_rfl
theorem p20_2 : ∀ feat, Dec feat p20 2 (FV7z.mk .test 64 [gr 64 15, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.st 32 (some 2) none 1 0 1,
  Op.test 64 15 (.r 15)]

theorem b20 (prof : Profile) : Blk prof p20 0 5 o20 :=
  .cons (p20_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p20_2 _) (OpI.test (.r 15) (.inr rfl)) (by decide) <|
  .nil 5

def j10 : List Byte := [0x74, 0x3a]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 58] 2) := by dec_rfl

/-- The stretch at `391`. -/
def p21 : List Byte := [
  0x49, 0x83, 0xef, 0x01]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .sub 64 [gr 64 15, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.sub 64 15 (.i 1)]

theorem b21 (prof : Profile) : Blk prof p21 0 4 o21 :=
  .cons (p21_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 4

def j11 : List Byte := [0xe9, 0x40, 0xff, 0xff, 0xff]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551424] 5) := by dec_rfl

/-- The stretch at `400`. -/
def p22 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x38, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 56 64)] 5) := by dec_rfl
theorem p22_5 : ∀ feat, Dec feat p22 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o22 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 56,
  Op.xormf fb 64 0 none none 1 40]

theorem b22 (prof : Profile) (fb : Addr) : BlkF prof p22 (0x5dcc00 : Addr) fb 0 14 (o22 fb) :=
  .cons (p22_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p22_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j12 : List Byte := [0x0f, 0x85, 0xd8, 0x00, 0x00, 0x00]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 216] 6) := by dec_rfl

/-- The stretch at `420`. -/
def p23 : List Byte := [
  0x48, 0x83, 0xc4, 0x48, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 72)] 4) := by dec_rfl
theorem p23_4 : ∀ feat, Dec feat p23 4 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p23_6 : ∀ feat, Dec feat p23 6 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p23_8 : ∀ feat, Dec feat p23 8 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p23_10 : ∀ feat, Dec feat p23 10 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p23_12 : ∀ feat, Dec feat p23 12 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.add 64 4 (.i 72),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b23 (prof : Profile) : Blk prof p23 0 14 o23 :=
  .cons (p23_0 _) (OpI.add (.i 72) (.inr rfl)) (by decide) <|
  .cons (p23_4 _) (OpI.pop) (by decide) <|
  .cons (p23_5 _) (OpI.pop) (by decide) <|
  .cons (p23_6 _) (OpI.pop) (by decide) <|
  .cons (p23_8 _) (OpI.pop) (by decide) <|
  .cons (p23_10 _) (OpI.pop) (by decide) <|
  .cons (p23_12 _) (OpI.pop) (by decide) <|
  .nil 14

/-- The stretch at `440`. -/
def p24 : List Byte := [
  0x8b, 0x54, 0x24, 0x34, 0x4c, 0x89, 0xf8, 0x89, 0x10]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 52 32)] 4) := by dec_rfl
theorem p24_4 : ∀ feat, Dec feat p24 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p24_7 : ∀ feat, Dec feat p24 7 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), gr 32 2] 2) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.ld 32 2 (some 4) none 1 52,
  Op.mov 64 0 (.r 15),
  Op.st 32 (some 0) none 1 0 2]

theorem b24 (prof : Profile) : Blk prof p24 0 9 o24 :=
  .cons (p24_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p24_4 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p24_7 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 9

/-- The stretch at `449`. -/
def p25 : List Byte := [
  0x8b, 0x04, 0xab, 0x8b, 0x13, 0x89, 0x14, 0xab, 0x89, 0x03, 0x89, 0x44, 0x24, 0x34, 0x48, 0x83,
  0xed, 0x01]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) (some 5) 4 0 32)] 3) := by dec_rfl
theorem p25_3 : ∀ feat, Dec feat p25 3 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 3) none 1 0 32)] 2) := by dec_rfl
theorem p25_5 : ∀ feat, Dec feat p25 5 (FV7z.mk .mov 32 [.mem (mg (some 3) (some 5) 4 0 32), gr 32 2] 3) := by dec_rfl
theorem p25_8 : ∀ feat, Dec feat p25 8 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p25_10 : ∀ feat, Dec feat p25 10 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 52 32), gr 32 0] 4) := by dec_rfl
theorem p25_14 : ∀ feat, Dec feat p25 14 (FV7z.mk .sub 64 [gr 64 5, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.ld 32 0 (some 3) (some 5) 4 0,
  Op.ld 32 2 (some 3) none 1 0,
  Op.st 32 (some 3) (some 5) 4 0 2,
  Op.st 32 (some 3) none 1 0 0,
  Op.st 32 (some 4) none 1 52 0,
  Op.sub 64 5 (.i 1)]

theorem b25 (prof : Profile) : Blk prof p25 0 18 o25 :=
  .cons (p25_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p25_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p25_5 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p25_8 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p25_10 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p25_14 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .nil 18

def j13 : List Byte := [0x74, 0xbb]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551547] 2) := by dec_rfl

/-- The stretch at `469`. -/
def p26 : List Byte := [
  0x48, 0x8d, 0x4c, 0x24, 0x34, 0x31, 0xc0, 0x45, 0x31, 0xf6, 0x41, 0xbc, 0x01, 0x00, 0x00, 0x00,
  0x48, 0x89, 0x4c, 0x24, 0x18]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 4) none 1 52 0)] 5) := by dec_rfl
theorem p26_5 : ∀ feat, Dec feat p26 5 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p26_7 : ∀ feat, Dec feat p26 7 (FV7z.mk .xor 32 [gr 32 14, Src.opd 32 (.r 14)] 3) := by dec_rfl
theorem p26_10 : ∀ feat, Dec feat p26 10 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p26_16 : ∀ feat, Dec feat p26 16 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 1] 5) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.lea 64 1 (some 4) none 1 52,
  Op.xor 32 0 (.r 0),
  Op.xor 32 14 (.r 14),
  Op.mov 32 12 (.i 1),
  Op.st 64 (some 4) none 1 24 1]

theorem b26 (prof : Profile) : Blk prof p26 0 21 o26 :=
  .cons (p26_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p26_5 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p26_7 _) (OpI.xor (.r 14) (.inl rfl)) (by decide) <|
  .cons (p26_10 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p26_16 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 21

def j14 : List Byte := [0xeb, 0x1c]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk .jmp 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `496`. -/
def p27 : List Byte := [
  0x41, 0x8b, 0x17, 0x89, 0x10, 0x4b, 0x8d, 0x04, 0x24, 0x48, 0x8d, 0x50, 0x01, 0x48, 0x39, 0xd5]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 15) none 1 0 32)] 3) := by dec_rfl
theorem p27_3 : ∀ feat, Dec feat p27 3 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), gr 32 2] 2) := by dec_rfl
theorem p27_5 : ∀ feat, Dec feat p27 5 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 12) (some 12) 1 0 0)] 4) := by dec_rfl
theorem p27_9 : ∀ feat, Dec feat p27 9 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 1 0)] 4) := by dec_rfl
theorem p27_13 : ∀ feat, Dec feat p27 13 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.ld 32 2 (some 15) none 1 0,
  Op.st 32 (some 0) none 1 0 2,
  Op.lea 64 0 (some 12) (some 12) 1 0,
  Op.lea 64 2 (some 0) none 1 1,
  Op.cmp 64 5 (.r 2)]

theorem b27 (prof : Profile) : Blk prof p27 0 16 o27 :=
  .cons (p27_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p27_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p27_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p27_9 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p27_13 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 16

def j15 : List Byte := [0x72, 0xb6]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551542] 2) := by dec_rfl

/-- The stretch at `514`. -/
def p28 : List Byte := [
  0x4d, 0x89, 0xe6, 0x49, 0x89, 0xd4]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p28_3 : ∀ feat, Dec feat p28 3 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.mov 64 14 (.r 12),
  Op.mov 64 12 (.r 2)]

theorem b28 (prof : Profile) : Blk prof p28 0 6 o28 :=
  .cons (p28_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p28_3 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `520`. -/
def p29 : List Byte := [
  0x4e, 0x8d, 0x3c, 0xa3, 0x4c, 0x39, 0xe5]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .lea 64 [gr 64 15, .mem (mg (some 3) (some 12) 4 0 0)] 4) := by dec_rfl
theorem p29_4 : ∀ feat, Dec feat p29 4 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.lea 64 15 (some 3) (some 12) 4 0,
  Op.cmp 64 5 (.r 12)]

theorem b29 (prof : Profile) : Blk prof p29 0 7 o29 :=
  .cons (p29_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p29_4 _) (OpI.cmp (.r 12) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `529`. -/
def p30 : List Byte := [
  0x48, 0x8d, 0x48, 0x02, 0x4c, 0x89, 0xfe, 0x4c, 0x89, 0xea, 0x48, 0x8d, 0x3c, 0x8b, 0x48, 0x89,
  0x4c, 0x24, 0x10, 0x48, 0x89, 0x7c, 0x24, 0x08]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 2 0)] 4) := by dec_rfl
theorem p30_4 : ∀ feat, Dec feat p30 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p30_7 : ∀ feat, Dec feat p30 7 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p30_10 : ∀ feat, Dec feat p30 10 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) (some 1) 4 0 0)] 4) := by dec_rfl
theorem p30_14 : ∀ feat, Dec feat p30 14 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 1] 5) := by dec_rfl
theorem p30_19 : ∀ feat, Dec feat p30 19 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 7] 5) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.lea 64 1 (some 0) none 1 2,
  Op.mov 64 6 (.r 15),
  Op.mov 64 2 (.r 13),
  Op.lea 64 7 (some 3) (some 1) 4 0,
  Op.st 64 (some 4) none 1 16 1,
  Op.st 64 (some 4) none 1 8 7]

theorem b30 (prof : Profile) : Blk prof p30 0 24 o30 :=
  .cons (p30_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p30_4 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .cons (p30_7 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p30_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p30_14 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p30_19 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 24

/-- The stretch at `558`. -/
def p31 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x08, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x85, 0xc0, 0x4c, 0x0f, 0x4f, 0xff,
  0x4c, 0x0f, 0x4f, 0xe1]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p31_5 : ∀ feat, Dec feat p31 5 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p31_10 : ∀ feat, Dec feat p31 10 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p31_12 : ∀ feat, Dec feat p31 12 (FV7z.mk (.cmovcc 15) 64 [gr 64 15, gr 64 7] 4) := by dec_rfl
theorem p31_16 : ∀ feat, Dec feat p31 16 (FV7z.mk (.cmovcc 15) 64 [gr 64 12, gr 64 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.ld 64 7 (some 4) none 1 8,
  Op.ld 64 1 (some 4) none 1 16,
  Op.test 32 0 (.r 0),
  Op.cmov64 15 15 7,
  Op.cmov64 15 12 1]

theorem b31 (prof : Profile) : Blk prof p31 0 20 o31 :=
  .cons (p31_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_5 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p31_10 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .cons (p31_12 _) (OpI.cmov64) (by decide) <|
  .cons (p31_16 _) (OpI.cmov64) (by decide) <|
  .nil 20

/-- The stretch at `578`. -/
def p32 : List Byte := [
  0x48, 0x8b, 0x7c, 0x24, 0x18, 0x4c, 0x89, 0xea, 0x4c, 0x89, 0xfe]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p32_5 : ∀ feat, Dec feat p32 5 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p32_8 : ∀ feat, Dec feat p32 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.ld 64 7 (some 4) none 1 24,
  Op.mov 64 2 (.r 13),
  Op.mov 64 6 (.r 15)]

theorem b32 (prof : Profile) : Blk prof p32 0 11 o32 :=
  .cons (p32_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p32_5 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p32_8 _) (OpI.mov (.r 15) (.inr rfl)) (by decide) <|
  .nil 11

/-- The stretch at `594`. -/
def p33 : List Byte := [
  0x41, 0x89, 0xc0, 0x4a, 0x8d, 0x04, 0xb3, 0x45, 0x85, 0xc0]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p33_3 : ∀ feat, Dec feat p33 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) (some 14) 4 0 0)] 4) := by dec_rfl
theorem p33_7 : ∀ feat, Dec feat p33 7 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.mov 32 8 (.r 0),
  Op.lea 64 0 (some 3) (some 14) 4 0,
  Op.test 32 8 (.r 8)]

theorem b33 (prof : Profile) : Blk prof p33 0 10 o33 :=
  .cons (p33_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p33_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p33_7 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 10

def j16 : List Byte := [0x78, 0x92]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 8) 64 [.rel 18446744073709551506] 2) := by dec_rfl

/-- The stretch at `606`. -/
def p34 : List Byte := [
  0x8b, 0x54, 0x24, 0x34, 0x89, 0x10]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 4) none 1 52 32)] 4) := by dec_rfl
theorem p34_4 : ∀ feat, Dec feat p34 4 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), gr 32 2] 2) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.ld 32 2 (some 4) none 1 52,
  Op.st 32 (some 0) none 1 0 2]

theorem b34 (prof : Profile) : Blk prof p34 0 6 o34 :=
  .cons (p34_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p34_4 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 6

def j17 : List Byte := [0xe9, 0x58, 0xff, 0xff, 0xff]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551448] 5) := by dec_rfl

/-- The stretch at `624`. -/
def p35 : List Byte := [
  0x8b, 0x4c, 0x24, 0x34, 0x4c, 0x89, 0xe2]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 4) none 1 52 32)] 4) := by dec_rfl
theorem p35_4 : ∀ feat, Dec feat p35 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.ld 32 1 (some 4) none 1 52,
  Op.mov 64 2 (.r 12)]

theorem b35 (prof : Profile) : Blk prof p35 0 7 o35 :=
  .cons (p35_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p35_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 7

def j18 : List Byte := [0xe9, 0xfe, 0xfe, 0xff, 0xff]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk .jmp 64 [.rel 18446744073709551358] 5) := by dec_rfl

end FV7z.Sfn
