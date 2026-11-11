import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps4
/-!
# The stretches of straight-line code of `__libc_setup_tls` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 16 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Tls
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83,
  0xec, 0x28, 0x48, 0x8b, 0x05, 0x57, 0x4b, 0x19, 0x00, 0x4c, 0x8b, 0x35, 0x10, 0xfa, 0x17, 0x00,
  0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1657687 64)] 7) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [gr 64 14, .mem (mrip 1571344 64)] 7) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 40),
  Op.lda 64 0 8029568,
  Op.lda 64 14 7943232,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x613a10 : Addr) 0 35 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_8 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_10 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_12 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_14 _) ((OpI.sub (.i 40) (.inr rfl)).at _) (by decide) <|
  .cons (p0_18 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_25 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_32 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 35

def j0 : List Byte := [0x0f, 0x84, 0xe7, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 487] 6) := by dec_rfl

/-- The stretch at `41`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x0d, 0x58, 0x4b, 0x19, 0x00, 0x48, 0x8d, 0x14, 0xcd, 0x00, 0x00, 0x00, 0x00, 0x48,
  0x29, 0xca, 0x48, 0x8d, 0x14, 0xd0, 0x48, 0x39, 0xd0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mrip 1657688 64)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .lea 64 [gr 64 2, .mem (mg none (some 1) 8 0 0)] 8) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p1_18 : ∀ feat, Dec feat p1 18 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) (some 2) 8 0 0)] 4) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lda 64 1 8029592,
  Op.lea 64 2 none (some 1) 8 0,
  Op.sub 64 2 (.r 1),
  Op.lea 64 2 (some 0) (some 2) 8 0,
  Op.cmp 64 0 (.r 2)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x613a39 : Addr) 0 25 o1 :=
  .cons (p1_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_7 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p1_15 _) ((OpI.sub (.r 1) (.inr rfl)).at _) (by decide) <|
  .cons (p1_18 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p1_22 _) ((OpI.cmp (.r 2) (.inr rfl)).at _) (by decide) <|
  .nil 25

def j1 : List Byte := [0x72, 0x19]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 2) 64 [.rel 25] 2) := by dec_rfl

def j2 : List Byte := [0xe9, 0xc7, 0x01, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 455] 5) := by dec_rfl

/-- The stretch at `80`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc0, 0x38, 0x48, 0x39, 0xd0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 56)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 0 (.i 56),
  Op.cmp 64 0 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.add (.i 56) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x0f, 0x83, 0xb3, 0x01, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 3) 64 [.rel 435] 6) := by dec_rfl

/-- The stretch at `93`. -/
def p3 : List Byte := [
  0x83, 0x38, 0x07]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [.mem (mg (some 0) none 1 0 32), .imm 32 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpmi 32 (some 0) none 1 0 7]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x75, 0xee]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `98`. -/
def p4 : List Byte := [
  0x4c, 0x8b, 0x60, 0x30, 0x48, 0x8b, 0x58, 0x28, 0xbd, 0x40, 0x00, 0x00, 0x00, 0x41, 0xbf, 0x01,
  0x00, 0x00, 0x00, 0x48, 0x8b, 0x48, 0x20, 0x4c, 0x8b, 0x40, 0x10, 0x48, 0x8b, 0x05, 0x1c, 0xe8,
  0x17, 0x00, 0x4d, 0x03, 0x06, 0x49, 0x83, 0xfc, 0x40, 0x48, 0x89, 0x5c, 0x24, 0x10, 0x49, 0x0f,
  0x43, 0xec, 0x31, 0xd2, 0x48, 0x89, 0x4c, 0x24, 0x08, 0x4d, 0x89, 0xc5, 0x48, 0x8d, 0x44, 0x03,
  0xff, 0x48, 0x01, 0xe8]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mg (some 0) none 1 48 64)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 0) none 1 40 64)] 4) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.i 64)] 5) := by dec_rfl
theorem p4_13 : ∀ feat, Dec feat p4 13 (FV7z.mk .mov 32 [gr 32 15, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p4_19 : ∀ feat, Dec feat p4 19 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 0) none 1 32 64)] 4) := by dec_rfl
theorem p4_23 : ∀ feat, Dec feat p4 23 (FV7z.mk .mov 64 [gr 64 8, .mem (mg (some 0) none 1 16 64)] 4) := by dec_rfl
theorem p4_27 : ∀ feat, Dec feat p4 27 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1566748 64)] 7) := by dec_rfl
theorem p4_34 : ∀ feat, Dec feat p4 34 (FV7z.mk .add 64 [gr 64 8, .mem (mg (some 14) none 1 0 64)] 3) := by dec_rfl
theorem p4_37 : ∀ feat, Dec feat p4 37 (FV7z.mk .cmp 64 [gr 64 12, Src.opd 64 (.i 64)] 4) := by dec_rfl
theorem p4_41 : ∀ feat, Dec feat p4 41 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 3] 5) := by dec_rfl
theorem p4_46 : ∀ feat, Dec feat p4 46 (FV7z.mk (.cmovcc 3) 64 [gr 64 5, gr 64 12] 4) := by dec_rfl
theorem p4_50 : ∀ feat, Dec feat p4 50 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p4_52 : ∀ feat, Dec feat p4 52 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 1] 5) := by dec_rfl
theorem p4_57 : ∀ feat, Dec feat p4 57 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p4_60 : ∀ feat, Dec feat p4 60 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) (some 0) 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p4_65 : ∀ feat, Dec feat p4 65 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 12 (some 0) none 1 48,
  Op.ld 64 3 (some 0) none 1 40,
  Op.mov 32 5 (.i 64),
  Op.mov 32 15 (.i 1),
  Op.ld 64 1 (some 0) none 1 32,
  Op.ld 64 8 (some 0) none 1 16,
  Op.lda 64 0 7938736,
  Op.addm 64 8 (some 14) none 1 0,
  Op.cmp 64 12 (.i 64),
  Op.st 64 (some 4) none 1 16 3,
  Op.cmov64 3 5 12,
  Op.xor 32 2 (.r 2),
  Op.st 64 (some 4) none 1 8 1,
  Op.mov 64 13 (.r 8),
  Op.lea 64 0 (some 3) (some 0) 1 18446744073709551615,
  Op.add 64 0 (.r 5)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x613a72 : Addr) 0 68 o4 :=
  .cons (p4_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p4_4 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p4_8 _) ((OpI.mov (.i 64) (.inl rfl)).at _) (by decide) <|
  .cons (p4_13 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p4_19 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p4_23 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p4_27 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p4_34 _) ((OpI.addm (.inr rfl)).at _) (by decide) <|
  .cons (p4_37 _) ((OpI.cmp (.i 64) (.inr rfl)).at _) (by decide) <|
  .cons (p4_41 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p4_46 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p4_50 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p4_52 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p4_57 _) ((OpI.mov (.r 8) (.inr rfl)).at _) (by decide) <|
  .cons (p4_60 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p4_65 _) ((OpI.add (.r 5) (.inr rfl)).at _) (by decide) <|
  .nil 68

/-- The stretch at `169`. -/
def p5 : List Byte := [
  0x48, 0x0f, 0xaf, 0xc5, 0x48, 0x8d, 0xbc, 0x05, 0x00, 0x09, 0x00, 0x00, 0x48, 0x89, 0xc3]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .imul 64 [gr 64 0, gr 64 5] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 5) (some 0) 1 2304 0)] 8) := by dec_rfl
theorem p5_12 : ∀ feat, Dec feat p5 12 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.imul64 0 5,
  Op.lea 64 7 (some 5) (some 0) 1 2304,
  Op.mov 64 3 (.r 0)]

theorem b5 (prof : Profile) : Blk prof p5 0 15 o5 :=
  .cons (p5_0 _) (OpI.imul64) (by decide) <|
  .cons (p5_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p5_12 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 15

/-- The stretch at `189`. -/
def p6 : List Byte := [
  0x48, 0x89, 0xee, 0x48, 0xc7, 0x05, 0x25, 0x44, 0x19, 0x00, 0x3e, 0x00, 0x00, 0x00, 0x48, 0xf7,
  0xde, 0x48, 0x8d, 0x4c, 0x05, 0xff, 0x48, 0x21, 0xf1, 0x4d, 0x85, 0xe4, 0x4c, 0x89, 0xfe, 0x49,
  0x0f, 0x45, 0xf4]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .mov 64 [.mem (mrip 1655845 64), .imm 64 62] 11) := by dec_rfl
theorem p6_14 : ∀ feat, Dec feat p6 14 (FV7z.mk .neg 64 [gr 64 6] 3) := by dec_rfl
theorem p6_17 : ∀ feat, Dec feat p6 17 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 5) (some 0) 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p6_22 : ∀ feat, Dec feat p6 22 (FV7z.mk .and 64 [gr 64 1, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p6_25 : ∀ feat, Dec feat p6 25 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_28 : ∀ feat, Dec feat p6 28 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 15)] 3) := by dec_rfl
theorem p6_31 : ∀ feat, Dec feat p6 31 (FV7z.mk (.cmovcc 5) 64 [gr 64 6, gr 64 12] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.stia 64 8027904 62,
  Op.neg 64 6,
  Op.lea 64 1 (some 5) (some 0) 1 18446744073709551615,
  Op.and 64 1 (.r 6),
  Op.test 64 12 (.r 12),
  Op.mov 64 6 (.r 15),
  Op.cmov64 5 6 12]

theorem b6 (prof : Profile) : BlkA prof p6 (0x613acd : Addr) 0 35 o6 :=
  .cons (p6_0 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p6_3 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p6_14 _) ((OpI.neg (.inr rfl)).at _) (by decide) <|
  .cons (p6_17 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p6_22 _) ((OpI.and (.r 6) (.inr rfl)).at _) (by decide) <|
  .cons (p6_25 _) ((OpI.test (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p6_28 _) ((OpI.mov (.r 15) (.inr rfl)).at _) (by decide) <|
  .cons (p6_31 _) ((OpI.cmov64).at _) (by decide) <|
  .nil 35

def j5 : List Byte := [0x0f, 0x84, 0x8a, 0x01, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 394] 6) := by dec_rfl

/-- The stretch at `230`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x10, 0x31, 0xd2, 0x48, 0x89, 0xdf, 0x4a, 0x8d, 0x44, 0x20, 0xff]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 0) (some 12) 1 18446744073709551615 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 0 (some 4) none 1 16,
  Op.xor 32 2 (.r 2),
  Op.mov 64 7 (.r 3),
  Op.lea 64 0 (some 0) (some 12) 1 18446744073709551615]

theorem b7 (prof : Profile) : Blk prof p7 0 15 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 15

/-- The stretch at `248`. -/
def p8 : List Byte := [
  0x48, 0x0f, 0xaf, 0xc6, 0x49, 0x89, 0xc7, 0x48, 0x29, 0xc7]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .imul 64 [gr 64 0, gr 64 6] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.imul64 0 6,
  Op.mov 64 15 (.r 0),
  Op.sub 64 7 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 10 o8 :=
  .cons (p8_0 _) (OpI.imul64) (by decide) <|
  .cons (p8_4 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `258`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x54, 0x24, 0x08, 0x48, 0x01, 0xcf, 0x4c, 0x89, 0xee, 0x48, 0x89, 0x4c, 0x24, 0x18,
  0x49, 0x89, 0x86, 0x50, 0x04, 0x00, 0x00, 0x48, 0x89, 0x3d, 0xf0, 0x43, 0x19, 0x00, 0x48, 0xc7,
  0x05, 0xed, 0x43, 0x19, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p9_8 : ∀ feat, Dec feat p9 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p9_11 : ∀ feat, Dec feat p9 11 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 1] 5) := by dec_rfl
theorem p9_16 : ∀ feat, Dec feat p9 16 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 1104 64), gr 64 0] 7) := by dec_rfl
theorem p9_23 : ∀ feat, Dec feat p9 23 (FV7z.mk .mov 64 [.mem (mrip 1655792 64), gr 64 7] 7) := by dec_rfl
theorem p9_30 : ∀ feat, Dec feat p9 30 (FV7z.mk .mov 64 [.mem (mrip 1655789 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 2 (some 4) none 1 8,
  Op.add 64 7 (.r 1),
  Op.mov 64 6 (.r 13),
  Op.st 64 (some 4) none 1 24 1,
  Op.st 64 (some 14) none 1 1104 0,
  Op.sta 64 8027936 7,
  Op.stia 64 8027944 0]

theorem b9 (prof : Profile) : BlkA prof p9 (0x613b12 : Addr) 0 41 o9 :=
  .cons (p9_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p9_5 _) ((OpI.add (.r 1) (.inr rfl)).at _) (by decide) <|
  .cons (p9_8 _) ((OpI.mov (.r 13) (.inr rfl)).at _) (by decide) <|
  .cons (p9_11 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p9_16 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p9_23 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p9_30 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 41

/-- The stretch at `304`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x18, 0xbf, 0x02, 0x10, 0x00, 0x00, 0x48, 0x8d, 0x05, 0xbf, 0x43, 0x19,
  0x00, 0x48, 0x8d, 0x34, 0x19, 0x48, 0x89, 0x46, 0x08, 0xb8, 0x9e, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x36, 0x48, 0x89, 0x76, 0x10]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 4098)] 5) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1655743 0)] 7) := by dec_rfl
theorem p10_17 : ∀ feat, Dec feat p10 17 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 1) (some 3) 1 0 0)] 4) := by dec_rfl
theorem p10_21 : ∀ feat, Dec feat p10 21 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p10_25 : ∀ feat, Dec feat p10 25 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 158)] 5) := by dec_rfl
theorem p10_30 : ∀ feat, Dec feat p10 30 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 0 64), gr 64 6] 3) := by dec_rfl
theorem p10_33 : ∀ feat, Dec feat p10 33 (FV7z.mk .mov 64 [.mem (mg (some 6) none 1 16 64), gr 64 6] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ld 64 1 (some 4) none 1 24,
  Op.mov 32 7 (.i 4098),
  Op.mov 64 0 (.i 8027920),
  Op.lea 64 6 (some 1) (some 3) 1 0,
  Op.st 64 (some 6) none 1 8 0,
  Op.mov 32 0 (.i 158),
  Op.st 64 (some 6) none 1 0 6,
  Op.st 64 (some 6) none 1 16 6]

theorem b10 (prof : Profile) : BlkA prof p10 (0x613b40 : Addr) 0 37 o10 :=
  .cons (p10_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p10_5 _) ((OpI.mov (.i 4098) (.inl rfl)).at _) (by decide) <|
  .cons (p10_10 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_17 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p10_21 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p10_25 _) ((OpI.mov (.i 158) (.inl rfl)).at _) (by decide) <|
  .cons (p10_30 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p10_33 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 37

/-- The stretch at `343`. -/
def p11 : List Byte := [
  0x85, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 2 o11 :=
  .cons (p11_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j6 : List Byte := [0x74, 0x15]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 21] 2) := by dec_rfl

/-- The stretch at `368`. -/
def p12 : List Byte := [
  0x48, 0x8d, 0x05, 0x59, 0xf8, 0x18, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1636441 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 0 (.i 8008672)]

theorem b12 (prof : Profile) : BlkA prof p12 (0x613b80 : Addr) 0 7 o12 :=
  .cons (p12_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 7

/-- The stretch at `381`. -/
def p13 : List Byte := [
  0x4d, 0x89, 0xa6, 0x40, 0x04, 0x00, 0x00, 0x48, 0x89, 0x05, 0x55, 0x43, 0x19, 0x00, 0x48, 0x8b,
  0x05, 0x0e, 0xe7, 0x17, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 1088 64), gr 64 12] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .mov 64 [.mem (mrip 1655637 64), gr 64 0] 7) := by dec_rfl
theorem p13_14 : ∀ feat, Dec feat p13 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1566478 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.st 64 (some 14) none 1 1088 12,
  Op.sta 64 8027888 0,
  Op.lda 64 0 7938736]

theorem b13 (prof : Profile) : BlkA prof p13 (0x613b8d : Addr) 0 21 o13 :=
  .cons (p13_0 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p13_7 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p13_14 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 21

/-- The stretch at `407`. -/
def p14 : List Byte := [
  0x4d, 0x89, 0xae, 0x28, 0x04, 0x00, 0x00, 0x49, 0x8d, 0x44, 0x07, 0x3f]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 1064 64), gr 64 13] 7) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 15) (some 0) 1 63 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.st 64 (some 14) none 1 1064 13,
  Op.lea 64 0 (some 15) (some 0) 1 63]

theorem b14 (prof : Profile) : Blk prof p14 0 12 o14 :=
  .cons (p14_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p14_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `427`. -/
def p15 : List Byte := [
  0x48, 0x83, 0xe0, 0xc0, 0x4c, 0x89, 0x35, 0x42, 0xf8, 0x18, 0x00, 0x48, 0x05, 0x00, 0x09, 0x00,
  0x00, 0x4c, 0x89, 0x3d, 0x15, 0x43, 0x19, 0x00, 0x49, 0xc7, 0x86, 0x58, 0x04, 0x00, 0x00, 0x01,
  0x00, 0x00, 0x00, 0x48, 0x89, 0x2d, 0xeb, 0x42, 0x19, 0x00, 0x48, 0xc7, 0x05, 0xf0, 0xf7, 0x18,
  0x00, 0x40, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x05, 0xdd, 0x42, 0x19, 0x00, 0x01, 0x00, 0x00, 0x00,
  0x48, 0x89, 0x05, 0xae, 0xe6, 0x17, 0x00, 0x48, 0xc7, 0x05, 0xd3, 0x42, 0x19, 0x00, 0x01, 0x00,
  0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 64 [.mem (mrip 1636418 64), gr 64 14] 7) := by dec_rfl
theorem p15_11 : ∀ feat, Dec feat p15 11 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 2304)] 6) := by dec_rfl
theorem p15_17 : ∀ feat, Dec feat p15 17 (FV7z.mk .mov 64 [.mem (mrip 1655573 64), gr 64 15] 7) := by dec_rfl
theorem p15_24 : ∀ feat, Dec feat p15 24 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 1112 64), .imm 64 1] 11) := by dec_rfl
theorem p15_35 : ∀ feat, Dec feat p15 35 (FV7z.mk .mov 64 [.mem (mrip 1655531 64), gr 64 5] 7) := by dec_rfl
theorem p15_42 : ∀ feat, Dec feat p15 42 (FV7z.mk .mov 64 [.mem (mrip 1636336 64), .imm 64 64] 11) := by dec_rfl
theorem p15_53 : ∀ feat, Dec feat p15 53 (FV7z.mk .mov 64 [.mem (mrip 1655517 64), .imm 64 1] 11) := by dec_rfl
theorem p15_64 : ∀ feat, Dec feat p15 64 (FV7z.mk .mov 64 [.mem (mrip 1566382 64), gr 64 0] 7) := by dec_rfl
theorem p15_71 : ∀ feat, Dec feat p15 71 (FV7z.mk .mov 64 [.mem (mrip 1655507 64), .imm 64 1] 11) := by dec_rfl
theorem p15_82 : ∀ feat, Dec feat p15 82 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p15_86 : ∀ feat, Dec feat p15 86 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p15_87 : ∀ feat, Dec feat p15 87 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p15_88 : ∀ feat, Dec feat p15 88 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p15_90 : ∀ feat, Dec feat p15 90 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p15_92 : ∀ feat, Dec feat p15 92 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p15_94 : ∀ feat, Dec feat p15 94 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.and 64 0 (.i 18446744073709551552),
  Op.sta 64 8008712 14,
  Op.add 64 0 (.i 2304),
  Op.sta 64 8027880 15,
  Op.sti 64 (some 14) none 1 1112 1,
  Op.sta 64 8027856 5,
  Op.stia 64 8008672 64,
  Op.stia 64 8027864 1,
  Op.sta 64 7938736 0,
  Op.stia 64 8027872 1,
  Op.add 64 4 (.i 40),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b15 (prof : Profile) : BlkA prof p15 (0x613bbb : Addr) 0 96 o15 :=
  .cons (p15_0 _) ((OpI.and (.i 18446744073709551552) (.inr rfl)).at _) (by decide) <|
  .cons (p15_4 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p15_11 _) ((OpI.add (.i 2304) (.inr rfl)).at _) (by decide) <|
  .cons (p15_17 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p15_24 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p15_35 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p15_42 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p15_53 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p15_64 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p15_71 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p15_82 _) ((OpI.add (.i 40) (.inr rfl)).at _) (by decide) <|
  .cons (p15_86 _) ((OpI.pop).at _) (by decide) <|
  .cons (p15_87 _) ((OpI.pop).at _) (by decide) <|
  .cons (p15_88 _) ((OpI.pop).at _) (by decide) <|
  .cons (p15_90 _) ((OpI.pop).at _) (by decide) <|
  .cons (p15_92 _) ((OpI.pop).at _) (by decide) <|
  .cons (p15_94 _) ((OpI.pop).at _) (by decide) <|
  .nil 96

end FV7z.Tls
