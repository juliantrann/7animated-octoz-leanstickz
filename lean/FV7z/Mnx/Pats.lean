import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps9
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `__libc_malloc` (PLAN.md G3, `malloc`)

Each distinct stretch between labels and jumps (`p*`, 14 of them) and each distinct jump (`j*`, 12) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Mnx
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x48, 0x8b, 0x05, 0xc3, 0xf8, 0x15, 0x00, 0x55, 0x48, 0x89,
  0xfd, 0x53, 0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1439939 64)] 7) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.lda 64 0 7940656,
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x633160 : Addr) 0 21 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_14 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_17 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_18 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 21

def j0 : List Byte := [0x0f, 0x85, 0x55, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 341] 6) := by dec_rfl

/-- The stretch at `27`. -/
def p1 : List Byte := [
  0x48, 0x85, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x0f, 0x88, 0x2c, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 8) 64 [.rel 300] 6) := by dec_rfl

/-- The stretch at `36`. -/
def p2 : List Byte := [
  0x48, 0x8d, 0x47, 0x17, 0x31, 0xdb, 0x48, 0x83, 0xf8, 0x1f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 23 0)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 31)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 64 0 (some 7) none 1 23,
  Op.xor 32 3 (.r 3),
  Op.cmp 64 0 (.i 31)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.cmp (.i 31) (.inr rfl)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x0f, 0x87, 0x7c, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 7) 64 [.rel 124] 6) := by dec_rfl

/-- The stretch at `52`. -/
def p3 : List Byte := [
  0x64, 0x48, 0x8b, 0x04, 0x25, 0xd8, 0xff, 0xff, 0xff, 0x48, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 18446744073709551576 64)] 9) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.ldf fb 64 0 none none 1 18446744073709551576,
  Op.test 64 0 (.r 0)]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x633194 : Addr) fb 0 12 (o3 fb) :=
  .cons (p3_0 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p3_9 _) (((OpI.test (.r 0) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 12

def j3 : List Byte := [0x0f, 0x84, 0x82, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 130] 6) := by dec_rfl

/-- The stretch at `70`. -/
def p4 : List Byte := [
  0x48, 0x3b, 0x1d, 0x43, 0xf8, 0x15, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 64 [gr 64 3, .mem (mrip 1439811 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmpma 64 3 7940592]

theorem b4 (prof : Profile) : BlkA prof p4 (0x6331a6 : Addr) 0 7 o4 :=
  .cons (p4_0 _) (OpIA.cmpm_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x0f, 0x82, 0xad, 0x00, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 2) 64 [.rel 173] 6) := by dec_rfl

/-- The stretch at `83`. -/
def p5 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x6331b3 : Addr) fb 0 10 (o5 fb) :=
  .cons (p5_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 10

def j5 : List Byte := [0x0f, 0x85, 0x1d, 0x01, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 285] 6) := by dec_rfl

/-- The stretch at `99`. -/
def p6 : List Byte := [
  0x48, 0x89, 0xee, 0x48, 0x8d, 0x3d, 0x73, 0xf8, 0x15, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1439859 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.i 7940672)]

theorem b6 (prof : Profile) : BlkA prof p6 (0x6331c3 : Addr) 0 10 o6 :=
  .cons (p6_0 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p6_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 10

/-- The stretch at `114`. -/
def p7 : List Byte := [
  0x49, 0x89, 0xc0, 0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p7_3 : ∀ feat, Dec feat p7 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 8 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p7_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x0f, 0x84, 0xc2, 0x00, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 194] 6) := by dec_rfl

/-- The stretch at `126`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x40, 0xf8, 0xa8, 0x02]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 18446744073709551608 64)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 0 (some 0) none 1 18446744073709551608,
  Op.test 8 0 (.i 2)]

theorem b8 (prof : Profile) : Blk prof p8 0 6 o8 :=
  .cons (p8_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 6

def j7 : List Byte := [0x75, 0x1e]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `134`. -/
def p9 : List Byte := [
  0xa8, 0x04]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 4)] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.test 8 0 (.i 4)]

theorem b9 (prof : Profile) : Blk prof p9 0 2 o9 :=
  .cons (p9_0 _) (OpI.test8 (.i 4)) (by decide) <|
  .nil 2

def j8 : List Byte := [0x74, 0x1a]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `138`. -/
def p10 : List Byte := [
  0x49, 0x8d, 0x40, 0xf0, 0x48, 0x8d, 0x15, 0x4b, 0xf8, 0x15, 0x00, 0x48, 0x25, 0x00, 0x00, 0x00,
  0xfc, 0x48, 0x39, 0x10]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 8) none 1 18446744073709551600 0)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1439819 0)] 7) := by dec_rfl
theorem p10_11 : ∀ feat, Dec feat p10 11 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073642442752)] 6) := by dec_rfl
theorem p10_17 : ∀ feat, Dec feat p10 17 (FV7z.mk .cmp 64 [.mem (mg (some 0) none 1 0 64), gr 64 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.lea 64 0 (some 8) none 1 18446744073709551600,
  Op.mov 64 2 (.i 7940672),
  Op.and 64 0 (.i 18446744073642442752),
  Op.cmpmr 64 (some 0) none 1 0 2]

theorem b10 (prof : Profile) : BlkA prof p10 (0x6331ea : Addr) 0 20 o10 :=
  .cons (p10_0 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p10_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_11 _) ((OpI.and (.i 18446744073642442752) (.inr rfl)).at _) (by decide) <|
  .cons (p10_17 _) ((OpI.cmpmr (.inr rfl)).at _) (by decide) <|
  .nil 20

def j9 : List Byte := [0x0f, 0x85, 0x42, 0x02, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 578] 6) := by dec_rfl

/-- The stretch at `164`. -/
def p11 : List Byte := [
  0x5b, 0x4c, 0x89, 0xc0, 0x5d, 0x41, 0x5c]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p11_1 : ∀ feat, Dec feat p11 1 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.pop 3,
  Op.mov 64 0 (.r 8),
  Op.pop 5,
  Op.pop 12]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.pop) (by decide) <|
  .cons (p11_1 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.pop) (by decide) <|
  .cons (p11_5 _) (OpI.pop) (by decide) <|
  .nil 7

/-- The stretch at `176`. -/
def p12 : List Byte := [
  0x48, 0x83, 0xe0, 0xf0, 0x48, 0x8d, 0x58, 0xef, 0x48, 0xc1, 0xeb, 0x04]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551600)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 0) none 1 18446744073709551599 0)] 4) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .shr 64 [gr 64 3, Src.opd 8 (.i 4)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.and 64 0 (.i 18446744073709551600),
  Op.lea 64 3 (some 0) none 1 18446744073709551599,
  Op.shr64 3 (.i 4)]

theorem b12 (prof : Profile) : Blk prof p12 0 12 o12 :=
  .cons (p12_0 _) (OpI.and (.i 18446744073709551600) (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p12_8 _) (OpI.shr64 (.i 4)) (by decide) <|
  .nil 12

def j10 : List Byte := [0xe9, 0x73, 0xff, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551475] 5) := by dec_rfl

/-- The stretch at `256`. -/
def p13 : List Byte := [
  0x48, 0x8d, 0x0c, 0x58, 0x0f, 0xb7, 0x11, 0x66, 0x85, 0xd2]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) (some 3) 2 0 0)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 1) none 1 0 16)] 3) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .test 16 [gr 16 2, Src.opd 16 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.lea 64 1 (some 0) (some 3) 2 0,
  Op.ldzx 16 2 (some 1) none 1 0,
  Op.test 16 2 (.r 2)]

theorem b13 (prof : Profile) : Blk prof p13 0 10 o13 :=
  .cons (p13_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p13_7 _) (OpI.test16 (.r 2)) (by decide) <|
  .nil 10

def j11 : List Byte := [0x0f, 0x84, 0x43, 0xff, 0xff, 0xff]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551427] 6) := by dec_rfl

end FV7z.Mnx
