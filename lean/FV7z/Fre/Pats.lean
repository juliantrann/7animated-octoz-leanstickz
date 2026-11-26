import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps13
import FV7z.Lemmas.BlkOps9
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_free` (PLAN.md G3, `free`)

Each distinct stretch between labels and jumps (`p*`, 16 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fre
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x18, 0x48, 0x8b, 0x05, 0x09, 0x0e, 0x17, 0x00, 0x48,
  0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1510921 64)] 7) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 24),
  Op.lda 64 0 8013160,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x633750 : Addr) 0 18 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.sub (.i 24) (.inr rfl)).at _) (by decide) <|
  .cons (p0_8 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_15 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 18

def j0 : List Byte := [0x0f, 0x85, 0x80, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 128] 6) := by dec_rfl

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x48, 0x85, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 64 7 (.r 7)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x74, 0x73]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 115] 2) := by dec_rfl

/-- The stretch at `29`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x47, 0xf8, 0x48, 0x8d, 0x77, 0xf0, 0xa8, 0x02]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 18446744073709551608 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 7) none 1 18446744073709551600 0)] 4) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 0 (some 7) none 1 18446744073709551608,
  Op.lea 64 6 (some 7) none 1 18446744073709551600,
  Op.test 8 0 (.i 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 10

def j2 : List Byte := [0x75, 0x37]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 55] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0x64, 0x48, 0x83, 0x3c, 0x25, 0xd8, 0xff, 0xff, 0xff, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [.mem (mf none none 1 18446744073709551576 64), .imm 64 0] 10) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.cmpmif fb 64 none none 1 18446744073709551576 0]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x633779 : Addr) fb 0 10 (o3 fb) :=
  .cons (p3_0 _) (OpIF.cmpmif (.inr rfl)) (by decide) <|
  .nil 10

def j3 : List Byte := [0x0f, 0x84, 0x8f, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 143] 6) := by dec_rfl

/-- The stretch at `57`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x3d, 0xb0, 0xf2, 0x15, 0x00, 0xa8, 0x04]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1438384 0)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 4)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.i 7940672),
  Op.test 8 0 (.i 4)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x633789 : Addr) 0 9 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_7 _) ((OpI.test8 (.i 4)).at _) (by decide) <|
  .nil 9

def j4 : List Byte := [0x74, 0x0c]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `68`. -/
def p5 : List Byte := [
  0x48, 0x89, 0xf0, 0x48, 0x25, 0x00, 0x00, 0x00, 0xfc, 0x48, 0x8b, 0x38]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073642442752)] 6) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 0 (.r 6),
  Op.and 64 0 (.i 18446744073642442752),
  Op.ld 64 7 (some 0) none 1 0]

theorem b5 (prof : Profile) : Blk prof p5 0 12 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.and (.i 18446744073642442752) (.inr rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 12

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x31, 0xd2, 0x48, 0x83, 0xc4, 0x18]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p6_2 : ∀ feat, Dec feat p6 2 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.add 64 4 (.i 24)]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p6_2 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x8b, 0x15, 0x1e, 0xf2, 0x15, 0x00, 0x85, 0xd2]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip 1438238 32)] 6) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lda 32 2 7940564,
  Op.test 32 2 (.r 2)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x6337b0 : Addr) 0 8 o7 :=
  .cons (p7_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p7_6 _) ((OpI.test (.r 2) (.inl rfl)).at _) (by decide) <|
  .nil 8

def j5 : List Byte := [0x75, 0x11]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `106`. -/
def p8 : List Byte := [
  0x48, 0x3b, 0x05, 0xef, 0xf1, 0x15, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 64 [gr 64 0, .mem (mrip 1438191 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmpma 64 0 7940528]

theorem b8 (prof : Profile) : BlkA prof p8 (0x6337ba : Addr) 0 7 o8 :=
  .cons (p8_0 _) (OpIA.cmpm_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 7

def j6 : List Byte := [0x76, 0x08]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 6) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `115`. -/
def p9 : List Byte := [
  0x48, 0x3d, 0x00, 0x00, 0x00, 0x02]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 33554432)] 6) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmp 64 0 (.i 33554432)]

theorem b9 (prof : Profile) : Blk prof p9 0 6 o9 :=
  .cons (p9_0 _) (OpI.cmp (.i 33554432) (.inr rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0x76, 0x2d]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 6) 64 [.rel 45] 2) := by dec_rfl

/-- The stretch at `123`. -/
def p10 : List Byte := [
  0x48, 0x89, 0xf7, 0x48, 0x83, 0xc4, 0x18]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 7 (.r 6),
  Op.add 64 4 (.i 24)]

theorem b10 (prof : Profile) : Blk prof p10 0 7 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `144`. -/
def p11 : List Byte := [
  0x48, 0x83, 0xc4, 0x18]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.add 64 4 (.i 24)]

theorem b11 (prof : Profile) : Blk prof p11 0 4 o11 :=
  .cons (p11_0 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `152`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x74, 0x24, 0x18, 0x48, 0x83, 0xc4, 0x18]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 6 (some 4) none 1 24,
  Op.add 64 4 (.i 24)]

theorem b12 (prof : Profile) : Blk prof p12 0 9 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_5 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `168`. -/
def p13 : List Byte := [
  0x48, 0x83, 0xe0, 0xf8, 0x48, 0x8d, 0x14, 0x00, 0x48, 0x89, 0x05, 0xa9, 0xf1, 0x15, 0x00, 0x48,
  0x89, 0x15, 0x92, 0xf1, 0x15, 0x00, 0x90]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) (some 0) 1 0 0)] 4) := by dec_rfl
theorem p13_8 : ∀ feat, Dec feat p13 8 (FV7z.mk .mov 64 [.mem (mrip 1438121 64), gr 64 0] 7) := by dec_rfl
theorem p13_15 : ∀ feat, Dec feat p13 15 (FV7z.mk .mov 64 [.mem (mrip 1438098 64), gr 64 2] 7) := by dec_rfl
theorem p13_22 : ∀ feat, Dec feat p13 22 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.and 64 0 (.i 18446744073709551608),
  Op.lea 64 2 (some 0) (some 0) 1 0,
  Op.sta 64 7940528 0,
  Op.sta 64 7940512 2,
  Op.nop]

theorem b13 (prof : Profile) : BlkA prof p13 (0x6337f8 : Addr) 0 23 o13 :=
  .cons (p13_0 _) ((OpI.and (.i 18446744073709551608) (.inr rfl)).at _) (by decide) <|
  .cons (p13_4 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p13_8 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p13_15 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p13_22 _) ((OpI.nop).at _) (by decide) <|
  .nil 23

def j8 : List Byte := [0xeb, 0xba]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551546] 2) := by dec_rfl

/-- The stretch at `200`. -/
def p14 : List Byte := [
  0x48, 0x89, 0x3c, 0x24, 0x64, 0x80, 0x3c, 0x25, 0xe0, 0xff, 0xff, 0xff, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 7] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .cmp 8 [.mem (mf none none 1 18446744073709551584 8), .imm 8 0] 9) := by dec_rfl

/-- What the stretch does. -/
def o14 (fb : Addr) : List Op := [
  Op.st 64 (some 4) none 1 0 7,
  Op.cmpmif fb 8 none none 1 18446744073709551584 0]

theorem b14 (prof : Profile) (fb : Addr) : BlkF prof p14 (0x633818 : Addr) fb 0 13 (o14 fb) :=
  .cons (p14_0 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p14_4 _) (OpIF.cmpmif8) (by decide) <|
  .nil 13

def j9 : List Byte := [0x0f, 0x85, 0x5e, 0xff, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551454] 6) := by dec_rfl

/-- The stretch at `219`. -/
def p15 : List Byte := [
  0x48, 0x89, 0x74, 0x24, 0x08]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 6] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.st 64 (some 4) none 1 8 6]

theorem b15 (prof : Profile) : Blk prof p15 0 5 o15 :=
  .cons (p15_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 5

end FV7z.Fre
