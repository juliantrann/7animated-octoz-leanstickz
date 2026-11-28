import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps13
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_check_standard_fds` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 21 of them) and each distinct jump (`j*`, 13) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cfd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x81, 0xec, 0x98, 0x00, 0x00, 0x00, 0x31, 0xff, 0x31, 0xc0, 0xbe,
  0x01, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 152)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 152),
  Op.xor 32 7 (.r 7),
  Op.xor 32 0 (.r 0),
  Op.mov 32 6 (.i 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 20 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 152) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 20

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x83, 0xf8, 0xff]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 0 (.i 4294967295)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 3

def j0 : List Byte := [0x74, 0x42]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 66] 2) := by dec_rfl

/-- The stretch at `30`. -/
def p2 : List Byte := [
  0x31, 0xc0, 0xbe, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.mov 32 6 (.i 1),
  Op.mov 32 7 (.i 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 12 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0x0f, 0x84, 0x90, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 144] 6) := by dec_rfl

/-- The stretch at `56`. -/
def p3 : List Byte := [
  0x31, 0xc0, 0xbe, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x02, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.mov 32 6 (.i 1),
  Op.mov 32 7 (.i 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 12 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 12

def j2 : List Byte := [0x0f, 0x84, 0xe6, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 230] 6) := by dec_rfl

/-- The stretch at `82`. -/
def p4 : List Byte := [
  0x48, 0x81, 0xc4, 0x98, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 152)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 152)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.add (.i 152) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `96`. -/
def p5 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0x83, 0x38, 0x09]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .cmp 32 [.mem (mf (some 0) none 1 0 32), .imm 32 9] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.cmpmif fb 32 (some 0) none 1 0 9]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x6138c0 : Addr) fb 0 11 (o5 fb) :=
  .cons (p5_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p5_7 _) (OpIF.cmpmif (.inl rfl)) (by decide) <|
  .nil 11

def j3 : List Byte := [0x75, 0xb1]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551537] 2) := by dec_rfl

/-- The stretch at `109`. -/
def p6 : List Byte := [
  0x31, 0xd2, 0x31, 0xc0, 0x48, 0x8d, 0x3d, 0x2a, 0xaf, 0x0d, 0x00, 0xbe, 0x01, 0x00, 0x02, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p6_2 : ∀ feat, Dec feat p6 2 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 896810 0)] 7) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 131073)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.xor 32 0 (.r 0),
  Op.mov 64 7 (.i 7268354),
  Op.mov 32 6 (.i 131073)]

theorem b6 (prof : Profile) : BlkA prof p6 (0x6138cd : Addr) 0 16 o6 :=
  .cons (p6_0 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p6_2 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p6_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_11 _) ((OpI.mov (.i 131073) (.inl rfl)).at _) (by decide) <|
  .nil 16

/-- The stretch at `130`. -/
def p7 : List Byte := [
  0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b7 (prof : Profile) : Blk prof p7 0 2 o7 :=
  .cons (p7_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j4 : List Byte := [0x75, 0x3a]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 58] 2) := by dec_rfl

/-- The stretch at `134`. -/
def p8 : List Byte := [
  0x31, 0xf6, 0x48, 0x89, 0xe2, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p8_2 : ∀ feat, Dec feat p8 2 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 6 (.r 6),
  Op.mov 64 2 (.r 4),
  Op.mov 32 7 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 10 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p8_2 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p8_5 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 10

def j5 : List Byte := [0x75, 0x27]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 39] 2) := by dec_rfl

/-- The stretch at `153`. -/
def p9 : List Byte := [
  0x8b, 0x44, 0x24, 0x18, 0x25, 0x00, 0xf0, 0x00, 0x00, 0x3d, 0x00, 0x20, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 24 32)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 61440)] 5) := by dec_rfl
theorem p9_9 : ∀ feat, Dec feat p9 9 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 8192)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 32 0 (some 4) none 1 24,
  Op.and 32 0 (.i 61440),
  Op.cmp 32 0 (.i 8192)]

theorem b9 (prof : Profile) : Blk prof p9 0 14 o9 :=
  .cons (p9_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.and (.i 61440) (.inl rfl)) (by decide) <|
  .cons (p9_9 _) (OpI.cmp (.i 8192) (.inl rfl)) (by decide) <|
  .nil 14

def j6 : List Byte := [0x75, 0x17]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `169`. -/
def p10 : List Byte := [
  0x48, 0x81, 0x7c, 0x24, 0x28, 0x07, 0x01, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 64 [.mem (mg (some 4) none 1 40 64), .imm 64 263] 9) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmpmi 64 (some 4) none 1 40 263]

theorem b10 (prof : Profile) : Blk prof p10 0 9 o10 :=
  .cons (p10_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 9

def j7 : List Byte := [0x0f, 0x84, 0x66, 0xff, 0xff, 0xff]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551462] 6) := by dec_rfl

/-- The stretch at `184`. -/
def p11 : List Byte := [
  0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .nop 32 [.mem (mg (some 0) (some 0) 1 0 32)] 8) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.nop]

theorem b11 (prof : Profile) : Blk prof p11 0 8 o11 :=
  .cons (p11_0 _) (OpI.nop) (by decide) <|
  .nil 8

/-- The stretch at `200`. -/
def p12 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0x83, 0x38, 0x09]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .cmp 32 [.mem (mf (some 0) none 1 0 32), .imm 32 9] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.cmpmif fb 32 (some 0) none 1 0 9]

theorem b12 (prof : Profile) (fb : Addr) : BlkF prof p12 (0x613928 : Addr) fb 0 11 (o12 fb) :=
  .cons (p12_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p12_7 _) (OpIF.cmpmif (.inl rfl)) (by decide) <|
  .nil 11

def j8 : List Byte := [0x0f, 0x85, 0x5f, 0xff, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551455] 6) := by dec_rfl

/-- The stretch at `217`. -/
def p13 : List Byte := [
  0x31, 0xd2, 0x31, 0xc0, 0x48, 0x8d, 0x3d, 0xc8, 0xae, 0x0d, 0x00, 0xbe, 0x00, 0x00, 0x02, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 896712 0)] 7) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 131072)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.xor 32 0 (.r 0),
  Op.mov 64 7 (.i 7268364),
  Op.mov 32 6 (.i 131072)]

theorem b13 (prof : Profile) : BlkA prof p13 (0x613939 : Addr) 0 16 o13 :=
  .cons (p13_0 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p13_2 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p13_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p13_11 _) ((OpI.mov (.i 131072) (.inl rfl)).at _) (by decide) <|
  .nil 16

/-- The stretch at `238`. -/
def p14 : List Byte := [
  0x83, 0xf8, 0x01]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.cmp 32 0 (.i 1)]

theorem b14 (prof : Profile) : Blk prof p14 0 3 o14 :=
  .cons (p14_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j9 : List Byte := [0x75, 0x3d]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `243`. -/
def p15 : List Byte := [
  0x48, 0x89, 0xe2, 0xbe, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p15_8 : ∀ feat, Dec feat p15 8 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 2 (.r 4),
  Op.mov 32 6 (.i 1),
  Op.mov 32 7 (.i 1)]

theorem b15 (prof : Profile) : Blk prof p15 0 13 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p15_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `281`. -/
def p16 : List Byte := [
  0x48, 0x81, 0x7c, 0x24, 0x28, 0x03, 0x01, 0x00, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .cmp 64 [.mem (mg (some 4) none 1 40 64), .imm 64 259] 9) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.cmpmi 64 (some 4) none 1 40 259]

theorem b16 (prof : Profile) : Blk prof p16 0 9 o16 :=
  .cons (p16_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 9

def j10 : List Byte := [0x0f, 0x84, 0x10, 0xff, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551376] 6) := by dec_rfl

/-- The stretch at `312`. -/
def p17 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb8, 0xff, 0xff, 0xff, 0x64, 0x83, 0x38, 0x09]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551544)] 7) := by dec_rfl
theorem p17_7 : ∀ feat, Dec feat p17 7 (FV7z.mk .cmp 32 [.mem (mf (some 0) none 1 0 32), .imm 32 9] 4) := by dec_rfl

/-- What the stretch does. -/
def o17 (fb : Addr) : List Op := [
  Op.mov 64 0 (.i 18446744073709551544),
  Op.cmpmif fb 32 (some 0) none 1 0 9]

theorem b17 (prof : Profile) (fb : Addr) : BlkF prof p17 (0x613998 : Addr) fb 0 11 (o17 fb) :=
  .cons (p17_0 _) (((OpI.mov (.i 18446744073709551544) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p17_7 _) (OpIF.cmpmif (.inl rfl)) (by decide) <|
  .nil 11

def j11 : List Byte := [0x0f, 0x85, 0x09, 0xff, 0xff, 0xff]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551369] 6) := by dec_rfl

/-- The stretch at `329`. -/
def p18 : List Byte := [
  0x31, 0xd2, 0x31, 0xc0, 0x48, 0x8d, 0x3d, 0x58, 0xae, 0x0d, 0x00, 0xbe, 0x00, 0x00, 0x02, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p18_2 : ∀ feat, Dec feat p18 2 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 896600 0)] 7) := by dec_rfl
theorem p18_11 : ∀ feat, Dec feat p18 11 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 131072)] 5) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.xor 32 0 (.r 0),
  Op.mov 64 7 (.i 7268364),
  Op.mov 32 6 (.i 131072)]

theorem b18 (prof : Profile) : BlkA prof p18 (0x6139a9 : Addr) 0 16 o18 :=
  .cons (p18_0 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p18_2 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p18_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p18_11 _) ((OpI.mov (.i 131072) (.inl rfl)).at _) (by decide) <|
  .nil 16

/-- The stretch at `350`. -/
def p19 : List Byte := [
  0x83, 0xf8, 0x02]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmp 32 0 (.i 2)]

theorem b19 (prof : Profile) : Blk prof p19 0 3 o19 :=
  .cons (p19_0 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `355`. -/
def p20 : List Byte := [
  0x48, 0x89, 0xe2, 0xbe, 0x02, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p20_3 : ∀ feat, Dec feat p20 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p20_8 : ∀ feat, Dec feat p20 8 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 64 2 (.r 4),
  Op.mov 32 6 (.i 2),
  Op.mov 32 7 (.i 1)]

theorem b20 (prof : Profile) : Blk prof p20 0 13 o20 :=
  .cons (p20_0 _) (OpI.mov (.r 4) (.inr rfl)) (by decide) <|
  .cons (p20_3 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p20_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

def j12 : List Byte := [0x0f, 0x84, 0xba, 0xfe, 0xff, 0xff]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551290] 6) := by dec_rfl

end FV7z.Cfd
