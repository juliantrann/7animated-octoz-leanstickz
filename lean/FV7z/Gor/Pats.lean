import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_dl_get_origin` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 19 of them) and each distinct jump (`j*`, 12) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gor
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x81, 0xec, 0x00, 0x10, 0x00,
  0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 4096)] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 4096)]

theorem b0 (prof : Profile) : Blk prof p0 0 17 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.sub (.i 4096) (.inr rfl)) (by decide) <|
  .nil 17

/-- The stretch at `22`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xec, 0x08, 0xba, 0x00, 0x10, 0x00, 0x00, 0x48, 0x8d, 0x3d, 0x5d, 0x78, 0x05, 0x00,
  0xb8, 0x59, 0x00, 0x00, 0x00, 0x48, 0x89, 0xe5, 0x48, 0x89, 0xee]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 4096)] 5) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 358493 0)] 7) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 89)] 5) := by dec_rfl
theorem p1_21 : ∀ feat, Dec feat p1 21 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p1_24 : ∀ feat, Dec feat p1 24 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sub 64 4 (.i 8),
  Op.mov 32 2 (.i 4096),
  Op.mov 64 7 (.i 7366691),
  Op.mov 32 0 (.i 89),
  Op.mov 64 5 (.r 4),
  Op.mov 64 6 (.r 5)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x6aefb6 : Addr) 0 27 o1 :=
  .cons (p1_0 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p1_4 _) ((OpI.mov (.i 4096) (.inl rfl)).at _) (by decide) <|
  .cons (p1_9 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_16 _) ((OpI.mov (.i 89) (.inl rfl)).at _) (by decide) <|
  .cons (p1_21 _) ((OpI.mov (.r 4) (.inr rfl)).at _) (by decide) <|
  .cons (p1_24 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .nil 27

/-- The stretch at `51`. -/
def p2 : List Byte := [
  0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4294963200)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 32 0 (.i 4294963200)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 4294963200) (.inl rfl)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x77, 0x5e]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 94] 2) := by dec_rfl

/-- The stretch at `58`. -/
def p3 : List Byte := [
  0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x7e, 0x5a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 14) 64 [.rel 90] 2) := by dec_rfl

/-- The stretch at `62`. -/
def p4 : List Byte := [
  0x0f, 0xb6, 0x14, 0x24, 0x80, 0xfa, 0x5b]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 4) none 1 0 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 91)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 2 (some 4) none 1 0,
  Op.cmp 8 2 (.i 91)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.cmp8 (.i 91)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x74, 0x51]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 81] 2) := by dec_rfl

/-- The stretch at `71`. -/
def p5 : List Byte := [
  0x80, 0xfa, 0x2f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 47)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 8 2 (.i 47)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.cmp8 (.i 47)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x0f, 0x85, 0xe6, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 230] 6) := by dec_rfl

/-- The stretch at `80`. -/
def p6 : List Byte := [
  0x89, 0xc1, 0x48, 0x98, 0x48, 0x01, 0xe8]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_2 : ∀ feat, Dec feat p6 2 (FV7z.mk .cbw 64 [] 2) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.cdqe,
  Op.add 64 0 (.r 5)]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p6_2 _) (OpI.cdqe) (by decide) <|
  .cons (p6_4 _) (OpI.add (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0xeb, 0x19]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p7 : List Byte := [
  0x48, 0x83, 0xe8, 0x01, 0x8d, 0x59, 0xff, 0x80, 0x38, 0x2f]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 1) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 47] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.sub 64 0 (.i 1),
  Op.lea 32 3 (some 1) none 1 18446744073709551615,
  Op.cmpmi 8 (some 0) none 1 0 47]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 10

def j5 : List Byte := [0x0f, 0x84, 0xa0, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 160] 6) := by dec_rfl

/-- The stretch at `112`. -/
def p8 : List Byte := [
  0x89, 0xd9]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 1 (.r 3)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `114`. -/
def p9 : List Byte := [
  0x83, 0xf9, 0x01]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmp 32 1 (.i 1)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0x75, 0xe9]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551593] 2) := by dec_rfl

/-- The stretch at `119`. -/
def p10 : List Byte := [
  0xbf, 0x02, 0x00, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 7 (.i 2)]

theorem b10 (prof : Profile) : Blk prof p10 0 5 o10 :=
  .cons (p10_0 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `129`. -/
def p11 : List Byte := [
  0x49, 0x89, 0xc4, 0x48, 0x85, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 12 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 6 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0x74, 0x6f]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 111] 2) := by dec_rfl

/-- The stretch at `137`. -/
def p12 : List Byte := [
  0xb8, 0x2f, 0x00, 0x00, 0x00, 0x66, 0x41, 0x89, 0x04, 0x24]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 47)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .mov 16 [.mem (mg (some 12) none 1 0 16), gr 16 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 32 0 (.i 47),
  Op.st 16 (some 12) none 1 0 0]

theorem b12 (prof : Profile) : Blk prof p12 0 10 o12 :=
  .cons (p12_0 _) (OpI.mov (.i 47) (.inl rfl)) (by decide) <|
  .cons (p12_5 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 10

def j8 : List Byte := [0xeb, 0x6a]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 106] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p13 : List Byte := [
  0x48, 0x8b, 0x2d, 0xc1, 0x94, 0x0f, 0x00, 0x48, 0x85, 0xed]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mrip 1021121 64)] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.lda 64 5 8029440,
  Op.test 64 5 (.r 5)]

theorem b13 (prof : Profile) : BlkA prof p13 (0x6af038 : Addr) 0 10 o13 :=
  .cons (p13_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p13_7 _) ((OpI.test (.r 5) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j9 : List Byte := [0x74, 0x54]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 84] 2) := by dec_rfl

/-- The stretch at `248`. -/
def p14 : List Byte := [
  0x49, 0xc7, 0xc4, 0xff, 0xff, 0xff, 0xff]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.i 18446744073709551615)] 7) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 12 (.i 18446744073709551615)]

theorem b14 (prof : Profile) : Blk prof p14 0 7 o14 :=
  .cons (p14_0 _) (OpI.mov (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `255`. -/
def p15 : List Byte := [
  0x48, 0x81, 0xc4, 0x08, 0x10, 0x00, 0x00, 0x4c, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 4104)] 7) := by dec_rfl
theorem p15_7 : ∀ feat, Dec feat p15 7 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p15_11 : ∀ feat, Dec feat p15 11 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p15_12 : ∀ feat, Dec feat p15 12 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p15_14 : ∀ feat, Dec feat p15 14 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.add 64 4 (.i 4104),
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13]

theorem b15 (prof : Profile) : Blk prof p15 0 16 o15 :=
  .cons (p15_0 _) (OpI.add (.i 4104) (.inr rfl)) (by decide) <|
  .cons (p15_7 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p15_10 _) (OpI.pop) (by decide) <|
  .cons (p15_11 _) (OpI.pop) (by decide) <|
  .cons (p15_12 _) (OpI.pop) (by decide) <|
  .cons (p15_14 _) (OpI.pop) (by decide) <|
  .nil 16

/-- The stretch at `272`. -/
def p16 : List Byte := [
  0x83, 0xc1, 0x01, 0x48, 0x63, 0xf9]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p16_3 : ∀ feat, Dec feat p16 3 (FV7z.mk .movsxd 64 [gr 64 7, gr 32 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.add 32 1 (.i 1),
  Op.sxr 7 1]

theorem b16 (prof : Profile) : Blk prof p16 0 6 o16 :=
  .cons (p16_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p16_3 _) (OpI.sxr) (by decide) <|
  .nil 6

def j10 : List Byte := [0x74, 0xd5]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551573] 2) := by dec_rfl

/-- The stretch at `291`. -/
def p17 : List Byte := [
  0x48, 0x63, 0xd3, 0x48, 0x89, 0xee, 0x4c, 0x89, 0xe7]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .movsxd 64 [gr 64 2, gr 32 3] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p17_6 : ∀ feat, Dec feat p17 6 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.sxr 2 3,
  Op.mov 64 6 (.r 5),
  Op.mov 64 7 (.r 12)]

theorem b17 (prof : Profile) : Blk prof p17 0 9 o17 :=
  .cons (p17_0 _) (OpI.sxr) (by decide) <|
  .cons (p17_3 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p17_6 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `305`. -/
def p18 : List Byte := [
  0xc6, 0x00, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.sti 8 (some 0) none 1 0 0]

theorem b18 (prof : Profile) : Blk prof p18 0 3 o18 :=
  .cons (p18_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 3

def j11 : List Byte := [0xeb, 0xc9]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551561] 2) := by dec_rfl

end FV7z.Gor
