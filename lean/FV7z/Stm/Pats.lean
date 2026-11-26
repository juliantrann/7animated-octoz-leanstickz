import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `systrim.isra.0.constprop.0` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Stm
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x8b, 0x05, 0xb9, 0x31, 0x16, 0x00, 0x41, 0x54, 0x55, 0x53, 0x48, 0x8b, 0x58, 0x08, 0x48,
  0x83, 0xe3, 0xf8, 0x48, 0x8d, 0x43, 0xdf, 0x48, 0x39, 0xf8]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1454521 64)] 7) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .and 64 [gr 64 3, Src.opd 64 (.i 18446744073709551608)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) none 1 18446744073709551583 0)] 4) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.lda 64 0 7940768,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.ld 64 3 (some 0) none 1 8,
  Op.and 64 3 (.i 18446744073709551608),
  Op.lea 64 0 (some 3) none 1 18446744073709551583,
  Op.cmp 64 0 (.r 7)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x62f8e0 : Addr) 0 26 o0 :=
  .cons (p0_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_7 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_9 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_10 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_11 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p0_15 _) ((OpI.and (.i 18446744073709551608) (.inr rfl)).at _) (by decide) <|
  .cons (p0_19 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p0_23 _) ((OpI.cmp (.r 7) (.inr rfl)).at _) (by decide) <|
  .nil 26

def j0 : List Byte := [0x76, 0x2f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `28`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x15, 0xd5, 0x3a, 0x16, 0x00, 0x48, 0x29, 0xf8, 0x48, 0xf7, 0xda, 0x48, 0x21, 0xc2,
  0x49, 0x89, 0xd4]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip 1456853 64)] 7) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .neg 64 [gr 64 2] 3) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lda 64 2 7943128,
  Op.sub 64 0 (.r 7),
  Op.neg 64 2,
  Op.and 64 2 (.r 0),
  Op.mov 64 12 (.r 2)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x62f8fc : Addr) 0 19 o1 :=
  .cons (p1_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p1_7 _) ((OpI.sub (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p1_10 _) ((OpI.neg (.inr rfl)).at _) (by decide) <|
  .cons (p1_13 _) ((OpI.and (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p1_16 _) ((OpI.mov (.r 2) (.inr rfl)).at _) (by decide) <|
  .nil 19

def j1 : List Byte := [0x74, 0x1a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p2 : List Byte := [
  0x31, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `57`. -/
def p3 : List Byte := [
  0x48, 0x89, 0xc5, 0x48, 0x8b, 0x05, 0x7d, 0x31, 0x16, 0x00, 0x48, 0x01, 0xd8, 0x48, 0x39, 0xc5]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1454461 64)] 7) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .cmp 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 5 (.r 0),
  Op.lda 64 0 7940768,
  Op.add 64 0 (.r 3),
  Op.cmp 64 5 (.r 0)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x62f919 : Addr) 0 16 o3 :=
  .cons (p3_0 _) ((OpI.mov (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p3_3 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p3_10 _) ((OpI.add (.r 3) (.inr rfl)).at _) (by decide) <|
  .cons (p3_13 _) ((OpI.cmp (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 16

def j2 : List Byte := [0x74, 0x0d]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `75`. -/
def p4 : List Byte := [
  0x31, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `77`. -/
def p5 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_1 : ∀ feat, Dec feat p5 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_2 : ∀ feat, Dec feat p5 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.pop) (by decide) <|
  .cons (p5_1 _) (OpI.pop) (by decide) <|
  .cons (p5_2 _) (OpI.pop) (by decide) <|
  .nil 4

/-- The stretch at `88`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xe7, 0x48, 0xf7, 0xdf]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .neg 64 [gr 64 7] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 7 (.r 12),
  Op.neg 64 7]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.neg (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `100`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x05, 0x15, 0x4c, 0x17, 0x00, 0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1526805 64)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lda 64 0 8013152,
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x62f944 : Addr) 0 10 o7 :=
  .cons (p7_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p7_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j3 : List Byte := [0x75, 0x38]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 56] 2) := by dec_rfl

/-- The stretch at `120`. -/
def p8 : List Byte := [
  0x90, 0x48, 0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .nop 32 [] 1) := by dec_rfl
theorem p8_1 : ∀ feat, Dec feat p8 1 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.nop,
  Op.test 64 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 4 o8 :=
  .cons (p8_0 _) (OpI.nop) (by decide) <|
  .cons (p8_1 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x74, 0xcd]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `126`. -/
def p9 : List Byte := [
  0x48, 0x29, 0xc5]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .sub 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.sub 64 5 (.r 0)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.sub (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0x74, 0xc8]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551560] 2) := by dec_rfl

/-- The stretch at `131`. -/
def p10 : List Byte := [
  0x48, 0x8b, 0x05, 0x36, 0x31, 0x16, 0x00, 0x48, 0x29, 0xeb]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1454390 64)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .sub 64 [gr 64 3, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.lda 64 0 7940768,
  Op.sub 64 3 (.r 5)]

theorem b10 (prof : Profile) : BlkA prof p10 (0x62f963 : Addr) 0 10 o10 :=
  .cons (p10_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p10_7 _) ((OpI.sub (.r 5) (.inr rfl)).at _) (by decide) <|
  .nil 10

/-- The stretch at `148`. -/
def p11 : List Byte := [
  0x48, 0x83, 0xcb, 0x01, 0x48, 0x89, 0x58, 0x08, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .or 64 [gr 64 3, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .mov 64 [.mem (mg (some 0) none 1 8 64), gr 64 3] 4) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.or 64 3 (.i 1),
  Op.st 64 (some 0) none 1 8 3,
  Op.mov 32 0 (.i 1)]

theorem b11 (prof : Profile) : Blk prof p11 0 13 o11 :=
  .cons (p11_0 _) (OpI.or (.i 1) (.inr rfl)) (by decide) <|
  .cons (p11_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

def j6 : List Byte := [0xeb, 0xaa]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551530] 2) := by dec_rfl

def j7 : List Byte := [0xeb, 0xc4]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551556] 2) := by dec_rfl

end FV7z.Stm
