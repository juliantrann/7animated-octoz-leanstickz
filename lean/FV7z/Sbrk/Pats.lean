import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__sbrk` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 9 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sbrk
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x08, 0x4c, 0x8b,
  0x25, 0x93, 0xe8, 0x13, 0x00, 0x4d, 0x85, 0xe4]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 12, .mem (mrip 1304723 64)] 7) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 8),
  Op.lda 64 12 8014904,
  Op.test 64 12 (.r 12)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x666390 : Addr) 0 24 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_7 _) ((OpI.mov (.r 7) (.inr rfl)).at _) (by decide) <|
  .cons (p0_10 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_14 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_21 _) ((OpI.test (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 24

def j0 : List Byte := [0x74, 0x46]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 70] 2) := by dec_rfl

/-- The stretch at `26`. -/
def p1 : List Byte := [
  0x8b, 0x05, 0x10, 0xd6, 0x12, 0x00, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1234448 32)] 6) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lda 32 0 7944640,
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x6663aa : Addr) 0 8 o1 :=
  .cons (p1_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p1_6 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 8

def j1 : List Byte := [0x75, 0x3c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 60] 2) := by dec_rfl

/-- The stretch at `36`. -/
def p2 : List Byte := [
  0x48, 0x85, 0xdb]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 64 3 (.r 3)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j2 : List Byte := [0x74, 0x24]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 36] 2) := by dec_rfl

def j3 : List Byte := [0x7e, 0x4d]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 14) 64 [.rel 77] 2) := by dec_rfl

/-- The stretch at `43`. -/
def p3 : List Byte := [
  0x4c, 0x89, 0xe0, 0x48, 0x01, 0xd8, 0x0f, 0x92, 0xc0, 0x84, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk (.setcc 2) 8 [gr 8 0] 3) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 0 (.r 12),
  Op.add 64 0 (.r 3),
  Op.setcc 2 0,
  Op.test 8 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 11 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.add (.r 3) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.setcc) (by decide) <|
  .cons (p3_9 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 11

def j4 : List Byte := [0x74, 0x50]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 80] 2) := by dec_rfl

/-- The stretch at `77`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08, 0x4c, 0x89, 0xe0, 0x5b, 0x41, 0x5c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8),
  Op.mov 64 0 (.r 12),
  Op.pop 3,
  Op.pop 12]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.pop) (by decide) <|
  .cons (p4_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `96`. -/
def p5 : List Byte := [
  0x31, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.xor 32 7 (.r 7)]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `103`. -/
def p6 : List Byte := [
  0x4c, 0x8b, 0x25, 0x3a, 0xe8, 0x13, 0x00, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 12, .mem (mrip 1304634 64)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lda 64 12 8014904,
  Op.test 32 0 (.r 0)]

theorem b6 (prof : Profile) : BlkA prof p6 (0x6663f7 : Addr) 0 9 o6 :=
  .cons (p6_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p6_7 _) ((OpI.test (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 9

def j5 : List Byte := [0x79, 0xb2]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551538] 2) := by dec_rfl

def j6 : List Byte := [0xeb, 0xd2]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `136`. -/
def p7 : List Byte := [
  0x49, 0x8d, 0x3c, 0x1c]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 12) (some 3) 1 0 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 64 7 (some 12) (some 3) 1 0]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `145`. -/
def p8 : List Byte := [
  0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j7 : List Byte := [0x78, 0xb1]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 8) 64 [.rel 18446744073709551537] 2) := by dec_rfl

end FV7z.Sbrk
