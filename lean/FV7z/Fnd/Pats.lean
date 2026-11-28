import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NFind::CFileInfo::Find` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Fnd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x0f, 0xb6, 0xd2, 0x55, 0x48, 0x89, 0xf5, 0x53, 0x48, 0x89,
  0xfb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .movzx 32 [gr 32 2, gr 8 2] 3) := by dec_rfl
theorem p0_9 : ∀ feat, Dec feat p0 9 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.zxr 2 2,
  Op.push 5,
  Op.mov 64 5 (.r 6),
  Op.push 3,
  Op.mov 64 3 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 17 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.zxr) (by decide) <|
  .cons (p0_9 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_14 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 17

/-- The stretch at `22`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc4, 0x84, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.test 8 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test8 (.r 0)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x74, 0x5d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 93] 2) := by dec_rfl

/-- The stretch at `29`. -/
def p2 : List Byte := [
  0x0f, 0xb6, 0x4d, 0x00, 0x48, 0x8d, 0x45, 0x01, 0x84, 0xc9]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .movzx 32 [gr 32 1, .mem (mg (some 5) none 1 0 8)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 5) none 1 1 0)] 4) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk .test 8 [gr 8 1, Src.opd 8 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ldzx 8 1 (some 5) none 1 0,
  Op.lea 64 0 (some 5) none 1 1,
  Op.test 8 1 (.r 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.test8 (.r 1)) (by decide) <|
  .nil 10

def j1 : List Byte := [0x75, 0x11]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl

def j2 : List Byte := [0xeb, 0x25]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 37] 2) := by dec_rfl

/-- The stretch at `48`. -/
def p3 : List Byte := [
  0x84, 0xd2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 8 [gr 8 2, Src.opd 8 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 8 2 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.test8 (.r 2)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0x1c]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `52`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc0, 0x01, 0x89, 0xd1]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 0 (.i 1),
  Op.mov 32 1 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `58`. -/
def p5 : List Byte := [
  0x0f, 0xb6, 0x10, 0x80, 0xf9, 0x2f]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 2, .mem (mg (some 0) none 1 0 8)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .cmp 8 [gr 8 1, Src.opd 8 (.i 47)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 8 2 (some 0) none 1 0,
  Op.cmp 8 1 (.i 47)]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.cmp8 (.i 47)) (by decide) <|
  .nil 6

def j4 : List Byte := [0x75, 0xee]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

def j5 : List Byte := [0x74, 0x0a]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `70`. -/
def p6 : List Byte := [
  0x48, 0x89, 0xc5]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 5 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0xeb, 0xe9]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551593] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x7b, 0x68, 0x48, 0x89, 0xee]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 104 0)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lea 64 7 (some 3) none 1 104,
  Op.mov 64 6 (.r 5)]

theorem b7 (prof : Profile) : Blk prof p7 0 7 o7 :=
  .cons (p7_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `92`. -/
def p8 : List Byte := [
  0x8b, 0x43, 0x70, 0x85, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 112 32)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 32 0 (some 3) none 1 112,
  Op.test 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 5 o8 :=
  .cons (p8_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j7 : List Byte := [0x74, 0x17]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `99`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x53, 0x68, 0x89, 0xc1, 0x80, 0x7c, 0x0a, 0xff, 0x2f]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 3) none 1 104 64)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .cmp 8 [.mem (mg (some 2) (some 1) 1 18446744073709551615 8), .imm 8 47] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 2 (some 3) none 1 104,
  Op.mov 32 1 (.r 0),
  Op.cmpmi 8 (some 2) (some 1) 1 18446744073709551615 47]

theorem b9 (prof : Profile) : Blk prof p9 0 11 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p9_6 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 11

def j8 : List Byte := [0x75, 0x0a]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `112`. -/
def p10 : List Byte := [
  0x83, 0xe8, 0x01, 0x89, 0x43, 0x70, 0xc6, 0x04, 0x02, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 112 32), gr 32 0] 3) := by dec_rfl
theorem p10_6 : ∀ feat, Dec feat p10 6 (FV7z.mk .mov 8 [.mem (mg (some 2) (some 0) 1 0 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.sub 32 0 (.i 1),
  Op.st 32 (some 3) none 1 112 0,
  Op.sti 8 (some 2) (some 0) 1 0 0]

theorem b10 (prof : Profile) : Blk prof p10 0 10 o10 :=
  .cons (p10_0 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p10_6 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 10

/-- The stretch at `122`. -/
def p11 : List Byte := [
  0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p11_4 : ∀ feat, Dec feat p11 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b11 (prof : Profile) : Blk prof p11 0 7 o11 :=
  .cons (p11_0 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.pop) (by decide) <|
  .cons (p11_4 _) (OpI.pop) (by decide) <|
  .cons (p11_5 _) (OpI.pop) (by decide) <|
  .nil 7

end FV7z.Fnd
