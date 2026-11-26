import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Normalize_UString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 15 of them) and each distinct jump (`j*`, 14) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Nus
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0x7f, 0x08, 0x00, 0x8b, 0x56, 0x08, 0x48, 0x8b, 0x06]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 8 8), .imm 8 0] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 6) none 1 8 32)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 8 (some 7) none 1 8 0,
  Op.ld 32 2 (some 6) none 1 8,
  Op.ld 64 0 (some 6) none 1 0]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x60]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 96] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x85, 0xd2]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 32 2 (.r 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x0f, 0x84, 0x7c, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 124] 6) := by dec_rfl

/-- The stretch at `24`. -/
def p2 : List Byte := [
  0x83, 0xea, 0x01, 0x48, 0x8d, 0x4c, 0x90, 0x04]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) (some 2) 4 4 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sub 32 2 (.i 1),
  Op.lea 64 1 (some 0) (some 2) 4 4]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 8

def j2 : List Byte := [0xeb, 0x37]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 55] 2) := by dec_rfl

/-- The stretch at `40`. -/
def p3 : List Byte := [
  0x83, 0xfa, 0x7e]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 126)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 2 (.i 126)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 126) (.inl rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x7e, 0x23]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 14) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p4 : List Byte := [
  0x81, 0xfa, 0x9f, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 159)] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 32 2 (.i 159)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.cmp (.i 159) (.inl rfl)) (by decide) <|
  .nil 6

def j4 : List Byte := [0x7e, 0x2b]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 14) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `53`. -/
def p5 : List Byte := [
  0x81, 0xfa, 0x29, 0x20, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 8233)] 6) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 32 2 (.i 8233)]

theorem b5 (prof : Profile) : Blk prof p5 0 6 o5 :=
  .cons (p5_0 _) (OpI.cmp (.i 8233) (.inl rfl)) (by decide) <|
  .nil 6

def j5 : List Byte := [0x7e, 0x13]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 14) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `61`. -/
def p6 : List Byte := [
  0x81, 0xfa, 0x2e, 0x20, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 8238)] 6) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 2 (.i 8238)]

theorem b6 (prof : Profile) : Blk prof p6 0 6 o6 :=
  .cons (p6_0 _) (OpI.cmp (.i 8238) (.inl rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x7e, 0x1b]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 14) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `69`. -/
def p7 : List Byte := [
  0x81, 0xea, 0x66, 0x20, 0x00, 0x00, 0x83, 0xfa, 0x03]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 8294)] 6) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.sub 32 2 (.i 8294),
  Op.cmp 32 2 (.i 3)]

theorem b7 (prof : Profile) : Blk prof p7 0 9 o7 :=
  .cons (p7_0 _) (OpI.sub (.i 8294) (.inl rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 9

def j7 : List Byte := [0x76, 0x10]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 6) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `80`. -/
def p8 : List Byte := [
  0x48, 0x83, 0xc0, 0x04, 0x48, 0x39, 0xc8]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.add 64 0 (.i 4),
  Op.cmp 64 0 (.r 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p8_4 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 7

def j8 : List Byte := [0x74, 0x16]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `89`. -/
def p9 : List Byte := [
  0x8b, 0x10, 0x83, 0xfa, 0x1f]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 0) none 1 0 32)] 2) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 31)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 32 2 (some 0) none 1 0,
  Op.cmp 32 2 (.i 31)]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p9_2 _) (OpI.cmp (.i 31) (.inl rfl)) (by decide) <|
  .nil 5

def j9 : List Byte := [0x7f, 0xc8]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 15) 64 [.rel 18446744073709551560] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p10 : List Byte := [
  0xc7, 0x00, 0x5f, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc0, 0x04, 0x48, 0x39, 0xc8]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 95] 6) := by dec_rfl
theorem p10_6 : ∀ feat, Dec feat p10 6 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.sti 32 (some 0) none 1 0 95,
  Op.add 64 0 (.i 4),
  Op.cmp 64 0 (.r 1)]

theorem b10 (prof : Profile) : Blk prof p10 0 13 o10 :=
  .cons (p10_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p10_6 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p10_10 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 13

def j10 : List Byte := [0x75, 0xea]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551594] 2) := by dec_rfl

def j11 : List Byte := [0x74, 0x20]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 4) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `116`. -/
def p11 : List Byte := [
  0x83, 0xea, 0x01, 0x48, 0x8d, 0x54, 0x90, 0x04, 0x0f, 0x1f, 0x40, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) (some 2) 4 4 0)] 5) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.sub 32 2 (.i 1),
  Op.lea 64 2 (some 0) (some 2) 4 4,
  Op.nop]

theorem b11 (prof : Profile) : Blk prof p11 0 12 o11 :=
  .cons (p11_0 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_8 _) (OpI.nop) (by decide) <|
  .nil 12

/-- The stretch at `128`. -/
def p12 : List Byte := [
  0x83, 0x38, 0x0a]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cmp 32 [.mem (mg (some 0) none 1 0 32), .imm 32 10] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cmpmi 32 (some 0) none 1 0 10]

theorem b12 (prof : Profile) : Blk prof p12 0 3 o12 :=
  .cons (p12_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 3

def j12 : List Byte := [0x75, 0x06]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `133`. -/
def p13 : List Byte := [
  0xc7, 0x00, 0x5f, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [.mem (mg (some 0) none 1 0 32), .imm 32 95] 6) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sti 32 (some 0) none 1 0 95]

theorem b13 (prof : Profile) : Blk prof p13 0 6 o13 :=
  .cons (p13_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 6

/-- The stretch at `139`. -/
def p14 : List Byte := [
  0x48, 0x83, 0xc0, 0x04, 0x48, 0x39, 0xd0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.add 64 0 (.i 4),
  Op.cmp 64 0 (.r 2)]

theorem b14 (prof : Profile) : Blk prof p14 0 7 o14 :=
  .cons (p14_0 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p14_4 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 7

def j13 : List Byte := [0x75, 0xec]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551596] 2) := by dec_rfl

end FV7z.Nus
