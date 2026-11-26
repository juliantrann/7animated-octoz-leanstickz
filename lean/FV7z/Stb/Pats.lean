import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_IO_setb` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Stb
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x89, 0xcd, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xec, 0x18, 0x48,
  0x8b, 0x7f, 0x38, 0x8b, 0x03, 0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0x54, 0x24, 0x08, 0x48, 0x85,
  0xff]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 56 64)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 0 32)] 2) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 6] 4) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 2] 5) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 32 5 (.r 1),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 4 (.i 24),
  Op.ld 64 7 (some 7) none 1 56,
  Op.ld 32 0 (some 3) none 1 0,
  Op.st 64 (some 4) none 1 0 6,
  Op.st 64 (some 4) none 1 8 2,
  Op.test 64 7 (.r 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 33 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_5 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.sub (.i 24) (.inr rfl)) (by decide) <|
  .cons (p0_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_21 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_25 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_30 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 33

def j0 : List Byte := [0x74, 0x04]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p1 : List Byte := [
  0xa8, 0x01]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.test 8 0 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 2 o1 :=
  .cons (p1_0 _) (OpI.test8 (.i 1)) (by decide) <|
  .nil 2

def j1 : List Byte := [0x74, 0x29]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 41] 2) := by dec_rfl

/-- The stretch at `39`. -/
def p2 : List Byte := [
  0x89, 0xc2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 2 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `46`. -/
def p3 : List Byte := [
  0x83, 0xc8, 0x01, 0x83, 0xe2, 0xfe, 0x85, 0xed, 0x0f, 0x45, 0xc2]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 4294967294)] 3) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .test 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk (.cmovcc 5) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.or 32 0 (.i 1),
  Op.and 32 2 (.i 4294967294),
  Op.test 32 5 (.r 5),
  Op.cmov32 5 0 2]

theorem b3 (prof : Profile) : Blk prof p3 0 11 o3 :=
  .cons (p3_0 _) (OpI.or (.i 1) (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.and (.i 4294967294) (.inl rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.test (.r 5) (.inl rfl)) (by decide) <|
  .cons (p3_8 _) (OpI.cmov32) (by decide) <|
  .nil 11

/-- The stretch at `66`. -/
def p4 : List Byte := [
  0x89, 0x03, 0x48, 0x83, 0xc4, 0x18, 0x5b, 0x5d]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p4_2 : ∀ feat, Dec feat p4 2 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 24)] 4) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 32 (some 3) none 1 0 0,
  Op.add 64 4 (.i 24),
  Op.pop 3,
  Op.pop 5]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_2 _) (OpI.add (.i 24) (.inr rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.pop) (by decide) <|
  .cons (p4_7 _) (OpI.pop) (by decide) <|
  .nil 8

/-- The stretch at `85`. -/
def p5 : List Byte := [
  0x8b, 0x03]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 0 32)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 32 0 (some 3) none 1 0]

theorem b5 (prof : Profile) : Blk prof p5 0 2 o5 :=
  .cons (p5_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 2

def j2 : List Byte := [0xeb, 0xce]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [.rel 18446744073709551566] 2) := by dec_rfl

end FV7z.Stb
