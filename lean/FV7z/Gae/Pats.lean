import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps25
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `GetOpenArcErrorFlags` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gae
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0xec, 0x08, 0x0f, 0xb7, 0x07, 0x48, 0x85, 0xf6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 16)] 3) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sub 64 4 (.i 8),
  Op.ldzx 16 0 (some 7) none 1 0,
  Op.test 64 6 (.r 6)]

theorem b0 (prof : Profile) : Blk prof p0 0 14 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x38]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 56] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0xc6, 0x06, 0x00, 0x66, 0x83, 0xf8, 0x13]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 19)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sti 8 (some 6) none 1 0 0,
  Op.cmp 16 0 (.i 19)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.cmp16 (.i 19)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x74, 0x17]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `25`. -/
def p2 : List Byte := [
  0x66, 0x83, 0xf8, 0x15]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 21)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 16 0 (.i 21)]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmp16 (.i 21)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x74, 0x11]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 17] 2) := by dec_rfl

/-- The stretch at `31`. -/
def p3 : List Byte := [
  0x66, 0x85, 0xc0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 16 [gr 16 0, Src.opd 16 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 16 0 (.r 0)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test16 (.r 0)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x75, 0x1c]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `36`. -/
def p4 : List Byte := [
  0x31, 0xc0, 0x48, 0x83, 0xc4, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_2 : ∀ feat, Dec feat p4 2 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.add 64 4 (.i 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_2 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `48`. -/
def p5 : List Byte := [
  0xc6, 0x06, 0x01]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), .imm 8 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sti 8 (some 6) none 1 0 1]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `51`. -/
def p6 : List Byte := [
  0x8b, 0x47, 0x08, 0x48, 0x83, 0xc4, 0x08]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 32 0 (some 7) none 1 8,
  Op.add 64 4 (.i 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `72`. -/
def p7 : List Byte := [
  0x66, 0x83, 0xf8, 0x13]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 19)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 16 0 (.i 19)]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.cmp16 (.i 19)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x74, 0xe5]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551589] 2) := by dec_rfl

def j5 : List Byte := [0x74, 0xdf]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551583] 2) := by dec_rfl

def j6 : List Byte := [0x74, 0xcb]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551563] 2) := by dec_rfl

end FV7z.Gae
