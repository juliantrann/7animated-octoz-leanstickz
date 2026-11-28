import FV7z.Lemmas.Sp
import FV7z.Lemmas.CmpMr8
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArchiveExtractCallback::QueryInterface` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 21 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Aeq
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0x02, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc1, 0x70, 0xb9,
  0x6e, 0x00, 0x31, 0xc0, 0x0f, 0x1f, 0x40, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7256432)] 7) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sti 64 (some 2) none 1 0 0,
  Op.mov 64 1 (.i 7256432),
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b0 (prof : Profile) : Blk prof p0 0 24 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.i 7256432) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_20 _) (OpI.nop) (by decide) <|
  .nil 24

/-- The stretch at `24`. -/
def p1 : List Byte := [
  0x44, 0x0f, 0xb6, 0x04, 0x06, 0x44, 0x38, 0x04, 0x08]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .movzx 32 [gr 32 8, .mem (mg (some 6) (some 0) 1 0 8)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .cmp 8 [.mem (mg (some 0) (some 1) 1 0 8), gr 8 8] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ldzx 8 8 (some 6) (some 0) 1 0,
  Op.cmpmr 8 (some 0) (some 1) 1 0 8]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.cmpmr8) (by decide) <|
  .nil 9

def j0 : List Byte := [0x75, 0x1d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `35`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc0, 0x01, 0x48, 0x83, 0xf8, 0x10]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 0 (.i 1),
  Op.cmp 64 0 (.i 16)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmp (.i 16) (.inr rfl)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x75, 0xeb]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `45`. -/
def p3 : List Byte := [
  0x48, 0x8d, 0x47, 0x08, 0x48, 0x89, 0x02]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 8 0)] 4) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.lea 64 0 (some 7) none 1 8,
  Op.st 64 (some 2) none 1 0 0]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

/-- The stretch at `56`. -/
def p4 : List Byte := [
  0x31, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `64`. -/
def p5 : List Byte := [
  0x48, 0xc7, 0xc1, 0x90, 0xb8, 0x6e, 0x00, 0x31, 0xc0, 0x44, 0x0f, 0xb6, 0x0c, 0x08, 0x44, 0x38,
  0x0c, 0x06]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7256208)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_9 : ∀ feat, Dec feat p5 9 (FV7z.mk .movzx 32 [gr 32 9, .mem (mg (some 0) (some 1) 1 0 8)] 5) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .cmp 8 [.mem (mg (some 6) (some 0) 1 0 8), gr 8 9] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 1 (.i 7256208),
  Op.xor 32 0 (.r 0),
  Op.ldzx 8 9 (some 0) (some 1) 1 0,
  Op.cmpmr 8 (some 6) (some 0) 1 0 9]

theorem b5 (prof : Profile) : Blk prof p5 0 18 o5 :=
  .cons (p5_0 _) (OpI.mov (.i 7256208) (.inr rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p5_9 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p5_14 _) (OpI.cmpmr8) (by decide) <|
  .nil 18

def j2 : List Byte := [0x75, 0x19]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 25] 2) := by dec_rfl

/-- The stretch at `84`. -/
def p6 : List Byte := [
  0x0f, 0x1f, 0x40, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.nop]

theorem b6 (prof : Profile) : Blk prof p6 0 4 o6 :=
  .cons (p6_0 _) (OpI.nop) (by decide) <|
  .nil 4

def j3 : List Byte := [0x74, 0xcb]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551563] 2) := by dec_rfl

/-- The stretch at `98`. -/
def p7 : List Byte := [
  0x44, 0x0f, 0xb6, 0x0c, 0x08, 0x44, 0x38, 0x0c, 0x06]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movzx 32 [gr 32 9, .mem (mg (some 0) (some 1) 1 0 8)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .cmp 8 [.mem (mg (some 6) (some 0) 1 0 8), gr 8 9] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldzx 8 9 (some 0) (some 1) 1 0,
  Op.cmpmr 8 (some 6) (some 0) 1 0 9]

theorem b7 (prof : Profile) : Blk prof p7 0 9 o7 :=
  .cons (p7_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.cmpmr8) (by decide) <|
  .nil 9

def j4 : List Byte := [0x74, 0xeb]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `109`. -/
def p8 : List Byte := [
  0x48, 0xc7, 0xc1, 0x80, 0xb7, 0x6e, 0x00, 0x31, 0xc0, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00,
  0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7255936)] 7) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p8_9 : ∀ feat, Dec feat p8 9 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 1 (.i 7255936),
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b8 (prof : Profile) : Blk prof p8 0 19 o8 :=
  .cons (p8_0 _) (OpI.mov (.i 7255936) (.inr rfl)) (by decide) <|
  .cons (p8_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p8_9 _) (OpI.nop) (by decide) <|
  .nil 19

/-- The stretch at `128`. -/
def p9 : List Byte := [
  0x44, 0x0f, 0xb6, 0x14, 0x08, 0x44, 0x38, 0x14, 0x06]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .movzx 32 [gr 32 10, .mem (mg (some 0) (some 1) 1 0 8)] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .cmp 8 [.mem (mg (some 6) (some 0) 1 0 8), gr 8 10] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ldzx 8 10 (some 0) (some 1) 1 0,
  Op.cmpmr 8 (some 6) (some 0) 1 0 10]

theorem b9 (prof : Profile) : Blk prof p9 0 9 o9 :=
  .cons (p9_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p9_5 _) (OpI.cmpmr8) (by decide) <|
  .nil 9

/-- The stretch at `149`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0x47, 0x10, 0x48, 0x89, 0x02, 0x31, 0xc0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 16 0)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.lea 64 0 (some 7) none 1 16,
  Op.st 64 (some 2) none 1 0 0,
  Op.xor 32 0 (.r 0)]

theorem b10 (prof : Profile) : Blk prof p10 0 9 o10 :=
  .cons (p10_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `168`. -/
def p11 : List Byte := [
  0x48, 0xc7, 0xc1, 0x60, 0xb7, 0x6e, 0x00, 0x31, 0xc0, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7255904)] 7) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p11_9 : ∀ feat, Dec feat p11 9 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 1 (.i 7255904),
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b11 (prof : Profile) : Blk prof p11 0 16 o11 :=
  .cons (p11_0 _) (OpI.mov (.i 7255904) (.inr rfl)) (by decide) <|
  .cons (p11_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p11_9 _) (OpI.nop) (by decide) <|
  .nil 16

/-- The stretch at `184`. -/
def p12 : List Byte := [
  0x44, 0x0f, 0xb6, 0x1c, 0x08, 0x44, 0x38, 0x1c, 0x06]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .movzx 32 [gr 32 11, .mem (mg (some 0) (some 1) 1 0 8)] 5) := by dec_rfl
theorem p12_5 : ∀ feat, Dec feat p12 5 (FV7z.mk .cmp 8 [.mem (mg (some 6) (some 0) 1 0 8), gr 8 11] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ldzx 8 11 (some 0) (some 1) 1 0,
  Op.cmpmr 8 (some 6) (some 0) 1 0 11]

theorem b12 (prof : Profile) : Blk prof p12 0 9 o12 :=
  .cons (p12_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p12_5 _) (OpI.cmpmr8) (by decide) <|
  .nil 9

def j5 : List Byte := [0x75, 0x16]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `205`. -/
def p13 : List Byte := [
  0x48, 0x8d, 0x47, 0x18, 0x48, 0x89, 0x02]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 24 0)] 4) := by dec_rfl
theorem p13_4 : ∀ feat, Dec feat p13 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.lea 64 0 (some 7) none 1 24,
  Op.st 64 (some 2) none 1 0 0]

theorem b13 (prof : Profile) : Blk prof p13 0 7 o13 :=
  .cons (p13_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p13_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

def j6 : List Byte := [0xe9, 0x5b, 0xff, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551451] 5) := by dec_rfl

/-- The stretch at `217`. -/
def p14 : List Byte := [
  0x48, 0xc7, 0xc1, 0xf0, 0xb7, 0x6e, 0x00, 0x31, 0xc0, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7256048)] 7) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p14_9 : ∀ feat, Dec feat p14 9 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 1 (.i 7256048),
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b14 (prof : Profile) : Blk prof p14 0 15 o14 :=
  .cons (p14_0 _) (OpI.mov (.i 7256048) (.inr rfl)) (by decide) <|
  .cons (p14_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p14_9 _) (OpI.nop) (by decide) <|
  .nil 15

/-- The stretch at `253`. -/
def p15 : List Byte := [
  0x48, 0x8d, 0x47, 0x20, 0x48, 0x89, 0x02]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 32 0)] 4) := by dec_rfl
theorem p15_4 : ∀ feat, Dec feat p15 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.lea 64 0 (some 7) none 1 32,
  Op.st 64 (some 2) none 1 0 0]

theorem b15 (prof : Profile) : Blk prof p15 0 7 o15 :=
  .cons (p15_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p15_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

def j7 : List Byte := [0xe9, 0x2b, 0xff, 0xff, 0xff]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551403] 5) := by dec_rfl

/-- The stretch at `265`. -/
def p16 : List Byte := [
  0x48, 0xc7, 0xc1, 0xe0, 0xb7, 0x6e, 0x00, 0x31, 0xc0, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7256032)] 7) := by dec_rfl
theorem p16_7 : ∀ feat, Dec feat p16 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p16_9 : ∀ feat, Dec feat p16 9 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 64 1 (.i 7256032),
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b16 (prof : Profile) : Blk prof p16 0 15 o16 :=
  .cons (p16_0 _) (OpI.mov (.i 7256032) (.inr rfl)) (by decide) <|
  .cons (p16_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p16_9 _) (OpI.nop) (by decide) <|
  .nil 15

/-- The stretch at `301`. -/
def p17 : List Byte := [
  0x48, 0x8d, 0x47, 0x28, 0x48, 0x89, 0x02]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 40 0)] 4) := by dec_rfl
theorem p17_4 : ∀ feat, Dec feat p17 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.lea 64 0 (some 7) none 1 40,
  Op.st 64 (some 2) none 1 0 0]

theorem b17 (prof : Profile) : Blk prof p17 0 7 o17 :=
  .cons (p17_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p17_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

def j8 : List Byte := [0xe9, 0xfb, 0xfe, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551355] 5) := by dec_rfl

/-- The stretch at `313`. -/
def p18 : List Byte := [
  0x48, 0xc7, 0xc1, 0x90, 0xb7, 0x6e, 0x00, 0x31, 0xc0, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7255952)] 7) := by dec_rfl
theorem p18_7 : ∀ feat, Dec feat p18 7 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p18_9 : ∀ feat, Dec feat p18 9 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 6) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.mov 64 1 (.i 7255952),
  Op.xor 32 0 (.r 0),
  Op.nop]

theorem b18 (prof : Profile) : Blk prof p18 0 15 o18 :=
  .cons (p18_0 _) (OpI.mov (.i 7255952) (.inr rfl)) (by decide) <|
  .cons (p18_7 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p18_9 _) (OpI.nop) (by decide) <|
  .nil 15

/-- The stretch at `349`. -/
def p19 : List Byte := [
  0x48, 0x8d, 0x47, 0x30, 0x48, 0x89, 0x02]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) none 1 48 0)] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.lea 64 0 (some 7) none 1 48,
  Op.st 64 (some 2) none 1 0 0]

theorem b19 (prof : Profile) : Blk prof p19 0 7 o19 :=
  .cons (p19_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 7

def j9 : List Byte := [0xe9, 0xcb, 0xfe, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551307] 5) := by dec_rfl

/-- The stretch at `361`. -/
def p20 : List Byte := [
  0xb8, 0x02, 0x40, 0x00, 0x80]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147500034)] 5) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 32 0 (.i 2147500034)]

theorem b20 (prof : Profile) : Blk prof p20 0 5 o20 :=
  .cons (p20_0 _) (OpI.mov (.i 2147500034) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Aeq
