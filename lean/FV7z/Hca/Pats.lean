import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `handle_amd` (PLAN.md M, ctor 103)

Each distinct stretch between labels and jumps (`p*`, 15 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Hca
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x53, 0xb8, 0x00, 0x00, 0x00, 0x80]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_1 : ∀ feat, Dec feat p0 1 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147483648)] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.push 3,
  Op.mov 32 0 (.i 2147483648)]

theorem b0 (prof : Profile) : Blk prof p0 0 6 o0 :=
  .cons (p0_0 _) (OpI.push) (by decide) <|
  .cons (p0_1 _) (OpI.mov (.i 2147483648) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `8`. -/
def p1 : List Byte := [
  0x81, 0xff, 0xc4, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 196)] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 7 (.i 196)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 196) (.inl rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x7f, 0x50]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 15) 64 [.rel 80] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p2 : List Byte := [
  0x31, 0xd2, 0x81, 0xff, 0xbe, 0x00, 0x00, 0x00, 0x0f, 0x9f, 0xc2, 0x81, 0xea, 0xfb, 0xff, 0xff,
  0x7f, 0x39, 0xc2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 190)] 6) := by dec_rfl
theorem p2_8 : ∀ feat, Dec feat p2 8 (FV7z.mk (.setcc 15) 8 [gr 8 2] 3) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .sub 32 [gr 32 2, Src.opd 32 (.i 2147483643)] 6) := by dec_rfl
theorem p2_17 : ∀ feat, Dec feat p2 17 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.cmp 32 7 (.i 190),
  Op.setcc 15 2,
  Op.sub 32 2 (.i 2147483643),
  Op.cmp 32 2 (.r 0)]

theorem b2 (prof : Profile) : Blk prof p2 0 19 o2 :=
  .cons (p2_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.cmp (.i 190) (.inl rfl)) (by decide) <|
  .cons (p2_8 _) (OpI.setcc) (by decide) <|
  .cons (p2_11 _) (OpI.sub (.i 2147483643) (.inl rfl)) (by decide) <|
  .cons (p2_17 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 19

def j1 : List Byte := [0x77, 0x3b]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 59] 2) := by dec_rfl

/-- The stretch at `37`. -/
def p3 : List Byte := [
  0x89, 0xd0]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `41`. -/
def p4 : List Byte := [
  0x81, 0xff, 0xbb, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 187)] 6) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmp 32 7 (.i 187)]

theorem b4 (prof : Profile) : Blk prof p4 0 6 o4 :=
  .cons (p4_0 _) (OpI.cmp (.i 187) (.inl rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x7f, 0x05]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 15) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p5 : List Byte := [
  0x83, 0xc7, 0x03, 0x89, 0xd1]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 3)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.add 32 7 (.i 3),
  Op.mov 32 1 (.r 2)]

theorem b5 (prof : Profile) : Blk prof p5 0 5 o5 :=
  .cons (p5_0 _) (OpI.add (.i 3) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `54`. -/
def p6 : List Byte := [
  0x81, 0xef, 0xbc, 0x00, 0x00, 0x00, 0x83, 0xff, 0x08]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.i 188)] 6) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .cmp 32 [gr 32 7, Src.opd 32 (.i 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.sub 32 7 (.i 188),
  Op.cmp 32 7 (.i 8)]

theorem b6 (prof : Profile) : Blk prof p6 0 9 o6 :=
  .cons (p6_0 _) (OpI.sub (.i 188) (.inl rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.cmp (.i 8) (.inl rfl)) (by decide) <|
  .nil 9

def j3 : List Byte := [0x0f, 0x87, 0x6b, 0x01, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 7) 64 [.rel 363] 6) := by dec_rfl

/-- The stretch at `69`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x35, 0xa4, 0x54, 0x09, 0x00, 0x48, 0x63, 0x04, 0xbe, 0x48, 0x01, 0xf0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 611492 0)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 6) (some 7) 4 0 32)] 4) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 6 (.i 7282688),
  Op.ldsx 0 (some 6) (some 7) 4 0,
  Op.add 64 0 (.r 6)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x65cb55 : Addr) 0 14 o7 :=
  .cons (p7_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_7 _) ((OpI.ldsx).at _) (by decide) <|
  .cons (p7_11 _) ((OpI.add (.r 6) (.inr rfl)).at _) (by decide) <|
  .nil 14

def j4 : List Byte := [0x3e, 0xff, 0xe0]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [gr 64 0] 3) := by dec_rfl

/-- The stretch at `96`. -/
def p8 : List Byte := [
  0x31, 0xc0]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 2 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `98`. -/
def p9 : List Byte := [
  0x5b]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.pop 3]

theorem b9 (prof : Profile) : Blk prof p9 0 1 o9 :=
  .cons (p9_0 _) (OpI.pop) (by decide) <|
  .nil 1

/-- The stretch at `160`. -/
def p10 : List Byte := [
  0x89, 0xc8, 0x5b, 0xc1, 0xe8, 0x0e, 0x25, 0x00, 0xfc, 0x03, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 14)] 3) := by dec_rfl
theorem p10_6 : ∀ feat, Dec feat p10 6 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 261120)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 0 (.r 1),
  Op.pop 3,
  Op.shr 0 (.i 14),
  Op.and 32 0 (.i 261120)]

theorem b10 (prof : Profile) : Blk prof p10 0 11 o10 :=
  .cons (p10_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.pop) (by decide) <|
  .cons (p10_3 _) (OpI.shr (.i 14)) (by decide) <|
  .cons (p10_6 _) (OpI.and (.i 261120) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `224`. -/
def p11 : List Byte := [
  0x31, 0xc0, 0xf6, 0xc5, 0xf0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p11_2 : ∀ feat, Dec feat p11 2 (FV7z.mk .test 8 [gh 1, .imm 8 240] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.testh 1 240]

theorem b11 (prof : Profile) : Blk prof p11 0 5 o11 :=
  .cons (p11_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p11_2 _) (OpI.testh) (by decide) <|
  .nil 5

def j5 : List Byte := [0x0f, 0x84, 0x77, 0xff, 0xff, 0xff]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551479] 6) := by dec_rfl

/-- The stretch at `235`. -/
def p12 : List Byte := [
  0x89, 0xc8, 0x5b, 0xc1, 0xe8, 0x06, 0x25, 0x00, 0xfc, 0xff, 0x03]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p12_2 : ∀ feat, Dec feat p12 2 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 6)] 3) := by dec_rfl
theorem p12_6 : ∀ feat, Dec feat p12 6 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 67107840)] 5) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 32 0 (.r 1),
  Op.pop 3,
  Op.shr 0 (.i 6),
  Op.and 32 0 (.i 67107840)]

theorem b12 (prof : Profile) : Blk prof p12 0 11 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p12_2 _) (OpI.pop) (by decide) <|
  .cons (p12_3 _) (OpI.shr (.i 6)) (by decide) <|
  .cons (p12_6 _) (OpI.and (.i 67107840) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `312`. -/
def p13 : List Byte := [
  0x31, 0xc0, 0xf6, 0xc6, 0xf0]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .test 8 [gh 2, .imm 8 240] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.testh 2 240]

theorem b13 (prof : Profile) : Blk prof p13 0 5 o13 :=
  .cons (p13_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p13_2 _) (OpI.testh) (by decide) <|
  .nil 5

def j6 : List Byte := [0x0f, 0x84, 0x1f, 0xff, 0xff, 0xff]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551391] 6) := by dec_rfl

/-- The stretch at `323`. -/
def p14 : List Byte := [
  0x8d, 0x04, 0x12, 0x5b, 0x25, 0x00, 0x00, 0xf8, 0x7f]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 2) (some 2) 1 0 0)] 3) := by dec_rfl
theorem p14_3 : ∀ feat, Dec feat p14 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 2146959360)] 5) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.lea 32 0 (some 2) (some 2) 1 0,
  Op.pop 3,
  Op.and 32 0 (.i 2146959360)]

theorem b14 (prof : Profile) : Blk prof p14 0 9 o14 :=
  .cons (p14_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p14_3 _) (OpI.pop) (by decide) <|
  .cons (p14_4 _) (OpI.and (.i 2146959360) (.inl rfl)) (by decide) <|
  .nil 9

end FV7z.Hca
