import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `Utf16_To_Utf8` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 30 of them) and each distinct jump (`j*`, 25) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.U8w
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x89, 0xf8, 0x41, 0x89, 0xc8, 0x48, 0x39, 0xd6]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.mov 64 0 (.r 7),
  Op.mov 32 8 (.r 1),
  Op.cmp 64 6 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 9

def j0 : List Byte := [0x0f, 0x84, 0xb2, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 178] 6) := by dec_rfl

/-- The stretch at `15`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc9, 0x41, 0x81, 0xe0, 0x00, 0x01, 0x00, 0x00, 0x41, 0x81, 0xe1, 0x00, 0x02, 0x00,
  0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .and 32 [gr 32 8, Src.opd 32 (.i 256)] 7) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .and 32 [gr 32 9, Src.opd 32 (.i 512)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 9 (.r 1),
  Op.and 32 8 (.i 256),
  Op.and 32 9 (.i 512)]

theorem b1 (prof : Profile) : Blk prof p1 0 17 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.and (.i 256) (.inl rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.and (.i 512) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x8b, 0x0e, 0x48, 0x8d, 0x7e, 0x04, 0x41, 0x89, 0xca, 0x83, 0xf9, 0x7f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 6) none 1 0 32)] 2) := by dec_rfl
theorem p2_2 : ∀ feat, Dec feat p2 2 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 6) none 1 4 0)] 4) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 127)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 1 (some 6) none 1 0,
  Op.lea 64 7 (some 6) none 1 4,
  Op.mov 32 10 (.r 1),
  Op.cmp 32 1 (.i 127)]

theorem b2 (prof : Profile) : Blk prof p2 0 12 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_2 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.cmp (.i 127) (.inl rfl)) (by decide) <|
  .nil 12

def j1 : List Byte := [0x0f, 0x86, 0x96, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 150] 6) := by dec_rfl

/-- The stretch at `50`. -/
def p3 : List Byte := [
  0x81, 0xf9, 0xff, 0x07, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 2047)] 6) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmp 32 1 (.i 2047)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.cmp (.i 2047) (.inl rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x0f, 0x86, 0x9a, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 154] 6) := by dec_rfl

/-- The stretch at `62`. -/
def p4 : List Byte := [
  0x45, 0x85, 0xc9]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.test 32 9 (.r 9)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.test (.r 9) (.inl rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x10]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `67`. -/
def p5 : List Byte := [
  0x41, 0x89, 0xcb, 0x41, 0x83, 0xe3, 0x80, 0x41, 0x81, 0xfb, 0x80, 0xef, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .and 32 [gr 32 11, Src.opd 32 (.i 4294967168)] 4) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .cmp 32 [gr 32 11, Src.opd 32 (.i 61312)] 7) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 11 (.r 1),
  Op.and 32 11 (.i 4294967168),
  Op.cmp 32 11 (.i 61312)]

theorem b5 (prof : Profile) : Blk prof p5 0 14 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.and (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p5_7 _) (OpI.cmp (.i 61312) (.inl rfl)) (by decide) <|
  .nil 14

def j4 : List Byte := [0x74, 0x75]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 117] 2) := by dec_rfl

/-- The stretch at `83`. -/
def p6 : List Byte := [
  0x41, 0x89, 0xcb, 0x41, 0x81, 0xe3, 0x00, 0xf8, 0xff, 0xff, 0x41, 0x81, 0xfb, 0x00, 0xd8, 0x00,
  0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .and 32 [gr 32 11, Src.opd 32 (.i 4294965248)] 7) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .cmp 32 [gr 32 11, Src.opd 32 (.i 55296)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 32 11 (.r 1),
  Op.and 32 11 (.i 4294965248),
  Op.cmp 32 11 (.i 55296)]

theorem b6 (prof : Profile) : Blk prof p6 0 17 o6 :=
  .cons (p6_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p6_3 _) (OpI.and (.i 4294965248) (.inl rfl)) (by decide) <|
  .cons (p6_10 _) (OpI.cmp (.i 55296) (.inl rfl)) (by decide) <|
  .nil 17

def j5 : List Byte := [0x0f, 0x84, 0x96, 0x00, 0x00, 0x00]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 150] 6) := by dec_rfl

/-- The stretch at `106`. -/
def p7 : List Byte := [
  0x81, 0xf9, 0xff, 0xff, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 65535)] 6) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 32 1 (.i 65535)]

theorem b7 (prof : Profile) : Blk prof p7 0 6 o7 :=
  .cons (p7_0 _) (OpI.cmp (.i 65535) (.inl rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x0f, 0x86, 0xea, 0x00, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 6) 64 [.rel 234] 6) := by dec_rfl

/-- The stretch at `118`. -/
def p8 : List Byte := [
  0x81, 0xf9, 0xff, 0xff, 0x1f, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 2097151)] 6) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.cmp 32 1 (.i 2097151)]

theorem b8 (prof : Profile) : Blk prof p8 0 6 o8 :=
  .cons (p8_0 _) (OpI.cmp (.i 2097151) (.inl rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0x0f, 0x87, 0xfe, 0x00, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 7) 64 [.rel 254] 6) := by dec_rfl

/-- The stretch at `130`. -/
def p9 : List Byte := [
  0xc1, 0xe9, 0x12, 0x8d, 0x71, 0xf0, 0xb9, 0x12, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 18)] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 1) none 1 18446744073709551600 0)] 3) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 18)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.shr 1 (.i 18),
  Op.lea 32 6 (some 1) none 1 18446744073709551600,
  Op.mov 32 1 (.i 18)]

theorem b9 (prof : Profile) : Blk prof p9 0 11 o9 :=
  .cons (p9_0 _) (OpI.shr (.i 18)) (by decide) <|
  .cons (p9_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p9_6 _) (OpI.mov (.i 18) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `141`. -/
def p10 : List Byte := [
  0x40, 0x88, 0x30, 0x48, 0x83, 0xc0, 0x01, 0x0f, 0x1f, 0x40, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), gr 8 6] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.st 8 (some 0) none 1 0 6,
  Op.add 64 0 (.i 1),
  Op.nop]

theorem b10 (prof : Profile) : Blk prof p10 0 11 o10 :=
  .cons (p10_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p10_3 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.nop) (by decide) <|
  .nil 11

/-- The stretch at `152`. -/
def p11 : List Byte := [
  0x83, 0xe9, 0x06, 0x44, 0x89, 0xd6, 0x48, 0x83, 0xc0, 0x01, 0xd3, 0xee, 0x83, 0xe6, 0x3f, 0x83,
  0xc6, 0x80, 0x40, 0x88, 0x70, 0xff, 0x85, 0xc9]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 6)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p11_6 : ∀ feat, Dec feat p11 6 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p11_12 : ∀ feat, Dec feat p11 12 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p11_15 : ∀ feat, Dec feat p11 15 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p11_18 : ∀ feat, Dec feat p11 18 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551615 8), gr 8 6] 4) := by dec_rfl
theorem p11_22 : ∀ feat, Dec feat p11 22 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.sub 32 1 (.i 6),
  Op.mov 32 6 (.r 10),
  Op.add 64 0 (.i 1),
  Op.shr 6 (.r 1),
  Op.and 32 6 (.i 63),
  Op.add 32 6 (.i 4294967168),
  Op.st 8 (some 0) none 1 18446744073709551615 6,
  Op.test 32 1 (.r 1)]

theorem b11 (prof : Profile) : Blk prof p11 0 24 o11 :=
  .cons (p11_0 _) (OpI.sub (.i 6) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p11_6 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .cons (p11_10 _) (OpI.shr (.r 1)) (by decide) <|
  .cons (p11_12 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p11_15 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p11_18 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p11_22 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 24

def j8 : List Byte := [0x75, 0xe6]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551590] 2) := by dec_rfl

/-- The stretch at `178`. -/
def p12 : List Byte := [
  0x48, 0x89, 0xfe, 0x0f, 0x1f, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 6 (.r 7),
  Op.nop]

theorem b12 (prof : Profile) : Blk prof p12 0 6 o12 :=
  .cons (p12_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p12_3 _) (OpI.nop) (by decide) <|
  .nil 6

/-- The stretch at `184`. -/
def p13 : List Byte := [
  0x48, 0x39, 0xd6]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .cmp 64 [gr 64 6, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.cmp 64 6 (.r 2)]

theorem b13 (prof : Profile) : Blk prof p13 0 3 o13 :=
  .cons (p13_0 _) (OpI.cmp (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

def j9 : List Byte := [0x0f, 0x85, 0x5f, 0xff, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551455] 6) := by dec_rfl

/-- The stretch at `200`. -/
def p14 : List Byte := [
  0x88, 0x08, 0x48, 0x89, 0xfe, 0x48, 0x83, 0xc0, 0x01]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 0 8), gr 8 1] 2) := by dec_rfl
theorem p14_2 : ∀ feat, Dec feat p14 2 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p14_5 : ∀ feat, Dec feat p14 5 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.st 8 (some 0) none 1 0 1,
  Op.mov 64 6 (.r 7),
  Op.add 64 0 (.i 1)]

theorem b14 (prof : Profile) : Blk prof p14 0 9 o14 :=
  .cons (p14_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p14_2 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p14_5 _) (OpI.add (.i 1) (.inr rfl)) (by decide) <|
  .nil 9

def j10 : List Byte := [0xeb, 0xe5]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551589] 2) := by dec_rfl

/-- The stretch at `216`. -/
def p15 : List Byte := [
  0x89, 0xce, 0x83, 0xe1, 0x3f, 0x48, 0x83, 0xc0, 0x02, 0xc1, 0xee, 0x06, 0x83, 0xc1, 0x80, 0x83,
  0xee, 0x40, 0x88, 0x48, 0xff, 0x40, 0x88, 0x70, 0xfe, 0x48, 0x89, 0xfe]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p15_2 : ∀ feat, Dec feat p15 2 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p15_9 : ∀ feat, Dec feat p15 9 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.i 6)] 3) := by dec_rfl
theorem p15_12 : ∀ feat, Dec feat p15 12 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p15_15 : ∀ feat, Dec feat p15 15 (FV7z.mk .sub 32 [gr 32 6, Src.opd 32 (.i 64)] 3) := by dec_rfl
theorem p15_18 : ∀ feat, Dec feat p15 18 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551615 8), gr 8 1] 3) := by dec_rfl
theorem p15_21 : ∀ feat, Dec feat p15 21 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551614 8), gr 8 6] 4) := by dec_rfl
theorem p15_25 : ∀ feat, Dec feat p15 25 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 32 6 (.r 1),
  Op.and 32 1 (.i 63),
  Op.add 64 0 (.i 2),
  Op.shr 6 (.i 6),
  Op.add 32 1 (.i 4294967168),
  Op.sub 32 6 (.i 64),
  Op.st 8 (some 0) none 1 18446744073709551615 1,
  Op.st 8 (some 0) none 1 18446744073709551614 6,
  Op.mov 64 6 (.r 7)]

theorem b15 (prof : Profile) : Blk prof p15 0 28 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p15_2 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p15_5 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p15_9 _) (OpI.shr (.i 6)) (by decide) <|
  .cons (p15_12 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p15_15 _) (OpI.sub (.i 64) (.inl rfl)) (by decide) <|
  .cons (p15_18 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p15_21 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p15_25 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 28

def j11 : List Byte := [0xeb, 0xc2]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk .jmp 64 [.rel 18446744073709551554] 2) := by dec_rfl

/-- The stretch at `256`. -/
def p16 : List Byte := [
  0x81, 0xf9, 0xff, 0xdb, 0x00, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 56319)] 6) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.cmp 32 1 (.i 56319)]

theorem b16 (prof : Profile) : Blk prof p16 0 6 o16 :=
  .cons (p16_0 _) (OpI.cmp (.i 56319) (.inl rfl)) (by decide) <|
  .nil 6

def j12 : List Byte := [0x77, 0x20]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 7) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `264`. -/
def p17 : List Byte := [
  0x48, 0x39, 0xfa]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.cmp 64 2 (.r 7)]

theorem b17 (prof : Profile) : Blk prof p17 0 3 o17 :=
  .cons (p17_0 _) (OpI.cmp (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

def j13 : List Byte := [0x74, 0x1b]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 27] 2) := by dec_rfl

/-- The stretch at `269`. -/
def p18 : List Byte := [
  0x44, 0x8b, 0x56, 0x04, 0x45, 0x89, 0xd3, 0x41, 0x81, 0xe3, 0x00, 0xfc, 0xff, 0xff, 0x41, 0x81,
  0xfb, 0x00, 0xdc, 0x00, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 32 [gr 32 10, .mem (mg (some 6) none 1 4 32)] 4) := by dec_rfl
theorem p18_4 : ∀ feat, Dec feat p18 4 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p18_7 : ∀ feat, Dec feat p18 7 (FV7z.mk .and 32 [gr 32 11, Src.opd 32 (.i 4294966272)] 7) := by dec_rfl
theorem p18_14 : ∀ feat, Dec feat p18 14 (FV7z.mk .cmp 32 [gr 32 11, Src.opd 32 (.i 56320)] 7) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.ld 32 10 (some 6) none 1 4,
  Op.mov 32 11 (.r 10),
  Op.and 32 11 (.i 4294966272),
  Op.cmp 32 11 (.i 56320)]

theorem b18 (prof : Profile) : Blk prof p18 0 21 o18 :=
  .cons (p18_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p18_4 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .cons (p18_7 _) (OpI.and (.i 4294966272) (.inl rfl)) (by decide) <|
  .cons (p18_14 _) (OpI.cmp (.i 56320) (.inl rfl)) (by decide) <|
  .nil 21

def j14 : List Byte := [0x0f, 0x84, 0xc0, 0x00, 0x00, 0x00]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 4) 64 [.rel 192] 6) := by dec_rfl

/-- The stretch at `296`. -/
def p19 : List Byte := [
  0x45, 0x85, 0xc0]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.test 32 8 (.r 8)]

theorem b19 (prof : Profile) : Blk prof p19 0 3 o19 :=
  .cons (p19_0 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

def j15 : List Byte := [0x0f, 0x85, 0x87, 0x00, 0x00, 0x00]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 5) 64 [.rel 135] 6) := by dec_rfl

/-- The stretch at `305`. -/
def p20 : List Byte := [
  0x89, 0xce, 0x83, 0xe1, 0x3f, 0x41, 0xba, 0xed, 0xff, 0xff, 0xff, 0xc1, 0xee, 0x06, 0x83, 0xc1,
  0x80, 0x83, 0xe6, 0x3f, 0x83, 0xc6, 0x80]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p20_2 : ∀ feat, Dec feat p20 2 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p20_5 : ∀ feat, Dec feat p20 5 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 4294967277)] 6) := by dec_rfl
theorem p20_11 : ∀ feat, Dec feat p20 11 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.i 6)] 3) := by dec_rfl
theorem p20_14 : ∀ feat, Dec feat p20 14 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p20_17 : ∀ feat, Dec feat p20 17 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p20_20 : ∀ feat, Dec feat p20 20 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.mov 32 6 (.r 1),
  Op.and 32 1 (.i 63),
  Op.mov 32 10 (.i 4294967277),
  Op.shr 6 (.i 6),
  Op.add 32 1 (.i 4294967168),
  Op.and 32 6 (.i 63),
  Op.add 32 6 (.i 4294967168)]

theorem b20 (prof : Profile) : Blk prof p20 0 23 o20 :=
  .cons (p20_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p20_2 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p20_5 _) (OpI.mov (.i 4294967277) (.inl rfl)) (by decide) <|
  .cons (p20_11 _) (OpI.shr (.i 6)) (by decide) <|
  .cons (p20_14 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p20_17 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p20_20 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .nil 23

/-- The stretch at `328`. -/
def p21 : List Byte := [
  0x40, 0x88, 0x70, 0x01, 0x48, 0x83, 0xc0, 0x03, 0x48, 0x89, 0xfe, 0x44, 0x88, 0x50, 0xfd, 0x88,
  0x48, 0xff]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 1 8), gr 8 6] 4) := by dec_rfl
theorem p21_4 : ∀ feat, Dec feat p21 4 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 3)] 4) := by dec_rfl
theorem p21_8 : ∀ feat, Dec feat p21 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p21_11 : ∀ feat, Dec feat p21 11 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551613 8), gr 8 10] 4) := by dec_rfl
theorem p21_15 : ∀ feat, Dec feat p21 15 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551615 8), gr 8 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.st 8 (some 0) none 1 1 6,
  Op.add 64 0 (.i 3),
  Op.mov 64 6 (.r 7),
  Op.st 8 (some 0) none 1 18446744073709551613 10,
  Op.st 8 (some 0) none 1 18446744073709551615 1]

theorem b21 (prof : Profile) : Blk prof p21 0 18 o21 :=
  .cons (p21_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p21_4 _) (OpI.add (.i 3) (.inr rfl)) (by decide) <|
  .cons (p21_8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p21_11 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p21_15 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 18

def j16 : List Byte := [0xe9, 0x59, 0xff, 0xff, 0xff]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 18446744073709551449] 5) := by dec_rfl

/-- The stretch at `352`. -/
def p22 : List Byte := [
  0x89, 0xce, 0x41, 0x89, 0xca, 0x83, 0xe1, 0x3f, 0xc1, 0xee, 0x06, 0x41, 0xc1, 0xea, 0x0c, 0x83,
  0xc1, 0x80, 0x83, 0xe6, 0x3f, 0x41, 0x83, 0xea, 0x20, 0x83, 0xc6, 0x80]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p22_2 : ∀ feat, Dec feat p22 2 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.r 1)] 3) := by dec_rfl
theorem p22_5 : ∀ feat, Dec feat p22 5 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p22_8 : ∀ feat, Dec feat p22 8 (FV7z.mk .shr 32 [gr 32 6, Src.opd 8 (.i 6)] 3) := by dec_rfl
theorem p22_11 : ∀ feat, Dec feat p22 11 (FV7z.mk .shr 32 [gr 32 10, Src.opd 8 (.i 12)] 4) := by dec_rfl
theorem p22_15 : ∀ feat, Dec feat p22 15 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p22_18 : ∀ feat, Dec feat p22 18 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p22_21 : ∀ feat, Dec feat p22 21 (FV7z.mk .sub 32 [gr 32 10, Src.opd 32 (.i 32)] 4) := by dec_rfl
theorem p22_25 : ∀ feat, Dec feat p22 25 (FV7z.mk .add 32 [gr 32 6, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.mov 32 6 (.r 1),
  Op.mov 32 10 (.r 1),
  Op.and 32 1 (.i 63),
  Op.shr 6 (.i 6),
  Op.shr 10 (.i 12),
  Op.add 32 1 (.i 4294967168),
  Op.and 32 6 (.i 63),
  Op.sub 32 10 (.i 32),
  Op.add 32 6 (.i 4294967168)]

theorem b22 (prof : Profile) : Blk prof p22 0 28 o22 :=
  .cons (p22_0 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p22_2 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p22_5 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p22_8 _) (OpI.shr (.i 6)) (by decide) <|
  .cons (p22_11 _) (OpI.shr (.i 12)) (by decide) <|
  .cons (p22_15 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p22_18 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p22_21 _) (OpI.sub (.i 32) (.inl rfl)) (by decide) <|
  .cons (p22_25 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .nil 28

def j17 : List Byte := [0xeb, 0xca]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551562] 2) := by dec_rfl

/-- The stretch at `384`. -/
def p23 : List Byte := [
  0x81, 0xf9, 0xff, 0xff, 0xff, 0x03]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 67108863)] 6) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.cmp 32 1 (.i 67108863)]

theorem b23 (prof : Profile) : Blk prof p23 0 6 o23 :=
  .cons (p23_0 _) (OpI.cmp (.i 67108863) (.inl rfl)) (by decide) <|
  .nil 6

def j18 : List Byte := [0x77, 0x18]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 7) 64 [.rel 24] 2) := by dec_rfl

/-- The stretch at `392`. -/
def p24 : List Byte := [
  0xc1, 0xe9, 0x18, 0x8d, 0x71, 0xf8, 0xb9, 0x18, 0x00, 0x00, 0x00]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 24)] 3) := by dec_rfl
theorem p24_3 : ∀ feat, Dec feat p24 3 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 1) none 1 18446744073709551608 0)] 3) := by dec_rfl
theorem p24_6 : ∀ feat, Dec feat p24 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 24)] 5) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.shr 1 (.i 24),
  Op.lea 32 6 (some 1) none 1 18446744073709551608,
  Op.mov 32 1 (.i 24)]

theorem b24 (prof : Profile) : Blk prof p24 0 11 o24 :=
  .cons (p24_0 _) (OpI.shr (.i 24)) (by decide) <|
  .cons (p24_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p24_6 _) (OpI.mov (.i 24) (.inl rfl)) (by decide) <|
  .nil 11

def j19 : List Byte := [0xe9, 0xf5, 0xfe, 0xff, 0xff]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 18446744073709551349] 5) := by dec_rfl

/-- The stretch at `416`. -/
def p25 : List Byte := [
  0x85, 0xc9]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.test 32 1 (.r 1)]

theorem b25 (prof : Profile) : Blk prof p25 0 2 o25 :=
  .cons (p25_0 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 2

def j20 : List Byte := [0x78, 0x2c]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 8) 64 [.rel 44] 2) := by dec_rfl

/-- The stretch at `420`. -/
def p26 : List Byte := [
  0xc1, 0xe9, 0x1e, 0x8d, 0x71, 0xfc, 0xb9, 0x1e, 0x00, 0x00, 0x00]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 30)] 3) := by dec_rfl
theorem p26_3 : ∀ feat, Dec feat p26 3 (FV7z.mk .lea 32 [gr 32 6, .mem (mg (some 1) none 1 18446744073709551612 0)] 3) := by dec_rfl
theorem p26_6 : ∀ feat, Dec feat p26 6 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 30)] 5) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.shr 1 (.i 30),
  Op.lea 32 6 (some 1) none 1 18446744073709551612,
  Op.mov 32 1 (.i 30)]

theorem b26 (prof : Profile) : Blk prof p26 0 11 o26 :=
  .cons (p26_0 _) (OpI.shr (.i 30)) (by decide) <|
  .cons (p26_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p26_6 _) (OpI.mov (.i 30) (.inl rfl)) (by decide) <|
  .nil 11

def j21 : List Byte := [0xe9, 0xd9, 0xfe, 0xff, 0xff]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk .jmp 64 [.rel 18446744073709551321] 5) := by dec_rfl

/-- The stretch at `440`. -/
def p27 : List Byte := [
  0xb9, 0xbd, 0xff, 0xff, 0xff, 0xbe, 0xbf, 0xff, 0xff, 0xff, 0x41, 0xba, 0xef, 0xff, 0xff, 0xff]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 4294967229)] 5) := by dec_rfl
theorem p27_5 : ∀ feat, Dec feat p27 5 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 4294967231)] 5) := by dec_rfl
theorem p27_10 : ∀ feat, Dec feat p27 10 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 4294967279)] 6) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.mov 32 1 (.i 4294967229),
  Op.mov 32 6 (.i 4294967231),
  Op.mov 32 10 (.i 4294967279)]

theorem b27 (prof : Profile) : Blk prof p27 0 16 o27 :=
  .cons (p27_0 _) (OpI.mov (.i 4294967229) (.inl rfl)) (by decide) <|
  .cons (p27_5 _) (OpI.mov (.i 4294967231) (.inl rfl)) (by decide) <|
  .cons (p27_10 _) (OpI.mov (.i 4294967279) (.inl rfl)) (by decide) <|
  .nil 16

def j22 : List Byte := [0xe9, 0x7b, 0xff, 0xff, 0xff]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk .jmp 64 [.rel 18446744073709551483] 5) := by dec_rfl

/-- The stretch at `464`. -/
def p28 : List Byte := [
  0xb9, 0x12, 0x00, 0x00, 0x00, 0xbe, 0xf0, 0xff, 0xff, 0xff, 0x41, 0xba, 0xfd, 0xff, 0x00, 0x00]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 18)] 5) := by dec_rfl
theorem p28_5 : ∀ feat, Dec feat p28 5 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 4294967280)] 5) := by dec_rfl
theorem p28_10 : ∀ feat, Dec feat p28 10 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 65533)] 6) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.mov 32 1 (.i 18),
  Op.mov 32 6 (.i 4294967280),
  Op.mov 32 10 (.i 65533)]

theorem b28 (prof : Profile) : Blk prof p28 0 16 o28 :=
  .cons (p28_0 _) (OpI.mov (.i 18) (.inl rfl)) (by decide) <|
  .cons (p28_5 _) (OpI.mov (.i 4294967280) (.inl rfl)) (by decide) <|
  .cons (p28_10 _) (OpI.mov (.i 65533) (.inl rfl)) (by decide) <|
  .nil 16

def j23 : List Byte := [0xe9, 0xa8, 0xfe, 0xff, 0xff]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk .jmp 64 [.rel 18446744073709551272] 5) := by dec_rfl

/-- The stretch at `488`. -/
def p29 : List Byte := [
  0x81, 0xe9, 0x00, 0xd8, 0x00, 0x00, 0x41, 0x81, 0xea, 0x00, 0xdc, 0x00, 0x00, 0x48, 0x83, 0xc6,
  0x08, 0x48, 0x83, 0xc0, 0x04, 0xc1, 0xe1, 0x0a, 0x44, 0x09, 0xd1, 0x81, 0xc1, 0x00, 0x00, 0x01,
  0x00, 0x89, 0xcf, 0xc1, 0xef, 0x12, 0x83, 0xef, 0x10, 0x40, 0x88, 0x78, 0xfc, 0x89, 0xcf, 0xc1,
  0xef, 0x0c, 0x83, 0xe7, 0x3f, 0x83, 0xc7, 0x80, 0x40, 0x88, 0x78, 0xfd, 0x89, 0xcf, 0x83, 0xe1,
  0x3f, 0xc1, 0xef, 0x06, 0x83, 0xc1, 0x80, 0x83, 0xe7, 0x3f, 0x88, 0x48, 0xff, 0x83, 0xc7, 0x80,
  0x40, 0x88, 0x78, 0xfe]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.i 55296)] 6) := by dec_rfl
theorem p29_6 : ∀ feat, Dec feat p29 6 (FV7z.mk .sub 32 [gr 32 10, Src.opd 32 (.i 56320)] 7) := by dec_rfl
theorem p29_13 : ∀ feat, Dec feat p29 13 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p29_17 : ∀ feat, Dec feat p29 17 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 4)] 4) := by dec_rfl
theorem p29_21 : ∀ feat, Dec feat p29 21 (FV7z.mk .shl 32 [gr 32 1, Src.opd 8 (.i 10)] 3) := by dec_rfl
theorem p29_24 : ∀ feat, Dec feat p29 24 (FV7z.mk .or 32 [gr 32 1, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p29_27 : ∀ feat, Dec feat p29 27 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 65536)] 6) := by dec_rfl
theorem p29_33 : ∀ feat, Dec feat p29 33 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p29_35 : ∀ feat, Dec feat p29 35 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 18)] 3) := by dec_rfl
theorem p29_38 : ∀ feat, Dec feat p29 38 (FV7z.mk .sub 32 [gr 32 7, Src.opd 32 (.i 16)] 3) := by dec_rfl
theorem p29_41 : ∀ feat, Dec feat p29 41 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551612 8), gr 8 7] 4) := by dec_rfl
theorem p29_45 : ∀ feat, Dec feat p29 45 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p29_47 : ∀ feat, Dec feat p29 47 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 12)] 3) := by dec_rfl
theorem p29_50 : ∀ feat, Dec feat p29 50 (FV7z.mk .and 32 [gr 32 7, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p29_53 : ∀ feat, Dec feat p29 53 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p29_56 : ∀ feat, Dec feat p29 56 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551613 8), gr 8 7] 4) := by dec_rfl
theorem p29_60 : ∀ feat, Dec feat p29 60 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p29_62 : ∀ feat, Dec feat p29 62 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p29_65 : ∀ feat, Dec feat p29 65 (FV7z.mk .shr 32 [gr 32 7, Src.opd 8 (.i 6)] 3) := by dec_rfl
theorem p29_68 : ∀ feat, Dec feat p29 68 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p29_71 : ∀ feat, Dec feat p29 71 (FV7z.mk .and 32 [gr 32 7, Src.opd 32 (.i 63)] 3) := by dec_rfl
theorem p29_74 : ∀ feat, Dec feat p29 74 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551615 8), gr 8 1] 3) := by dec_rfl
theorem p29_77 : ∀ feat, Dec feat p29 77 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 4294967168)] 3) := by dec_rfl
theorem p29_80 : ∀ feat, Dec feat p29 80 (FV7z.mk .mov 8 [.mem (mg (some 0) none 1 18446744073709551614 8), gr 8 7] 4) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.sub 32 1 (.i 55296),
  Op.sub 32 10 (.i 56320),
  Op.add 64 6 (.i 8),
  Op.add 64 0 (.i 4),
  Op.shl 1 (.i 10),
  Op.or 32 1 (.r 10),
  Op.add 32 1 (.i 65536),
  Op.mov 32 7 (.r 1),
  Op.shr 7 (.i 18),
  Op.sub 32 7 (.i 16),
  Op.st 8 (some 0) none 1 18446744073709551612 7,
  Op.mov 32 7 (.r 1),
  Op.shr 7 (.i 12),
  Op.and 32 7 (.i 63),
  Op.add 32 7 (.i 4294967168),
  Op.st 8 (some 0) none 1 18446744073709551613 7,
  Op.mov 32 7 (.r 1),
  Op.and 32 1 (.i 63),
  Op.shr 7 (.i 6),
  Op.add 32 1 (.i 4294967168),
  Op.and 32 7 (.i 63),
  Op.st 8 (some 0) none 1 18446744073709551615 1,
  Op.add 32 7 (.i 4294967168),
  Op.st 8 (some 0) none 1 18446744073709551614 7]

theorem b29 (prof : Profile) : Blk prof p29 0 84 o29 :=
  .cons (p29_0 _) (OpI.sub (.i 55296) (.inl rfl)) (by decide) <|
  .cons (p29_6 _) (OpI.sub (.i 56320) (.inl rfl)) (by decide) <|
  .cons (p29_13 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p29_17 _) (OpI.add (.i 4) (.inr rfl)) (by decide) <|
  .cons (p29_21 _) (OpI.shl (.i 10)) (by decide) <|
  .cons (p29_24 _) (OpI.or (.r 10) (.inl rfl)) (by decide) <|
  .cons (p29_27 _) (OpI.add (.i 65536) (.inl rfl)) (by decide) <|
  .cons (p29_33 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p29_35 _) (OpI.shr (.i 18)) (by decide) <|
  .cons (p29_38 _) (OpI.sub (.i 16) (.inl rfl)) (by decide) <|
  .cons (p29_41 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p29_45 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p29_47 _) (OpI.shr (.i 12)) (by decide) <|
  .cons (p29_50 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p29_53 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p29_56 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p29_60 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p29_62 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p29_65 _) (OpI.shr (.i 6)) (by decide) <|
  .cons (p29_68 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p29_71 _) (OpI.and (.i 63) (.inl rfl)) (by decide) <|
  .cons (p29_74 _) (OpI.st (.inl rfl)) (by decide) <|
  .cons (p29_77 _) (OpI.add (.i 4294967168) (.inl rfl)) (by decide) <|
  .cons (p29_80 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 84

def j24 : List Byte := [0xe9, 0x77, 0xfe, 0xff, 0xff]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk .jmp 64 [.rel 18446744073709551223] 5) := by dec_rfl

end FV7z.U8w
