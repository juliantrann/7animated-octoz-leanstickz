import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `NWindows::NFile::NName::ResolveDotsFolders` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 31 of them) and each distinct jump (`j*`, 21) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rdf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x8b, 0x37, 0x8b, 0x06, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) none 1 0 32)] 2) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.ld 64 6 (some 7) none 1 0,
  Op.ld 32 0 (some 6) none 1 0,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) : Blk prof p0 0 7 o0 :=
  .cons (p0_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_5 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x0f, 0x84, 0x28, 0x01, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 296] 6) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x41, 0x54, 0x49, 0x89, 0xfc, 0x55, 0x31, 0xed, 0x53, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00,
  0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .nop 16 [.mem (mg (some 0) (some 0) 1 0 16)] 10) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 12,
  Op.mov 64 12 (.r 7),
  Op.push 5,
  Op.xor 32 5 (.r 5),
  Op.push 3,
  Op.nop]

theorem b1 (prof : Profile) : Blk prof p1 0 19 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_5 _) (OpI.push) (by decide) <|
  .cons (p1_6 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .cons (p1_8 _) (OpI.push) (by decide) <|
  .cons (p1_9 _) (OpI.nop) (by decide) <|
  .nil 19

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x8d, 0x4d, 0x01, 0x48, 0x89, 0xca, 0x48, 0x8d, 0x1c, 0x8d, 0x00, 0x00, 0x00, 0x00, 0x83, 0xf8,
  0x2e]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 5) none 1 1 0)] 3) := by dec_rfl
theorem p2_3 : ∀ feat, Dec feat p2 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .lea 64 [gr 64 3, .mem (mg none (some 1) 4 0 0)] 8) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 46)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lea 32 1 (some 5) none 1 1,
  Op.mov 64 2 (.r 1),
  Op.lea 64 3 none (some 1) 4 0,
  Op.cmp 32 0 (.i 46)]

theorem b2 (prof : Profile) : Blk prof p2 0 17 o2 :=
  .cons (p2_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p2_3 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.cmp (.i 46) (.inl rfl)) (by decide) <|
  .nil 17

def j1 : List Byte := [0x74, 0x1d]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `51`. -/
def p3 : List Byte := [
  0x89, 0xd5]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 5 (.r 2)]

theorem b3 (prof : Profile) : Blk prof p3 0 2 o3 :=
  .cons (p3_0 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `53`. -/
def p4 : List Byte := [
  0x8b, 0x04, 0x1e, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) (some 3) 1 0 32)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 32 0 (some 6) (some 3) 1 0,
  Op.test 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 5 o4 :=
  .cons (p4_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j2 : List Byte := [0x75, 0xe4]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551588] 2) := by dec_rfl

/-- The stretch at `60`. -/
def p5 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 0 (.i 1)]

theorem b5 (prof : Profile) : Blk prof p5 0 5 o5 :=
  .cons (p5_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `65`. -/
def p6 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p6_1 : ∀ feat, Dec feat p6 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p6_2 : ∀ feat, Dec feat p6 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b6 (prof : Profile) : Blk prof p6 0 4 o6 :=
  .cons (p6_0 _) (OpI.pop) (by decide) <|
  .cons (p6_1 _) (OpI.pop) (by decide) <|
  .cons (p6_2 _) (OpI.pop) (by decide) <|
  .nil 4

/-- The stretch at `80`. -/
def p7 : List Byte := [
  0x85, 0xed]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 32 5 (.r 5)]

theorem b7 (prof : Profile) : Blk prof p7 0 2 o7 :=
  .cons (p7_0 _) (OpI.test (.r 5) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0x09]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `84`. -/
def p8 : List Byte := [
  0x8d, 0x45, 0xff, 0x83, 0x3c, 0x86, 0x2f]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 5) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .cmp 32 [.mem (mg (some 6) (some 0) 4 0 32), .imm 32 47] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.lea 32 0 (some 5) none 1 18446744073709551615,
  Op.cmpmi 32 (some 6) (some 0) 4 0 47]

theorem b8 (prof : Profile) : Blk prof p8 0 7 o8 :=
  .cons (p8_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 7

def j4 : List Byte := [0x75, 0xd6]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551574] 2) := by dec_rfl

/-- The stretch at `93`. -/
def p9 : List Byte := [
  0x8b, 0x04, 0x8e, 0x83, 0xf8, 0x2e]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 6) (some 1) 4 0 32)] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 46)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 32 0 (some 6) (some 1) 4 0,
  Op.cmp 32 0 (.i 46)]

theorem b9 (prof : Profile) : Blk prof p9 0 6 o9 :=
  .cons (p9_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p9_3 _) (OpI.cmp (.i 46) (.inl rfl)) (by decide) <|
  .nil 6

def j5 : List Byte := [0x74, 0x33]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 51] 2) := by dec_rfl

/-- The stretch at `101`. -/
def p10 : List Byte := [
  0x83, 0xf8, 0x2f]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 47)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.cmp 32 0 (.i 47)]

theorem b10 (prof : Profile) : Blk prof p10 0 3 o10 :=
  .cons (p10_0 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .nil 3

def j6 : List Byte := [0x74, 0x04]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `106`. -/
def p11 : List Byte := [
  0x85, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b11 (prof : Profile) : Blk prof p11 0 2 o11 :=
  .cons (p11_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j7 : List Byte := [0x75, 0xc5]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551557] 2) := by dec_rfl

def j8 : List Byte := [0x74, 0x5e]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 4) 64 [.rel 94] 2) := by dec_rfl

/-- The stretch at `114`. -/
def p12 : List Byte := [
  0x8d, 0x5d, 0xff, 0xba, 0x02, 0x00, 0x00, 0x00, 0x48, 0x89, 0xdd, 0x48, 0xc1, 0xe3, 0x02]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 32 [gr 32 3, .mem (mg (some 5) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p12_3 : ∀ feat, Dec feat p12 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 2)] 5) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p12_11 : ∀ feat, Dec feat p12 11 (FV7z.mk .shl 64 [gr 64 3, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.lea 32 3 (some 5) none 1 18446744073709551615,
  Op.mov 32 2 (.i 2),
  Op.mov 64 5 (.r 3),
  Op.shl64 3 (.i 2)]

theorem b12 (prof : Profile) : Blk prof p12 0 15 o12 :=
  .cons (p12_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p12_3 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .cons (p12_8 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .cons (p12_11 _) (OpI.shl64 (.i 2)) (by decide) <|
  .nil 15

/-- The stretch at `129`. -/
def p13 : List Byte := [
  0x89, 0xee, 0x4c, 0x89, 0xe7]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p13_2 : ∀ feat, Dec feat p13 2 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 32 6 (.r 5),
  Op.mov 64 7 (.r 12)]

theorem b13 (prof : Profile) : Blk prof p13 0 5 o13 :=
  .cons (p13_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p13_2 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `139`. -/
def p14 : List Byte := [
  0x49, 0x8b, 0x34, 0x24]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.ld 64 6 (some 12) none 1 0]

theorem b14 (prof : Profile) : Blk prof p14 0 4 o14 :=
  .cons (p14_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

def j9 : List Byte := [0xeb, 0xa4]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551524] 2) := by dec_rfl

/-- The stretch at `152`. -/
def p15 : List Byte := [
  0x8d, 0x45, 0x02, 0x8b, 0x0c, 0x86, 0x49, 0x89, 0xc0, 0x83, 0xf9, 0x2f]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 5) none 1 2 0)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .mov 32 [gr 32 1, .mem (mg (some 6) (some 0) 4 0 32)] 3) := by dec_rfl
theorem p15_6 : ∀ feat, Dec feat p15 6 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p15_9 : ∀ feat, Dec feat p15 9 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 47)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.lea 32 0 (some 5) none 1 2,
  Op.ld 32 1 (some 6) (some 0) 4 0,
  Op.mov 64 8 (.r 0),
  Op.cmp 32 1 (.i 47)]

theorem b15 (prof : Profile) : Blk prof p15 0 12 o15 :=
  .cons (p15_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p15_6 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p15_9 _) (OpI.cmp (.i 47) (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `166`. -/
def p16 : List Byte := [
  0x85, 0xc9]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.test 32 1 (.r 1)]

theorem b16 (prof : Profile) : Blk prof p16 0 2 o16 :=
  .cons (p16_0 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 2

def j10 : List Byte := [0x75, 0x89]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551497] 2) := by dec_rfl

/-- The stretch at `170`. -/
def p17 : List Byte := [
  0x8d, 0x55, 0xfe, 0x81, 0xfa, 0xfd, 0xff, 0xff, 0x7f]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .lea 32 [gr 32 2, .mem (mg (some 5) none 1 18446744073709551614 0)] 3) := by dec_rfl
theorem p17_3 : ∀ feat, Dec feat p17 3 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 2147483645)] 6) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.lea 32 2 (some 5) none 1 18446744073709551614,
  Op.cmp 32 2 (.i 2147483645)]

theorem b17 (prof : Profile) : Blk prof p17 0 9 o17 :=
  .cons (p17_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p17_3 _) (OpI.cmp (.i 2147483645) (.inl rfl)) (by decide) <|
  .nil 9

def j11 : List Byte := [0x77, 0x13]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 7) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `181`. -/
def p18 : List Byte := [
  0x48, 0x63, 0xd2]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .movsxd 64 [gr 64 2, gr 32 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.sxr 2 2]

theorem b18 (prof : Profile) : Blk prof p18 0 3 o18 :=
  .cons (p18_0 _) (OpI.sxr) (by decide) <|
  .nil 3

/-- The stretch at `184`. -/
def p19 : List Byte := [
  0x83, 0x3c, 0x96, 0x2f, 0x89, 0xd0]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 32 [.mem (mg (some 6) (some 2) 4 0 32), .imm 32 47] 4) := by dec_rfl
theorem p19_4 : ∀ feat, Dec feat p19 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmpmi 32 (some 6) (some 2) 4 0 47,
  Op.mov 32 0 (.r 2)]

theorem b19 (prof : Profile) : Blk prof p19 0 6 o19 :=
  .cons (p19_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .cons (p19_4 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

def j12 : List Byte := [0x75, 0x20]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 5) 64 [.rel 32] 2) := by dec_rfl

/-- The stretch at `192`. -/
def p20 : List Byte := [
  0x48, 0x83, 0xea, 0x01, 0x85, 0xd2]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .sub 64 [gr 64 2, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.sub 64 2 (.i 1),
  Op.test 32 2 (.r 2)]

theorem b20 (prof : Profile) : Blk prof p20 0 6 o20 :=
  .cons (p20_0 _) (OpI.sub (.i 1) (.inr rfl)) (by decide) <|
  .cons (p20_4 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

def j13 : List Byte := [0x79, 0xf0]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551600] 2) := by dec_rfl

/-- The stretch at `200`. -/
def p21 : List Byte := [
  0x31, 0xc0]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b21 (prof : Profile) : Blk prof p21 0 2 o21 :=
  .cons (p21_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j14 : List Byte := [0xe9, 0x72, 0xff, 0xff, 0xff]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk .jmp 64 [.rel 18446744073709551474] 5) := by dec_rfl

/-- The stretch at `208`. -/
def p22 : List Byte := [
  0x31, 0xdb, 0x83, 0xf8, 0x01, 0x19, 0xd2, 0x83, 0xc2, 0x02]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p22_2 : ∀ feat, Dec feat p22 2 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p22_5 : ∀ feat, Dec feat p22 5 (FV7z.mk .sbb 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p22_7 : ∀ feat, Dec feat p22 7 (FV7z.mk .add 32 [gr 32 2, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.xor 32 3 (.r 3),
  Op.cmp 32 0 (.i 1),
  Op.sbb 32 2 (.r 2),
  Op.add 32 2 (.i 2)]

theorem b22 (prof : Profile) : Blk prof p22 0 10 o22 :=
  .cons (p22_0 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p22_2 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .cons (p22_5 _) (OpI.sbb (.r 2) (.inl rfl)) (by decide) <|
  .cons (p22_7 _) (OpI.add (.i 2) (.inl rfl)) (by decide) <|
  .nil 10

def j15 : List Byte := [0xeb, 0xa5]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk .jmp 64 [.rel 18446744073709551525] 2) := by dec_rfl

/-- The stretch at `224`. -/
def p23 : List Byte := [
  0x83, 0xe8, 0x01, 0x48, 0x98]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p23_3 : ∀ feat, Dec feat p23 3 (FV7z.mk .cbw 64 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.sub 32 0 (.i 1),
  Op.cdqe]

theorem b23 (prof : Profile) : Blk prof p23 0 5 o23 :=
  .cons (p23_0 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p23_3 _) (OpI.cdqe) (by decide) <|
  .nil 5

def j16 : List Byte := [0xeb, 0x16]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk .jmp 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `240`. -/
def p24 : List Byte := [
  0x83, 0x3c, 0x86, 0x2f, 0x48, 0x8d, 0x50, 0xff]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .cmp 32 [.mem (mg (some 6) (some 0) 4 0 32), .imm 32 47] 4) := by dec_rfl
theorem p24_4 : ∀ feat, Dec feat p24 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.cmpmi 32 (some 6) (some 0) 4 0 47,
  Op.lea 64 2 (some 0) none 1 18446744073709551615]

theorem b24 (prof : Profile) : Blk prof p24 0 8 o24 :=
  .cons (p24_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .cons (p24_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 8

def j17 : List Byte := [0x74, 0x16]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk (.jcc 4) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `250`. -/
def p25 : List Byte := [
  0x48, 0x89, 0xd0]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.mov 64 0 (.r 2)]

theorem b25 (prof : Profile) : Blk prof p25 0 3 o25 :=
  .cons (p25_0 _) (OpI.mov (.r 2) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `253`. -/
def p26 : List Byte := [
  0x83, 0xf8, 0xff]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.cmp 32 0 (.i 4294967295)]

theorem b26 (prof : Profile) : Blk prof p26 0 3 o26 :=
  .cons (p26_0 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 3

def j18 : List Byte := [0x75, 0xee]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `262`. -/
def p27 : List Byte := [
  0x44, 0x8d, 0x45, 0x03]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .lea 32 [gr 32 8, .mem (mg (some 5) none 1 3 0)] 4) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.lea 32 8 (some 5) none 1 3]

theorem b27 (prof : Profile) : Blk prof p27 0 4 o27 :=
  .cons (p27_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `266`. -/
def p28 : List Byte := [
  0x31, 0xdb, 0x31, 0xed]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .xor 32 [gr 32 3, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p28_2 : ∀ feat, Dec feat p28 2 (FV7z.mk .xor 32 [gr 32 5, Src.opd 32 (.r 5)] 2) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.xor 32 3 (.r 3),
  Op.xor 32 5 (.r 5)]

theorem b28 (prof : Profile) : Blk prof p28 0 4 o28 :=
  .cons (p28_0 _) (OpI.xor (.r 3) (.inl rfl)) (by decide) <|
  .cons (p28_2 _) (OpI.xor (.r 5) (.inl rfl)) (by decide) <|
  .nil 4

def j19 : List Byte := [0xeb, 0x0f]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk .jmp 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `272`. -/
def p29 : List Byte := [
  0x89, 0xc5, 0x41, 0x29, 0xc0, 0x89, 0xc0, 0x48, 0x8d, 0x1c, 0x85, 0x00, 0x00, 0x00, 0x00]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .mov 32 [gr 32 5, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p29_2 : ∀ feat, Dec feat p29 2 (FV7z.mk .sub 32 [gr 32 8, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p29_5 : ∀ feat, Dec feat p29 5 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p29_7 : ∀ feat, Dec feat p29 7 (FV7z.mk .lea 64 [gr 64 3, .mem (mg none (some 0) 4 0 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.mov 32 5 (.r 0),
  Op.sub 32 8 (.r 0),
  Op.mov 32 0 (.r 0),
  Op.lea 64 3 none (some 0) 4 0]

theorem b29 (prof : Profile) : Blk prof p29 0 15 o29 :=
  .cons (p29_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p29_2 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (p29_5 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p29_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 15

/-- The stretch at `287`. -/
def p30 : List Byte := [
  0x89, 0xee, 0x44, 0x89, 0xc2, 0x4c, 0x89, 0xe7]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 5)] 2) := by dec_rfl
theorem p30_2 : ∀ feat, Dec feat p30 2 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p30_5 : ∀ feat, Dec feat p30 5 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.mov 32 6 (.r 5),
  Op.mov 32 2 (.r 8),
  Op.mov 64 7 (.r 12)]

theorem b30 (prof : Profile) : Blk prof p30 0 8 o30 :=
  .cons (p30_0 _) (OpI.mov (.r 5) (.inl rfl)) (by decide) <|
  .cons (p30_2 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p30_5 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 8

def j20 : List Byte := [0xe9, 0x00, 0xff, 0xff, 0xff]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk .jmp 64 [.rel 18446744073709551360] 5) := by dec_rfl

end FV7z.Rdf
