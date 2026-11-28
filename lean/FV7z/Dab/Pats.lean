import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps19
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_IO_doallocbuf` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 10) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dab
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0x7f, 0x38, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 56 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 64 (some 7) none 1 56 0]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi64) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x05]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p1 : List Byte := [
  0x41, 0x54, 0x55, 0x53, 0x8b, 0x07, 0x48, 0x89, 0xfb, 0xa8, 0x02]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 0 32)] 2) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.ld 32 0 (some 7) none 1 0,
  Op.mov 64 3 (.r 7),
  Op.test 8 0 (.i 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 11 o1 :=
  .cons (p1_0 _) (OpI.push) (by decide) <|
  .cons (p1_2 _) (OpI.push) (by decide) <|
  .cons (p1_3 _) (OpI.push) (by decide) <|
  .cons (p1_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 11

def j1 : List Byte := [0x74, 0x0a]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `29`. -/
def p2 : List Byte := [
  0x8b, 0x97, 0xc0, 0x00, 0x00, 0x00, 0x85, 0xd2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 192 32)] 6) := by dec_rfl
theorem p2_6 : ∀ feat, Dec feat p2 6 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 32 2 (some 7) none 1 192,
  Op.test 32 2 (.r 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 8 o2 :=
  .cons (p2_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p2_6 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 8

def j2 : List Byte := [0x7e, 0x69]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 14) 64 [.rel 105] 2) := by dec_rfl

/-- The stretch at `39`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0xab, 0xd8, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc2, 0xa0, 0x3d, 0x79, 0x00, 0x48, 0xc7,
  0xc0, 0xc8, 0x45, 0x79, 0x00, 0x48, 0x89, 0xe9, 0x48, 0x29, 0xd0, 0x48, 0x29, 0xd1, 0x48, 0x39,
  0xc8]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 5, .mem (mg (some 3) none 1 216 64)] 7) := by dec_rfl
theorem p3_7 : ∀ feat, Dec feat p3 7 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 7945632)] 7) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7947720)] 7) := by dec_rfl
theorem p3_21 : ∀ feat, Dec feat p3 21 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p3_24 : ∀ feat, Dec feat p3 24 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p3_27 : ∀ feat, Dec feat p3 27 (FV7z.mk .sub 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p3_30 : ∀ feat, Dec feat p3 30 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 5 (some 3) none 1 216,
  Op.mov 64 2 (.i 7945632),
  Op.mov 64 0 (.i 7947720),
  Op.mov 64 1 (.r 5),
  Op.sub 64 0 (.r 2),
  Op.sub 64 1 (.r 2),
  Op.cmp 64 0 (.r 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 33 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p3_7 _) (OpI.mov (.i 7945632) (.inr rfl)) (by decide) <|
  .cons (p3_14 _) (OpI.mov (.i 7947720) (.inr rfl)) (by decide) <|
  .cons (p3_21 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p3_24 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p3_27 _) (OpI.sub (.r 2) (.inr rfl)) (by decide) <|
  .cons (p3_30 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 33

def j3 : List Byte := [0x76, 0x66]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 6) 64 [.rel 102] 2) := by dec_rfl

/-- The stretch at `74`. -/
def p4 : List Byte := [
  0x48, 0x89, 0xdf]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 7 (.r 3)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `80`. -/
def p5 : List Byte := [
  0x83, 0xf8, 0xff]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmp 32 0 (.i 4294967295)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.cmp (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x75, 0x34]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 52] 2) := by dec_rfl

/-- The stretch at `85`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x7b, 0x38, 0x8b, 0x03, 0x48, 0x8d, 0xab, 0x84, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0xa3,
  0x83, 0x00, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 56 64)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 0 32)] 2) := by dec_rfl
theorem p6_6 : ∀ feat, Dec feat p6 6 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 3) none 1 132 0)] 7) := by dec_rfl
theorem p6_13 : ∀ feat, Dec feat p6 13 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 3) none 1 131 0)] 7) := by dec_rfl
theorem p6_20 : ∀ feat, Dec feat p6 20 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 64 7 (some 3) none 1 56,
  Op.ld 32 0 (some 3) none 1 0,
  Op.lea 64 5 (some 3) none 1 132,
  Op.lea 64 12 (some 3) none 1 131,
  Op.test 64 7 (.r 7)]

theorem b6 (prof : Profile) : Blk prof p6 0 23 o6 :=
  .cons (p6_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p6_6 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_20 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 23

def j5 : List Byte := [0x74, 0x04]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `110`. -/
def p7 : List Byte := [
  0xa8, 0x01]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 8 0 (.i 1)]

theorem b7 (prof : Profile) : Blk prof p7 0 2 o7 :=
  .cons (p7_0 _) (OpI.test8 (.i 1)) (by decide) <|
  .nil 2

def j6 : List Byte := [0x74, 0x2e]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 4) 64 [.rel 46] 2) := by dec_rfl

/-- The stretch at `114`. -/
def p8 : List Byte := [
  0x83, 0xc8, 0x01, 0x66, 0x49, 0x0f, 0x6e, 0xc4, 0x66, 0x48, 0x0f, 0x6e, 0xcd, 0x89, 0x03, 0x66,
  0x0f, 0x6c, 0xc1, 0x0f, 0x11, 0x43, 0x38]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .or 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk (.sse (SseMn.movq)) 64 [.xmm 0, gr 64 12] 5) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk (.sse (SseMn.movq)) 64 [.xmm 1, gr 64 5] 5) := by dec_rfl
theorem p8_13 : ∀ feat, Dec feat p8 13 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p8_15 : ∀ feat, Dec feat p8 15 (FV7z.mk (.sse (SseMn.punpcklqdq)) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem p8_19 : ∀ feat, Dec feat p8 19 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 3) none 1 56 128), .xmm 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.or 32 0 (.i 1),
  Op.vld 0 fun _ => 0,
  Op.vld 0 fun _ => 0,
  Op.st 32 (some 3) none 1 0 0,
  Op.vld 0 fun _ => 0,
  Op.vs 16 (some 3) none 1 56]

theorem b8 (prof : Profile) : Blk prof p8 0 23 o8 :=
  .cons (p8_0 _) (OpI.or (.i 1) (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.vz_movq_xr) (by decide) <|
  .cons (p8_8 _) (OpI.vz_movq_xr) (by decide) <|
  .cons (p8_13 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p8_15 _) (OpI.vz_punpcklqdq) (by decide) <|
  .cons (p8_19 _) (OpI.vs_movups) (by decide) <|
  .nil 23

/-- The stretch at `137`. -/
def p9 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p9_1 : ∀ feat, Dec feat p9 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p9_2 : ∀ feat, Dec feat p9 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b9 (prof : Profile) : Blk prof p9 0 4 o9 :=
  .cons (p9_0 _) (OpI.pop) (by decide) <|
  .cons (p9_1 _) (OpI.pop) (by decide) <|
  .cons (p9_2 _) (OpI.pop) (by decide) <|
  .nil 4

/-- The stretch at `144`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0xaf, 0x84, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0xa7, 0x83, 0x00, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 7) none 1 132 0)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 7) none 1 131 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.lea 64 5 (some 7) none 1 132,
  Op.lea 64 12 (some 7) none 1 131]

theorem b10 (prof : Profile) : Blk prof p10 0 14 o10 :=
  .cons (p10_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 14

def j7 : List Byte := [0xeb, 0xd2]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551570] 2) := by dec_rfl

/-- The stretch at `165`. -/
def p11 : List Byte := [
  0x8b, 0x03]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 3) none 1 0 32)] 2) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 32 0 (some 3) none 1 0]

theorem b11 (prof : Profile) : Blk prof p11 0 2 o11 :=
  .cons (p11_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 2

def j8 : List Byte := [0xeb, 0xc9]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk .jmp 64 [.rel 18446744073709551561] 2) := by dec_rfl

def j9 : List Byte := [0xeb, 0x93]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk .jmp 64 [.rel 18446744073709551507] 2) := by dec_rfl

end FV7z.Dab
