import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps18
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CInFileStream::Seek` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Isk
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x55, 0x53, 0x83, 0xfa, 0x02]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.cmp 32 2 (.i 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.push) (by decide) <|
  .cons (p0_7 _) (OpI.push) (by decide) <|
  .cons (p0_8 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x77, 0x5b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 91] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x48, 0x8d, 0x6f, 0x2c, 0x48, 0x89, 0xcb, 0x48, 0x89, 0xef]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 7) none 1 44 0)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p1_7 : ∀ feat, Dec feat p1 7 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 64 5 (some 7) none 1 44,
  Op.mov 64 3 (.r 1),
  Op.mov 64 7 (.r 5)]

theorem b1 (prof : Profile) : Blk prof p1 0 10 o1 :=
  .cons (p1_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p1_7 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 10

/-- The stretch at `28`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xf8, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 64 0 (.i 18446744073709551615)]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmp (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x74, 0x16]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `34`. -/
def p3 : List Byte := [
  0x45, 0x31, 0xe4, 0x48, 0x85, 0xdb]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 12, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p3_3 : ∀ feat, Dec feat p3 3 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 12 (.r 12),
  Op.test 64 3 (.r 3)]

theorem b3 (prof : Profile) : Blk prof p3 0 6 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 12) (.inl rfl)) (by decide) <|
  .cons (p3_3 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 6

def j2 : List Byte := [0x74, 0x03]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 3] 2) := by dec_rfl

/-- The stretch at `42`. -/
def p4 : List Byte := [
  0x48, 0x89, 0x03]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 64 (some 3) none 1 0 0]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 3

/-- The stretch at `45`. -/
def p5 : List Byte := [
  0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p5_5 : ∀ feat, Dec feat p5 5 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b5 (prof : Profile) : Blk prof p5 0 7 o5 :=
  .cons (p5_0 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.pop) (by decide) <|
  .cons (p5_4 _) (OpI.pop) (by decide) <|
  .cons (p5_5 _) (OpI.pop) (by decide) <|
  .nil 7

/-- The stretch at `61`. -/
def p6 : List Byte := [
  0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x74, 0x2f]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `65`. -/
def p7 : List Byte := [
  0x44, 0x0f, 0xb7, 0xe0, 0x41, 0x81, 0xcc, 0x00, 0x00, 0x00, 0x88, 0x85, 0xc0, 0x44, 0x0f, 0x4e,
  0xe0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movzx 32 [gr 32 12, gr 16 0] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .or 32 [gr 32 12, Src.opd 32 (.i 2281701376)] 7) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_13 : ∀ feat, Dec feat p7 13 (FV7z.mk (.cmovcc 14) 32 [gr 32 12, gr 32 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.zxr16 12 0,
  Op.or 32 12 (.i 2281701376),
  Op.test 32 0 (.r 0),
  Op.cmov32 14 12 0]

theorem b7 (prof : Profile) : Blk prof p7 0 17 o7 :=
  .cons (p7_0 _) (OpI.zxr16) (by decide) <|
  .cons (p7_4 _) (OpI.or (.i 2281701376) (.inl rfl)) (by decide) <|
  .cons (p7_11 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .cons (p7_13 _) (OpI.cmov32) (by decide) <|
  .nil 17

/-- The stretch at `82`. -/
def p8 : List Byte := [
  0x48, 0x85, 0xdb]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 64 [gr 64 3, Src.opd 64 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 64 3 (.r 3)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.test (.r 3) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0xd6]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551574] 2) := by dec_rfl

/-- The stretch at `87`. -/
def p9 : List Byte := [
  0x48, 0x89, 0xef]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j5 : List Byte := [0xeb, 0xc9]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551561] 2) := by dec_rfl

/-- The stretch at `104`. -/
def p10 : List Byte := [
  0x41, 0xbc, 0x01, 0x00, 0x03, 0x80]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 2147680257)] 6) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 32 12 (.i 2147680257)]

theorem b10 (prof : Profile) : Blk prof p10 0 6 o10 :=
  .cons (p10_0 _) (OpI.mov (.i 2147680257) (.inl rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0xeb, 0xbd]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551549] 2) := by dec_rfl

/-- The stretch at `112`. -/
def p11 : List Byte := [
  0x41, 0xbc, 0x05, 0x40, 0x00, 0x80]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.i 2147500037)] 6) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 32 12 (.i 2147500037)]

theorem b11 (prof : Profile) : Blk prof p11 0 6 o11 :=
  .cons (p11_0 _) (OpI.mov (.i 2147500037) (.inl rfl)) (by decide) <|
  .nil 6

def j7 : List Byte := [0xeb, 0xda]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551578] 2) := by dec_rfl

end FV7z.Isk
