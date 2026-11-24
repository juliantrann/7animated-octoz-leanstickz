import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps15
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `csuTg 103` (PLAN.md M, ctor 103)

Each distinct stretch between labels and jumps (`p*`, 92 of them) and each distinct jump (`j*`, 65) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.C103
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `3504`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x55, 0x53, 0x48, 0x83,
  0xec, 0x08, 0x8b, 0x05, 0x40, 0x7c, 0x38, 0x00, 0x83, 0xf8, 0x01]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 3701824 32)] 6) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.sub 64 4 (.i 8),
  Op.lda 32 0 8014664,
  Op.cmp 32 0 (.i 1)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x41cef0 : Addr) 0 27 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_8 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_10 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_12 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_14 _) ((OpI.sub (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p0_18 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p0_24 _) ((OpI.cmp (.i 1) (.inl rfl)).at _) (by decide) <|
  .nil 27

def j0 : List Byte := [0x0f, 0x84, 0xd1, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 209] 6) := by dec_rfl

/-- The stretch at `3537`. -/
def p1 : List Byte := [
  0x83, 0xf8, 0x02]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmp 32 0 (.i 2)]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 3

def j1 : List Byte := [0x0f, 0x84, 0xe9, 0x01, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 489] 6) := by dec_rfl

/-- The stretch at `3546`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x05, 0x4f, 0x7c, 0x38, 0x00, 0x48, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 3701839 64)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.lda 64 0 8014704,
  Op.test 64 0 (.r 0)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x41cf1a : Addr) 0 10 o2 :=
  .cons (p2_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j2 : List Byte := [0x0f, 0x84, 0xaa, 0x00, 0x00, 0x00]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 170] 6) := by dec_rfl

/-- The stretch at `3562`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xcd, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .or 64 [gr 64 5, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.or 64 5 (.i 18446744073709551615)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.or (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `3566`. -/
def p4 : List Byte := [
  0x49, 0x89, 0xc4]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 12 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 3 o4 :=
  .cons (p4_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `3569`. -/
def p5 : List Byte := [
  0x4d, 0x85, 0xe4]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 64 12 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x7e, 0x2b]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 14) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `3574`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xe0, 0x4c, 0x89, 0x25, 0xc0, 0x63, 0x37, 0x00, 0x45, 0x30, 0xe4, 0x48, 0xd1, 0xf8,
  0x4c, 0x89, 0x25, 0xc3, 0x63, 0x37, 0x00, 0x48, 0x89, 0x05, 0xb4, 0x63, 0x37, 0x00, 0x4c, 0x89,
  0xe0, 0x48, 0xd1, 0xf8, 0x48, 0x89, 0x05, 0xb7, 0x63, 0x37, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .mov 64 [.mem (mrip 3630016 64), gr 64 12] 7) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .xor 8 [gr 8 12, Src.opd 8 (.r 12)] 3) := by dec_rfl
theorem p6_13 : ∀ feat, Dec feat p6 13 (FV7z.mk .sar 64 [gr 64 0, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p6_16 : ∀ feat, Dec feat p6 16 (FV7z.mk .mov 64 [.mem (mrip 3630019 64), gr 64 12] 7) := by dec_rfl
theorem p6_23 : ∀ feat, Dec feat p6 23 (FV7z.mk .mov 64 [.mem (mrip 3630004 64), gr 64 0] 7) := by dec_rfl
theorem p6_30 : ∀ feat, Dec feat p6 30 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_33 : ∀ feat, Dec feat p6 33 (FV7z.mk .sar 64 [gr 64 0, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p6_36 : ∀ feat, Dec feat p6 36 (FV7z.mk .mov 64 [.mem (mrip 3630007 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 0 (.r 12),
  Op.sta 64 7942912 12,
  Op.xor8 12 (.r 12),
  Op.sar64 0 (.i 1),
  Op.sta 64 7942928 12,
  Op.sta 64 7942920 0,
  Op.mov 64 0 (.r 12),
  Op.sar64 0 (.i 1),
  Op.sta 64 7942936 0]

theorem b6 (prof : Profile) : BlkA prof p6 (0x41cf36 : Addr) 0 43 o6 :=
  .cons (p6_0 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p6_3 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p6_10 _) ((OpI.xor8 (.r 12)).at _) (by decide) <|
  .cons (p6_13 _) ((OpI.sar64 (.i 1)).at _) (by decide) <|
  .cons (p6_16 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p6_23 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p6_30 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p6_33 _) ((OpI.sar64 (.i 1)).at _) (by decide) <|
  .cons (p6_36 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 43

/-- The stretch at `3617`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x05, 0x10, 0x7c, 0x38, 0x00, 0x48, 0x85, 0xc0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 3701776 64)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.lda 64 0 8014712,
  Op.test 64 0 (.r 0)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x41cf61 : Addr) 0 10 o7 :=
  .cons (p7_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p7_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j4 : List Byte := [0x74, 0x03]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 3] 2) := by dec_rfl

/-- The stretch at `3629`. -/
def p8 : List Byte := [
  0x48, 0x89, 0xc5]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 5 (.r 0)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `3632`. -/
def p9 : List Byte := [
  0x48, 0x85, 0xed]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b9 (prof : Profile) : Blk prof p9 0 3 o9 :=
  .cons (p9_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `3637`. -/
def p10 : List Byte := [
  0x48, 0x89, 0xe8, 0x48, 0x89, 0x2d, 0x61, 0x63, 0x37, 0x00, 0x40, 0x30, 0xed, 0x48, 0xd1, 0xf8,
  0x48, 0x89, 0x2d, 0x64, 0x63, 0x37, 0x00, 0x48, 0x89, 0x05, 0x55, 0x63, 0x37, 0x00, 0x48, 0x89,
  0xe8, 0x48, 0xd1, 0xf8, 0x48, 0x89, 0x05, 0x58, 0x63, 0x37, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p10_3 : ∀ feat, Dec feat p10 3 (FV7z.mk .mov 64 [.mem (mrip 3629921 64), gr 64 5] 7) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .xor 8 [gr 8 5, Src.opd 8 (.r 5)] 3) := by dec_rfl
theorem p10_13 : ∀ feat, Dec feat p10 13 (FV7z.mk .sar 64 [gr 64 0, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p10_16 : ∀ feat, Dec feat p10 16 (FV7z.mk .mov 64 [.mem (mrip 3629924 64), gr 64 5] 7) := by dec_rfl
theorem p10_23 : ∀ feat, Dec feat p10 23 (FV7z.mk .mov 64 [.mem (mrip 3629909 64), gr 64 0] 7) := by dec_rfl
theorem p10_30 : ∀ feat, Dec feat p10 30 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p10_33 : ∀ feat, Dec feat p10 33 (FV7z.mk .sar 64 [gr 64 0, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem p10_36 : ∀ feat, Dec feat p10 36 (FV7z.mk .mov 64 [.mem (mrip 3629912 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 0 (.r 5),
  Op.sta 64 7942880 5,
  Op.xor8 5 (.r 5),
  Op.sar64 0 (.i 1),
  Op.sta 64 7942896 5,
  Op.sta 64 7942888 0,
  Op.mov 64 0 (.r 5),
  Op.sar64 0 (.i 1),
  Op.sta 64 7942904 0]

theorem b10 (prof : Profile) : BlkA prof p10 (0x41cf75 : Addr) 0 43 o10 :=
  .cons (p10_0 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p10_3 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p10_10 _) ((OpI.xor8 (.r 5)).at _) (by decide) <|
  .cons (p10_13 _) ((OpI.sar64 (.i 1)).at _) (by decide) <|
  .cons (p10_16 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p10_23 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p10_30 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p10_33 _) ((OpI.sar64 (.i 1)).at _) (by decide) <|
  .cons (p10_36 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 43

/-- The stretch at `3680`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x05, 0xd9, 0x7b, 0x38, 0x00, 0x48, 0x85, 0xc0]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 3701721 64)] 7) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.lda 64 0 8014720,
  Op.test 64 0 (.r 0)]

theorem b11 (prof : Profile) : BlkA prof p11 (0x41cfa0 : Addr) 0 10 o11 :=
  .cons (p11_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p11_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j5 : List Byte := [0x75, 0x12]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `3692`. -/
def p12 : List Byte := [
  0x48, 0x6b, 0x05, 0x3c, 0x63, 0x37, 0x00, 0x03, 0xb9, 0x04, 0x00, 0x00, 0x00, 0x48, 0x99]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .imul 64 [gr 64 0, .mem (mrip 3629884 64), .imm 64 3] 8) := by dec_rfl
theorem p12_8 : ∀ feat, Dec feat p12 8 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 4)] 5) := by dec_rfl
theorem p12_13 : ∀ feat, Dec feat p12 13 (FV7z.mk .cwd 64 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.imul3ma 0 7942896 3,
  Op.mov 32 1 (.i 4),
  Op.cqo]

theorem b12 (prof : Profile) : BlkA prof p12 (0x41cfac : Addr) 0 15 o12 :=
  .cons (p12_0 _) (OpIA.imul3_rip (by decide)) (by decide) <|
  .cons (p12_8 _) ((OpI.mov (.i 4) (.inl rfl)).at _) (by decide) <|
  .cons (p12_13 _) ((OpI.cqo).at _) (by decide) <|
  .nil 15

/-- The stretch at `3710`. -/
def p13 : List Byte := [
  0x48, 0x89, 0x05, 0x63, 0xb4, 0x38, 0x00, 0x48, 0x83, 0xc4, 0x08, 0x5b, 0x5d, 0x41, 0x5c, 0x41,
  0x5d, 0x41, 0x5e, 0x41, 0x5f]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mrip 3716195 64), gr 64 0] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p13_12 : ∀ feat, Dec feat p13 12 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p13_13 : ∀ feat, Dec feat p13 13 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p13_15 : ∀ feat, Dec feat p13 15 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p13_17 : ∀ feat, Dec feat p13 17 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p13_19 : ∀ feat, Dec feat p13 19 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sta 64 8029224 0,
  Op.add 64 4 (.i 8),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15]

theorem b13 (prof : Profile) : BlkA prof p13 (0x41cfbe : Addr) 0 21 o13 :=
  .cons (p13_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p13_7 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p13_11 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_12 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_13 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_15 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_17 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_19 _) ((OpI.pop).at _) (by decide) <|
  .nil 21

/-- The stretch at `3732`. -/
def p14 : List Byte := [
  0x48, 0x8b, 0x05, 0x9d, 0x7b, 0x38, 0x00, 0x48, 0x85, 0xc0]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 3701661 64)] 7) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.lda 64 0 8014712,
  Op.test 64 0 (.r 0)]

theorem b14 (prof : Profile) : BlkA prof p14 (0x41cfd4 : Addr) 0 10 o14 :=
  .cons (p14_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p14_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j6 : List Byte := [0x75, 0x8d]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551501] 2) := by dec_rfl

def j7 : List Byte := [0xeb, 0xbe]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551550] 2) := by dec_rfl

/-- The stretch at `3746`. -/
def p15 : List Byte := [
  0xbf, 0xbc, 0x00, 0x00, 0x00, 0x44, 0x8b, 0x2d, 0x5e, 0x7b, 0x38, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 188)] 5) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .mov 32 [gr 32 13, .mem (mrip 3701598 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 32 7 (.i 188),
  Op.lda 32 13 8014668]

theorem b15 (prof : Profile) : BlkA prof p15 (0x41cfe2 : Addr) 0 12 o15 :=
  .cons (p15_0 _) ((OpI.mov (.i 188) (.inl rfl)).at _) (by decide) <|
  .cons (p15_5 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `3763`. -/
def p16 : List Byte := [
  0xbf, 0xbf, 0x00, 0x00, 0x00, 0x49, 0x89, 0xc4]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 191)] 5) := by dec_rfl
theorem p16_5 : ∀ feat, Dec feat p16 5 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.mov 32 7 (.i 191),
  Op.mov 64 12 (.r 0)]

theorem b16 (prof : Profile) : Blk prof p16 0 8 o16 :=
  .cons (p16_0 _) (OpI.mov (.i 191) (.inl rfl)) (by decide) <|
  .cons (p16_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `3776`. -/
def p17 : List Byte := [
  0xbf, 0xc2, 0x00, 0x00, 0x00, 0x49, 0x89, 0xc6]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 194)] 5) := by dec_rfl
theorem p17_5 : ∀ feat, Dec feat p17 5 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.mov 32 7 (.i 194),
  Op.mov 64 14 (.r 0)]

theorem b17 (prof : Profile) : Blk prof p17 0 8 o17 :=
  .cons (p17_0 _) (OpI.mov (.i 194) (.inl rfl)) (by decide) <|
  .cons (p17_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `3789`. -/
def p18 : List Byte := [
  0x48, 0x89, 0xc5, 0x48, 0x85, 0xc0]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p18_3 : ∀ feat, Dec feat p18 3 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.mov 64 5 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b18 (prof : Profile) : Blk prof p18 0 6 o18 :=
  .cons (p18_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p18_3 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

def j8 : List Byte := [0x0f, 0x8e, 0x85, 0x00, 0x00, 0x00]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 14) 64 [.rel 133] 6) := by dec_rfl

/-- The stretch at `3801`. -/
def p19 : List Byte := [
  0x31, 0xff, 0x41, 0xbf, 0x03, 0x00, 0x00, 0x00]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p19_2 : ∀ feat, Dec feat p19 2 (FV7z.mk .mov 32 [gr 32 15, Src.opd 32 (.i 3)] 6) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.xor 32 7 (.r 7),
  Op.mov 32 15 (.i 3)]

theorem b19 (prof : Profile) : Blk prof p19 0 8 o19 :=
  .cons (p19_0 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p19_2 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `3809`. -/
def p20 : List Byte := [
  0xf6, 0x05, 0xc7, 0x7a, 0x38, 0x00, 0x10]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .test 8 [.mem (mrip 3701447 8), .imm 8 16] 7) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.testmia 8 8014575 16]

theorem b20 (prof : Profile) : BlkA prof p20 (0x41d021 : Addr) 0 7 o20 :=
  .cons (p20_0 _) (OpIA.testmi8_rip (by decide)) (by decide) <|
  .nil 7

def j9 : List Byte := [0x0f, 0x84, 0xc0, 0x00, 0x00, 0x00]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 4) 64 [.rel 192] 6) := by dec_rfl

/-- The stretch at `3822`. -/
def p21 : List Byte := [
  0x41, 0x83, 0xfd, 0x03]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.i 3)] 4) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.cmp 32 13 (.i 3)]

theorem b21 (prof : Profile) : Blk prof p21 0 4 o21 :=
  .cons (p21_0 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 4

def j10 : List Byte := [0x7e, 0x7b]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk (.jcc 14) 64 [.rel 123] 2) := by dec_rfl

/-- The stretch at `3828`. -/
def p22 : List Byte := [
  0xbe, 0x03, 0x00, 0x00, 0x00, 0x85, 0xff]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 3)] 5) := by dec_rfl
theorem p22_5 : ∀ feat, Dec feat p22 5 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.mov 32 6 (.i 3),
  Op.test 32 7 (.r 7)]

theorem b22 (prof : Profile) : Blk prof p22 0 7 o22 :=
  .cons (p22_0 _) (OpI.mov (.i 3) (.inl rfl)) (by decide) <|
  .cons (p22_5 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .nil 7

def j11 : List Byte := [0x0f, 0x85, 0x90, 0x01, 0x00, 0x00]
theorem j11_0 : ∀ feat, Dec feat j11 0 (FV7z.mk (.jcc 5) 64 [.rel 400] 6) := by dec_rfl

/-- The stretch at `3841`. -/
def p23 : List Byte := [
  0x31, 0xc9, 0x45, 0x31, 0xc9, 0x41, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x41, 0xba, 0x04, 0x00, 0x00,
  0x00]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p23_2 : ∀ feat, Dec feat p23 2 (FV7z.mk .xor 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p23_5 : ∀ feat, Dec feat p23 5 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p23_11 : ∀ feat, Dec feat p23 11 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 4)] 6) := by dec_rfl

/-- What the stretch does. -/
def o23 : List Op := [
  Op.xor 32 1 (.r 1),
  Op.xor 32 9 (.r 9),
  Op.mov 32 11 (.i 1),
  Op.mov 32 10 (.i 4)]

theorem b23 (prof : Profile) : Blk prof p23 0 17 o23 :=
  .cons (p23_0 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .cons (p23_2 _) (OpI.xor (.r 9) (.inl rfl)) (by decide) <|
  .cons (p23_5 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p23_11 _) (OpI.mov (.i 4) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `3858`. -/
def p24 : List Byte := [
  0x44, 0x8d, 0x41, 0x01, 0x44, 0x89, 0xd0]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .lea 32 [gr 32 8, .mem (mg (some 1) none 1 1 0)] 4) := by dec_rfl
theorem p24_4 : ∀ feat, Dec feat p24 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.lea 32 8 (some 1) none 1 1,
  Op.mov 32 0 (.r 10)]

theorem b24 (prof : Profile) : Blk prof p24 0 7 o24 :=
  .cons (p24_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p24_4 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .nil 7

/-- The stretch at `3867`. -/
def p25 : List Byte := [
  0xa8, 0x1f]

theorem p25_0 : ∀ feat, Dec feat p25 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 31)] 2) := by dec_rfl

/-- What the stretch does. -/
def o25 : List Op := [
  Op.test 8 0 (.i 31)]

theorem b25 (prof : Profile) : Blk prof p25 0 2 o25 :=
  .cons (p25_0 _) (OpI.test8 (.i 31)) (by decide) <|
  .nil 2

def j12 : List Byte := [0x74, 0x59]
theorem j12_0 : ∀ feat, Dec feat j12 0 (FV7z.mk (.jcc 4) 64 [.rel 89] 2) := by dec_rfl

/-- The stretch at `3871`. -/
def p26 : List Byte := [
  0x89, 0xc1, 0xc1, 0xe9, 0x05, 0x83, 0xe1, 0x07, 0x83, 0xf9, 0x02]

theorem p26_0 : ∀ feat, Dec feat p26 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p26_2 : ∀ feat, Dec feat p26 2 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 5)] 3) := by dec_rfl
theorem p26_5 : ∀ feat, Dec feat p26 5 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 7)] 3) := by dec_rfl
theorem p26_8 : ∀ feat, Dec feat p26 8 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o26 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.shr 1 (.i 5),
  Op.and 32 1 (.i 7),
  Op.cmp 32 1 (.i 2)]

theorem b26 (prof : Profile) : Blk prof p26 0 11 o26 :=
  .cons (p26_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p26_2 _) (OpI.shr (.i 5)) (by decide) <|
  .cons (p26_5 _) (OpI.and (.i 7) (.inl rfl)) (by decide) <|
  .cons (p26_8 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 11

def j13 : List Byte := [0x0f, 0x84, 0x13, 0x01, 0x00, 0x00]
theorem j13_0 : ∀ feat, Dec feat j13 0 (FV7z.mk (.jcc 4) 64 [.rel 275] 6) := by dec_rfl

/-- The stretch at `3888`. -/
def p27 : List Byte := [
  0x83, 0xf9, 0x03]

theorem p27_0 : ∀ feat, Dec feat p27 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o27 : List Op := [
  Op.cmp 32 1 (.i 3)]

theorem b27 (prof : Profile) : Blk prof p27 0 3 o27 :=
  .cons (p27_0 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 3

def j14 : List Byte := [0x75, 0x24]
theorem j14_0 : ∀ feat, Dec feat j14 0 (FV7z.mk (.jcc 5) 64 [.rel 36] 2) := by dec_rfl

/-- The stretch at `3893`. -/
def p28 : List Byte := [
  0x40, 0xf6, 0xc6, 0x02]

theorem p28_0 : ∀ feat, Dec feat p28 0 (FV7z.mk .test 8 [gr 8 6, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o28 : List Op := [
  Op.test 8 6 (.i 2)]

theorem b28 (prof : Profile) : Blk prof p28 0 4 o28 :=
  .cons (p28_0 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 4

def j15 : List Byte := [0x74, 0x1e]
theorem j15_0 : ∀ feat, Dec feat j15 0 (FV7z.mk (.jcc 4) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `3899`. -/
def p29 : List Byte := [
  0xc1, 0xe8, 0x0e, 0xd1, 0xea, 0x83, 0xe6, 0xfd, 0x25, 0xff, 0x03, 0x00, 0x00, 0x41, 0x89, 0xd3,
  0x89, 0xc7, 0x41, 0x83, 0xe3, 0x01]

theorem p29_0 : ∀ feat, Dec feat p29 0 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 14)] 3) := by dec_rfl
theorem p29_3 : ∀ feat, Dec feat p29 3 (FV7z.mk .shr 32 [gr 32 2, Src.opd 8 (.i 1)] 2) := by dec_rfl
theorem p29_5 : ∀ feat, Dec feat p29 5 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 4294967293)] 3) := by dec_rfl
theorem p29_8 : ∀ feat, Dec feat p29 8 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 1023)] 5) := by dec_rfl
theorem p29_13 : ∀ feat, Dec feat p29 13 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.r 2)] 3) := by dec_rfl
theorem p29_16 : ∀ feat, Dec feat p29 16 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p29_18 : ∀ feat, Dec feat p29 18 (FV7z.mk .and 32 [gr 32 11, Src.opd 32 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o29 : List Op := [
  Op.shr 0 (.i 14),
  Op.shr 2 (.i 1),
  Op.and 32 6 (.i 4294967293),
  Op.and 32 0 (.i 1023),
  Op.mov 32 11 (.r 2),
  Op.mov 32 7 (.r 0),
  Op.and 32 11 (.i 1)]

theorem b29 (prof : Profile) : Blk prof p29 0 22 o29 :=
  .cons (p29_0 _) (OpI.shr (.i 14)) (by decide) <|
  .cons (p29_3 _) (OpI.shr (.i 1)) (by decide) <|
  .cons (p29_5 _) (OpI.and (.i 4294967293) (.inl rfl)) (by decide) <|
  .cons (p29_8 _) (OpI.and (.i 1023) (.inl rfl)) (by decide) <|
  .cons (p29_13 _) (OpI.mov (.r 2) (.inl rfl)) (by decide) <|
  .cons (p29_16 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p29_18 _) (OpI.and (.i 1) (.inl rfl)) (by decide) <|
  .nil 22

/-- The stretch at `3921`. -/
def p30 : List Byte := [
  0x85, 0xf6]

theorem p30_0 : ∀ feat, Dec feat p30 0 (FV7z.mk .test 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o30 : List Op := [
  Op.test 32 6 (.r 6)]

theorem b30 (prof : Profile) : Blk prof p30 0 2 o30 :=
  .cons (p30_0 _) (OpI.test (.r 6) (.inl rfl)) (by decide) <|
  .nil 2

def j16 : List Byte := [0x0f, 0x84, 0x45, 0x01, 0x00, 0x00]
theorem j16_0 : ∀ feat, Dec feat j16 0 (FV7z.mk (.jcc 4) 64 [.rel 325] 6) := by dec_rfl

/-- The stretch at `3929`. -/
def p31 : List Byte := [
  0x44, 0x89, 0xc1]

theorem p31_0 : ∀ feat, Dec feat p31 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o31 : List Op := [
  Op.mov 32 1 (.r 8)]

theorem b31 (prof : Profile) : Blk prof p31 0 3 o31 :=
  .cons (p31_0 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

def j17 : List Byte := [0xeb, 0xb4]
theorem j17_0 : ∀ feat, Dec feat j17 0 (FV7z.mk .jmp 64 [.rel 18446744073709551540] 2) := by dec_rfl

/-- The stretch at `3934`. -/
def p32 : List Byte := [
  0x4c, 0x89, 0xf5, 0x83, 0xcf, 0xff, 0x41, 0xbf, 0x02, 0x00, 0x00, 0x00]

theorem p32_0 : ∀ feat, Dec feat p32 0 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p32_3 : ∀ feat, Dec feat p32 3 (FV7z.mk .or 32 [gr 32 7, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p32_6 : ∀ feat, Dec feat p32 6 (FV7z.mk .mov 32 [gr 32 15, Src.opd 32 (.i 2)] 6) := by dec_rfl

/-- What the stretch does. -/
def o32 : List Op := [
  Op.mov 64 5 (.r 14),
  Op.or 32 7 (.i 4294967295),
  Op.mov 32 15 (.i 2)]

theorem b32 (prof : Profile) : Blk prof p32 0 12 o32 :=
  .cons (p32_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p32_3 _) (OpI.or (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p32_6 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 12

def j18 : List Byte := [0xe9, 0x72, 0xff, 0xff, 0xff]
theorem j18_0 : ∀ feat, Dec feat j18 0 (FV7z.mk .jmp 64 [.rel 18446744073709551474] 5) := by dec_rfl

/-- The stretch at `3951`. -/
def p33 : List Byte := [
  0x45, 0x31, 0xc9, 0x41, 0xbb, 0x01, 0x00, 0x00, 0x00]

theorem p33_0 : ∀ feat, Dec feat p33 0 (FV7z.mk .xor 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p33_3 : ∀ feat, Dec feat p33 3 (FV7z.mk .mov 32 [gr 32 11, Src.opd 32 (.i 1)] 6) := by dec_rfl

/-- What the stretch does. -/
def o33 : List Op := [
  Op.xor 32 9 (.r 9),
  Op.mov 32 11 (.i 1)]

theorem b33 (prof : Profile) : Blk prof p33 0 9 o33 :=
  .cons (p33_0 _) (OpI.xor (.r 9) (.inl rfl)) (by decide) <|
  .cons (p33_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `3960`. -/
def p34 : List Byte := [
  0x0f, 0xb6, 0x3d, 0x27, 0x7a, 0x38, 0x00]

theorem p34_0 : ∀ feat, Dec feat p34 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mrip 3701287 8)] 7) := by dec_rfl

/-- What the stretch does. -/
def o34 : List Op := [
  Op.ldzxa 8 7 8014566]

theorem b34 (prof : Profile) : BlkA prof p34 (0x41d0b8 : Addr) 0 7 o34 :=
  .cons (p34_0 _) (OpIA.ldzx_rip (.inl rfl) (by decide)) (by decide) <|
  .nil 7

def j19 : List Byte := [0x7e, 0x0f]
theorem j19_0 : ∀ feat, Dec feat j19 0 (FV7z.mk (.jcc 14) 64 [.rel 15] 2) := by dec_rfl

/-- The stretch at `3972`. -/
def p35 : List Byte := [
  0x85, 0xff]

theorem p35_0 : ∀ feat, Dec feat p35 0 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o35 : List Op := [
  Op.test 32 7 (.r 7)]

theorem b35 (prof : Profile) : Blk prof p35 0 2 o35 :=
  .cons (p35_0 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .nil 2

def j20 : List Byte := [0x74, 0x0b]
theorem j20_0 : ∀ feat, Dec feat j20 0 (FV7z.mk (.jcc 4) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `3976`. -/
def p36 : List Byte := [
  0x48, 0x89, 0xe8, 0x48, 0x99]

theorem p36_0 : ∀ feat, Dec feat p36 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p36_3 : ∀ feat, Dec feat p36 3 (FV7z.mk .cwd 64 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o36 : List Op := [
  Op.mov 64 0 (.r 5),
  Op.cqo]

theorem b36 (prof : Profile) : Blk prof p36 0 5 o36 :=
  .cons (p36_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p36_3 _) (OpI.cqo) (by decide) <|
  .nil 5

/-- The stretch at `3987`. -/
def p37 : List Byte := [
  0x45, 0x84, 0xdb]

theorem p37_0 : ∀ feat, Dec feat p37 0 (FV7z.mk .test 8 [gr 8 11, Src.opd 8 (.r 11)] 3) := by dec_rfl

/-- What the stretch does. -/
def o37 : List Op := [
  Op.test 8 11 (.r 11)]

theorem b37 (prof : Profile) : Blk prof p37 0 3 o37 :=
  .cons (p37_0 _) (OpI.test8 (.r 11)) (by decide) <|
  .nil 3

def j21 : List Byte := [0x75, 0x16]
theorem j21_0 : ∀ feat, Dec feat j21 0 (FV7z.mk (.jcc 5) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `3992`. -/
def p38 : List Byte := [
  0x45, 0x85, 0xc9]

theorem p38_0 : ∀ feat, Dec feat p38 0 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o38 : List Op := [
  Op.test 32 9 (.r 9)]

theorem b38 (prof : Profile) : Blk prof p38 0 3 o38 :=
  .cons (p38_0 _) (OpI.test (.r 9) (.inl rfl)) (by decide) <|
  .nil 3

def j22 : List Byte := [0x74, 0x0e]
theorem j22_0 : ∀ feat, Dec feat j22 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `3997`. -/
def p39 : List Byte := [
  0x4c, 0x89, 0xf0, 0x4d, 0x63, 0xc9, 0x48, 0x99]

theorem p39_0 : ∀ feat, Dec feat p39 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 14)] 3) := by dec_rfl
theorem p39_3 : ∀ feat, Dec feat p39 3 (FV7z.mk .movsxd 64 [gr 64 9, gr 32 9] 3) := by dec_rfl
theorem p39_6 : ∀ feat, Dec feat p39 6 (FV7z.mk .cwd 64 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o39 : List Op := [
  Op.mov 64 0 (.r 14),
  Op.sxr 9 9,
  Op.cqo]

theorem b39 (prof : Profile) : Blk prof p39 0 8 o39 :=
  .cons (p39_0 _) (OpI.mov (.r 14) (.inr rfl)) (by decide) <|
  .cons (p39_3 _) (OpI.sxr) (by decide) <|
  .cons (p39_6 _) (OpI.cqo) (by decide) <|
  .nil 8

/-- The stretch at `4008`. -/
def p40 : List Byte := [
  0x49, 0x89, 0xc6]

theorem p40_0 : ∀ feat, Dec feat p40 0 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o40 : List Op := [
  Op.mov 64 14 (.r 0)]

theorem b40 (prof : Profile) : Blk prof p40 0 3 o40 :=
  .cons (p40_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `4011`. -/
def p41 : List Byte := [
  0x4c, 0x01, 0xf5]

theorem p41_0 : ∀ feat, Dec feat p41 0 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.r 14)] 3) := by dec_rfl

/-- What the stretch does. -/
def o41 : List Op := [
  Op.add 64 5 (.r 14)]

theorem b41 (prof : Profile) : Blk prof p41 0 3 o41 :=
  .cons (p41_0 _) (OpI.add (.r 14) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `4014`. -/
def p42 : List Byte := [
  0x48, 0x8b, 0x05, 0x7b, 0x7a, 0x38, 0x00, 0x48, 0x85, 0xc0]

theorem p42_0 : ∀ feat, Dec feat p42 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 3701371 64)] 7) := by dec_rfl
theorem p42_7 : ∀ feat, Dec feat p42 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o42 : List Op := [
  Op.lda 64 0 8014704,
  Op.test 64 0 (.r 0)]

theorem b42 (prof : Profile) : BlkA prof p42 (0x41d0ee : Addr) 0 10 o42 :=
  .cons (p42_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p42_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j23 : List Byte := [0x0f, 0x84, 0x33, 0xfe, 0xff, 0xff]
theorem j23_0 : ∀ feat, Dec feat j23 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551155] 6) := by dec_rfl

def j24 : List Byte := [0xe9, 0x2b, 0xfe, 0xff, 0xff]
theorem j24_0 : ∀ feat, Dec feat j24 0 (FV7z.mk .jmp 64 [.rel 18446744073709551147] 5) := by dec_rfl

/-- The stretch at `4035`. -/
def p43 : List Byte := [
  0xbf, 0xbc, 0x00, 0x00, 0x00]

theorem p43_0 : ∀ feat, Dec feat p43 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 188)] 5) := by dec_rfl

/-- What the stretch does. -/
def o43 : List Op := [
  Op.mov 32 7 (.i 188)]

theorem b43 (prof : Profile) : Blk prof p43 0 5 o43 :=
  .cons (p43_0 _) (OpI.mov (.i 188) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `4058`. -/
def p44 : List Byte := [
  0xbf, 0xc2, 0x00, 0x00, 0x00, 0x48, 0x89, 0xc5]

theorem p44_0 : ∀ feat, Dec feat p44 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 194)] 5) := by dec_rfl
theorem p44_5 : ∀ feat, Dec feat p44 5 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o44 : List Op := [
  Op.mov 32 7 (.i 194),
  Op.mov 64 5 (.r 0)]

theorem b44 (prof : Profile) : Blk prof p44 0 8 o44 :=
  .cons (p44_0 _) (OpI.mov (.i 194) (.inl rfl)) (by decide) <|
  .cons (p44_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 8

/-- The stretch at `4071`. -/
def p45 : List Byte := [
  0x48, 0x89, 0xc7, 0xb8, 0x00, 0x00, 0x00, 0x80]

theorem p45_0 : ∀ feat, Dec feat p45 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p45_3 : ∀ feat, Dec feat p45 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147483648)] 5) := by dec_rfl

/-- What the stretch does. -/
def o45 : List Op := [
  Op.mov 64 7 (.r 0),
  Op.mov 32 0 (.i 2147483648)]

theorem b45 (prof : Profile) : Blk prof p45 0 8 o45 :=
  .cons (p45_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p45_3 _) (OpI.mov (.i 2147483648) (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `4081`. -/
def p46 : List Byte := [
  0x89, 0xc6, 0x48, 0x85, 0xff]

theorem p46_0 : ∀ feat, Dec feat p46 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p46_2 : ∀ feat, Dec feat p46 2 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o46 : List Op := [
  Op.mov 32 6 (.r 0),
  Op.test 64 7 (.r 7)]

theorem b46 (prof : Profile) : Blk prof p46 0 5 o46 :=
  .cons (p46_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p46_2 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 5

def j25 : List Byte := [0x7e, 0x28]
theorem j25_0 : ∀ feat, Dec feat j25 0 (FV7z.mk (.jcc 14) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `4088`. -/
def p47 : List Byte := [
  0x3d, 0x07, 0x00, 0x00, 0x80]

theorem p47_0 : ∀ feat, Dec feat p47 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 2147483655)] 5) := by dec_rfl

/-- What the stretch does. -/
def o47 : List Op := [
  Op.cmp 32 0 (.i 2147483655)]

theorem b47 (prof : Profile) : Blk prof p47 0 5 o47 :=
  .cons (p47_0 _) (OpI.cmp (.i 2147483655) (.inl rfl)) (by decide) <|
  .nil 5

def j26 : List Byte := [0x77, 0x61]
theorem j26_0 : ∀ feat, Dec feat j26 0 (FV7z.mk (.jcc 7) 64 [.rel 97] 2) := by dec_rfl

/-- The stretch at `4095`. -/
def p48 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p48_0 : ∀ feat, Dec feat p48 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o48 : List Op := [
  Op.mov 32 0 (.i 1)]

theorem b48 (prof : Profile) : Blk prof p48 0 5 o48 :=
  .cons (p48_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `4102`. -/
def p49 : List Byte := [
  0x81, 0xe2, 0x00, 0x00, 0x00, 0x10, 0x89, 0xc6]

theorem p49_0 : ∀ feat, Dec feat p49 0 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.i 268435456)] 6) := by dec_rfl
theorem p49_6 : ∀ feat, Dec feat p49 6 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o49 : List Op := [
  Op.and 32 2 (.i 268435456),
  Op.mov 32 6 (.r 0)]

theorem b49 (prof : Profile) : Blk prof p49 0 8 o49 :=
  .cons (p49_0 _) (OpI.and (.i 268435456) (.inl rfl)) (by decide) <|
  .cons (p49_6 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 8

def j27 : List Byte := [0x74, 0x0d]
theorem j27_0 : ∀ feat, Dec feat j27 0 (FV7z.mk (.jcc 4) 64 [.rel 13] 2) := by dec_rfl

/-- The stretch at `4112`. -/
def p50 : List Byte := [
  0xc1, 0xeb, 0x10, 0x89, 0xd9, 0x81, 0xe1, 0xff, 0x00, 0x00, 0x00]

theorem p50_0 : ∀ feat, Dec feat p50 0 (FV7z.mk .shr 32 [gr 32 3, Src.opd 8 (.i 16)] 3) := by dec_rfl
theorem p50_3 : ∀ feat, Dec feat p50 3 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 3)] 2) := by dec_rfl
theorem p50_5 : ∀ feat, Dec feat p50 5 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 255)] 6) := by dec_rfl

/-- What the stretch does. -/
def o50 : List Op := [
  Op.shr 3 (.i 16),
  Op.mov 32 1 (.r 3),
  Op.and 32 1 (.i 255)]

theorem b50 (prof : Profile) : Blk prof p50 0 11 o50 :=
  .cons (p50_0 _) (OpI.shr (.i 16)) (by decide) <|
  .cons (p50_3 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .cons (p50_5 _) (OpI.and (.i 255) (.inl rfl)) (by decide) <|
  .nil 11

def j28 : List Byte := [0x75, 0x5b]
theorem j28_0 : ∀ feat, Dec feat j28 0 (FV7z.mk (.jcc 5) 64 [.rel 91] 2) := by dec_rfl

/-- The stretch at `4125`. -/
def p51 : List Byte := [
  0x48, 0x01, 0xfd]

theorem p51_0 : ∀ feat, Dec feat p51 0 (FV7z.mk .add 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o51 : List Op := [
  Op.add 64 5 (.r 7)]

theorem b51 (prof : Profile) : Blk prof p51 0 3 o51 :=
  .cons (p51_0 _) (OpI.add (.r 7) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `4128`. -/
def p52 : List Byte := [
  0x81, 0xfe, 0x00, 0x00, 0x00, 0x80]

theorem p52_0 : ∀ feat, Dec feat p52 0 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 2147483648)] 6) := by dec_rfl

/-- What the stretch does. -/
def o52 : List Op := [
  Op.cmp 32 6 (.i 2147483648)]

theorem b52 (prof : Profile) : Blk prof p52 0 6 o52 :=
  .cons (p52_0 _) (OpI.cmp (.i 2147483648) (.inl rfl)) (by decide) <|
  .nil 6

def j29 : List Byte := [0x76, 0x86]
theorem j29_0 : ∀ feat, Dec feat j29 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551494] 2) := by dec_rfl

/-- The stretch at `4136`. -/
def p53 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x80]

theorem p53_0 : ∀ feat, Dec feat p53 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147483649)] 5) := by dec_rfl

/-- What the stretch does. -/
def o53 : List Op := [
  Op.mov 32 0 (.i 2147483649)]

theorem b53 (prof : Profile) : Blk prof p53 0 5 o53 :=
  .cons (p53_0 _) (OpI.mov (.i 2147483649) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `4143`. -/
def p54 : List Byte := [
  0x80, 0xe5, 0x01]

theorem p54_0 : ∀ feat, Dec feat p54 0 (FV7z.mk .and 8 [gh 1, .imm 8 1] 3) := by dec_rfl

/-- What the stretch does. -/
def o54 : List Op := [
  Op.andh 1 1]

theorem b54 (prof : Profile) : Blk prof p54 0 3 o54 :=
  .cons (p54_0 _) (OpI.andh) (by decide) <|
  .nil 3

def j30 : List Byte := [0x74, 0x53]
theorem j30_0 : ∀ feat, Dec feat j30 0 (FV7z.mk (.jcc 4) 64 [.rel 83] 2) := by dec_rfl

/-- The stretch at `4148`. -/
def p55 : List Byte := [
  0xc7, 0x05, 0xb2, 0xb2, 0x38, 0x00, 0xff, 0xff, 0xff, 0xff]

theorem p55_0 : ∀ feat, Dec feat p55 0 (FV7z.mk .mov 32 [.mem (mrip 3715762 32), .imm 32 4294967295] 10) := by dec_rfl

/-- What the stretch does. -/
def o55 : List Op := [
  Op.stia 32 8029232 4294967295]

theorem b55 (prof : Profile) : BlkA prof p55 (0x41d174 : Addr) 0 10 o55 :=
  .cons (p55_0 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 10

def j31 : List Byte := [0xe9, 0x6b, 0xff, 0xff, 0xff]
theorem j31_0 : ∀ feat, Dec feat j31 0 (FV7z.mk .jmp 64 [.rel 18446744073709551467] 5) := by dec_rfl

/-- The stretch at `4163`. -/
def p56 : List Byte := [
  0x40, 0xf6, 0xc6, 0x01]

theorem p56_0 : ∀ feat, Dec feat p56 0 (FV7z.mk .test 8 [gr 8 6, Src.opd 8 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o56 : List Op := [
  Op.test 8 6 (.i 1)]

theorem b56 (prof : Profile) : Blk prof p56 0 4 o56 :=
  .cons (p56_0 _) (OpI.test8 (.i 1)) (by decide) <|
  .nil 4

def j32 : List Byte := [0x0f, 0x84, 0x0c, 0xff, 0xff, 0xff]
theorem j32_0 : ∀ feat, Dec feat j32 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551372] 6) := by dec_rfl

/-- The stretch at `4173`. -/
def p57 : List Byte := [
  0xc1, 0xe8, 0x0e, 0x83, 0xe6, 0xfe, 0x25, 0xff, 0x03, 0x00, 0x00, 0x41, 0x89, 0xc1]

theorem p57_0 : ∀ feat, Dec feat p57 0 (FV7z.mk .shr 32 [gr 32 0, Src.opd 8 (.i 14)] 3) := by dec_rfl
theorem p57_3 : ∀ feat, Dec feat p57 3 (FV7z.mk .and 32 [gr 32 6, Src.opd 32 (.i 4294967294)] 3) := by dec_rfl
theorem p57_6 : ∀ feat, Dec feat p57 6 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 1023)] 5) := by dec_rfl
theorem p57_11 : ∀ feat, Dec feat p57 11 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o57 : List Op := [
  Op.shr 0 (.i 14),
  Op.and 32 6 (.i 4294967294),
  Op.and 32 0 (.i 1023),
  Op.mov 32 9 (.r 0)]

theorem b57 (prof : Profile) : Blk prof p57 0 14 o57 :=
  .cons (p57_0 _) (OpI.shr (.i 14)) (by decide) <|
  .cons (p57_3 _) (OpI.and (.i 4294967294) (.inl rfl)) (by decide) <|
  .cons (p57_6 _) (OpI.and (.i 1023) (.inl rfl)) (by decide) <|
  .cons (p57_11 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 14

def j33 : List Byte := [0xe9, 0xf1, 0xfe, 0xff, 0xff]
theorem j33_0 : ∀ feat, Dec feat j33 0 (FV7z.mk .jmp 64 [.rel 18446744073709551345] 5) := by dec_rfl

/-- The stretch at `4192`. -/
def p58 : List Byte := [
  0xb8, 0x08, 0x00, 0x00, 0x80]

theorem p58_0 : ∀ feat, Dec feat p58 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147483656)] 5) := by dec_rfl

/-- What the stretch does. -/
def o58 : List Op := [
  Op.mov 32 0 (.i 2147483656)]

theorem b58 (prof : Profile) : Blk prof p58 0 5 o58 :=
  .cons (p58_0 _) (OpI.mov (.i 2147483656) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `4199`. -/
def p59 : List Byte := [
  0xc1, 0xe9, 0x0c, 0xbb, 0x01, 0x00, 0x00, 0x00, 0x89, 0xc6, 0x83, 0xe1, 0x0f, 0xd3, 0xe3, 0x89,
  0xd9]

theorem p59_0 : ∀ feat, Dec feat p59 0 (FV7z.mk .shr 32 [gr 32 1, Src.opd 8 (.i 12)] 3) := by dec_rfl
theorem p59_3 : ∀ feat, Dec feat p59 3 (FV7z.mk .mov 32 [gr 32 3, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p59_8 : ∀ feat, Dec feat p59 8 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p59_10 : ∀ feat, Dec feat p59 10 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 15)] 3) := by dec_rfl
theorem p59_13 : ∀ feat, Dec feat p59 13 (FV7z.mk .shl 32 [gr 32 3, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p59_15 : ∀ feat, Dec feat p59 15 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o59 : List Op := [
  Op.shr 1 (.i 12),
  Op.mov 32 3 (.i 1),
  Op.mov 32 6 (.r 0),
  Op.and 32 1 (.i 15),
  Op.shl 3 (.r 1),
  Op.mov 32 1 (.r 3)]

theorem b59 (prof : Profile) : Blk prof p59 0 17 o59 :=
  .cons (p59_0 _) (OpI.shr (.i 12)) (by decide) <|
  .cons (p59_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p59_8 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p59_10 _) (OpI.and (.i 15) (.inl rfl)) (by decide) <|
  .cons (p59_13 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p59_15 _) (OpI.mov (.r 3) (.inl rfl)) (by decide) <|
  .nil 17

/-- The stretch at `4216`. -/
def p60 : List Byte := [
  0x48, 0x89, 0xf8, 0x89, 0xc9, 0x48, 0x99]

theorem p60_0 : ∀ feat, Dec feat p60 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p60_3 : ∀ feat, Dec feat p60 3 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p60_5 : ∀ feat, Dec feat p60 5 (FV7z.mk .cwd 64 [] 2) := by dec_rfl

/-- What the stretch does. -/
def o60 : List Op := [
  Op.mov 64 0 (.r 7),
  Op.mov 32 1 (.r 1),
  Op.cqo]

theorem b60 (prof : Profile) : Blk prof p60 0 7 o60 :=
  .cons (p60_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p60_3 _) (OpI.mov (.r 1) (.inl rfl)) (by decide) <|
  .cons (p60_5 _) (OpI.cqo) (by decide) <|
  .nil 7

/-- The stretch at `4226`. -/
def p61 : List Byte := [
  0x48, 0x89, 0xc7]

theorem p61_0 : ∀ feat, Dec feat p61 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o61 : List Op := [
  Op.mov 64 7 (.r 0)]

theorem b61 (prof : Profile) : Blk prof p61 0 3 o61 :=
  .cons (p61_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 3

def j34 : List Byte := [0xeb, 0x96]
theorem j34_0 : ∀ feat, Dec feat j34 0 (FV7z.mk .jmp 64 [.rel 18446744073709551510] 2) := by dec_rfl

/-- The stretch at `4231`. -/
def p62 : List Byte := [
  0x85, 0xd2]

theorem p62_0 : ∀ feat, Dec feat p62 0 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o62 : List Op := [
  Op.test 32 2 (.r 2)]

theorem b62 (prof : Profile) : Blk prof p62 0 2 o62 :=
  .cons (p62_0 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 2

def j35 : List Byte := [0x0f, 0x89, 0x1f, 0xff, 0xff, 0xff]
theorem j35_0 : ∀ feat, Dec feat j35 0 (FV7z.mk (.jcc 9) 64 [.rel 18446744073709551391] 6) := by dec_rfl

def j36 : List Byte := [0xeb, 0xa3]
theorem j36_0 : ∀ feat, Dec feat j36 0 (FV7z.mk .jmp 64 [.rel 18446744073709551523] 2) := by dec_rfl

/-- The stretch at `4241`. -/
def p63 : List Byte := [
  0xbe, 0x01, 0x00, 0x00, 0x00, 0x83, 0xcf, 0xff]

theorem p63_0 : ∀ feat, Dec feat p63 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p63_5 : ∀ feat, Dec feat p63 5 (FV7z.mk .or 32 [gr 32 7, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl

/-- What the stretch does. -/
def o63 : List Op := [
  Op.mov 32 6 (.i 1),
  Op.or 32 7 (.i 4294967295)]

theorem b63 (prof : Profile) : Blk prof p63 0 8 o63 :=
  .cons (p63_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p63_5 _) (OpI.or (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 8

def j37 : List Byte := [0xe9, 0x63, 0xfe, 0xff, 0xff]
theorem j37_0 : ∀ feat, Dec feat j37 0 (FV7z.mk .jmp 64 [.rel 18446744073709551203] 5) := by dec_rfl

/-- The stretch at `4254`. -/
def p64 : List Byte := [
  0x41, 0x83, 0xfd, 0x0a]

theorem p64_0 : ∀ feat, Dec feat p64 0 (FV7z.mk .cmp 32 [gr 32 13, Src.opd 32 (.i 10)] 4) := by dec_rfl

/-- What the stretch does. -/
def o64 : List Op := [
  Op.cmp 32 13 (.i 10)]

theorem b64 (prof : Profile) : Blk prof p64 0 4 o64 :=
  .cons (p64_0 _) (OpI.cmp (.i 10) (.inl rfl)) (by decide) <|
  .nil 4

def j38 : List Byte := [0x0f, 0x8e, 0x91, 0x00, 0x00, 0x00]
theorem j38_0 : ∀ feat, Dec feat j38 0 (FV7z.mk (.jcc 14) 64 [.rel 145] 6) := by dec_rfl

/-- The stretch at `4264`. -/
def p65 : List Byte := [
  0x45, 0x85, 0xc9, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x0f, 0x9f, 0xc1, 0x45, 0x31, 0xc0, 0x41, 0x83,
  0xff, 0x03, 0x41, 0x0f, 0x94, 0xc0, 0x44, 0x89, 0xc2, 0x21, 0xca, 0x85, 0xff]

theorem p65_0 : ∀ feat, Dec feat p65 0 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p65_3 : ∀ feat, Dec feat p65 3 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p65_8 : ∀ feat, Dec feat p65 8 (FV7z.mk (.setcc 15) 8 [gr 8 1] 3) := by dec_rfl
theorem p65_11 : ∀ feat, Dec feat p65 11 (FV7z.mk .xor 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p65_14 : ∀ feat, Dec feat p65 14 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.i 3)] 4) := by dec_rfl
theorem p65_18 : ∀ feat, Dec feat p65 18 (FV7z.mk (.setcc 4) 8 [gr 8 8] 4) := by dec_rfl
theorem p65_22 : ∀ feat, Dec feat p65 22 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p65_25 : ∀ feat, Dec feat p65 25 (FV7z.mk .and 32 [gr 32 2, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem p65_27 : ∀ feat, Dec feat p65 27 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o65 : List Op := [
  Op.test 32 9 (.r 9),
  Op.mov 32 0 (.i 1),
  Op.setcc 15 1,
  Op.xor 32 8 (.r 8),
  Op.cmp 32 15 (.i 3),
  Op.setcc 4 8,
  Op.mov 32 2 (.r 8),
  Op.and 32 2 (.r 1),
  Op.test 32 7 (.r 7)]

theorem b65 (prof : Profile) : Blk prof p65 0 29 o65 :=
  .cons (p65_0 _) (OpI.test (.r 9) (.inl rfl)) (by decide) <|
  .cons (p65_3 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p65_8 _) (OpI.setcc) (by decide) <|
  .cons (p65_11 _) (OpI.xor (.r 8) (.inl rfl)) (by decide) <|
  .cons (p65_14 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .cons (p65_18 _) (OpI.setcc) (by decide) <|
  .cons (p65_22 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p65_25 _) (OpI.and (.r 1) (.inl rfl)) (by decide) <|
  .cons (p65_27 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .nil 29

def j39 : List Byte := [0x7f, 0x0b]
theorem j39_0 : ∀ feat, Dec feat j39 0 (FV7z.mk (.jcc 15) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `4295`. -/
def p66 : List Byte := [
  0x31, 0xc0, 0x41, 0x83, 0xff, 0x02, 0x0f, 0x94, 0xc0, 0x21, 0xc8]

theorem p66_0 : ∀ feat, Dec feat p66 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p66_2 : ∀ feat, Dec feat p66 2 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.i 2)] 4) := by dec_rfl
theorem p66_6 : ∀ feat, Dec feat p66 6 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl
theorem p66_9 : ∀ feat, Dec feat p66 9 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o66 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.cmp 32 15 (.i 2),
  Op.setcc 4 0,
  Op.and 32 0 (.r 1)]

theorem b66 (prof : Profile) : Blk prof p66 0 11 o66 :=
  .cons (p66_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p66_2 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .cons (p66_6 _) (OpI.setcc) (by decide) <|
  .cons (p66_9 _) (OpI.and (.r 1) (.inl rfl)) (by decide) <|
  .nil 11

/-- The stretch at `4306`. -/
def p67 : List Byte := [
  0x44, 0x8d, 0x04, 0x00, 0x41, 0xbd, 0x0b, 0x00, 0x00, 0x00, 0x41, 0x09, 0xd0]

theorem p67_0 : ∀ feat, Dec feat p67 0 (FV7z.mk .lea 32 [gr 32 8, .mem (mg (some 0) (some 0) 1 0 0)] 4) := by dec_rfl
theorem p67_4 : ∀ feat, Dec feat p67 4 (FV7z.mk .mov 32 [gr 32 13, Src.opd 32 (.i 11)] 6) := by dec_rfl
theorem p67_10 : ∀ feat, Dec feat p67 10 (FV7z.mk .or 32 [gr 32 8, Src.opd 32 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o67 : List Op := [
  Op.lea 32 8 (some 0) (some 0) 1 0,
  Op.mov 32 13 (.i 11),
  Op.or 32 8 (.r 2)]

theorem b67 (prof : Profile) : Blk prof p67 0 13 o67 :=
  .cons (p67_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p67_4 _) (OpI.mov (.i 11) (.inl rfl)) (by decide) <|
  .cons (p67_10 _) (OpI.or (.r 2) (.inl rfl)) (by decide) <|
  .nil 13

def j40 : List Byte := [0xeb, 0x0b]
theorem j40_0 : ∀ feat, Dec feat j40 0 (FV7z.mk .jmp 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `4321`. -/
def p68 : List Byte := [
  0x81, 0xf9, 0x00, 0x02, 0x00, 0x00]

theorem p68_0 : ∀ feat, Dec feat p68 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 512)] 6) := by dec_rfl

/-- What the stretch does. -/
def o68 : List Op := [
  Op.cmp 32 1 (.i 512)]

theorem b68 (prof : Profile) : Blk prof p68 0 6 o68 :=
  .cons (p68_0 _) (OpI.cmp (.i 512) (.inl rfl)) (by decide) <|
  .nil 6

def j41 : List Byte := [0x74, 0x6a]
theorem j41_0 : ∀ feat, Dec feat j41 0 (FV7z.mk (.jcc 4) 64 [.rel 106] 2) := by dec_rfl

/-- The stretch at `4329`. -/
def p69 : List Byte := [
  0x44, 0x89, 0xd6]

theorem p69_0 : ∀ feat, Dec feat p69 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 10)] 3) := by dec_rfl

/-- What the stretch does. -/
def o69 : List Op := [
  Op.mov 32 6 (.r 10)]

theorem b69 (prof : Profile) : Blk prof p69 0 3 o69 :=
  .cons (p69_0 _) (OpI.mov (.r 10) (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `4332`. -/
def p70 : List Byte := [
  0x45, 0x85, 0xc0]

theorem p70_0 : ∀ feat, Dec feat p70 0 (FV7z.mk .test 32 [gr 32 8, Src.opd 32 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o70 : List Op := [
  Op.test 32 8 (.r 8)]

theorem b70 (prof : Profile) : Blk prof p70 0 3 o70 :=
  .cons (p70_0 _) (OpI.test (.r 8) (.inl rfl)) (by decide) <|
  .nil 3

def j42 : List Byte := [0x74, 0x48]
theorem j42_0 : ∀ feat, Dec feat j42 0 (FV7z.mk (.jcc 4) 64 [.rel 72] 2) := by dec_rfl

/-- The stretch at `4337`. -/
def p71 : List Byte := [
  0x44, 0x8d, 0x56, 0x01, 0x44, 0x89, 0xe8, 0x89, 0xf1]

theorem p71_0 : ∀ feat, Dec feat p71 0 (FV7z.mk .lea 32 [gr 32 10, .mem (mg (some 6) none 1 1 0)] 4) := by dec_rfl
theorem p71_4 : ∀ feat, Dec feat p71 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 13)] 3) := by dec_rfl
theorem p71_7 : ∀ feat, Dec feat p71 7 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o71 : List Op := [
  Op.lea 32 10 (some 6) none 1 1,
  Op.mov 32 0 (.r 13),
  Op.mov 32 1 (.r 6)]

theorem b71 (prof : Profile) : Blk prof p71 0 9 o71 :=
  .cons (p71_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p71_4 _) (OpI.mov (.r 13) (.inl rfl)) (by decide) <|
  .cons (p71_7 _) (OpI.mov (.r 6) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `4348`. -/
def p72 : List Byte := [
  0x81, 0xe1, 0x00, 0xff, 0x00, 0x00, 0x81, 0xe3, 0xff, 0x00, 0x00, 0x00]

theorem p72_0 : ∀ feat, Dec feat p72 0 (FV7z.mk .and 32 [gr 32 1, Src.opd 32 (.i 65280)] 6) := by dec_rfl
theorem p72_6 : ∀ feat, Dec feat p72 6 (FV7z.mk .and 32 [gr 32 3, Src.opd 32 (.i 255)] 6) := by dec_rfl

/-- What the stretch does. -/
def o72 : List Op := [
  Op.and 32 1 (.i 65280),
  Op.and 32 3 (.i 255)]

theorem b72 (prof : Profile) : Blk prof p72 0 12 o72 :=
  .cons (p72_0 _) (OpI.and (.i 65280) (.inl rfl)) (by decide) <|
  .cons (p72_6 _) (OpI.and (.i 255) (.inl rfl)) (by decide) <|
  .nil 12

def j43 : List Byte := [0x74, 0x2f]
theorem j43_0 : ∀ feat, Dec feat j43 0 (FV7z.mk (.jcc 4) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `4362`. -/
def p73 : List Byte := [
  0x85, 0xc9]

theorem p73_0 : ∀ feat, Dec feat p73 0 (FV7z.mk .test 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o73 : List Op := [
  Op.test 32 1 (.r 1)]

theorem b73 (prof : Profile) : Blk prof p73 0 2 o73 :=
  .cons (p73_0 _) (OpI.test (.r 1) (.inl rfl)) (by decide) <|
  .nil 2

def j44 : List Byte := [0x74, 0x2b]
theorem j44_0 : ∀ feat, Dec feat j44 0 (FV7z.mk (.jcc 4) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `4366`. -/
def p74 : List Byte := [
  0x81, 0xf9, 0x00, 0x01, 0x00, 0x00]

theorem p74_0 : ∀ feat, Dec feat p74 0 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 256)] 6) := by dec_rfl

/-- What the stretch does. -/
def o74 : List Op := [
  Op.cmp 32 1 (.i 256)]

theorem b74 (prof : Profile) : Blk prof p74 0 6 o74 :=
  .cons (p74_0 _) (OpI.cmp (.i 256) (.inl rfl)) (by decide) <|
  .nil 6

def j45 : List Byte := [0x75, 0xcb]
theorem j45_0 : ∀ feat, Dec feat j45 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551563] 2) := by dec_rfl

/-- The stretch at `4374`. -/
def p75 : List Byte := [
  0x41, 0xf6, 0xc0, 0x01]

theorem p75_0 : ∀ feat, Dec feat p75 0 (FV7z.mk .test 8 [gr 8 8, Src.opd 8 (.i 1)] 4) := by dec_rfl

/-- What the stretch does. -/
def o75 : List Op := [
  Op.test 8 8 (.i 1)]

theorem b75 (prof : Profile) : Blk prof p75 0 4 o75 :=
  .cons (p75_0 _) (OpI.test8 (.i 1)) (by decide) <|
  .nil 4

def j46 : List Byte := [0x74, 0xcd]
theorem j46_0 : ∀ feat, Dec feat j46 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `4384`. -/
def p76 : List Byte := [
  0x41, 0x83, 0xc9, 0xff, 0x83, 0xc1, 0x01, 0x8d, 0x43, 0xff, 0x41, 0x83, 0xe0, 0xfe, 0x41, 0xd3,
  0xe1, 0x41, 0xf7, 0xd1, 0x41, 0x21, 0xc1]

theorem p76_0 : ∀ feat, Dec feat p76 0 (FV7z.mk .or 32 [gr 32 9, Src.opd 32 (.i 4294967295)] 4) := by dec_rfl
theorem p76_4 : ∀ feat, Dec feat p76 4 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p76_7 : ∀ feat, Dec feat p76 7 (FV7z.mk .lea 32 [gr 32 0, .mem (mg (some 3) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p76_10 : ∀ feat, Dec feat p76 10 (FV7z.mk .and 32 [gr 32 8, Src.opd 32 (.i 4294967294)] 4) := by dec_rfl
theorem p76_14 : ∀ feat, Dec feat p76 14 (FV7z.mk .shl 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p76_17 : ∀ feat, Dec feat p76 17 (FV7z.mk .not 32 [gr 32 9] 3) := by dec_rfl
theorem p76_20 : ∀ feat, Dec feat p76 20 (FV7z.mk .and 32 [gr 32 9, Src.opd 32 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o76 : List Op := [
  Op.or 32 9 (.i 4294967295),
  Op.add 32 1 (.i 1),
  Op.lea 32 0 (some 3) none 1 18446744073709551615,
  Op.and 32 8 (.i 4294967294),
  Op.shl 9 (.r 1),
  Op.not32 9,
  Op.and 32 9 (.r 0)]

theorem b76 (prof : Profile) : Blk prof p76 0 23 o76 :=
  .cons (p76_0 _) (OpI.or (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p76_4 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p76_7 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p76_10 _) (OpI.and (.i 4294967294) (.inl rfl)) (by decide) <|
  .cons (p76_14 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p76_17 _) (OpI.not32) (by decide) <|
  .cons (p76_20 _) (OpI.and (.r 0) (.inl rfl)) (by decide) <|
  .nil 23

def j47 : List Byte := [0xeb, 0xb0]
theorem j47_0 : ∀ feat, Dec feat j47 0 (FV7z.mk .jmp 64 [.rel 18446744073709551536] 2) := by dec_rfl

/-- The stretch at `4409`. -/
def p77 : List Byte := [
  0x41, 0x83, 0xf9, 0x01, 0x41, 0x83, 0xd9, 0xff, 0x85, 0xff]

theorem p77_0 : ∀ feat, Dec feat p77 0 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 1)] 4) := by dec_rfl
theorem p77_4 : ∀ feat, Dec feat p77 4 (FV7z.mk .sbb 32 [gr 32 9, Src.opd 32 (.i 4294967295)] 4) := by dec_rfl
theorem p77_8 : ∀ feat, Dec feat p77 8 (FV7z.mk .test 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl

/-- What the stretch does. -/
def o77 : List Op := [
  Op.cmp 32 9 (.i 1),
  Op.sbb 32 9 (.i 4294967295),
  Op.test 32 7 (.r 7)]

theorem b77 (prof : Profile) : Blk prof p77 0 10 o77 :=
  .cons (p77_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .cons (p77_4 _) (OpI.sbb (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p77_8 _) (OpI.test (.r 7) (.inl rfl)) (by decide) <|
  .nil 10

def j48 : List Byte := [0x7e, 0x39]
theorem j48_0 : ∀ feat, Dec feat j48 0 (FV7z.mk (.jcc 14) 64 [.rel 57] 2) := by dec_rfl

/-- The stretch at `4421`. -/
def p78 : List Byte := [
  0x41, 0x83, 0xff, 0x02]

theorem p78_0 : ∀ feat, Dec feat p78 0 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o78 : List Op := [
  Op.cmp 32 15 (.i 2)]

theorem b78 (prof : Profile) : Blk prof p78 0 4 o78 :=
  .cons (p78_0 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 4

def j49 : List Byte := [0x74, 0x4b]
theorem j49_0 : ∀ feat, Dec feat j49 0 (FV7z.mk (.jcc 4) 64 [.rel 75] 2) := by dec_rfl

/-- The stretch at `4427`. -/
def p79 : List Byte := [
  0x83, 0xc7, 0x01]

theorem p79_0 : ∀ feat, Dec feat p79 0 (FV7z.mk .add 32 [gr 32 7, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o79 : List Op := [
  Op.add 32 7 (.i 1)]

theorem b79 (prof : Profile) : Blk prof p79 0 3 o79 :=
  .cons (p79_0 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j50 : List Byte := [0xe9, 0x2c, 0xfe, 0xff, 0xff]
theorem j50_0 : ∀ feat, Dec feat j50 0 (FV7z.mk .jmp 64 [.rel 18446744073709551148] 5) := by dec_rfl

/-- The stretch at `4435`. -/
def p80 : List Byte := [
  0x41, 0xf6, 0xc0, 0x02]

theorem p80_0 : ∀ feat, Dec feat p80 0 (FV7z.mk .test 8 [gr 8 8, Src.opd 8 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o80 : List Op := [
  Op.test 8 8 (.i 2)]

theorem b80 (prof : Profile) : Blk prof p80 0 4 o80 :=
  .cons (p80_0 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 4

def j51 : List Byte := [0x74, 0x90]
theorem j51_0 : ∀ feat, Dec feat j51 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551504] 2) := by dec_rfl

/-- The stretch at `4441`. -/
def p81 : List Byte := [
  0x83, 0xeb, 0x01, 0x41, 0x83, 0xff, 0x02]

theorem p81_0 : ∀ feat, Dec feat p81 0 (FV7z.mk .sub 32 [gr 32 3, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p81_3 : ∀ feat, Dec feat p81 3 (FV7z.mk .cmp 32 [gr 32 15, Src.opd 32 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o81 : List Op := [
  Op.sub 32 3 (.i 1),
  Op.cmp 32 15 (.i 2)]

theorem b81 (prof : Profile) : Blk prof p81 0 7 o81 :=
  .cons (p81_0 _) (OpI.sub (.i 1) (.inl rfl)) (by decide) <|
  .cons (p81_3 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 7

def j52 : List Byte := [0x0f, 0x84, 0x8c, 0x00, 0x00, 0x00]
theorem j52_0 : ∀ feat, Dec feat j52 0 (FV7z.mk (.jcc 4) 64 [.rel 140] 6) := by dec_rfl

/-- The stretch at `4457`. -/
def p82 : List Byte := [
  0x83, 0xcf, 0xff, 0x83, 0xc1, 0x01, 0xd3, 0xe7, 0xf7, 0xd7, 0x21, 0xdf]

theorem p82_0 : ∀ feat, Dec feat p82 0 (FV7z.mk .or 32 [gr 32 7, Src.opd 32 (.i 4294967295)] 3) := by dec_rfl
theorem p82_3 : ∀ feat, Dec feat p82 3 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p82_6 : ∀ feat, Dec feat p82 6 (FV7z.mk .shl 32 [gr 32 7, Src.opd 8 (.r 1)] 2) := by dec_rfl
theorem p82_8 : ∀ feat, Dec feat p82 8 (FV7z.mk .not 32 [gr 32 7] 2) := by dec_rfl
theorem p82_10 : ∀ feat, Dec feat p82 10 (FV7z.mk .and 32 [gr 32 7, Src.opd 32 (.r 3)] 2) := by dec_rfl

/-- What the stretch does. -/
def o82 : List Op := [
  Op.or 32 7 (.i 4294967295),
  Op.add 32 1 (.i 1),
  Op.shl 7 (.r 1),
  Op.not32 7,
  Op.and 32 7 (.r 3)]

theorem b82 (prof : Profile) : Blk prof p82 0 12 o82 :=
  .cons (p82_0 _) (OpI.or (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p82_3 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p82_6 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p82_8 _) (OpI.not32) (by decide) <|
  .cons (p82_10 _) (OpI.and (.r 3) (.inl rfl)) (by decide) <|
  .nil 12

/-- The stretch at `4469`. -/
def p83 : List Byte := [
  0x41, 0x83, 0xe0, 0xfd]

theorem p83_0 : ∀ feat, Dec feat p83 0 (FV7z.mk .and 32 [gr 32 8, Src.opd 32 (.i 4294967293)] 4) := by dec_rfl

/-- What the stretch does. -/
def o83 : List Op := [
  Op.and 32 8 (.i 4294967293)]

theorem b83 (prof : Profile) : Blk prof p83 0 4 o83 :=
  .cons (p83_0 _) (OpI.and (.i 4294967293) (.inl rfl)) (by decide) <|
  .nil 4

def j53 : List Byte := [0x74, 0x12]
theorem j53_0 : ∀ feat, Dec feat j53 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

def j54 : List Byte := [0x0f, 0x84, 0x07, 0xfe, 0xff, 0xff]
theorem j54_0 : ∀ feat, Dec feat j54 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551111] 6) := by dec_rfl

/-- The stretch at `4492`. -/
def p84 : List Byte := [
  0xbf, 0xff, 0xff, 0xff, 0xff]

theorem p84_0 : ∀ feat, Dec feat p84 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 4294967295)] 5) := by dec_rfl

/-- What the stretch does. -/
def o84 : List Op := [
  Op.mov 32 7 (.i 4294967295)]

theorem b84 (prof : Profile) : Blk prof p84 0 5 o84 :=
  .cons (p84_0 _) (OpI.mov (.i 4294967295) (.inl rfl)) (by decide) <|
  .nil 5

def j55 : List Byte := [0xe9, 0xe9, 0xfd, 0xff, 0xff]
theorem j55_0 : ∀ feat, Dec feat j55 0 (FV7z.mk .jmp 64 [.rel 18446744073709551081] 5) := by dec_rfl

/-- The stretch at `4502`. -/
def p85 : List Byte := [
  0x8b, 0x15, 0x74, 0x78, 0x38, 0x00, 0x8b, 0x05, 0x72, 0x78, 0x38, 0x00, 0x45, 0x85, 0xc9]

theorem p85_0 : ∀ feat, Dec feat p85 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip 3700852 32)] 6) := by dec_rfl
theorem p85_6 : ∀ feat, Dec feat p85 6 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 3700850 32)] 6) := by dec_rfl
theorem p85_12 : ∀ feat, Dec feat p85 12 (FV7z.mk .test 32 [gr 32 9, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o85 : List Op := [
  Op.lda 32 2 8014672,
  Op.lda 32 0 8014676,
  Op.test 32 9 (.r 9)]

theorem b85 (prof : Profile) : BlkA prof p85 (0x41d2d6 : Addr) 0 15 o85 :=
  .cons (p85_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p85_6 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p85_12 _) ((OpI.test (.r 9) (.inl rfl)).at _) (by decide) <|
  .nil 15

def j56 : List Byte := [0x74, 0x3d]
theorem j56_0 : ∀ feat, Dec feat j56 0 (FV7z.mk (.jcc 4) 64 [.rel 61] 2) := by dec_rfl

/-- The stretch at `4519`. -/
def p86 : List Byte := [
  0x44, 0x89, 0xcf, 0x41, 0x83, 0xf9, 0x02]

theorem p86_0 : ∀ feat, Dec feat p86 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 9)] 3) := by dec_rfl
theorem p86_3 : ∀ feat, Dec feat p86 3 (FV7z.mk .cmp 32 [gr 32 9, Src.opd 32 (.i 2)] 4) := by dec_rfl

/-- What the stretch does. -/
def o86 : List Op := [
  Op.mov 32 7 (.r 9),
  Op.cmp 32 9 (.i 2)]

theorem b86 (prof : Profile) : Blk prof p86 0 7 o86 :=
  .cons (p86_0 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .cons (p86_3 _) (OpI.cmp (.i 2) (.inl rfl)) (by decide) <|
  .nil 7

def j57 : List Byte := [0x0f, 0x86, 0xcb, 0xfd, 0xff, 0xff]
theorem j57_0 : ∀ feat, Dec feat j57 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551051] 6) := by dec_rfl

/-- The stretch at `4532`. -/
def p87 : List Byte := [
  0x83, 0xfa, 0x06]

theorem p87_0 : ∀ feat, Dec feat p87 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o87 : List Op := [
  Op.cmp 32 2 (.i 6)]

theorem b87 (prof : Profile) : Blk prof p87 0 3 o87 :=
  .cons (p87_0 _) (OpI.cmp (.i 6) (.inl rfl)) (by decide) <|
  .nil 3

def j58 : List Byte := [0x0f, 0x85, 0xc2, 0xfd, 0xff, 0xff]
theorem j58_0 : ∀ feat, Dec feat j58 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551042] 6) := by dec_rfl

/-- The stretch at `4541`. -/
def p88 : List Byte := [
  0x83, 0xe8, 0x37, 0x83, 0xf8, 0x26]

theorem p88_0 : ∀ feat, Dec feat p88 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 55)] 3) := by dec_rfl
theorem p88_3 : ∀ feat, Dec feat p88 3 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 38)] 3) := by dec_rfl

/-- What the stretch does. -/
def o88 : List Op := [
  Op.sub 32 0 (.i 55),
  Op.cmp 32 0 (.i 38)]

theorem b88 (prof : Profile) : Blk prof p88 0 6 o88 :=
  .cons (p88_0 _) (OpI.sub (.i 55) (.inl rfl)) (by decide) <|
  .cons (p88_3 _) (OpI.cmp (.i 38) (.inl rfl)) (by decide) <|
  .nil 6

def j59 : List Byte := [0x0f, 0x87, 0xb6, 0xfd, 0xff, 0xff]
theorem j59_0 : ∀ feat, Dec feat j59 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551030] 6) := by dec_rfl

/-- The stretch at `4553`. -/
def p89 : List Byte := [
  0x48, 0x8d, 0x15, 0x94, 0x4d, 0x2d, 0x00, 0x48, 0x63, 0x04, 0x82, 0x48, 0x01, 0xd0]

theorem p89_0 : ∀ feat, Dec feat p89 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 2968980 0)] 7) := by dec_rfl
theorem p89_7 : ∀ feat, Dec feat p89 7 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 2) (some 0) 4 0 32)] 4) := by dec_rfl
theorem p89_11 : ∀ feat, Dec feat p89 11 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o89 : List Op := [
  Op.mov 64 2 (.i 7282852),
  Op.ldsx 0 (some 2) (some 0) 4 0,
  Op.add 64 0 (.r 2)]

theorem b89 (prof : Profile) : BlkA prof p89 (0x41d309 : Addr) 0 14 o89 :=
  .cons (p89_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p89_7 _) ((OpI.ldsx).at _) (by decide) <|
  .cons (p89_11 _) ((OpI.add (.r 2) (.inr rfl)).at _) (by decide) <|
  .nil 14

def j60 : List Byte := [0x3e, 0xff, 0xe0]
theorem j60_0 : ∀ feat, Dec feat j60 0 (FV7z.mk .jmp 64 [gr 64 0] 3) := by dec_rfl

/-- The stretch at `4570`. -/
def p90 : List Byte := [
  0xbf, 0x02, 0x00, 0x00, 0x00]

theorem p90_0 : ∀ feat, Dec feat p90 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o90 : List Op := [
  Op.mov 32 7 (.i 2)]

theorem b90 (prof : Profile) : Blk prof p90 0 5 o90 :=
  .cons (p90_0 _) (OpI.mov (.i 2) (.inl rfl)) (by decide) <|
  .nil 5

def j61 : List Byte := [0xe9, 0x9b, 0xfd, 0xff, 0xff]
theorem j61_0 : ∀ feat, Dec feat j61 0 (FV7z.mk .jmp 64 [.rel 18446744073709551003] 5) := by dec_rfl

def j62 : List Byte := [0x0f, 0x84, 0xbe, 0xfd, 0xff, 0xff]
theorem j62_0 : ∀ feat, Dec feat j62 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551038] 6) := by dec_rfl

def j63 : List Byte := [0xe9, 0xbc, 0xfd, 0xff, 0xff]
theorem j63_0 : ∀ feat, Dec feat j63 0 (FV7z.mk .jmp 64 [.rel 18446744073709551036] 5) := by dec_rfl

/-- The stretch at `4598`. -/
def p91 : List Byte := [
  0x41, 0x83, 0xc9, 0xff, 0x83, 0xc1, 0x01, 0x41, 0xd3, 0xe1, 0x41, 0xf7, 0xd1, 0x41, 0x21, 0xd9]

theorem p91_0 : ∀ feat, Dec feat p91 0 (FV7z.mk .or 32 [gr 32 9, Src.opd 32 (.i 4294967295)] 4) := by dec_rfl
theorem p91_4 : ∀ feat, Dec feat p91 4 (FV7z.mk .add 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p91_7 : ∀ feat, Dec feat p91 7 (FV7z.mk .shl 32 [gr 32 9, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem p91_10 : ∀ feat, Dec feat p91 10 (FV7z.mk .not 32 [gr 32 9] 3) := by dec_rfl
theorem p91_13 : ∀ feat, Dec feat p91 13 (FV7z.mk .and 32 [gr 32 9, Src.opd 32 (.r 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o91 : List Op := [
  Op.or 32 9 (.i 4294967295),
  Op.add 32 1 (.i 1),
  Op.shl 9 (.r 1),
  Op.not32 9,
  Op.and 32 9 (.r 3)]

theorem b91 (prof : Profile) : Blk prof p91 0 16 o91 :=
  .cons (p91_0 _) (OpI.or (.i 4294967295) (.inl rfl)) (by decide) <|
  .cons (p91_4 _) (OpI.add (.i 1) (.inl rfl)) (by decide) <|
  .cons (p91_7 _) (OpI.shl (.r 1)) (by decide) <|
  .cons (p91_10 _) (OpI.not32) (by decide) <|
  .cons (p91_13 _) (OpI.and (.r 3) (.inl rfl)) (by decide) <|
  .nil 16

def j64 : List Byte := [0xe9, 0x6a, 0xff, 0xff, 0xff]
theorem j64_0 : ∀ feat, Dec feat j64 0 (FV7z.mk .jmp 64 [.rel 18446744073709551466] 5) := by dec_rfl

end FV7z.C103
