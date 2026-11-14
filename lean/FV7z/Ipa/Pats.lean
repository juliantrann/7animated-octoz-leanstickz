import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps17
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `_dl_init_paths` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 14 of them) and each distinct jump (`j*`, 9) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ipa
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x55, 0x48, 0x8d, 0x0d, 0x94, 0x95, 0x0e, 0x00, 0x48, 0x8d, 0x15, 0x95,
  0x95, 0x0e, 0x00, 0x48, 0x89, 0xe5, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48,
  0x83, 0xec, 0x28, 0x48, 0x89, 0x7d, 0xb0, 0x48, 0x8b, 0x35, 0x32, 0xfc, 0x0f, 0x00, 0x48, 0x8b,
  0x3d, 0x23, 0xfc, 0x0f, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 955796 0)] 7) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 955797 0)] 7) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .push 64 [gr 64 15] 2) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_28 : ∀ feat, Dec feat p0 28 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_31 : ∀ feat, Dec feat p0 31 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 40)] 4) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551536 64), gr 64 7] 4) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .mov 64 [gr 64 6, .mem (mrip 1047602 64)] 7) := by dec_rfl
theorem p0_46 : ∀ feat, Dec feat p0 46 (FV7z.mk .mov 64 [gr 64 7, .mem (mrip 1047587 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 5,
  Op.mov 64 1 (.i 7937680),
  Op.mov 64 2 (.i 7937688),
  Op.mov 64 5 (.r 4),
  Op.push 15,
  Op.push 14,
  Op.push 13,
  Op.push 12,
  Op.push 3,
  Op.sub 64 4 (.i 40),
  Op.st 64 (some 5) none 1 18446744073709551536 7,
  Op.lda 64 6 8029520,
  Op.lda 64 7 8029512]

theorem b0 (prof : Profile) : BlkA prof p0 (0x6a88f0 : Addr) 0 53 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_5 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_12 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_19 _) ((OpI.mov (.r 4) (.inr rfl)).at _) (by decide) <|
  .cons (p0_22 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_24 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_26 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_28 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_30 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_31 _) ((OpI.sub (.i 40) (.inr rfl)).at _) (by decide) <|
  .cons (p0_35 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p0_39 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_46 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 53

/-- The stretch at `58`. -/
def p1 : List Byte := [
  0xbf, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x05, 0x6a, 0x95, 0x0e, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 40)] 5) := by dec_rfl
theorem p1_5 : ∀ feat, Dec feat p1 5 (FV7z.mk .mov 64 [.mem (mrip 955754 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 7 (.i 40),
  Op.sta 64 7937696 0]

theorem b1 (prof : Profile) : BlkA prof p1 (0x6a892a : Addr) 0 12 o1 :=
  .cons (p1_0 _) ((OpI.mov (.i 40) (.inl rfl)).at _) (by decide) <|
  .cons (p1_5 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 12

/-- The stretch at `75`. -/
def p2 : List Byte := [
  0x48, 0x89, 0x05, 0x3e, 0x95, 0x0e, 0x00, 0x48, 0x85, 0xc0]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mrip 955710 64), gr 64 0] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sta 64 7937664 0,
  Op.test 64 0 (.r 0)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x6a893b : Addr) 0 10 o2 :=
  .cons (p2_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j0 : List Byte := [0x0f, 0x84, 0xc0, 0x02, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 704] 6) := by dec_rfl

/-- The stretch at `91`. -/
def p3 : List Byte := [
  0x48, 0xb9, 0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0x49, 0x89, 0xc6, 0x48, 0x8b, 0x05,
  0x39, 0x95, 0x0e, 0x00, 0x4c, 0x8d, 0x2c, 0x85, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45, 0xc8,
  0x49, 0x8d, 0x55, 0x4f, 0x48, 0x89, 0xd0, 0x48, 0xf7, 0xe1, 0x48, 0xc1, 0xea, 0x05, 0x48, 0x8d,
  0x1c, 0x92, 0x48, 0x89, 0xdf, 0x48, 0xc1, 0xe7, 0x05]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 14757395258967641293)] 10) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .mov 64 [gr 64 14, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 955705 64)] 7) := by dec_rfl
theorem p3_20 : ∀ feat, Dec feat p3 20 (FV7z.mk .lea 64 [gr 64 13, .mem (mg none (some 0) 4 0 0)] 8) := by dec_rfl
theorem p3_28 : ∀ feat, Dec feat p3 28 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551560 64), gr 64 0] 4) := by dec_rfl
theorem p3_32 : ∀ feat, Dec feat p3 32 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 13) none 1 79 0)] 4) := by dec_rfl
theorem p3_36 : ∀ feat, Dec feat p3 36 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p3_39 : ∀ feat, Dec feat p3 39 (FV7z.mk .mul 64 [gr 64 1] 3) := by dec_rfl
theorem p3_42 : ∀ feat, Dec feat p3 42 (FV7z.mk .shr 64 [gr 64 2, Src.opd 8 (.i 5)] 4) := by dec_rfl
theorem p3_46 : ∀ feat, Dec feat p3 46 (FV7z.mk .lea 64 [gr 64 3, .mem (mg (some 2) (some 2) 4 0 0)] 4) := by dec_rfl
theorem p3_50 : ∀ feat, Dec feat p3 50 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 3)] 3) := by dec_rfl
theorem p3_53 : ∀ feat, Dec feat p3 53 (FV7z.mk .shl 64 [gr 64 7, Src.opd 8 (.i 5)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 64 1 (.i 14757395258967641293),
  Op.mov 64 14 (.r 0),
  Op.lda 64 0 7937688,
  Op.lea 64 13 none (some 0) 4 0,
  Op.st 64 (some 5) none 1 18446744073709551560 0,
  Op.lea 64 2 (some 13) none 1 79,
  Op.mov 64 0 (.r 2),
  Op.mul64 1,
  Op.shr64 2 (.i 5),
  Op.lea 64 3 (some 2) (some 2) 4 0,
  Op.mov 64 7 (.r 3),
  Op.shl64 7 (.i 5)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x6a894b : Addr) 0 57 o3 :=
  .cons (p3_0 _) ((OpI.mov (.i 14757395258967641293) (.inr rfl)).at _) (by decide) <|
  .cons (p3_10 _) ((OpI.mov (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p3_13 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p3_20 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p3_28 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p3_32 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p3_36 _) ((OpI.mov (.r 2) (.inr rfl)).at _) (by decide) <|
  .cons (p3_39 _) ((OpI.mul64).at _) (by decide) <|
  .cons (p3_42 _) ((OpI.shr64 (.i 5)).at _) (by decide) <|
  .cons (p3_46 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p3_50 _) ((OpI.mov (.r 3) (.inr rfl)).at _) (by decide) <|
  .cons (p3_53 _) ((OpI.shl64 (.i 5)).at _) (by decide) <|
  .nil 57

/-- The stretch at `153`. -/
def p4 : List Byte := [
  0x49, 0x89, 0x06, 0x49, 0x89, 0xc7, 0x48, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 64 [gr 64 15, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 64 (some 14) none 1 0 0,
  Op.mov 64 15 (.r 0),
  Op.test 64 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 9 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.test (.r 0) (.inr rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x0f, 0x84, 0x5e, 0x02, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 606] 6) := by dec_rfl

/-- The stretch at `168`. -/
def p5 : List Byte := [
  0x48, 0x89, 0x05, 0xd1, 0xfb, 0x0f, 0x00, 0x48, 0x8d, 0x05, 0xe9, 0xcd, 0x05, 0x00, 0x49, 0x83,
  0xc6, 0x08, 0x4c, 0x8d, 0x25, 0x0f, 0xd4, 0x05, 0x00, 0x49, 0x89, 0x47, 0x08, 0x48, 0x8d, 0x05,
  0x24, 0xd4, 0x05, 0x00, 0x49, 0x89, 0x47, 0x18, 0x48, 0x8d, 0x04, 0xdd, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x8d, 0x1d, 0x28, 0xd4, 0x05, 0x00, 0x48, 0x89, 0x45, 0xc0, 0x48, 0xf7, 0xd8, 0x48, 0x83,
  0x7d, 0xc8, 0x00, 0xc7, 0x05, 0xa3, 0x94, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x47,
  0x10, 0x00, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x47, 0x20, 0x16, 0x00, 0x00, 0x00, 0x48, 0x89, 0x45,
  0xb8]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [.mem (mrip 1047505 64), gr 64 0] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 380393 0)] 7) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .add 64 [gr 64 14, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p5_18 : ∀ feat, Dec feat p5 18 (FV7z.mk .lea 64 [gr 64 12, .mem (mrip 381967 0)] 7) := by dec_rfl
theorem p5_25 : ∀ feat, Dec feat p5 25 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p5_29 : ∀ feat, Dec feat p5 29 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 381988 0)] 7) := by dec_rfl
theorem p5_36 : ∀ feat, Dec feat p5 36 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 24 64), gr 64 0] 4) := by dec_rfl
theorem p5_40 : ∀ feat, Dec feat p5 40 (FV7z.mk .lea 64 [gr 64 0, .mem (mg none (some 3) 8 0 0)] 8) := by dec_rfl
theorem p5_48 : ∀ feat, Dec feat p5 48 (FV7z.mk .lea 64 [gr 64 3, .mem (mrip 381992 0)] 7) := by dec_rfl
theorem p5_55 : ∀ feat, Dec feat p5 55 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551552 64), gr 64 0] 4) := by dec_rfl
theorem p5_59 : ∀ feat, Dec feat p5 59 (FV7z.mk .neg 64 [gr 64 0] 3) := by dec_rfl
theorem p5_62 : ∀ feat, Dec feat p5 62 (FV7z.mk .cmp 64 [.mem (mg (some 5) none 1 18446744073709551560 64), .imm 64 0] 5) := by dec_rfl
theorem p5_67 : ∀ feat, Dec feat p5 67 (FV7z.mk .mov 32 [.mem (mrip 955555 32), .imm 32 0] 10) := by dec_rfl
theorem p5_77 : ∀ feat, Dec feat p5 77 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 16 64), .imm 64 0] 8) := by dec_rfl
theorem p5_85 : ∀ feat, Dec feat p5 85 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 32 64), .imm 64 22] 8) := by dec_rfl
theorem p5_93 : ∀ feat, Dec feat p5 93 (FV7z.mk .mov 64 [.mem (mg (some 5) none 1 18446744073709551544 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.sta 64 8029552 0,
  Op.mov 64 0 (.i 7362447),
  Op.add 64 14 (.i 8),
  Op.mov 64 12 (.i 7364032),
  Op.st 64 (some 15) none 1 8 0,
  Op.mov 64 0 (.i 7364064),
  Op.st 64 (some 15) none 1 24 0,
  Op.lea 64 0 none (some 3) 8 0,
  Op.mov 64 3 (.i 7364087),
  Op.st 64 (some 5) none 1 18446744073709551552 0,
  Op.neg 64 0,
  Op.cmpmi 64 (some 5) none 1 18446744073709551560 0,
  Op.stia 32 7937672 0,
  Op.sti 64 (some 15) none 1 16 0,
  Op.sti 64 (some 15) none 1 32 22,
  Op.st 64 (some 5) none 1 18446744073709551544 0]

theorem b5 (prof : Profile) : BlkA prof p5 (0x6a8998 : Addr) 0 97 o5 :=
  .cons (p5_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p5_7 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_14 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p5_18 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_25 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p5_29 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_36 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p5_40 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p5_48 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_55 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p5_59 _) ((OpI.neg (.inr rfl)).at _) (by decide) <|
  .cons (p5_62 _) ((OpI.cmpmi64).at _) (by decide) <|
  .cons (p5_67 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p5_77 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p5_85 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p5_93 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 97

def j2 : List Byte := [0x74, 0x0e]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `267`. -/
def p6 : List Byte := [
  0x49, 0x8d, 0x7f, 0x28, 0x4c, 0x89, 0xea, 0x31, 0xf6]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 15) none 1 40 0)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 13)] 3) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 7 (some 15) none 1 40,
  Op.mov 64 2 (.r 13),
  Op.xor 32 6 (.r 6)]

theorem b6 (prof : Profile) : Blk prof p6 0 9 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 9

/-- The stretch at `281`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x05, 0xc8, 0xd3, 0x05, 0x00, 0x4c, 0x39, 0xe0]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 381896 0)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 0 (.i 7364056),
  Op.cmp 64 0 (.r 12)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x6a8a09 : Addr) 0 10 o7 :=
  .cons (p7_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_7 _) ((OpI.cmp (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j3 : List Byte := [0x74, 0x5b]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 91] 2) := by dec_rfl

/-- The stretch at `293`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x45, 0xb8, 0x4c, 0x03, 0x7d, 0xc0, 0x49, 0x83, 0xc6, 0x08, 0x49, 0x83, 0xc4, 0x08,
  0x4d, 0x89, 0x7e, 0xf8, 0x4d, 0x89, 0x3c, 0x07, 0x48, 0x8d, 0x05, 0x5b, 0xcd, 0x05, 0x00, 0x49,
  0x89, 0x47, 0x08, 0x49, 0x8b, 0x04, 0x24, 0x80, 0x3b, 0x2f, 0x49, 0xc7, 0x47, 0x10, 0x00, 0x00,
  0x00, 0x00, 0x49, 0x89, 0x47, 0x20, 0x48, 0x8d, 0x44, 0x03, 0x01, 0x49, 0x89, 0x5f, 0x18]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 18446744073709551544 64)] 4) := by dec_rfl
theorem p8_4 : ∀ feat, Dec feat p8 4 (FV7z.mk .add 64 [gr 64 15, .mem (mg (some 5) none 1 18446744073709551552 64)] 4) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .add 64 [gr 64 14, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p8_12 : ∀ feat, Dec feat p8 12 (FV7z.mk .add 64 [gr 64 12, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p8_16 : ∀ feat, Dec feat p8 16 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 18446744073709551608 64), gr 64 15] 4) := by dec_rfl
theorem p8_20 : ∀ feat, Dec feat p8 20 (FV7z.mk .mov 64 [.mem (mg (some 15) (some 0) 1 0 64), gr 64 15] 4) := by dec_rfl
theorem p8_24 : ∀ feat, Dec feat p8 24 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 380251 0)] 7) := by dec_rfl
theorem p8_31 : ∀ feat, Dec feat p8 31 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 8 64), gr 64 0] 4) := by dec_rfl
theorem p8_35 : ∀ feat, Dec feat p8 35 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 12) none 1 0 64)] 4) := by dec_rfl
theorem p8_39 : ∀ feat, Dec feat p8 39 (FV7z.mk .cmp 8 [.mem (mg (some 3) none 1 0 8), .imm 8 47] 3) := by dec_rfl
theorem p8_42 : ∀ feat, Dec feat p8 42 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 16 64), .imm 64 0] 8) := by dec_rfl
theorem p8_50 : ∀ feat, Dec feat p8 50 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 32 64), gr 64 0] 4) := by dec_rfl
theorem p8_54 : ∀ feat, Dec feat p8 54 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 3) (some 0) 1 1 0)] 5) := by dec_rfl
theorem p8_59 : ∀ feat, Dec feat p8 59 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 24 64), gr 64 3] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 0 (some 5) none 1 18446744073709551544,
  Op.addm 64 15 (some 5) none 1 18446744073709551552,
  Op.add 64 14 (.i 8),
  Op.add 64 12 (.i 8),
  Op.st 64 (some 14) none 1 18446744073709551608 15,
  Op.st 64 (some 15) (some 0) 1 0 15,
  Op.mov 64 0 (.i 7362447),
  Op.st 64 (some 15) none 1 8 0,
  Op.ld 64 0 (some 12) none 1 0,
  Op.cmpmi 8 (some 3) none 1 0 47,
  Op.sti 64 (some 15) none 1 16 0,
  Op.st 64 (some 15) none 1 32 0,
  Op.lea 64 0 (some 3) (some 0) 1 1,
  Op.st 64 (some 15) none 1 24 3]

theorem b8 (prof : Profile) : BlkA prof p8 (0x6a8a15 : Addr) 0 63 o8 :=
  .cons (p8_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p8_4 _) ((OpI.addm (.inr rfl)).at _) (by decide) <|
  .cons (p8_8 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p8_12 _) ((OpI.add (.i 8) (.inr rfl)).at _) (by decide) <|
  .cons (p8_16 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p8_20 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p8_24 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p8_31 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p8_35 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p8_39 _) ((OpI.cmpmi (.inl rfl)).at _) (by decide) <|
  .cons (p8_42 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p8_50 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p8_54 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p8_59 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 63

def j4 : List Byte := [0x0f, 0x85, 0x7d, 0x01, 0x00, 0x00]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 5) 64 [.rel 381] 6) := by dec_rfl

/-- The stretch at `362`. -/
def p9 : List Byte := [
  0x48, 0x83, 0x7d, 0xc8, 0x00, 0x48, 0x89, 0xc3]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .cmp 64 [.mem (mg (some 5) none 1 18446744073709551560 64), .imm 64 0] 5) := by dec_rfl
theorem p9_5 : ∀ feat, Dec feat p9 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.cmpmi 64 (some 5) none 1 18446744073709551560 0,
  Op.mov 64 3 (.r 0)]

theorem b9 (prof : Profile) : Blk prof p9 0 8 o9 :=
  .cons (p9_0 _) (OpI.cmpmi64) (by decide) <|
  .cons (p9_5 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 8

def j5 : List Byte := [0x75, 0x97]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551511] 2) := by dec_rfl

/-- The stretch at `372`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0x05, 0x6d, 0xd3, 0x05, 0x00, 0x4c, 0x39, 0xe0]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 381805 0)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 0 (.i 7364056),
  Op.cmp 64 0 (.r 12)]

theorem b10 (prof : Profile) : BlkA prof p10 (0x6a8a64 : Addr) 0 10 o10 :=
  .cons (p10_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_7 _) ((OpI.cmp (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 10

def j6 : List Byte := [0x75, 0xa5]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551525] 2) := by dec_rfl

/-- The stretch at `384`. -/
def p11 : List Byte := [
  0x48, 0x83, 0x7d, 0xb0, 0x00, 0x49, 0xc7, 0x07, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x05, 0xc1,
  0xc1, 0x0f, 0x00, 0x1a, 0x00, 0x00, 0x00, 0x49, 0xc7, 0x06, 0x00, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .cmp 64 [.mem (mg (some 5) none 1 18446744073709551536 64), .imm 64 0] 5) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .mov 64 [.mem (mg (some 15) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p11_12 : ∀ feat, Dec feat p11 12 (FV7z.mk .mov 64 [.mem (mrip 1032641 64), .imm 64 26] 11) := by dec_rfl
theorem p11_23 : ∀ feat, Dec feat p11 23 (FV7z.mk .mov 64 [.mem (mg (some 14) none 1 0 64), .imm 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.cmpmi 64 (some 5) none 1 18446744073709551536 0,
  Op.sti 64 (some 15) none 1 0 0,
  Op.stia 64 8014920 26,
  Op.sti 64 (some 14) none 1 0 0]

theorem b11 (prof : Profile) : BlkA prof p11 (0x6a8a70 : Addr) 0 30 o11 :=
  .cons (p11_0 _) ((OpI.cmpmi64).at _) (by decide) <|
  .cons (p11_5 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p11_12 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p11_23 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 30

def j7 : List Byte := [0x74, 0x09]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `416`. -/
def p12 : List Byte := [
  0x48, 0x8b, 0x45, 0xb0, 0x80, 0x38, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 5) none 1 18446744073709551536 64)] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .cmp 8 [.mem (mg (some 0) none 1 0 8), .imm 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.ld 64 0 (some 5) none 1 18446744073709551536,
  Op.cmpmi 8 (some 0) none 1 0 0]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p12_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j8 : List Byte := [0x75, 0x1a]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 5) 64 [.rel 26] 2) := by dec_rfl

/-- The stretch at `425`. -/
def p13 : List Byte := [
  0x48, 0xc7, 0x05, 0x0c, 0x94, 0x0e, 0x00, 0xff, 0xff, 0xff, 0xff, 0x48, 0x8d, 0x65, 0xd8, 0x5b,
  0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e, 0x41, 0x5f, 0x5d]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mrip 955404 64), .imm 64 18446744073709551615] 11) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .lea 64 [gr 64 4, .mem (mg (some 5) none 1 18446744073709551576 0)] 4) := by dec_rfl
theorem p13_15 : ∀ feat, Dec feat p13 15 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p13_16 : ∀ feat, Dec feat p13 16 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p13_18 : ∀ feat, Dec feat p13 18 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p13_20 : ∀ feat, Dec feat p13 20 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl
theorem p13_22 : ∀ feat, Dec feat p13 22 (FV7z.mk .pop 64 [gr 64 15] 2) := by dec_rfl
theorem p13_24 : ∀ feat, Dec feat p13 24 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.stia 64 7937712 18446744073709551615,
  Op.lea 64 4 (some 5) none 1 18446744073709551576,
  Op.pop 3,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14,
  Op.pop 15,
  Op.pop 5]

theorem b13 (prof : Profile) : BlkA prof p13 (0x6a8a99 : Addr) 0 25 o13 :=
  .cons (p13_0 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p13_11 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p13_15 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_16 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_18 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_20 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_22 _) ((OpI.pop).at _) (by decide) <|
  .cons (p13_24 _) ((OpI.pop).at _) (by decide) <|
  .nil 25

end FV7z.Ipa
