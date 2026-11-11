import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_start_main` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 7 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Start
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x56, 0x31, 0xc0, 0x41, 0x55, 0x4d, 0x89, 0xcd, 0x41, 0x54, 0x4d,
  0x89, 0xc4, 0x55, 0x48, 0x89, 0xcd, 0x53, 0x48, 0x81, 0xec, 0xe0, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x54, 0x24, 0x10, 0x48, 0xc7, 0xc2, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x7c, 0x24, 0x18, 0x89,
  0x74, 0x24, 0x0c, 0x48, 0x85, 0xd2]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 64 [gr 64 13, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_23 : ∀ feat, Dec feat p0 23 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 224)] 7) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 2] 5) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 0)] 7) := by dec_rfl
theorem p0_42 : ∀ feat, Dec feat p0 42 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 7] 5) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 12 32), gr 32 6] 4) := by dec_rfl
theorem p0_51 : ∀ feat, Dec feat p0 51 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 14,
  Op.xor 32 0 (.r 0),
  Op.push 13,
  Op.mov 64 13 (.r 9),
  Op.push 12,
  Op.mov 64 12 (.r 8),
  Op.push 5,
  Op.mov 64 5 (.r 1),
  Op.push 3,
  Op.sub 64 4 (.i 224),
  Op.st 64 (some 4) none 1 16 2,
  Op.mov 64 2 (.i 0),
  Op.st 64 (some 4) none 1 24 7,
  Op.st 32 (some 4) none 1 12 6,
  Op.test 64 2 (.r 2)]

theorem b0 (prof : Profile) : Blk prof p0 0 54 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.push) (by decide) <|
  .cons (p0_6 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_8 _) (OpI.push) (by decide) <|
  .cons (p0_10 _) (OpI.mov (.r 9) (.inr rfl)) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.mov (.r 8) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.push) (by decide) <|
  .cons (p0_19 _) (OpI.mov (.r 1) (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.push) (by decide) <|
  .cons (p0_23 _) (OpI.sub (.i 224) (.inr rfl)) (by decide) <|
  .cons (p0_30 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_35 _) (OpI.mov (.i 0) (.inr rfl)) (by decide) <|
  .cons (p0_42 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_47 _) (OpI.st (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p0_51 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 54

def j0 : List Byte := [0x74, 0x09]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `56`. -/
def p1 : List Byte := [
  0x8b, 0x12, 0x31, 0xc0, 0x85, 0xd2, 0x0f, 0x94, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 2) none 1 0 32)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 2 (some 2) none 1 0,
  Op.xor 32 0 (.r 0),
  Op.test 32 2 (.r 2),
  Op.setcc 4 0]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_2 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.setcc) (by decide) <|
  .nil 9

/-- The stretch at `65`. -/
def p2 : List Byte := [
  0x89, 0x05, 0x39, 0x09, 0x18, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [.mem (mrip 1575225 32), gr 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sta 32 7944640 0]

theorem b2 (prof : Profile) : BlkA prof p2 (0x613081 : Addr) 0 6 o2 :=
  .cons (p2_0 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 6

/-- The stretch at `76`. -/
def p3 : List Byte := [
  0x48, 0x63, 0x44, 0x24, 0x0c, 0x48, 0x8b, 0x5c, 0x24, 0x10, 0x48, 0x8d, 0x7c, 0xc3, 0x08, 0x48,
  0x8b, 0x84, 0x24, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0x3d, 0xee, 0x16, 0x19, 0x00, 0x48, 0x89,
  0x05, 0xff, 0xeb, 0x17, 0x00, 0x0f, 0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 4) none 1 12 32)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 64 [gr 64 3, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) (some 0) 8 8 0)] 5) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 272 64)] 8) := by dec_rfl
theorem p3_23 : ∀ feat, Dec feat p3 23 (FV7z.mk .mov 64 [.mem (mrip 1644270 64), gr 64 7] 7) := by dec_rfl
theorem p3_30 : ∀ feat, Dec feat p3 30 (FV7z.mk .mov 64 [.mem (mrip 1567743 64), gr 64 0] 7) := by dec_rfl
theorem p3_37 : ∀ feat, Dec feat p3 37 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ldsx 0 (some 4) none 1 12,
  Op.ld 64 3 (some 4) none 1 16,
  Op.lea 64 7 (some 3) (some 0) 8 8,
  Op.ld 64 0 (some 4) none 1 272,
  Op.sta 64 8013720 7,
  Op.sta 64 7937200 0,
  Op.nop]

theorem b3 (prof : Profile) : BlkA prof p3 (0x61308c : Addr) 0 44 o3 :=
  .cons (p3_0 _) ((OpI.ldsx).at _) (by decide) <|
  .cons (p3_5 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p3_10 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p3_15 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p3_23 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p3_30 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p3_37 _) ((OpI.nop).at _) (by decide) <|
  .nil 44

/-- The stretch at `120`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc7, 0x08, 0x48, 0x83, 0x7f, 0xf8, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 18446744073709551608 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 7 (.i 8),
  Op.cmpmi 64 (some 7) none 1 18446744073709551608 0]

theorem b4 (prof : Profile) : Blk prof p4 0 9 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.cmpmi64) (by decide) <|
  .nil 9

def j1 : List Byte := [0x75, 0xf5]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551605] 2) := by dec_rfl

/-- The stretch at `136`. -/
def p5 : List Byte := [
  0x48, 0x83, 0x3d, 0xb0, 0x54, 0x19, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 64 [.mem (mrip 1660080 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmpmia 64 8029568 0]

theorem b5 (prof : Profile) : BlkA prof p5 (0x6130c8 : Addr) 0 8 o5 :=
  .cons (p5_0 _) (OpIA.cmpmi_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 8

def j2 : List Byte := [0x75, 0x30]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 48] 2) := by dec_rfl

/-- The stretch at `199`. -/
def p6 : List Byte := [
  0x48, 0x8b, 0x3d, 0x8a, 0x16, 0x19, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mrip 1644170 64)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lda 64 7 8013720]

theorem b6 (prof : Profile) : BlkA prof p6 (0x613107 : Addr) 0 7 o6 :=
  .cons (p6_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 7

end FV7z.Start
