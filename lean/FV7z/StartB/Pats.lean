import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__libc_start_main` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 20 of them) and each distinct jump (`j*`, 11) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.StartB
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `896`. -/
def p0 : List Byte := [
  0x8b, 0x05, 0xf2, 0x51, 0x19, 0x00, 0x64, 0x89, 0x04, 0x25, 0x48, 0x00, 0x00, 0x00, 0x48, 0x8b,
  0x05, 0xcb, 0xe8, 0x17, 0x00, 0x48, 0x8b, 0x00, 0x30, 0xc0, 0x64, 0x48, 0x89, 0x04, 0x25, 0x28,
  0x00, 0x00, 0x00, 0x83, 0x3d, 0xd6, 0x05, 0x18, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1659378 32)] 6) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .mov 32 [.mem (mf none none 1 72 32), gr 32 0] 8) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1566923 64)] 7) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .xor 8 [gr 8 0, Src.opd 8 (.r 0)] 2) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [.mem (mf none none 1 40 64), gr 64 0] 9) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .cmp 32 [.mem (mrip 1574358 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.lda 32 0 8029624,
  Op.stf fb 32 none none 1 72 0,
  Op.lda 64 0 7937184,
  Op.ld 64 0 (some 0) none 1 0,
  Op.xor8 0 (.r 0),
  Op.stf fb 64 none none 1 40 0,
  Op.cmpmia 32 7944640 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x6133c0 : Addr) fb 0 42 (o0 fb) :=
  .cons (p0_0 _) ((OpIA.ld_rip (.inl rfl) (by decide)).fs _) (by decide) <|
  .cons (p0_6 _) (OpIF.stf (.inl rfl)) (by decide) <|
  .cons (p0_14 _) ((OpIA.ld_rip (.inr rfl) (by decide)).fs _) (by decide) <|
  .cons (p0_21 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_24 _) (((OpI.xor8 (.r 0)).at _).fs _) (by decide) <|
  .cons (p0_26 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p0_35 _) ((OpIA.cmpmi_rip (.inl rfl) (by decide)).fs _) (by decide) <|
  .nil 42

def j0 : List Byte := [0x0f, 0x84, 0x4e, 0x02, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 590] 6) := by dec_rfl

/-- The stretch at `944`. -/
def p1 : List Byte := [
  0x48, 0x83, 0x3d, 0xb8, 0xeb, 0x17, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [.mem (mrip 1567672 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmia 64 7937968 0]

theorem b1 (prof : Profile) : BlkA prof p1 (0x6133f0 : Addr) 0 8 o1 :=
  .cons (p1_0 _) (OpIA.cmpmi_rip (.inr rfl) (by decide)) (by decide) <|
  .nil 8

def j1 : List Byte := [0x74, 0x05]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 5] 2) := by dec_rfl

/-- The stretch at `959`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x05, 0x9a, 0xe8, 0x17, 0x00, 0x48, 0x8b, 0x40, 0x08, 0x64, 0x48, 0x89, 0x04, 0x25,
  0x30, 0x00, 0x00, 0x00, 0x4d, 0x85, 0xed]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1566874 64)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 8 64)] 4) := by dec_rfl
theorem p2_11 : ∀ feat, Dec feat p2 11 (FV7z.mk .mov 64 [.mem (mf none none 1 48 64), gr 64 0] 9) := by dec_rfl
theorem p2_20 : ∀ feat, Dec feat p2 20 (FV7z.mk .test 64 [gr 64 13, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.lda 64 0 7937184,
  Op.ld 64 0 (some 0) none 1 8,
  Op.stf fb 64 none none 1 48 0,
  Op.test 64 13 (.r 13)]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x6133ff : Addr) fb 0 23 (o2 fb) :=
  .cons (p2_0 _) ((OpIA.ld_rip (.inr rfl) (by decide)).fs _) (by decide) <|
  .cons (p2_7 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_11 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p2_20 _) (((OpI.test (.r 13) (.inr rfl)).at _).fs _) (by decide) <|
  .nil 23

def j2 : List Byte := [0x74, 0x0c]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `984`. -/
def p3 : List Byte := [
  0x31, 0xd2, 0x31, 0xf6, 0x4c, 0x89, 0xef]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p3_4 : ∀ feat, Dec feat p3 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 13)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.xor 32 6 (.r 6),
  Op.mov 64 7 (.r 13)]

theorem b3 (prof : Profile) : Blk prof p3 0 7 o3 :=
  .cons (p3_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p3_2 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p3_4 _) (OpI.mov (.r 13) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `996`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x15, 0x6d, 0x13, 0x19, 0x00, 0x48, 0x8b, 0x74, 0x24, 0x10, 0x8b, 0x7c, 0x24, 0x0c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip 1643373 64)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p4_12 : ∀ feat, Dec feat p4 12 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.lda 64 2 8013720,
  Op.ld 64 6 (some 4) none 1 16,
  Op.ld 32 7 (some 4) none 1 12]

theorem b4 (prof : Profile) : BlkA prof p4 (0x613424 : Addr) 0 16 o4 :=
  .cons (p4_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p4_7 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p4_12 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .nil 16

/-- The stretch at `1017`. -/
def p5 : List Byte := [
  0x4d, 0x85, 0xe4]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .test 64 [gr 64 12, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.test 64 12 (.r 12)]

theorem b5 (prof : Profile) : Blk prof p5 0 3 o5 :=
  .cons (p5_0 _) (OpI.test (.r 12) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `1022`. -/
def p6 : List Byte := [
  0x31, 0xd2, 0x31, 0xf6, 0x4c, 0x89, 0xe7]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p6_2 : ∀ feat, Dec feat p6 2 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.xor 32 6 (.r 6),
  Op.mov 64 7 (.r 12)]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p6_2 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p6_4 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `1034`. -/
def p7 : List Byte := [
  0x83, 0x3d, 0x8f, 0xe8, 0x17, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 32 [.mem (mrip 1566863 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmpmia 32 7937248 0]

theorem b7 (prof : Profile) : BlkA prof p7 (0x61344a : Addr) 0 7 o7 :=
  .cons (p7_0 _) (OpIA.cmpmi_rip (.inl rfl) (by decide)) (by decide) <|
  .nil 7

def j3 : List Byte := [0x0f, 0x85, 0xa2, 0x03, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 930] 6) := by dec_rfl

/-- The stretch at `1047`. -/
def p8 : List Byte := [
  0x48, 0x85, 0xed]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .test 64 [gr 64 5, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.test 64 5 (.r 5)]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.test (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x74, 0x12]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `1052`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x15, 0x35, 0x13, 0x19, 0x00, 0x48, 0x8b, 0x74, 0x24, 0x10, 0x8b, 0x7c, 0x24, 0x0c]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip 1643317 64)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p9_12 : ∀ feat, Dec feat p9 12 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lda 64 2 8013720,
  Op.ld 64 6 (some 4) none 1 16,
  Op.ld 32 7 (some 4) none 1 12]

theorem b9 (prof : Profile) : BlkA prof p9 (0x61345c : Addr) 0 16 o9 :=
  .cons (p9_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p9_7 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p9_12 _) ((OpI.ld (.inl rfl)).at _) (by decide) <|
  .nil 16

/-- The stretch at `1070`. -/
def p10 : List Byte := [
  0x31, 0xff, 0x31, 0xf6]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .xor 32 [gr 32 7, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.xor 32 7 (.r 7),
  Op.xor 32 6 (.r 6)]

theorem b10 (prof : Profile) : Blk prof p10 0 4 o10 :=
  .cons (p10_0 _) (OpI.xor (.r 7) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `1079`. -/
def p11 : List Byte := [
  0x48, 0x8d, 0x7c, 0x24, 0x70]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 4) none 1 112 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.lea 64 7 (some 4) none 1 112]

theorem b11 (prof : Profile) : Blk prof p11 0 5 o11 :=
  .cons (p11_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `1089`. -/
def p12 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x85, 0xc0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p12_4 : ∀ feat, Dec feat p12 4 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.nop,
  Op.test 32 0 (.r 0)]

theorem b12 (prof : Profile) : Blk prof p12 0 6 o12 :=
  .cons (p12_0 _) (OpI.endbr) (by decide) <|
  .cons (p12_4 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 6

def j5 : List Byte := [0x75, 0x4e]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 78] 2) := by dec_rfl

/-- The stretch at `1097`. -/
def p13 : List Byte := [
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x00, 0x03, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xb8, 0x00, 0x00,
  0x00, 0x64, 0x48, 0x8b, 0x04, 0x25, 0xf8, 0x02, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xc0, 0x00,
  0x00, 0x00, 0x48, 0x8d, 0x44, 0x24, 0x70, 0x64, 0x48, 0x89, 0x04, 0x25, 0x00, 0x03, 0x00, 0x00,
  0x48, 0x8b, 0x15, 0xd8, 0x12, 0x19, 0x00, 0x8b, 0x7c, 0x24, 0x0c, 0x48, 0x8b, 0x74, 0x24, 0x10,
  0x48, 0x8b, 0x44, 0x24, 0x18]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 768 64)] 9) := by dec_rfl
theorem p13_9 : ∀ feat, Dec feat p13 9 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 184 64), gr 64 0] 8) := by dec_rfl
theorem p13_17 : ∀ feat, Dec feat p13 17 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 760 64)] 9) := by dec_rfl
theorem p13_26 : ∀ feat, Dec feat p13 26 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 192 64), gr 64 0] 8) := by dec_rfl
theorem p13_34 : ∀ feat, Dec feat p13 34 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 4) none 1 112 0)] 5) := by dec_rfl
theorem p13_39 : ∀ feat, Dec feat p13 39 (FV7z.mk .mov 64 [.mem (mf none none 1 768 64), gr 64 0] 9) := by dec_rfl
theorem p13_48 : ∀ feat, Dec feat p13 48 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip 1643224 64)] 7) := by dec_rfl
theorem p13_55 : ∀ feat, Dec feat p13 55 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 4) none 1 12 32)] 4) := by dec_rfl
theorem p13_59 : ∀ feat, Dec feat p13 59 (FV7z.mk .mov 64 [gr 64 6, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p13_64 : ∀ feat, Dec feat p13 64 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 (fb : Addr) : List Op := [
  Op.ldf fb 64 0 none none 1 768,
  Op.st 64 (some 4) none 1 184 0,
  Op.ldf fb 64 0 none none 1 760,
  Op.st 64 (some 4) none 1 192 0,
  Op.lea 64 0 (some 4) none 1 112,
  Op.stf fb 64 none none 1 768 0,
  Op.lda 64 2 8013720,
  Op.ld 32 7 (some 4) none 1 12,
  Op.ld 64 6 (some 4) none 1 16,
  Op.ld 64 0 (some 4) none 1 24]

theorem b13 (prof : Profile) (fb : Addr) : BlkF prof p13 (0x613489 : Addr) fb 0 69 (o13 fb) :=
  .cons (p13_0 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p13_9 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p13_17 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p13_26 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p13_34 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p13_39 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p13_48 _) ((OpIA.ld_rip (.inr rfl) (by decide)).fs _) (by decide) <|
  .cons (p13_55 _) (((OpI.ld (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p13_59 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p13_64 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .nil 69

/-- The stretch at `1168`. -/
def p14 : List Byte := [
  0x89, 0xc7]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 32 7 (.r 0)]

theorem b14 (prof : Profile) : Blk prof p14 0 2 o14 :=
  .cons (p14_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `1539`. -/
def p15 : List Byte := [
  0x85, 0xc0]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.test 32 0 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 2 o15 :=
  .cons (p15_0 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j6 : List Byte := [0x0f, 0x88, 0x2b, 0x01, 0x00, 0x00]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 8) 64 [.rel 299] 6) := by dec_rfl

/-- The stretch at `1547`. -/
def p16 : List Byte := [
  0x8b, 0x15, 0xcf, 0x4e, 0x19, 0x00, 0x85, 0xd2]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip 1658575 32)] 6) := by dec_rfl
theorem p16_6 : ∀ feat, Dec feat p16 6 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.lda 32 2 8029472,
  Op.test 32 2 (.r 2)]

theorem b16 (prof : Profile) : BlkA prof p16 (0x61364b : Addr) 0 8 o16 :=
  .cons (p16_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p16_6 _) ((OpI.test (.r 2) (.inl rfl)).at _) (by decide) <|
  .nil 8

def j7 : List Byte := [0x0f, 0x85, 0x10, 0x01, 0x00, 0x00]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk (.jcc 5) 64 [.rel 272] 6) := by dec_rfl

/-- The stretch at `1561`. -/
def p17 : List Byte := [
  0x89, 0x05, 0xc1, 0x4e, 0x19, 0x00]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .mov 32 [.mem (mrip 1658561 32), gr 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.sta 32 8029472 0]

theorem b17 (prof : Profile) : BlkA prof p17 (0x613659 : Addr) 0 6 o17 :=
  .cons (p17_0 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 6

/-- The stretch at `1567`. -/
def p18 : List Byte := [
  0x3d, 0xff, 0x01, 0x03, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 197119)] 5) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.cmp 32 0 (.i 197119)]

theorem b18 (prof : Profile) : Blk prof p18 0 5 o18 :=
  .cons (p18_0 _) (OpI.cmp (.i 197119) (.inl rfl)) (by decide) <|
  .nil 5

def j8 : List Byte := [0x0f, 0x8f, 0x86, 0xfd, 0xff, 0xff]
theorem j8_0 : ∀ feat, Dec feat j8 0 (FV7z.mk (.jcc 15) 64 [.rel 18446744073709550982] 6) := by dec_rfl

/-- The stretch at `1833`. -/
def p19 : List Byte := [
  0x39, 0xc2]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.cmp 32 2 (.r 0)]

theorem b19 (prof : Profile) : Blk prof p19 0 2 o19 :=
  .cons (p19_0 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j9 : List Byte := [0x0f, 0x86, 0xee, 0xfe, 0xff, 0xff]
theorem j9_0 : ∀ feat, Dec feat j9 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551342] 6) := by dec_rfl

def j10 : List Byte := [0xe9, 0xe3, 0xfe, 0xff, 0xff]
theorem j10_0 : ∀ feat, Dec feat j10 0 (FV7z.mk .jmp 64 [.rel 18446744073709551331] 5) := by dec_rfl

end FV7z.StartB
