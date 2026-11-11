import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps8
import FV7z.Lemmas.BlkOps7
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `__register_atfork` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 8 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Raf
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x53, 0x48, 0x89, 0xd3, 0x48, 0x83, 0xec, 0x20, 0x48, 0x89, 0x7c, 0x24,
  0x08, 0x48, 0x89, 0x74, 0x24, 0x10, 0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_5 : ∀ feat, Dec feat p0 5 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 7] 5) := by dec_rfl
theorem p0_17 : ∀ feat, Dec feat p0 17 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 6] 5) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.nop,
  Op.push 3,
  Op.mov 64 3 (.r 2),
  Op.sub 64 4 (.i 32),
  Op.st 64 (some 4) none 1 8 7,
  Op.st 64 (some 4) none 1 16 6,
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x62da60 : Addr) fb 0 32 (o0 fb) :=
  .cons (p0_0 _) (((OpI.endbr).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_5 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.sub (.i 32) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_17 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_22 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p0_30 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 32

def j0 : List Byte := [0x0f, 0x85, 0xf2, 0x00, 0x00, 0x00]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 242] 6) := by dec_rfl

/-- The stretch at `38`. -/
def p1 : List Byte := [
  0xba, 0x01, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 2 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `50`. -/
def p2 : List Byte := [
  0x80, 0x3d, 0x8b, 0x64, 0x17, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [.mem (mrip 1533067 8), .imm 8 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmia 8 8011556 0]

theorem b2 (prof : Profile) : BlkA prof p2 (0x62da92 : Addr) 0 7 o2 :=
  .cons (p2_0 _) (OpIA.cmpmi8_rip (by decide)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x0f, 0x85, 0x81, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 129] 6) := by dec_rfl

/-- The stretch at `63`. -/
def p3 : List Byte := [
  0x66, 0x0f, 0x6f, 0x05, 0x29, 0x20, 0x0c, 0x00, 0xc6, 0x05, 0x76, 0x64, 0x17, 0x00, 0x01, 0x48,
  0x8d, 0x05, 0xa3, 0x64, 0x17, 0x00, 0x48, 0x89, 0x05, 0x94, 0x64, 0x17, 0x00, 0x31, 0xc0, 0x0f,
  0x29, 0x05, 0x7b, 0x64, 0x17, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk (.sse (SseMn.movdqa)) 16 [.xmm 0, .mem (mrip 794665 128)] 8) := by dec_rfl
theorem p3_8 : ∀ feat, Dec feat p3 8 (FV7z.mk .mov 8 [.mem (mrip 1533046 8), .imm 8 1] 7) := by dec_rfl
theorem p3_15 : ∀ feat, Dec feat p3 15 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 1533091 0)] 7) := by dec_rfl
theorem p3_22 : ∀ feat, Dec feat p3 22 (FV7z.mk .mov 64 [.mem (mrip 1533076 64), gr 64 0] 7) := by dec_rfl
theorem p3_29 : ∀ feat, Dec feat p3 29 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_31 : ∀ feat, Dec feat p3 31 (FV7z.mk (.sse (SseMn.movaps)) 32 [.mem (mrip 1533051 128), .xmm 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.vla 16 7273168,
  Op.stia 8 8011556 1,
  Op.mov 64 0 (.i 8011608),
  Op.sta 64 8011600 0,
  Op.xor 32 0 (.r 0),
  Op.vsa 16 8011584]

theorem b3 (prof : Profile) : BlkA prof p3 (0x62da9f : Addr) 0 38 o3 :=
  .cons (p3_0 _) (OpIA.vl_movdqa_rip (by decide) (by decide)) (by decide) <|
  .cons (p3_8 _) (OpIA.sti8_rip (by decide)) (by decide) <|
  .cons (p3_15 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p3_22 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p3_29 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p3_31 _) (OpIA.vs_movaps_rip (by decide) (by decide)) (by decide) <|
  .nil 38

/-- The stretch at `101`. -/
def p4 : List Byte := [
  0x49, 0x89, 0xc0, 0x48, 0x83, 0xc0, 0x01, 0x49, 0xc1, 0xe0, 0x05, 0x4c, 0x03, 0x05, 0x79, 0x64,
  0x17, 0x00, 0x48, 0x89, 0x05, 0x62, 0x64, 0x17, 0x00, 0x4d, 0x85, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .shl 64 [gr 64 8, Src.opd 8 (.i 5)] 4) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .add 64 [gr 64 8, .mem (mrip 1533049 64)] 7) := by dec_rfl
theorem p4_18 : ∀ feat, Dec feat p4 18 (FV7z.mk .mov 64 [.mem (mrip 1533026 64), gr 64 0] 7) := by dec_rfl
theorem p4_25 : ∀ feat, Dec feat p4 25 (FV7z.mk .test 64 [gr 64 8, Src.opd 64 (.r 8)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 8 (.r 0),
  Op.add 64 0 (.i 1),
  Op.shl64 8 (.i 5),
  Op.addma 64 8 8011600,
  Op.sta 64 8011584 0,
  Op.test 64 8 (.r 8)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x62dac5 : Addr) 0 28 o4 :=
  .cons (p4_0 _) ((OpI.mov (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p4_3 _) ((OpI.add (.i 1) (.inr rfl)).at _) (by decide) <|
  .cons (p4_7 _) ((OpI.shl64 (.i 5)).at _) (by decide) <|
  .cons (p4_11 _) (OpIA.addm_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p4_18 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p4_25 _) ((OpI.test (.r 8) (.inr rfl)).at _) (by decide) <|
  .nil 28

def j2 : List Byte := [0x74, 0x17]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `131`. -/
def p5 : List Byte := [
  0xf3, 0x0f, 0x7e, 0x44, 0x24, 0x08, 0x49, 0x89, 0x58, 0x10, 0x49, 0x89, 0x48, 0x18, 0x0f, 0x16,
  0x44, 0x24, 0x10, 0x41, 0x0f, 0x11, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk (.sse (SseMn.movq)) 32 [.xmm 0, .mem (mg (some 4) none 1 8 64)] 6) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 16 64), gr 64 3] 4) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .mov 64 [.mem (mg (some 8) none 1 24 64), gr 64 1] 4) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk (.sse (SseMn.movhps)) 32 [.xmm 0, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p5_19 : ∀ feat, Dec feat p5 19 (FV7z.mk (.sse (SseMn.movups)) 32 [.mem (mg (some 8) none 1 0 128), .xmm 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.vl 8 (some 4) none 1 8,
  Op.st 64 (some 8) none 1 16 3,
  Op.st 64 (some 8) none 1 24 1,
  Op.vl 8 (some 4) none 1 16,
  Op.vs 16 (some 8) none 1 0]

theorem b5 (prof : Profile) : Blk prof p5 0 23 o5 :=
  .cons (p5_0 _) (OpI.vl_movq) (by decide) <|
  .cons (p5_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_14 _) (OpI.vl_movhps) (by decide) <|
  .cons (p5_19 _) (OpI.vs_movups) (by decide) <|
  .nil 23

/-- The stretch at `154`. -/
def p6 : List Byte := [
  0x64, 0x8b, 0x04, 0x25, 0x18, 0x00, 0x00, 0x00, 0x85, 0xc0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mf none none 1 24 32)] 8) := by dec_rfl
theorem p6_8 : ∀ feat, Dec feat p6 8 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 (fb : Addr) : List Op := [
  Op.ldf fb 32 0 none none 1 24,
  Op.test 32 0 (.r 0)]

theorem b6 (prof : Profile) (fb : Addr) : BlkF prof p6 (0x62dafa : Addr) fb 0 10 (o6 fb) :=
  .cons (p6_0 _) (OpIF.ldf (.inl rfl)) (by decide) <|
  .cons (p6_8 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 10

def j3 : List Byte := [0x0f, 0x85, 0xa6, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 166] 6) := by dec_rfl

/-- The stretch at `177`. -/
def p7 : List Byte := [
  0x49, 0x83, 0xf8, 0x01, 0x19, 0xc0, 0x48, 0x83, 0xc4, 0x20, 0x83, 0xe0, 0x0c, 0x5b]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .cmp 64 [gr 64 8, Src.opd 64 (.i 1)] 4) := by dec_rfl
theorem p7_4 : ∀ feat, Dec feat p7 4 (FV7z.mk .sbb 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p7_6 : ∀ feat, Dec feat p7 6 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 12)] 3) := by dec_rfl
theorem p7_13 : ∀ feat, Dec feat p7 13 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.cmp 64 8 (.i 1),
  Op.sbb 32 0 (.r 0),
  Op.add 64 4 (.i 32),
  Op.and 32 0 (.i 12),
  Op.pop 3]

theorem b7 (prof : Profile) : Blk prof p7 0 14 o7 :=
  .cons (p7_0 _) (OpI.cmp (.i 1) (.inr rfl)) (by decide) <|
  .cons (p7_4 _) (OpI.sbb (.r 0) (.inl rfl)) (by decide) <|
  .cons (p7_6 _) (OpI.add (.i 32) (.inr rfl)) (by decide) <|
  .cons (p7_10 _) (OpI.and (.i 12) (.inl rfl)) (by decide) <|
  .cons (p7_13 _) (OpI.pop) (by decide) <|
  .nil 14

end FV7z.Raf
