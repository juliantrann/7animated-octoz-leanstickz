import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__pthread_once_slow` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 14 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pos
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x54, 0x41, 0xb9, 0xca, 0x00, 0x00, 0x00, 0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x55, 0x48,
  0x89, 0xfd, 0x53, 0x48, 0x89, 0xf3, 0x48, 0x83, 0xec, 0x30, 0x64, 0x48, 0x8b, 0x04, 0x25, 0x28,
  0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x31, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .mov 32 [gr 32 9, Src.opd 32 (.i 202)] 6) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.i 1)] 6) := by dec_rfl
theorem p0_14 : ∀ feat, Dec feat p0 14 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_35 : ∀ feat, Dec feat p0 35 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 40 64), gr 64 0] 5) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 12,
  Op.mov 32 9 (.i 202),
  Op.mov 32 8 (.i 1),
  Op.push 5,
  Op.mov 64 5 (.r 7),
  Op.push 3,
  Op.mov 64 3 (.r 6),
  Op.sub 64 4 (.i 48),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 40 0,
  Op.xor 32 0 (.r 0)]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5fee60 : Addr) fb 0 42 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_2 _) (((OpI.mov (.i 202) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.mov (.i 1) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_14 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_15 _) (((OpI.mov (.r 7) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_18 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_19 _) (((OpI.mov (.r 6) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_22 _) (((OpI.sub (.i 48) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_26 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_35 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 42

/-- The stretch at `42`. -/
def p1 : List Byte := [
  0x8b, 0x45, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 5) none 1 0 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 0 (some 5) none 1 0]

theorem b1 (prof : Profile) : Blk prof p1 0 3 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `45`. -/
def p2 : List Byte := [
  0xa8, 0x02]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.test 8 0 (.i 2)]

theorem b2 (prof : Profile) : Blk prof p2 0 2 o2 :=
  .cons (p2_0 _) (OpI.test8 (.i 2)) (by decide) <|
  .nil 2

def j0 : List Byte := [0x74, 0x1f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 31] 2) := by dec_rfl

/-- The stretch at `49`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x28, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 40 64)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 40,
  Op.xormf fb 64 0 none none 1 40]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x5fee91 : Addr) fb 0 14 (o3 fb) :=
  .cons (p3_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x0f, 0x85, 0xbb, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 187] 6) := by dec_rfl

/-- The stretch at `69`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x30, 0x31, 0xc0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p4_6 : ∀ feat, Dec feat p4 6 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 48),
  Op.xor 32 0 (.r 0),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b4 (prof : Profile) : Blk prof p4 0 10 o4 :=
  .cons (p4_0 _) (OpI.add (.i 48) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p4_6 _) (OpI.pop) (by decide) <|
  .cons (p4_7 _) (OpI.pop) (by decide) <|
  .cons (p4_8 _) (OpI.pop) (by decide) <|
  .nil 10

/-- The stretch at `80`. -/
def p5 : List Byte := [
  0x8b, 0x15, 0x6a, 0x8f, 0x1a, 0x00, 0x83, 0xca, 0x01]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mrip 1740650 32)] 6) := by dec_rfl
theorem p5_6 : ∀ feat, Dec feat p5 6 (FV7z.mk .or 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.lda 32 2 8027680,
  Op.or 32 2 (.i 1)]

theorem b5 (prof : Profile) : BlkA prof p5 (0x5feeb0 : Addr) 0 9 o5 :=
  .cons (p5_0 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p5_6 _) ((OpI.or (.i 1) (.inl rfl)).at _) (by decide) <|
  .nil 9

def j2 : List Byte := [0x75, 0xcd]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551565] 2) := by dec_rfl

/-- The stretch at `96`. -/
def p6 : List Byte := [
  0x39, 0xc2]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.cmp 32 2 (.r 0)]

theorem b6 (prof : Profile) : Blk prof p6 0 2 o6 :=
  .cons (p6_0 _) (OpI.cmp (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j3 : List Byte := [0x75, 0x44]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 68] 2) := by dec_rfl

/-- The stretch at `100`. -/
def p7 : List Byte := [
  0xa8, 0x01]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .test 8 [gr 8 0, Src.opd 8 (.i 1)] 2) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.test 8 0 (.i 1)]

theorem b7 (prof : Profile) : Blk prof p7 0 2 o7 :=
  .cons (p7_0 _) (OpI.test8 (.i 1)) (by decide) <|
  .nil 2

def j4 : List Byte := [0x74, 0x40]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 64] 2) := by dec_rfl

/-- The stretch at `104`. -/
def p8 : List Byte := [
  0x45, 0x31, 0xd2, 0xbe, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xef, 0x44, 0x89, 0xc8]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .xor 32 [gr 32 10, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 128)] 5) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 9)] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.xor 32 10 (.r 10),
  Op.mov 32 6 (.i 128),
  Op.mov 64 7 (.r 5),
  Op.mov 32 0 (.r 9)]

theorem b8 (prof : Profile) : Blk prof p8 0 14 o8 :=
  .cons (p8_0 _) (OpI.xor (.r 10) (.inl rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.mov (.i 128) (.inl rfl)) (by decide) <|
  .cons (p8_8 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p8_11 _) (OpI.mov (.r 9) (.inl rfl)) (by decide) <|
  .nil 14

/-- The stretch at `168`. -/
def p9 : List Byte := [
  0x49, 0x89, 0xe4, 0x48, 0x89, 0xea, 0x48, 0x8d, 0x35, 0x5b, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe7]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 12, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p9_3 : ∀ feat, Dec feat p9 3 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p9_6 : ∀ feat, Dec feat p9 6 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 91 0)] 7) := by dec_rfl
theorem p9_13 : ∀ feat, Dec feat p9 13 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 12 (.r 4),
  Op.mov 64 2 (.r 5),
  Op.mov 64 6 (.i 6287216),
  Op.mov 64 7 (.r 12)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x5fef08 : Addr) 0 16 o9 :=
  .cons (p9_0 _) ((OpI.mov (.r 4) (.inr rfl)).at _) (by decide) <|
  .cons (p9_3 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p9_6 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_13 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .nil 16

/-- The stretch at `191`. -/
def p10 : List Byte := [
  0x31, 0xf6, 0x4c, 0x89, 0xe7]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .xor 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p10_2 : ∀ feat, Dec feat p10 2 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.xor 32 6 (.r 6),
  Op.mov 64 7 (.r 12)]

theorem b10 (prof : Profile) : Blk prof p10 0 5 o10 :=
  .cons (p10_0 _) (OpI.xor (.r 6) (.inl rfl)) (by decide) <|
  .cons (p10_2 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 5

/-- The stretch at `201`. -/
def p11 : List Byte := [
  0x45, 0x31, 0xd2, 0xba, 0xff, 0xff, 0xff, 0x7f, 0x48, 0x89, 0xef, 0xbe, 0x81, 0x00, 0x00, 0x00,
  0xb8, 0xca, 0x00, 0x00, 0x00, 0xc7, 0x45, 0x00, 0x02, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .xor 32 [gr 32 10, Src.opd 32 (.r 10)] 3) := by dec_rfl
theorem p11_3 : ∀ feat, Dec feat p11 3 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 2147483647)] 5) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p11_11 : ∀ feat, Dec feat p11 11 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 129)] 5) := by dec_rfl
theorem p11_16 : ∀ feat, Dec feat p11 16 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 202)] 5) := by dec_rfl
theorem p11_21 : ∀ feat, Dec feat p11 21 (FV7z.mk .mov 32 [.mem (mg (some 5) none 1 0 32), .imm 32 2] 7) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.xor 32 10 (.r 10),
  Op.mov 32 2 (.i 2147483647),
  Op.mov 64 7 (.r 5),
  Op.mov 32 6 (.i 129),
  Op.mov 32 0 (.i 202),
  Op.sti 32 (some 5) none 1 0 2]

theorem b11 (prof : Profile) : Blk prof p11 0 28 o11 :=
  .cons (p11_0 _) (OpI.xor (.r 10) (.inl rfl)) (by decide) <|
  .cons (p11_3 _) (OpI.mov (.i 2147483647) (.inl rfl)) (by decide) <|
  .cons (p11_8 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p11_11 _) (OpI.mov (.i 129) (.inl rfl)) (by decide) <|
  .cons (p11_16 _) (OpI.mov (.i 202) (.inl rfl)) (by decide) <|
  .cons (p11_21 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 28

/-- The stretch at `231`. -/
def p12 : List Byte := [
  0x48, 0x3d, 0x00, 0xf0, 0xff, 0xff]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 18446744073709547520)] 6) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.cmp 64 0 (.i 18446744073709547520)]

theorem b12 (prof : Profile) : Blk prof p12 0 6 o12 :=
  .cons (p12_0 _) (OpI.cmp (.i 18446744073709547520) (.inr rfl)) (by decide) <|
  .nil 6

def j5 : List Byte := [0x0f, 0x86, 0x3e, 0xff, 0xff, 0xff]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551422] 6) := by dec_rfl

/-- The stretch at `243`. -/
def p13 : List Byte := [
  0x83, 0xc0, 0x16, 0x83, 0xe0, 0xf7]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 22)] 3) := by dec_rfl
theorem p13_3 : ∀ feat, Dec feat p13 3 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4294967287)] 3) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.add 32 0 (.i 22),
  Op.and 32 0 (.i 4294967287)]

theorem b13 (prof : Profile) : Blk prof p13 0 6 o13 :=
  .cons (p13_0 _) (OpI.add (.i 22) (.inl rfl)) (by decide) <|
  .cons (p13_3 _) (OpI.and (.i 4294967287) (.inl rfl)) (by decide) <|
  .nil 6

def j6 : List Byte := [0x75, 0x9a]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551514] 2) := by dec_rfl

def j7 : List Byte := [0xe9, 0x31, 0xff, 0xff, 0xff]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551409] 5) := by dec_rfl

end FV7z.Pos
