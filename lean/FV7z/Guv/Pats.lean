import FV7z.Lemmas.SpFs
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `GetUInt64Value` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 13 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Guv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x41, 0x54, 0x55, 0x53, 0x48, 0x89, 0xcb, 0x48, 0x83, 0xec, 0x20, 0x64, 0x48, 0x8b, 0x04, 0x25,
  0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x18, 0x31, 0xc0, 0x48, 0x8b, 0x07, 0x48, 0x89,
  0xe5, 0x48, 0xc7, 0x01, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x41, 0x08, 0x00, 0x48, 0x89, 0xe9, 0xc7,
  0x04, 0x24, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_2 : ∀ feat, Dec feat p0 2 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_20 : ∀ feat, Dec feat p0 20 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 24 64), gr 64 0] 5) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_27 : ∀ feat, Dec feat p0 27 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_33 : ∀ feat, Dec feat p0 33 (FV7z.mk .mov 64 [.mem (mg (some 1) none 1 0 64), .imm 64 0] 7) := by dec_rfl
theorem p0_40 : ∀ feat, Dec feat p0 40 (FV7z.mk .mov 8 [.mem (mg (some 1) none 1 8 8), .imm 8 0] 4) := by dec_rfl
theorem p0_44 : ∀ feat, Dec feat p0 44 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p0_47 : ∀ feat, Dec feat p0 47 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 0 32), .imm 32 0] 7) := by dec_rfl
theorem p0_54 : ∀ feat, Dec feat p0 54 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), .imm 64 0] 9) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 12,
  Op.push 5,
  Op.push 3,
  Op.mov 64 3 (.r 1),
  Op.sub 64 4 (.i 32),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 24 0,
  Op.xor 32 0 (.r 0),
  Op.ld 64 0 (some 7) none 1 0,
  Op.mov 64 5 (.r 4),
  Op.sti 64 (some 1) none 1 0 0,
  Op.sti 8 (some 1) none 1 8 0,
  Op.mov 64 1 (.r 5),
  Op.sti 32 (some 4) none 1 0 0,
  Op.sti 64 (some 4) none 1 8 0]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x5ebcd0 : Addr) fb 0 63 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_2 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_3 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_4 _) (((OpI.mov (.r 1) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_7 _) (((OpI.sub (.i 32) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_11 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_20 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_25 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_27 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_33 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_40 _) (((OpI.sti (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_44 _) (((OpI.mov (.r 5) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_47 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p0_54 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .nil 63

/-- The stretch at `66`. -/
def p1 : List Byte := [
  0x41, 0x89, 0xc4, 0x85, 0xc0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 12, Src.opd 32 (.r 0)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 12 (.r 0),
  Op.test 32 0 (.r 0)]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 0) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 5

def j0 : List Byte := [0x74, 0x2f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `73`. -/
def p2 : List Byte := [
  0x48, 0x89, 0xef]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 7 (.r 5)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `81`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x18, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 24 64)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 24,
  Op.xormf fb 64 0 none none 1 40]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x5ebd21 : Addr) fb 0 14 (o3 fb) :=
  .cons (p3_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_5 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 14

def j1 : List Byte := [0x0f, 0x85, 0x8f, 0x00, 0x00, 0x00]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 143] 6) := by dec_rfl

/-- The stretch at `101`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x20, 0x44, 0x89, 0xe0, 0x5b, 0x5d, 0x41, 0x5c]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.r 12)] 3) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p4_8 : ∀ feat, Dec feat p4 8 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p4_9 : ∀ feat, Dec feat p4 9 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 32),
  Op.mov 32 0 (.r 12),
  Op.pop 3,
  Op.pop 5,
  Op.pop 12]

theorem b4 (prof : Profile) : Blk prof p4 0 11 o4 :=
  .cons (p4_0 _) (OpI.add (.i 32) (.inr rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.mov (.r 12) (.inl rfl)) (by decide) <|
  .cons (p4_7 _) (OpI.pop) (by decide) <|
  .cons (p4_8 _) (OpI.pop) (by decide) <|
  .cons (p4_9 _) (OpI.pop) (by decide) <|
  .nil 11

/-- The stretch at `120`. -/
def p5 : List Byte := [
  0x66, 0x83, 0x3c, 0x24, 0x15]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .cmp 16 [.mem (mg (some 4) none 1 0 16), .imm 16 21] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.cmpmi 16 (some 4) none 1 0 21]

theorem b5 (prof : Profile) : Blk prof p5 0 5 o5 :=
  .cons (p5_0 _) (OpI.cmpmi16) (by decide) <|
  .nil 5

/-- The stretch at `131`. -/
def p6 : List Byte := [
  0x0f, 0xb7, 0x04, 0x24, 0x48, 0x8d, 0x15, 0xaa, 0xe4, 0x0f, 0x00, 0x48, 0x63, 0x04, 0x82, 0x48,
  0x01, 0xd0]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 0 16)] 4) := by dec_rfl
theorem p6_4 : ∀ feat, Dec feat p6 4 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1041578 0)] 7) := by dec_rfl
theorem p6_11 : ∀ feat, Dec feat p6 11 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 2) (some 0) 4 0 32)] 4) := by dec_rfl
theorem p6_15 : ∀ feat, Dec feat p6 15 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ldzx 16 0 (some 4) none 1 0,
  Op.mov 64 2 (.i 7250440),
  Op.ldsx 0 (some 2) (some 0) 4 0,
  Op.add 64 0 (.r 2)]

theorem b6 (prof : Profile) : BlkA prof p6 (0x5ebd53 : Addr) 0 18 o6 :=
  .cons (p6_0 _) ((OpI.ldzx (.inr rfl)).at _) (by decide) <|
  .cons (p6_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_11 _) ((OpI.ldsx).at _) (by decide) <|
  .cons (p6_15 _) ((OpI.add (.r 2) (.inr rfl)).at _) (by decide) <|
  .nil 18

def j2 : List Byte := [0x3e, 0xff, 0xe0]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk .jmp 64 [gr 64 0] 3) := by dec_rfl

/-- The stretch at `160`. -/
def p7 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x08, 0x48, 0x89, 0x03, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p7_8 : ∀ feat, Dec feat p7 8 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ld 64 0 (some 4) none 1 8,
  Op.st 64 (some 3) none 1 0 0,
  Op.mov 32 0 (.i 1)]

theorem b7 (prof : Profile) : Blk prof p7 0 13 o7 :=
  .cons (p7_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p7_5 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

/-- The stretch at `173`. -/
def p8 : List Byte := [
  0x88, 0x43, 0x08]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 8 [.mem (mg (some 3) none 1 8 8), gr 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.st 8 (some 3) none 1 8 0]

theorem b8 (prof : Profile) : Blk prof p8 0 3 o8 :=
  .cons (p8_0 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0xeb, 0x97]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk .jmp 64 [.rel 18446744073709551511] 2) := by dec_rfl

/-- The stretch at `184`. -/
def p9 : List Byte := [
  0x8b, 0x44, 0x24, 0x08, 0x48, 0x89, 0x03, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 4) none 1 8 32)] 4) := by dec_rfl
theorem p9_4 : ∀ feat, Dec feat p9 4 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 32 0 (some 4) none 1 8,
  Op.st 64 (some 3) none 1 0 0,
  Op.mov 32 0 (.i 1)]

theorem b9 (prof : Profile) : Blk prof p9 0 12 o9 :=
  .cons (p9_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p9_4 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p9_7 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 12

def j4 : List Byte := [0xeb, 0xe7]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk .jmp 64 [.rel 18446744073709551591] 2) := by dec_rfl

/-- The stretch at `208`. -/
def p10 : List Byte := [
  0x0f, 0xb7, 0x44, 0x24, 0x08, 0x48, 0x89, 0x03, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 8 16)] 5) := by dec_rfl
theorem p10_5 : ∀ feat, Dec feat p10 5 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p10_8 : ∀ feat, Dec feat p10 8 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.ldzx 16 0 (some 4) none 1 8,
  Op.st 64 (some 3) none 1 0 0,
  Op.mov 32 0 (.i 1)]

theorem b10 (prof : Profile) : Blk prof p10 0 13 o10 :=
  .cons (p10_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p10_5 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p10_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

def j5 : List Byte := [0xeb, 0xce]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk .jmp 64 [.rel 18446744073709551566] 2) := by dec_rfl

/-- The stretch at `224`. -/
def p11 : List Byte := [
  0x0f, 0xb6, 0x44, 0x24, 0x08, 0x48, 0x89, 0x03, 0xb8, 0x01, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 4) none 1 8 8)] 5) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 0 64), gr 64 0] 3) := by dec_rfl
theorem p11_8 : ∀ feat, Dec feat p11 8 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ldzx 8 0 (some 4) none 1 8,
  Op.st 64 (some 3) none 1 0 0,
  Op.mov 32 0 (.i 1)]

theorem b11 (prof : Profile) : Blk prof p11 0 13 o11 :=
  .cons (p11_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .cons (p11_5 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_8 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 13

def j6 : List Byte := [0xeb, 0xbe]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551550] 2) := by dec_rfl

/-- The stretch at `240`. -/
def p12 : List Byte := [
  0x31, 0xc0]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b12 (prof : Profile) : Blk prof p12 0 2 o12 :=
  .cons (p12_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

def j7 : List Byte := [0xeb, 0xb9]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551545] 2) := by dec_rfl

end FV7z.Guv
