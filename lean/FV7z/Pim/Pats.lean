import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps4
/-!
# The stretches of straight-line code of `__pthread_initialize_minimal_internal` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 25 of them) and each distinct jump (`j*`, 6) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pim
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x41, 0x54, 0x4c, 0x8d, 0x05, 0x53, 0xf0, 0x19, 0x00, 0x55]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .lea 64 [gr 64 8, .mem (mrip 1699923 0)] 7) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.push 12,
  Op.mov 64 8 (.i 7991568),
  Op.push 5]

theorem b0 (prof : Profile) : BlkA prof p0 (0x6000b0 : Addr) 0 14 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) ((OpI.push).at _) (by decide) <|
  .cons (p0_6 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p0_13 _) ((OpI.push).at _) (by decide) <|
  .nil 14

/-- The stretch at `19`. -/
def p1 : List Byte := [
  0x64, 0x48, 0x8b, 0x14, 0x25, 0x10, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mf none none 1 16 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o1 (fb : Addr) : List Op := [
  Op.ldf fb 64 2 none none 1 16]

theorem b1 (prof : Profile) (fb : Addr) : BlkF prof p1 (0x6000c3 : Addr) fb 0 9 (o1 fb) :=
  .cons (p1_0 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .nil 9

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x8d, 0xba, 0xd0, 0x02, 0x00, 0x00, 0x48, 0x81, 0xec, 0xc8, 0x00, 0x00, 0x00, 0x64, 0x48,
  0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x31,
  0xc0, 0xb8, 0xda, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 2) none 1 720 0)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 200)] 7) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p2_23 : ∀ feat, Dec feat p2 23 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 184 64), gr 64 0] 8) := by dec_rfl
theorem p2_31 : ∀ feat, Dec feat p2 31 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p2_33 : ∀ feat, Dec feat p2 33 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 218)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 (fb : Addr) : List Op := [
  Op.lea 64 7 (some 2) none 1 720,
  Op.sub 64 4 (.i 200),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 184 0,
  Op.xor 32 0 (.r 0),
  Op.mov 32 0 (.i 218)]

theorem b2 (prof : Profile) (fb : Addr) : BlkF prof p2 (0x6000d0 : Addr) fb 0 38 (o2 fb) :=
  .cons (p2_0 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_7 _) (((OpI.sub (.i 200) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p2_14 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p2_23 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p2_31 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p2_33 _) (((OpI.mov (.i 218) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 38

/-- The stretch at `72`. -/
def p3 : List Byte := [
  0x89, 0x82, 0xd0, 0x02, 0x00, 0x00, 0x48, 0x8d, 0x82, 0x10, 0x03, 0x00, 0x00, 0x64, 0x48, 0x89,
  0x04, 0x25, 0x10, 0x05, 0x00, 0x00, 0x64, 0xc6, 0x04, 0x25, 0x12, 0x06, 0x00, 0x00, 0x01, 0x48,
  0x8d, 0xba, 0xe0, 0x02, 0x00, 0x00, 0xbe, 0x18, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x82, 0xe8, 0x02,
  0x00, 0x00, 0xe0, 0xff, 0xff, 0xff, 0xb8, 0x11, 0x01, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [.mem (mg (some 2) none 1 720 32), gr 32 0] 6) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) none 1 784 0)] 7) := by dec_rfl
theorem p3_13 : ∀ feat, Dec feat p3 13 (FV7z.mk .mov 64 [.mem (mf none none 1 1296 64), gr 64 0] 9) := by dec_rfl
theorem p3_22 : ∀ feat, Dec feat p3 22 (FV7z.mk .mov 8 [.mem (mf none none 1 1554 8), .imm 8 1] 9) := by dec_rfl
theorem p3_31 : ∀ feat, Dec feat p3 31 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 2) none 1 736 0)] 7) := by dec_rfl
theorem p3_38 : ∀ feat, Dec feat p3 38 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 24)] 5) := by dec_rfl
theorem p3_43 : ∀ feat, Dec feat p3 43 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 744 64), .imm 64 18446744073709551584] 11) := by dec_rfl
theorem p3_54 : ∀ feat, Dec feat p3 54 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 273)] 5) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.st 32 (some 2) none 1 720 0,
  Op.lea 64 0 (some 2) none 1 784,
  Op.stf fb 64 none none 1 1296 0,
  Op.stfi fb 8 none none 1 1554 1,
  Op.lea 64 7 (some 2) none 1 736,
  Op.mov 32 6 (.i 24),
  Op.sti 64 (some 2) none 1 744 18446744073709551584,
  Op.mov 32 0 (.i 273)]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x6000f8 : Addr) fb 0 59 (o3 fb) :=
  .cons (p3_0 _) (((OpI.st (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .cons (p3_6 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_13 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p3_22 _) (OpIF.stfi (.inl rfl)) (by decide) <|
  .cons (p3_31 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_38 _) (((OpI.mov (.i 24) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p3_43 _) (((OpI.sti (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p3_54 _) (((OpI.mov (.i 273) (.inl rfl)).at _).fs _) (by decide) <|
  .nil 59

/-- The stretch at `149`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x05, 0x64, 0x1b, 0x19, 0x00, 0x64, 0x48, 0x89, 0x04, 0x25, 0x98, 0x06, 0x00, 0x00,
  0x48, 0x8d, 0x82, 0xc0, 0x02, 0x00, 0x00, 0x4c, 0x89, 0x05, 0xad, 0xef, 0x19, 0x00, 0x48, 0x89,
  0x05, 0xae, 0xef, 0x19, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1645412 64)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [.mem (mf none none 1 1688 64), gr 64 0] 9) := by dec_rfl
theorem p4_16 : ∀ feat, Dec feat p4 16 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) none 1 704 0)] 7) := by dec_rfl
theorem p4_23 : ∀ feat, Dec feat p4 23 (FV7z.mk .mov 64 [.mem (mrip 1699757 64), gr 64 8] 7) := by dec_rfl
theorem p4_30 : ∀ feat, Dec feat p4 30 (FV7z.mk .mov 64 [.mem (mrip 1699758 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.lda 64 0 7937200,
  Op.stf fb 64 none none 1 1688 0,
  Op.lea 64 0 (some 2) none 1 704,
  Op.sta 64 7991568 8,
  Op.sta 64 7991576 0]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x600145 : Addr) fb 0 37 (o4 fb) :=
  .cons (p4_0 _) ((OpIA.ld_rip (.inr rfl) (by decide)).fs _) (by decide) <|
  .cons (p4_7 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p4_16 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_23 _) ((OpIA.st_rip (.inr (.inr rfl)) (by decide)).fs _) (by decide) <|
  .cons (p4_30 _) ((OpIA.st_rip (.inr (.inr rfl)) (by decide)).fs _) (by decide) <|
  .nil 37

/-- The stretch at `193`. -/
def p5 : List Byte := [
  0x48, 0x89, 0x05, 0x98, 0xef, 0x19, 0x00, 0x0f, 0xb6, 0x05, 0xd1, 0xef, 0x19, 0x00, 0x64, 0x88,
  0x04, 0x25, 0x11, 0x06, 0x00, 0x00, 0x48, 0x8d, 0x6c, 0x24, 0x28, 0x31, 0xc0, 0xb9, 0x10, 0x00,
  0x00, 0x00, 0x31, 0xd2, 0x48, 0x89, 0xef, 0x4c, 0x8d, 0x64, 0x24, 0x20, 0xc7, 0x84, 0x24, 0xa8,
  0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [.mem (mrip 1699736 64), gr 64 0] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .movzx 32 [gr 32 0, .mem (mrip 1699793 8)] 7) := by dec_rfl
theorem p5_14 : ∀ feat, Dec feat p5 14 (FV7z.mk .mov 8 [.mem (mf none none 1 1553 8), gr 8 0] 8) := by dec_rfl
theorem p5_22 : ∀ feat, Dec feat p5 22 (FV7z.mk .lea 64 [gr 64 5, .mem (mg (some 4) none 1 40 0)] 5) := by dec_rfl
theorem p5_27 : ∀ feat, Dec feat p5 27 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p5_29 : ∀ feat, Dec feat p5 29 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p5_34 : ∀ feat, Dec feat p5 34 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p5_36 : ∀ feat, Dec feat p5 36 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p5_39 : ∀ feat, Dec feat p5 39 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 4) none 1 32 0)] 5) := by dec_rfl
theorem p5_44 : ∀ feat, Dec feat p5 44 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 168 32), .imm 32 4] 11) := by dec_rfl

/-- What the stretch does. -/
def o5 (fb : Addr) : List Op := [
  Op.sta 64 7991568 0,
  Op.ldzxa 8 0 7991632,
  Op.stf8 fb none none 1 1553 0,
  Op.lea 64 5 (some 4) none 1 40,
  Op.xor 32 0 (.r 0),
  Op.mov 32 1 (.i 16),
  Op.xor 32 2 (.r 2),
  Op.mov 64 7 (.r 5),
  Op.lea 64 12 (some 4) none 1 32,
  Op.sti 32 (some 4) none 1 168 4]

theorem b5 (prof : Profile) (fb : Addr) : BlkF prof p5 (0x600171 : Addr) fb 0 55 (o5 fb) :=
  .cons (p5_0 _) ((OpIA.st_rip (.inr (.inr rfl)) (by decide)).fs _) (by decide) <|
  .cons (p5_7 _) ((OpIA.ldzx_rip (.inl rfl) (by decide)).fs _) (by decide) <|
  .cons (p5_14 _) (OpIF.stf8) (by decide) <|
  .cons (p5_22 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p5_27 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p5_29 _) (((OpI.mov (.i 16) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p5_34 _) (((OpI.xor (.r 2) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p5_36 _) (((OpI.mov (.r 5) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p5_39 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p5_44 _) (((OpI.sti (.inr (.inr (.inl rfl)))).at _).fs _) (by decide) <|
  .nil 55

/-- The stretch at `251`. -/
def p6 : List Byte := [
  0x4c, 0x89, 0xe6, 0x48, 0x8d, 0x05, 0x0b, 0xfd, 0xff, 0xff, 0xbf, 0x20, 0x00, 0x00, 0x00, 0x48,
  0x89, 0x44, 0x24, 0x20]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p6_3 : ∀ feat, Dec feat p6 3 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 18446744073709550859 0)] 7) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 32)] 5) := by dec_rfl
theorem p6_15 : ∀ feat, Dec feat p6 15 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 32 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 6 (.r 12),
  Op.mov 64 0 (.i 6291136),
  Op.mov 32 7 (.i 32),
  Op.st 64 (some 4) none 1 32 0]

theorem b6 (prof : Profile) : BlkA prof p6 (0x6001ab : Addr) 0 20 o6 :=
  .cons (p6_0 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p6_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_10 _) ((OpI.mov (.i 32) (.inl rfl)).at _) (by decide) <|
  .cons (p6_15 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 20

/-- The stretch at `276`. -/
def p7 : List Byte := [
  0x31, 0xd2, 0x4c, 0x89, 0xe6, 0xbf, 0x21, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x05, 0x8b, 0xfd, 0xff,
  0xff, 0xc7, 0x84, 0x24, 0xa8, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x10, 0x48, 0x89, 0x44, 0x24,
  0x20]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p7_2 : ∀ feat, Dec feat p7 2 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 12)] 3) := by dec_rfl
theorem p7_5 : ∀ feat, Dec feat p7 5 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 33)] 5) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 18446744073709550987 0)] 7) := by dec_rfl
theorem p7_17 : ∀ feat, Dec feat p7 17 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 168 32), .imm 32 268435460] 11) := by dec_rfl
theorem p7_28 : ∀ feat, Dec feat p7 28 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 32 64), gr 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.xor 32 2 (.r 2),
  Op.mov 64 6 (.r 12),
  Op.mov 32 7 (.i 33),
  Op.mov 64 0 (.i 6291296),
  Op.sti 32 (some 4) none 1 168 268435460,
  Op.st 64 (some 4) none 1 32 0]

theorem b7 (prof : Profile) : BlkA prof p7 (0x6001c4 : Addr) 0 33 o7 :=
  .cons (p7_0 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p7_2 _) ((OpI.mov (.r 12) (.inr rfl)).at _) (by decide) <|
  .cons (p7_5 _) ((OpI.mov (.i 33) (.inl rfl)).at _) (by decide) <|
  .cons (p7_10 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_17 _) ((OpI.sti (.inr (.inr (.inl rfl)))).at _) (by decide) <|
  .cons (p7_28 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 33

/-- The stretch at `314`. -/
def p8 : List Byte := [
  0x41, 0xba, 0x08, 0x00, 0x00, 0x00, 0x31, 0xd2, 0x48, 0x89, 0xee, 0x48, 0xb8, 0x00, 0x00, 0x00,
  0x80, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 10, Src.opd 32 (.i 8)] 6) := by dec_rfl
theorem p8_6 : ∀ feat, Dec feat p8 6 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p8_8 : ∀ feat, Dec feat p8 8 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 6442450944)] 10) := by dec_rfl
theorem p8_21 : ∀ feat, Dec feat p8 21 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 10 (.i 8),
  Op.xor 32 2 (.r 2),
  Op.mov 64 6 (.r 5),
  Op.mov 64 0 (.i 6442450944),
  Op.mov 32 7 (.i 1)]

theorem b8 (prof : Profile) : Blk prof p8 0 26 o8 :=
  .cons (p8_0 _) (OpI.mov (.i 8) (.inl rfl)) (by decide) <|
  .cons (p8_6 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p8_8 _) (OpI.mov (.r 5) (.inr rfl)) (by decide) <|
  .cons (p8_11 _) (OpI.mov (.i 6442450944) (.inr rfl)) (by decide) <|
  .cons (p8_21 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .nil 26

/-- The stretch at `345`. -/
def p9 : List Byte := [
  0xb8, 0x0e, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 14)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 32 0 (.i 14)]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.mov (.i 14) (.inl rfl)) (by decide) <|
  .nil 5

/-- The stretch at `352`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0x3d, 0x29, 0x7c, 0x1a, 0x00, 0x48, 0x8d, 0x74, 0x24, 0x08]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1735721 0)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 4) none 1 8 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 7 (.i 8027712),
  Op.lea 64 6 (some 4) none 1 8]

theorem b10 (prof : Profile) : BlkA prof p10 (0x600210 : Addr) 0 12 o10 :=
  .cons (p10_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_7 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .nil 12

/-- The stretch at `369`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x4c, 0x24, 0x08, 0x48, 0x8d, 0x41, 0xff, 0x48, 0x83, 0xf9, 0x0f]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p11_5 : ∀ feat, Dec feat p11 5 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 1) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p11_9 : ∀ feat, Dec feat p11 9 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 15)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 1 (some 4) none 1 8,
  Op.lea 64 0 (some 1) none 1 18446744073709551615,
  Op.cmp 64 1 (.i 15)]

theorem b11 (prof : Profile) : Blk prof p11 0 13 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p11_5 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_9 _) (OpI.cmp (.i 15) (.inr rfl)) (by decide) <|
  .nil 13

def j0 : List Byte := [0x77, 0x13]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `384`. -/
def p12 : List Byte := [
  0x48, 0xc7, 0x44, 0x24, 0x08, 0x10, 0x00, 0x00, 0x00, 0xb8, 0x0f, 0x00, 0x00, 0x00, 0xb9, 0x10,
  0x00, 0x00, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), .imm 64 16] 9) := by dec_rfl
theorem p12_9 : ∀ feat, Dec feat p12 9 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 15)] 5) := by dec_rfl
theorem p12_14 : ∀ feat, Dec feat p12 14 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.sti 64 (some 4) none 1 8 16,
  Op.mov 32 0 (.i 15),
  Op.mov 32 1 (.i 16)]

theorem b12 (prof : Profile) : Blk prof p12 0 19 o12 :=
  .cons (p12_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p12_9 _) (OpI.mov (.i 15) (.inl rfl)) (by decide) <|
  .cons (p12_14 _) (OpI.mov (.i 16) (.inl rfl)) (by decide) <|
  .nil 19

/-- The stretch at `403`. -/
def p13 : List Byte := [
  0x48, 0x89, 0x05, 0xe6, 0x7b, 0x1a, 0x00, 0x48, 0x8b, 0x05, 0xef, 0x7b, 0x1a, 0x00, 0x31, 0xd2,
  0x48, 0x8d, 0x74, 0x24, 0x10, 0xbf, 0x03, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x44, 0x01, 0xff]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mrip 1735654 64), gr 64 0] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1735663 64)] 7) := by dec_rfl
theorem p13_14 : ∀ feat, Dec feat p13 14 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p13_16 : ∀ feat, Dec feat p13 16 (FV7z.mk .lea 64 [gr 64 6, .mem (mg (some 4) none 1 16 0)] 5) := by dec_rfl
theorem p13_21 : ∀ feat, Dec feat p13 21 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 3)] 5) := by dec_rfl
theorem p13_26 : ∀ feat, Dec feat p13 26 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 1) (some 0) 1 18446744073709551615 0)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sta 64 8027696 0,
  Op.lda 64 0 8027712,
  Op.xor 32 2 (.r 2),
  Op.lea 64 6 (some 4) none 1 16,
  Op.mov 32 7 (.i 3),
  Op.lea 64 0 (some 1) (some 0) 1 18446744073709551615]

theorem b13 (prof : Profile) : BlkA prof p13 (0x600243 : Addr) 0 31 o13 :=
  .cons (p13_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p13_7 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p13_14 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p13_16 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p13_21 _) ((OpI.mov (.i 3) (.inl rfl)).at _) (by decide) <|
  .cons (p13_26 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .nil 31

/-- The stretch at `437`. -/
def p14 : List Byte := [
  0x48, 0x0f, 0xaf, 0xc1, 0x48, 0x89, 0x05, 0xd0, 0x7b, 0x1a, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .imul 64 [gr 64 0, gr 64 1] 4) := by dec_rfl
theorem p14_4 : ∀ feat, Dec feat p14 4 (FV7z.mk .mov 64 [.mem (mrip 1735632 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.imul64 0 1,
  Op.sta 64 8027712 0]

theorem b14 (prof : Profile) : BlkA prof p14 (0x600265 : Addr) 0 11 o14 :=
  .cons (p14_0 _) ((OpI.imul64).at _) (by decide) <|
  .cons (p14_4 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 11

/-- The stretch at `453`. -/
def p15 : List Byte := [
  0xb9, 0x00, 0x00, 0x20, 0x00, 0x85, 0xc0]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 2097152)] 5) := by dec_rfl
theorem p15_5 : ∀ feat, Dec feat p15 5 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 32 1 (.i 2097152),
  Op.test 32 0 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 7 o15 :=
  .cons (p15_0 _) (OpI.mov (.i 2097152) (.inl rfl)) (by decide) <|
  .cons (p15_5 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x75, 0x1e]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 30] 2) := by dec_rfl

/-- The stretch at `462`. -/
def p16 : List Byte := [
  0x48, 0x8b, 0x54, 0x24, 0x10, 0x48, 0x83, 0xfa, 0xff]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p16_5 : ∀ feat, Dec feat p16 5 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 18446744073709551615)] 4) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.ld 64 2 (some 4) none 1 16,
  Op.cmp 64 2 (.i 18446744073709551615)]

theorem b16 (prof : Profile) : Blk prof p16 0 9 o16 :=
  .cons (p16_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p16_5 _) (OpI.cmp (.i 18446744073709551615) (.inr rfl)) (by decide) <|
  .nil 9

def j2 : List Byte := [0x74, 0x13]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 19] 2) := by dec_rfl

/-- The stretch at `473`. -/
def p17 : List Byte := [
  0x48, 0x81, 0xfa, 0x00, 0x40, 0x00, 0x00, 0xb8, 0x00, 0x40, 0x00, 0x00, 0x48, 0x0f, 0x47, 0xc2,
  0x48, 0x89, 0xc1]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 16384)] 7) := by dec_rfl
theorem p17_7 : ∀ feat, Dec feat p17 7 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 16384)] 5) := by dec_rfl
theorem p17_12 : ∀ feat, Dec feat p17 12 (FV7z.mk (.cmovcc 7) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem p17_16 : ∀ feat, Dec feat p17 16 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.cmp 64 2 (.i 16384),
  Op.mov 32 0 (.i 16384),
  Op.cmov64 7 0 2,
  Op.mov 64 1 (.r 0)]

theorem b17 (prof : Profile) : Blk prof p17 0 19 o17 :=
  .cons (p17_0 _) (OpI.cmp (.i 16384) (.inr rfl)) (by decide) <|
  .cons (p17_7 _) (OpI.mov (.i 16384) (.inl rfl)) (by decide) <|
  .cons (p17_12 _) (OpI.cmov64) (by decide) <|
  .cons (p17_16 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 19

/-- The stretch at `492`. -/
def p18 : List Byte := [
  0x48, 0x8b, 0x15, 0x35, 0x31, 0x19, 0x00, 0x48, 0x8b, 0x05, 0x96, 0x7b, 0x1a, 0x00, 0x48, 0x01,
  0xd0, 0x48, 0x05, 0x00, 0x08, 0x00, 0x00, 0x48, 0x39, 0xc8, 0x48, 0x0f, 0x42, 0xc1, 0x48, 0x8d,
  0x44, 0x02, 0xff, 0x48, 0xf7, 0xda, 0x48, 0x21, 0xc2, 0x31, 0xc0, 0x48, 0x89, 0x54, 0x24, 0x10,
  0xba, 0x01, 0x00, 0x00, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip 1650997 64)] 7) := by dec_rfl
theorem p18_7 : ∀ feat, Dec feat p18 7 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1735574 64)] 7) := by dec_rfl
theorem p18_14 : ∀ feat, Dec feat p18 14 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p18_17 : ∀ feat, Dec feat p18 17 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 2048)] 6) := by dec_rfl
theorem p18_23 : ∀ feat, Dec feat p18 23 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem p18_26 : ∀ feat, Dec feat p18 26 (FV7z.mk (.cmovcc 2) 64 [gr 64 0, gr 64 1] 4) := by dec_rfl
theorem p18_30 : ∀ feat, Dec feat p18 30 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) (some 0) 1 18446744073709551615 0)] 5) := by dec_rfl
theorem p18_35 : ∀ feat, Dec feat p18 35 (FV7z.mk .neg 64 [gr 64 2] 3) := by dec_rfl
theorem p18_38 : ∀ feat, Dec feat p18 38 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p18_41 : ∀ feat, Dec feat p18 41 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p18_43 : ∀ feat, Dec feat p18 43 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 16 64), gr 64 2] 5) := by dec_rfl
theorem p18_48 : ∀ feat, Dec feat p18 48 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.lda 64 2 7943128,
  Op.lda 64 0 8027712,
  Op.add 64 0 (.r 2),
  Op.add 64 0 (.i 2048),
  Op.cmp 64 0 (.r 1),
  Op.cmov64 2 0 1,
  Op.lea 64 0 (some 2) (some 0) 1 18446744073709551615,
  Op.neg 64 2,
  Op.and 64 2 (.r 0),
  Op.xor 32 0 (.r 0),
  Op.st 64 (some 4) none 1 16 2,
  Op.mov 32 2 (.i 1)]

theorem b18 (prof : Profile) : BlkA prof p18 (0x60029c : Addr) 0 53 o18 :=
  .cons (p18_0 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p18_7 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p18_14 _) ((OpI.add (.r 2) (.inr rfl)).at _) (by decide) <|
  .cons (p18_17 _) ((OpI.add (.i 2048) (.inr rfl)).at _) (by decide) <|
  .cons (p18_23 _) ((OpI.cmp (.r 1) (.inr rfl)).at _) (by decide) <|
  .cons (p18_26 _) ((OpI.cmov64).at _) (by decide) <|
  .cons (p18_30 _) ((OpI.lea (.inr rfl)).at _) (by decide) <|
  .cons (p18_35 _) ((OpI.neg (.inr rfl)).at _) (by decide) <|
  .cons (p18_38 _) ((OpI.and (.r 0) (.inr rfl)).at _) (by decide) <|
  .cons (p18_41 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p18_43 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p18_48 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .nil 53

def j3 : List Byte := [0x0f, 0x85, 0xac, 0x00, 0x00, 0x00]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 5) 64 [.rel 172] 6) := by dec_rfl

/-- The stretch at `559`. -/
def p19 : List Byte := [
  0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x89, 0x05, 0xb5, 0x7b, 0x1a, 0x00, 0x48, 0x8b, 0x05, 0xe6,
  0x30, 0x19, 0x00, 0x48, 0x89, 0x05, 0x97, 0x7b, 0x1a, 0x00, 0x31, 0xc0]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 16 64)] 5) := by dec_rfl
theorem p19_5 : ∀ feat, Dec feat p19 5 (FV7z.mk .mov 64 [.mem (mrip 1735605 64), gr 64 0] 7) := by dec_rfl
theorem p19_12 : ∀ feat, Dec feat p19 12 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1650918 64)] 7) := by dec_rfl
theorem p19_19 : ∀ feat, Dec feat p19 19 (FV7z.mk .mov 64 [.mem (mrip 1735575 64), gr 64 0] 7) := by dec_rfl
theorem p19_26 : ∀ feat, Dec feat p19 26 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.ld 64 0 (some 4) none 1 16,
  Op.sta 64 8027808 0,
  Op.lda 64 0 7943128,
  Op.sta 64 8027792 0,
  Op.xor 32 0 (.r 0)]

theorem b19 (prof : Profile) : BlkA prof p19 (0x6002df : Addr) 0 28 o19 :=
  .cons (p19_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p19_5 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p19_12 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p19_19 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p19_26 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .nil 28

/-- The stretch at `593`. -/
def p20 : List Byte := [
  0x83, 0xf8, 0x01]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.cmp 32 0 (.i 1)]

theorem b20 (prof : Profile) : Blk prof p20 0 3 o20 :=
  .cons (p20_0 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 3

def j4 : List Byte := [0x7f, 0x65]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 15) 64 [.rel 101] 2) := by dec_rfl

/-- The stretch at `598`. -/
def p21 : List Byte := [
  0x48, 0xc7, 0xc0, 0xb0, 0x9d, 0x5f, 0x00, 0x48, 0xc7, 0xc6, 0xf0, 0x96, 0x5f, 0x00, 0x31, 0xd2,
  0x48, 0x8d, 0x3d, 0x03, 0x7b, 0x1a, 0x00, 0x48, 0x89, 0x05, 0xdc, 0x30, 0x19, 0x00, 0x48, 0xc7,
  0xc0, 0xf0, 0x9e, 0x5f, 0x00, 0x48, 0x89, 0x05, 0x46, 0x82, 0x1a, 0x00]

theorem p21_0 : ∀ feat, Dec feat p21 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 6266288)] 7) := by dec_rfl
theorem p21_7 : ∀ feat, Dec feat p21 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 6264560)] 7) := by dec_rfl
theorem p21_14 : ∀ feat, Dec feat p21 14 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p21_16 : ∀ feat, Dec feat p21 16 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 1735427 0)] 7) := by dec_rfl
theorem p21_23 : ∀ feat, Dec feat p21 23 (FV7z.mk .mov 64 [.mem (mrip 1650908 64), gr 64 0] 7) := by dec_rfl
theorem p21_30 : ∀ feat, Dec feat p21 30 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 6266608)] 7) := by dec_rfl
theorem p21_37 : ∀ feat, Dec feat p21 37 (FV7z.mk .mov 64 [.mem (mrip 1737286 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o21 : List Op := [
  Op.mov 64 0 (.i 6266288),
  Op.mov 64 6 (.i 6264560),
  Op.xor 32 2 (.r 2),
  Op.mov 64 7 (.i 8027680),
  Op.sta 64 7943168 0,
  Op.mov 64 0 (.i 6266608),
  Op.sta 64 8029560 0]

theorem b21 (prof : Profile) : BlkA prof p21 (0x600306 : Addr) 0 44 o21 :=
  .cons (p21_0 _) ((OpI.mov (.i 6266288) (.inr rfl)).at _) (by decide) <|
  .cons (p21_7 _) ((OpI.mov (.i 6264560) (.inr rfl)).at _) (by decide) <|
  .cons (p21_14 _) ((OpI.xor (.r 2) (.inl rfl)).at _) (by decide) <|
  .cons (p21_16 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p21_23 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p21_30 _) ((OpI.mov (.i 6266608) (.inr rfl)).at _) (by decide) <|
  .cons (p21_37 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 44

/-- The stretch at `647`. -/
def p22 : List Byte := [
  0xc7, 0x05, 0x23, 0x7b, 0x1a, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x89, 0x05, 0xf0, 0x7a, 0x1a,
  0x00]

theorem p22_0 : ∀ feat, Dec feat p22 0 (FV7z.mk .mov 32 [.mem (mrip 1735459 32), .imm 32 1] 10) := by dec_rfl
theorem p22_10 : ∀ feat, Dec feat p22 10 (FV7z.mk .mov 64 [.mem (mrip 1735408 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o22 : List Op := [
  Op.stia 32 8027748 1,
  Op.sta 64 8027704 0]

theorem b22 (prof : Profile) : BlkA prof p22 (0x600337 : Addr) 0 17 o22 :=
  .cons (p22_0 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p22_10 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 17

/-- The stretch at `669`. -/
def p23 : List Byte := [
  0x48, 0x8b, 0x84, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x64, 0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00,
  0x00]

theorem p23_0 : ∀ feat, Dec feat p23 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 184 64)] 8) := by dec_rfl
theorem p23_8 : ∀ feat, Dec feat p23 8 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o23 (fb : Addr) : List Op := [
  Op.ld 64 0 (some 4) none 1 184,
  Op.xormf fb 64 0 none none 1 40]

theorem b23 (prof : Profile) (fb : Addr) : BlkF prof p23 (0x60034d : Addr) fb 0 17 (o23 fb) :=
  .cons (p23_0 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p23_8 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 17

def j5 : List Byte := [0x75, 0x3c]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 5) 64 [.rel 60] 2) := by dec_rfl

/-- The stretch at `688`. -/
def p24 : List Byte := [
  0x48, 0x81, 0xc4, 0xc8, 0x00, 0x00, 0x00, 0x5d, 0x41, 0x5c]

theorem p24_0 : ∀ feat, Dec feat p24 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 200)] 7) := by dec_rfl
theorem p24_7 : ∀ feat, Dec feat p24 7 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p24_8 : ∀ feat, Dec feat p24 8 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl

/-- What the stretch does. -/
def o24 : List Op := [
  Op.add 64 4 (.i 200),
  Op.pop 5,
  Op.pop 12]

theorem b24 (prof : Profile) : Blk prof p24 0 10 o24 :=
  .cons (p24_0 _) (OpI.add (.i 200) (.inr rfl)) (by decide) <|
  .cons (p24_7 _) (OpI.pop) (by decide) <|
  .cons (p24_8 _) (OpI.pop) (by decide) <|
  .nil 10

end FV7z.Pim
