import FV7z.Lemmas.SpFs
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `ptmalloc_init` (PLAN.md G3, malloc)

Each distinct stretch between labels and jumps (`p*`, 17 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pmi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x55, 0x48, 0x8d, 0x0d, 0xc8, 0x08, 0x16, 0x00, 0x48, 0x8d, 0x51, 0x60, 0x48, 0x83, 0xec, 0x10,
  0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x08, 0x31, 0xc0,
  0x48, 0xc7, 0xc0, 0xe8, 0xff, 0xff, 0xff, 0xc7, 0x05, 0xe3, 0x07, 0x16, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x64, 0x48, 0x89, 0x08, 0x48, 0x89, 0xd0, 0x48, 0x81, 0xc1, 0x50, 0x08, 0x00, 0x00, 0x90]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_1 : ∀ feat, Dec feat p0 1 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 1444040 0)] 7) := by dec_rfl
theorem p0_8 : ∀ feat, Dec feat p0 8 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 1) none 1 96 0)] 4) := by dec_rfl
theorem p0_12 : ∀ feat, Dec feat p0 12 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p0_16 : ∀ feat, Dec feat p0 16 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_25 : ∀ feat, Dec feat p0 25 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 8 64), gr 64 0] 5) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551592)] 7) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .mov 32 [.mem (mrip 1443811 32), .imm 32 0] 10) := by dec_rfl
theorem p0_49 : ∀ feat, Dec feat p0 49 (FV7z.mk .mov 64 [.mem (mf (some 0) none 1 0 64), gr 64 1] 4) := by dec_rfl
theorem p0_53 : ∀ feat, Dec feat p0 53 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_56 : ∀ feat, Dec feat p0 56 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 2128)] 7) := by dec_rfl
theorem p0_63 : ∀ feat, Dec feat p0 63 (FV7z.mk .nop 32 [] 1) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.push 5,
  Op.mov 64 1 (.i 7940672),
  Op.lea 64 2 (some 1) none 1 96,
  Op.sub 64 4 (.i 16),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 8 0,
  Op.xor 32 0 (.r 0),
  Op.mov 64 0 (.i 18446744073709551592),
  Op.stia 32 7940484 0,
  Op.stf fb 64 (some 0) none 1 0 1,
  Op.mov 64 0 (.r 2),
  Op.add 64 1 (.i 2128),
  Op.nop]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x632170 : Addr) fb 0 64 (o0 fb) :=
  .cons (p0_0 _) (((OpI.push).at _).fs _) (by decide) <|
  .cons (p0_1 _) ((OpIA.lea_rip (by decide)).fs _) (by decide) <|
  .cons (p0_8 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_12 _) (((OpI.sub (.i 16) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_16 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_25 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_30 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.mov (.i 18446744073709551592) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_39 _) ((OpIA.sti_rip (.inr (.inl rfl)) (by decide)).fs _) (by decide) <|
  .cons (p0_49 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p0_53 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_56 _) (((OpI.add (.i 2128) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_63 _) (((OpI.nop).at _).fs _) (by decide) <|
  .nil 64

/-- The stretch at `69`. -/
def p1 : List Byte := [
  0x48, 0x83, 0xc0, 0x10]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.add 64 0 (.i 16)]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `80`. -/
def p2 : List Byte := [
  0x48, 0x39, 0xc8]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmp 64 0 (.r 1)]

theorem b2 (prof : Profile) : Blk prof p2 0 3 o2 :=
  .cons (p2_0 _) (OpI.cmp (.r 1) (.inr rfl)) (by decide) <|
  .nil 3

def j0 : List Byte := [0x75, 0xeb]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551595] 2) := by dec_rfl

/-- The stretch at `85`. -/
def p3 : List Byte := [
  0x48, 0xc7, 0x05, 0xd8, 0x23, 0x17, 0x00, 0x80, 0x00, 0x00, 0x00, 0x48, 0x89, 0xe5, 0xbf, 0x19,
  0x00, 0x00, 0x00, 0xc7, 0x05, 0x66, 0x08, 0x16, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0xee,
  0x48, 0x89, 0x15, 0xb4, 0x08, 0x16, 0x00, 0x48, 0x8d, 0x15, 0x0d, 0xd1, 0xff, 0xff]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [.mem (mrip 1516504 64), .imm 64 128] 11) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 25)] 5) := by dec_rfl
theorem p3_19 : ∀ feat, Dec feat p3 19 (FV7z.mk .mov 32 [.mem (mrip 1443942 32), .imm 32 0] 10) := by dec_rfl
theorem p3_29 : ∀ feat, Dec feat p3 29 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p3_32 : ∀ feat, Dec feat p3 32 (FV7z.mk .mov 64 [.mem (mrip 1444020 64), gr 64 2] 7) := by dec_rfl
theorem p3_39 : ∀ feat, Dec feat p3 39 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709539597 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.stia 64 8013224 128,
  Op.mov 64 5 (.r 4),
  Op.mov 32 7 (.i 25),
  Op.stia 32 7940680 0,
  Op.mov 64 6 (.r 5),
  Op.sta 64 7940768 2,
  Op.mov 64 2 (.i 6484736)]

theorem b3 (prof : Profile) : BlkA prof p3 (0x6321c5 : Addr) 0 46 o3 :=
  .cons (p3_0 _) (OpIA.sti_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p3_11 _) ((OpI.mov (.r 4) (.inr rfl)).at _) (by decide) <|
  .cons (p3_14 _) ((OpI.mov (.i 25) (.inl rfl)).at _) (by decide) <|
  .cons (p3_19 _) (OpIA.sti_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .cons (p3_29 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p3_32 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p3_39 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 46

/-- The stretch at `136`. -/
def p4 : List Byte := [
  0x48, 0x8d, 0x15, 0x81, 0xc1, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x08, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709535617 0)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 8)] 5) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.mov 64 2 (.i 6480768),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 8)]

theorem b4 (prof : Profile) : BlkA prof p4 (0x6321f8 : Addr) 0 15 o4 :=
  .cons (p4_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p4_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p4_10 _) ((OpI.mov (.i 8) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `156`. -/
def p5 : List Byte := [
  0x48, 0x8d, 0x15, 0xdd, 0xc1, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x02, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709535709 0)] 7) := by dec_rfl
theorem p5_7 : ∀ feat, Dec feat p5 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 2)] 5) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.mov 64 2 (.i 6480880),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 2)]

theorem b5 (prof : Profile) : BlkA prof p5 (0x63220c : Addr) 0 15 o5 :=
  .cons (p5_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p5_10 _) ((OpI.mov (.i 2) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `176`. -/
def p6 : List Byte := [
  0x48, 0x8d, 0x15, 0x79, 0xc1, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x13, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709535609 0)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 19)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 2 (.i 6480800),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 19)]

theorem b6 (prof : Profile) : BlkA prof p6 (0x632220 : Addr) 0 15 o6 :=
  .cons (p6_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p6_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p6_10 _) ((OpI.mov (.i 19) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `196`. -/
def p7 : List Byte := [
  0x48, 0x8d, 0x15, 0x25, 0xc1, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x01, 0x00, 0x00, 0x00]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709535525 0)] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p7_10 : ∀ feat, Dec feat p7 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 1)] 5) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.mov 64 2 (.i 6480736),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 1)]

theorem b7 (prof : Profile) : BlkA prof p7 (0x632234 : Addr) 0 15 o7 :=
  .cons (p7_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p7_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p7_10 _) ((OpI.mov (.i 1) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `216`. -/
def p8 : List Byte := [
  0x48, 0x8d, 0x15, 0x81, 0xc1, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x0c, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709535617 0)] 7) := by dec_rfl
theorem p8_7 : ∀ feat, Dec feat p8 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 12)] 5) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 64 2 (.i 6480848),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 12)]

theorem b8 (prof : Profile) : BlkA prof p8 (0x632248 : Addr) 0 15 o8 :=
  .cons (p8_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p8_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p8_10 _) ((OpI.mov (.i 12) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `236`. -/
def p9 : List Byte := [
  0x48, 0x8d, 0x15, 0x7d, 0xbd, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x12, 0x00, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709534589 0)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p9_10 : ∀ feat, Dec feat p9 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 18)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.mov 64 2 (.i 6479840),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 18)]

theorem b9 (prof : Profile) : BlkA prof p9 (0x63225c : Addr) 0 15 o9 :=
  .cons (p9_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p9_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p9_10 _) ((OpI.mov (.i 18) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `256`. -/
def p10 : List Byte := [
  0x48, 0x8d, 0x15, 0x79, 0xbd, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x16, 0x00, 0x00, 0x00]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709534585 0)] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p10_10 : ∀ feat, Dec feat p10 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 22)] 5) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.mov 64 2 (.i 6479856),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 22)]

theorem b10 (prof : Profile) : BlkA prof p10 (0x632270 : Addr) 0 15 o10 :=
  .cons (p10_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p10_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p10_10 _) ((OpI.mov (.i 22) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `276`. -/
def p11 : List Byte := [
  0x48, 0x8d, 0x15, 0x75, 0xbd, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x18, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709534581 0)] 7) := by dec_rfl
theorem p11_7 : ∀ feat, Dec feat p11 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p11_10 : ∀ feat, Dec feat p11 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 24)] 5) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.mov 64 2 (.i 6479872),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 24)]

theorem b11 (prof : Profile) : BlkA prof p11 (0x632284 : Addr) 0 15 o11 :=
  .cons (p11_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p11_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p11_10 _) ((OpI.mov (.i 24) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `296`. -/
def p12 : List Byte := [
  0x48, 0x8d, 0x15, 0xa1, 0xbd, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x15, 0x00, 0x00, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709534625 0)] 7) := by dec_rfl
theorem p12_7 : ∀ feat, Dec feat p12 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p12_10 : ∀ feat, Dec feat p12 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 21)] 5) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.mov 64 2 (.i 6479936),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 21)]

theorem b12 (prof : Profile) : BlkA prof p12 (0x632298 : Addr) 0 15 o12 :=
  .cons (p12_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p12_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p12_10 _) ((OpI.mov (.i 21) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `316`. -/
def p13 : List Byte := [
  0x48, 0x8d, 0x15, 0xad, 0xbd, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x0e, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709534637 0)] 7) := by dec_rfl
theorem p13_7 : ∀ feat, Dec feat p13 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p13_10 : ∀ feat, Dec feat p13 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 14)] 5) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.mov 64 2 (.i 6479968),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 14)]

theorem b13 (prof : Profile) : BlkA prof p13 (0x6322ac : Addr) 0 15 o13 :=
  .cons (p13_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p13_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p13_10 _) ((OpI.mov (.i 14) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `336`. -/
def p14 : List Byte := [
  0x48, 0x8d, 0x15, 0x39, 0xc1, 0xff, 0xff, 0x48, 0x89, 0xee, 0xbf, 0x06, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 18446744073709535545 0)] 7) := by dec_rfl
theorem p14_7 : ∀ feat, Dec feat p14 7 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 5)] 3) := by dec_rfl
theorem p14_10 : ∀ feat, Dec feat p14 10 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 6)] 5) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.mov 64 2 (.i 6480896),
  Op.mov 64 6 (.r 5),
  Op.mov 32 7 (.i 6)]

theorem b14 (prof : Profile) : BlkA prof p14 (0x6322c0 : Addr) 0 15 o14 :=
  .cons (p14_0 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p14_7 _) ((OpI.mov (.r 5) (.inr rfl)).at _) (by decide) <|
  .cons (p14_10 _) ((OpI.mov (.i 6) (.inl rfl)).at _) (by decide) <|
  .nil 15

/-- The stretch at `356`. -/
def p15 : List Byte := [
  0xc7, 0x05, 0xa6, 0x06, 0x16, 0x00, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x44, 0x24, 0x08, 0x64,
  0x48, 0x33, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 32 [.mem (mrip 1443494 32), .imm 32 1] 10) := by dec_rfl
theorem p15_10 : ∀ feat, Dec feat p15 10 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 4) none 1 8 64)] 5) := by dec_rfl
theorem p15_15 : ∀ feat, Dec feat p15 15 (FV7z.mk .xor 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o15 (fb : Addr) : List Op := [
  Op.stia 32 7940484 1,
  Op.ld 64 0 (some 4) none 1 8,
  Op.xormf fb 64 0 none none 1 40]

theorem b15 (prof : Profile) (fb : Addr) : BlkF prof p15 (0x6322d4 : Addr) fb 0 24 (o15 fb) :=
  .cons (p15_0 _) ((OpIA.sti_rip (.inr (.inl rfl)) (by decide)).fs _) (by decide) <|
  .cons (p15_10 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p15_15 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 24

def j1 : List Byte := [0x75, 0x06]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `382`. -/
def p16 : List Byte := [
  0x48, 0x83, 0xc4, 0x10, 0x5d]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem p16_4 : ∀ feat, Dec feat p16 4 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.add 64 4 (.i 16),
  Op.pop 5]

theorem b16 (prof : Profile) : Blk prof p16 0 5 o16 :=
  .cons (p16_0 _) (OpI.add (.i 16) (.inr rfl)) (by decide) <|
  .cons (p16_4 _) (OpI.pop) (by decide) <|
  .nil 5

end FV7z.Pmi
