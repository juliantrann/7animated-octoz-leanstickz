import FV7z.Lemmas.SpFs
import FV7z.Lemmas.CmovLd
import FV7z.Lemmas.TestMr
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps3
/-!
# The stretches of straight-line code of `__bsd_signal.part.0` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Bsg
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x48, 0x81, 0xec, 0x48, 0x01, 0x00, 0x00, 0x41, 0x89, 0xf8, 0xb9, 0x10, 0x00, 0x00, 0x00, 0x64,
  0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0x38, 0x01, 0x00, 0x00,
  0x31, 0xc0, 0x48, 0x8d, 0x54, 0x24, 0x08, 0x48, 0x89, 0x34, 0x24, 0x48, 0x89, 0xe6, 0x48, 0x89,
  0xd7, 0x48, 0x8d, 0x94, 0x24, 0xa0, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 328)] 7) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .mov 32 [gr 32 8, Src.opd 32 (.r 7)] 3) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.i 16)] 5) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .mov 64 [gr 64 0, .mem (mf none none 1 40 64)] 9) := by dec_rfl
theorem p0_24 : ∀ feat, Dec feat p0 24 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 312 64), gr 64 0] 8) := by dec_rfl
theorem p0_32 : ∀ feat, Dec feat p0 32 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 4) none 1 8 0)] 5) := by dec_rfl
theorem p0_39 : ∀ feat, Dec feat p0 39 (FV7z.mk .mov 64 [.mem (mg (some 4) none 1 0 64), gr 64 6] 4) := by dec_rfl
theorem p0_43 : ∀ feat, Dec feat p0 43 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.r 4)] 3) := by dec_rfl
theorem p0_46 : ∀ feat, Dec feat p0 46 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem p0_49 : ∀ feat, Dec feat p0 49 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 4) none 1 160 0)] 8) := by dec_rfl

/-- What the stretch does. -/
def o0 (fb : Addr) : List Op := [
  Op.sub 64 4 (.i 328),
  Op.mov 32 8 (.r 7),
  Op.mov 32 1 (.i 16),
  Op.ldf fb 64 0 none none 1 40,
  Op.st 64 (some 4) none 1 312 0,
  Op.xor 32 0 (.r 0),
  Op.lea 64 2 (some 4) none 1 8,
  Op.st 64 (some 4) none 1 0 6,
  Op.mov 64 6 (.r 4),
  Op.mov 64 7 (.r 2),
  Op.lea 64 2 (some 4) none 1 160]

theorem b0 (prof : Profile) (fb : Addr) : BlkF prof p0 (0x622510 : Addr) fb 0 57 (o0 fb) :=
  .cons (p0_0 _) (((OpI.sub (.i 328) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_7 _) (((OpI.mov (.r 7) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_10 _) (((OpI.mov (.i 16) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_15 _) (OpIF.ldf (.inr rfl)) (by decide) <|
  .cons (p0_24 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_32 _) (((OpI.xor (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p0_34 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_39 _) (((OpI.st (.inr (.inr (.inr rfl)))).at _).fs _) (by decide) <|
  .cons (p0_43 _) (((OpI.mov (.r 4) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_46 _) (((OpI.mov (.r 2) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p0_49 _) (((OpI.lea (.inr rfl)).at _).fs _) (by decide) <|
  .nil 57

/-- The stretch at `60`. -/
def p1 : List Byte := [
  0x41, 0x8d, 0x48, 0xff, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x44, 0x89, 0xc7, 0x48, 0xd3, 0xe0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 8) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.r 8)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.r 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.lea 32 1 (some 8) none 1 18446744073709551615,
  Op.mov 32 0 (.i 1),
  Op.mov 32 7 (.r 8),
  Op.shl64 0 (.r 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 15 o1 :=
  .cons (p1_0 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p1_9 _) (OpI.mov (.r 8) (.inl rfl)) (by decide) <|
  .cons (p1_12 _) (OpI.shl64 (.r 1)) (by decide) <|
  .nil 15

/-- The stretch at `80`. -/
def p2 : List Byte := [
  0x48, 0x85, 0x05, 0x19, 0x5e, 0x18, 0x00, 0x0f, 0x94, 0xc0, 0x0f, 0xb6, 0xc0, 0xc1, 0xe0, 0x1c,
  0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .test 64 [.mem (mrip 1596953 64), gr 64 0] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk .movzx 32 [gr 32 0, gr 8 0] 3) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .shl 32 [gr 32 0, Src.opd 8 (.i 28)] 3) := by dec_rfl
theorem p2_16 : ∀ feat, Dec feat p2 16 (FV7z.mk .mov 32 [.mem (mg (some 4) none 1 136 32), gr 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.testmra 64 8029056 0,
  Op.setcc 4 0,
  Op.zxr 0 0,
  Op.shl 0 (.i 28),
  Op.st 32 (some 4) none 1 136 0]

theorem b2 (prof : Profile) : BlkA prof p2 (0x622560 : Addr) 0 23 o2 :=
  .cons (p2_0 _) (OpIA.testmr_rip (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.setcc).at _) (by decide) <|
  .cons (p2_10 _) ((OpI.zxr).at _) (by decide) <|
  .cons (p2_13 _) ((OpI.shl (.i 28)).at _) (by decide) <|
  .cons (p2_16 _) ((OpI.st (.inr (.inr (.inl rfl)))).at _) (by decide) <|
  .nil 23

/-- The stretch at `108`. -/
def p3 : List Byte := [
  0x85, 0xc0, 0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff, 0x48, 0x0f, 0x49, 0x84, 0x24, 0xa0, 0x00,
  0x00, 0x00, 0x48, 0x8b, 0x8c, 0x24, 0x38, 0x01, 0x00, 0x00, 0x64, 0x48, 0x33, 0x0c, 0x25, 0x28,
  0x00, 0x00, 0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_2 : ∀ feat, Dec feat p3 2 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 18446744073709551615)] 7) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk (.cmovcc 9) 64 [gr 64 0, .mem (mg (some 4) none 1 160 64)] 9) := by dec_rfl
theorem p3_18 : ∀ feat, Dec feat p3 18 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 4) none 1 312 64)] 8) := by dec_rfl
theorem p3_26 : ∀ feat, Dec feat p3 26 (FV7z.mk .xor 64 [gr 64 1, .mem (mf none none 1 40 64)] 9) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.test 32 0 (.r 0),
  Op.mov 64 0 (.i 18446744073709551615),
  Op.cmovld64 9 0 (some 4) none 1 160,
  Op.ld 64 1 (some 4) none 1 312,
  Op.xormf fb 64 1 none none 1 40]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x62257c : Addr) fb 0 35 (o3 fb) :=
  .cons (p3_0 _) (((OpI.test (.r 0) (.inl rfl)).at _).fs _) (by decide) <|
  .cons (p3_2 _) (((OpI.mov (.i 18446744073709551615) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_9 _) (((OpI.cmovld64).at _).fs _) (by decide) <|
  .cons (p3_18 _) (((OpI.ld (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p3_26 _) (OpIF.xormf (.inr rfl)) (by decide) <|
  .nil 35

def j0 : List Byte := [0x75, 0x08]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 8] 2) := by dec_rfl

/-- The stretch at `145`. -/
def p4 : List Byte := [
  0x48, 0x81, 0xc4, 0x48, 0x01, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 328)] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 328)]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.add (.i 328) (.inr rfl)) (by decide) <|
  .nil 7

end FV7z.Bsg
