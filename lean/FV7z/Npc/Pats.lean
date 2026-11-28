import FV7z.Lemmas.SpFs
import FV7z.Lemmas.CmpMrF
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `_nl_postload_ctype` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Npc
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x15, 0x75, 0x43, 0x11, 0x00, 0x48, 0xc7, 0xc7, 0x80, 0xff,
  0xff, 0xff, 0x48, 0x8d, 0x35, 0x67, 0x43, 0x11, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 2, .mem (mrip 1131381 64)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.i 18446744073709551488)] 7) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1131367 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lda 64 2 7938752,
  Op.mov 64 7 (.i 18446744073709551488),
  Op.mov 64 6 (.i 7938752)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x67df40 : Addr) 0 25 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_11 _) ((OpI.mov (.i 18446744073709551488) (.inr rfl)).at _) (by decide) <|
  .cons (p0_18 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 25

/-- The stretch at `25`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x42, 0x40, 0x48, 0x8d, 0x88, 0x00, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x42, 0x58, 0x48,
  0x8b, 0x52, 0x48]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 64 64)] 4) := by dec_rfl
theorem p1_4 : ∀ feat, Dec feat p1 4 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 256 0)] 7) := by dec_rfl
theorem p1_11 : ∀ feat, Dec feat p1 11 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 88 64)] 4) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 2) none 1 72 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 0 (some 2) none 1 64,
  Op.lea 64 1 (some 0) none 1 256,
  Op.ld 64 0 (some 2) none 1 88,
  Op.ld 64 2 (some 2) none 1 72]

theorem b1 (prof : Profile) : Blk prof p1 0 19 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_4 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_11 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_15 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 19

/-- The stretch at `44`. -/
def p2 : List Byte := [
  0x48, 0x89, 0x0d, 0xb5, 0x43, 0x11, 0x00, 0x48, 0x05, 0x00, 0x02, 0x00, 0x00, 0x48, 0x81, 0xc2,
  0x00, 0x02, 0x00, 0x00, 0x48, 0x89, 0x05, 0xa9, 0x43, 0x11, 0x00, 0x48, 0x89, 0x15, 0xaa, 0x43,
  0x11, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mrip 1131445 64), gr 64 1] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 512)] 6) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.i 512)] 7) := by dec_rfl
theorem p2_20 : ∀ feat, Dec feat p2 20 (FV7z.mk .mov 64 [.mem (mrip 1131433 64), gr 64 0] 7) := by dec_rfl
theorem p2_27 : ∀ feat, Dec feat p2 27 (FV7z.mk .mov 64 [.mem (mrip 1131434 64), gr 64 2] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.sta 64 7938856 1,
  Op.add 64 0 (.i 512),
  Op.add 64 2 (.i 512),
  Op.sta 64 7938864 0,
  Op.sta 64 7938872 2]

theorem b2 (prof : Profile) : BlkA prof p2 (0x67df6c : Addr) 0 34 o2 :=
  .cons (p2_0 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p2_7 _) ((OpI.add (.i 512) (.inr rfl)).at _) (by decide) <|
  .cons (p2_13 _) ((OpI.add (.i 512) (.inr rfl)).at _) (by decide) <|
  .cons (p2_20 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .cons (p2_27 _) (OpIA.st_rip (.inr (.inr rfl)) (by decide)) (by decide) <|
  .nil 34

/-- The stretch at `78`. -/
def p3 : List Byte := [
  0x64, 0x48, 0x39, 0x37]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [.mem (mf (some 7) none 1 0 64), gr 64 6] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 (fb : Addr) : List Op := [
  Op.cmpmrf fb 64 (some 7) none 1 0 6]

theorem b3 (prof : Profile) (fb : Addr) : BlkF prof p3 (0x67df8e : Addr) fb 0 4 (o3 fb) :=
  .cons (p3_0 _) (OpIF.cmpmrf (.inr rfl)) (by decide) <|
  .nil 4

def j0 : List Byte := [0x74, 0x04]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `88`. -/
def p4 : List Byte := [
  0x48, 0xc7, 0xc6, 0xd0, 0xff, 0xff, 0xff, 0x64, 0x48, 0x89, 0x0e, 0x48, 0xc7, 0xc1, 0xc8, 0xff,
  0xff, 0xff, 0x64, 0x48, 0x89, 0x11, 0x48, 0xc7, 0xc2, 0xc0, 0xff, 0xff, 0xff, 0x64, 0x48, 0x89,
  0x02]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 18446744073709551568)] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [.mem (mf (some 6) none 1 0 64), gr 64 1] 4) := by dec_rfl
theorem p4_11 : ∀ feat, Dec feat p4 11 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 18446744073709551560)] 7) := by dec_rfl
theorem p4_18 : ∀ feat, Dec feat p4 18 (FV7z.mk .mov 64 [.mem (mf (some 1) none 1 0 64), gr 64 2] 4) := by dec_rfl
theorem p4_22 : ∀ feat, Dec feat p4 22 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18446744073709551552)] 7) := by dec_rfl
theorem p4_29 : ∀ feat, Dec feat p4 29 (FV7z.mk .mov 64 [.mem (mf (some 2) none 1 0 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 (fb : Addr) : List Op := [
  Op.mov 64 6 (.i 18446744073709551568),
  Op.stf fb 64 (some 6) none 1 0 1,
  Op.mov 64 1 (.i 18446744073709551560),
  Op.stf fb 64 (some 1) none 1 0 2,
  Op.mov 64 2 (.i 18446744073709551552),
  Op.stf fb 64 (some 2) none 1 0 0]

theorem b4 (prof : Profile) (fb : Addr) : BlkF prof p4 (0x67df98 : Addr) fb 0 33 (o4 fb) :=
  .cons (p4_0 _) (((OpI.mov (.i 18446744073709551568) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_7 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p4_11 _) (((OpI.mov (.i 18446744073709551560) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_18 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .cons (p4_22 _) (((OpI.mov (.i 18446744073709551552) (.inr rfl)).at _).fs _) (by decide) <|
  .cons (p4_29 _) (OpIF.stf (.inr rfl)) (by decide) <|
  .nil 33

end FV7z.Npc
