import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps25
import FV7z.Lemmas.BlkOps16
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CPropVariant::~CPropVariant` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 3) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Pvd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x0f, 0xb7, 0x07, 0x66, 0x83, 0xf8, 0x07]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 16)] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 7)] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.ldzx 16 0 (some 7) none 1 0,
  Op.cmp 16 0 (.i 7)]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.cmp16 (.i 7)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x76, 0x2b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 6) 64 [.rel 43] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x83, 0xe8, 0x0a, 0x66, 0x83, 0xf8, 0x36]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .sub 32 [gr 32 0, Src.opd 32 (.i 10)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 16 [gr 16 0, Src.opd 16 (.i 54)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.sub 32 0 (.i 10),
  Op.cmp 16 0 (.i 54)]

theorem b1 (prof : Profile) : Blk prof p1 0 7 o1 :=
  .cons (p1_0 _) (OpI.sub (.i 10) (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.cmp16 (.i 54)) (by decide) <|
  .nil 7

def j1 : List Byte := [0x77, 0x10]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 7) 64 [.rel 16] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p2 : List Byte := [
  0x48, 0xba, 0xc3, 0x3f, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x48, 0x0f, 0xa3, 0xc2]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.i 18014398509498307)] 10) := by dec_rfl
theorem p2_10 : ∀ feat, Dec feat p2 10 (FV7z.mk (.bit (BitMn.bt)) 64 [gr 64 2, gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 64 2 (.i 18014398509498307),
  Op.bt64 2 0]

theorem b2 (prof : Profile) : Blk prof p2 0 14 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 18014398509498307) (.inr rfl)) (by decide) <|
  .cons (p2_10 _) (OpI.bt64) (by decide) <|
  .nil 14

def j2 : List Byte := [0x72, 0x0e]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 2) 64 [.rel 14] 2) := by dec_rfl

/-- The stretch at `38`. -/
def p3 : List Byte := [
  0x48, 0x83, 0xec, 0x08]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .sub 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.sub 64 4 (.i 8)]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.sub (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `47`. -/
def p4 : List Byte := [
  0x48, 0x83, 0xc4, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .add 64 [gr 64 4, Src.opd 64 (.i 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.add 64 4 (.i 8)]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Pvd
