import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CExtractScanConsole::StartScanning` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Sts
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x83, 0x7f, 0x50, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 80 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 64 (some 7) none 1 80 0]

theorem b0 (prof : Profile) : Blk prof p0 0 9 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi64) (by decide) <|
  .nil 9

def j0 : List Byte := [0x74, 0x1d]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 29] 2) := by dec_rfl

/-- The stretch at `11`. -/
def p1 : List Byte := [
  0x80, 0x7f, 0x58, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 88 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmi 8 (some 7) none 1 88 0]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x75, 0x17]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 5) 64 [.rel 23] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p2 : List Byte := [
  0x48, 0x83, 0xc7, 0x30, 0x48, 0x8d, 0x35, 0x87, 0x15, 0x10, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 48)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 1054087 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.add 64 7 (.i 48),
  Op.mov 64 6 (.i 7248739)]

theorem b2 (prof : Profile) : BlkA prof p2 (0x5e85d1 : Addr) 0 11 o2 :=
  .cons (p2_0 _) ((OpI.add (.i 48) (.inr rfl)).at _) (by decide) <|
  .cons (p2_4 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 11

end FV7z.Sts
