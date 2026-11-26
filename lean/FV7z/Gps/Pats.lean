import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `__getpagesize` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gps
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x05, 0x6d, 0xcf, 0x12, 0x00, 0x48, 0x85, 0xc0]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, .mem (mrip 1232749 64)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .test 64 [gr 64 0, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lda 64 0 7943128,
  Op.test 64 0 (.r 0)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x666460 : Addr) 0 14 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.ld_rip (.inr rfl) (by decide)) (by decide) <|
  .cons (p0_11 _) ((OpI.test (.r 0) (.inr rfl)).at _) (by decide) <|
  .nil 14

def j0 : List Byte := [0x74, 0x01]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 1] 2) := by dec_rfl

/-- The stretch at `17`. -/
def p1 : List Byte := [
  0x50, 0x48, 0x8d, 0x0d, 0x27, 0xc7, 0x08, 0x00, 0xba, 0x1c, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x35,
  0xeb, 0xc6, 0x08, 0x00, 0x48, 0x8d, 0x3d, 0x22, 0xc7, 0x08, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .push 64 [gr 64 0] 1) := by dec_rfl
theorem p1_1 : ∀ feat, Dec feat p1 1 (FV7z.mk .lea 64 [gr 64 1, .mem (mrip 575271 0)] 7) := by dec_rfl
theorem p1_8 : ∀ feat, Dec feat p1 8 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 28)] 5) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 575211 0)] 7) := by dec_rfl
theorem p1_20 : ∀ feat, Dec feat p1 20 (FV7z.mk .lea 64 [gr 64 7, .mem (mrip 575266 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.push 0,
  Op.mov 64 1 (.i 7285664),
  Op.mov 32 2 (.i 28),
  Op.mov 64 6 (.i 7285616),
  Op.mov 64 7 (.i 7285678)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x666471 : Addr) 0 27 o1 :=
  .cons (p1_0 _) ((OpI.push).at _) (by decide) <|
  .cons (p1_1 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_8 _) ((OpI.mov (.i 28) (.inl rfl)).at _) (by decide) <|
  .cons (p1_13 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_20 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .nil 27

end FV7z.Gps
