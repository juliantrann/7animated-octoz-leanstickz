import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `RegisterArc` (PLAN.md §M, constructors)

Each distinct stretch between labels and jumps (`p*`, 2 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Rga
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x05, 0xd6, 0x04, 0x1d, 0x00, 0x83, 0xf8, 0x47]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 32 [gr 32 0, .mem (mrip 1901782 32)] 6) := by dec_rfl
theorem p0_10 : ∀ feat, Dec feat p0 10 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 71)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.lda 32 0 7991296,
  Op.cmp 32 0 (.i 71)]

theorem b0 (prof : Profile) : BlkA prof p0 (0x5ceb20 : Addr) 0 13 o0 :=
  .cons (p0_0 _) ((OpI.endbr).at _) (by decide) <|
  .cons (p0_4 _) (OpIA.ld_rip (.inl rfl) (by decide)) (by decide) <|
  .cons (p0_10 _) ((OpI.cmp (.i 71) (.inl rfl)).at _) (by decide) <|
  .nil 13

def j0 : List Byte := [0x77, 0x16]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `15`. -/
def p1 : List Byte := [
  0x89, 0xc1, 0x48, 0x8d, 0x15, 0x88, 0x02, 0x1d, 0x00, 0x83, 0xc0, 0x01, 0x48, 0x89, 0x3c, 0xca,
  0x89, 0x05, 0xbb, 0x04, 0x1d, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 1901192 0)] 7) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl
theorem p1_12 : ∀ feat, Dec feat p1 12 (FV7z.mk .mov 64 [.mem (mg (some 2) (some 1) 8 0 64), gr 64 7] 4) := by dec_rfl
theorem p1_16 : ∀ feat, Dec feat p1 16 (FV7z.mk .mov 32 [.mem (mrip 1901755 32), gr 32 0] 6) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 1 (.r 0),
  Op.mov 64 2 (.i 7990720),
  Op.add 32 0 (.i 1),
  Op.st 64 (some 2) (some 1) 8 0 7,
  Op.sta 32 7991296 0]

theorem b1 (prof : Profile) : BlkA prof p1 (0x5ceb2f : Addr) 0 22 o1 :=
  .cons (p1_0 _) ((OpI.mov (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p1_2 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_9 _) ((OpI.add (.i 1) (.inl rfl)).at _) (by decide) <|
  .cons (p1_12 _) ((OpI.st (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .cons (p1_16 _) (OpIA.st_rip (.inr (.inl rfl)) (by decide)) (by decide) <|
  .nil 22

end FV7z.Rga
