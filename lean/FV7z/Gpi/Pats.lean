import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CHandler::GetArchivePropertyInfo` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 3 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Gpi
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x83, 0xfe, 0x01]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 32 [gr 32 6, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmp 32 6 (.i 1)]

theorem b0 (prof : Profile) : Blk prof p0 0 7 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 7

def j0 : List Byte := [0x77, 0x2f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `9`. -/
def p1 : List Byte := [
  0x89, 0xf6, 0x48, 0x8d, 0x05, 0x1a, 0xf3, 0x23, 0x00, 0x0f, 0xb6, 0x04, 0x30, 0x89, 0x01, 0x48,
  0xc7, 0xc1, 0xa0, 0x9b, 0x6d, 0x00, 0x0f, 0xb6, 0x04, 0x01, 0x66, 0x41, 0x89, 0x00, 0x31, 0xc0,
  0x48, 0xc7, 0x02, 0x00, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.r 6)] 2) := by dec_rfl
theorem p1_2 : ∀ feat, Dec feat p1 2 (FV7z.mk .lea 64 [gr 64 0, .mem (mrip 2355994 0)] 7) := by dec_rfl
theorem p1_9 : ∀ feat, Dec feat p1 9 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 0) (some 6) 1 0 8)] 4) := by dec_rfl
theorem p1_13 : ∀ feat, Dec feat p1 13 (FV7z.mk .mov 32 [.mem (mg (some 1) none 1 0 32), gr 32 0] 2) := by dec_rfl
theorem p1_15 : ∀ feat, Dec feat p1 15 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.i 7183264)] 7) := by dec_rfl
theorem p1_22 : ∀ feat, Dec feat p1 22 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 1) (some 0) 1 0 8)] 4) := by dec_rfl
theorem p1_26 : ∀ feat, Dec feat p1 26 (FV7z.mk .mov 16 [.mem (mg (some 8) none 1 0 16), gr 16 0] 4) := by dec_rfl
theorem p1_30 : ∀ feat, Dec feat p1 30 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p1_32 : ∀ feat, Dec feat p1 32 (FV7z.mk .mov 64 [.mem (mg (some 2) none 1 0 64), .imm 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 32 6 (.r 6),
  Op.mov 64 0 (.i 7199788),
  Op.ldzx 8 0 (some 0) (some 6) 1 0,
  Op.st 32 (some 1) none 1 0 0,
  Op.mov 64 1 (.i 7183264),
  Op.ldzx 8 0 (some 1) (some 0) 1 0,
  Op.st 16 (some 8) none 1 0 0,
  Op.xor 32 0 (.r 0),
  Op.sti 64 (some 2) none 1 0 0]

theorem b1 (prof : Profile) : BlkA prof p1 (0x49e909 : Addr) 0 39 o1 :=
  .cons (p1_0 _) ((OpI.mov (.r 6) (.inl rfl)).at _) (by decide) <|
  .cons (p1_2 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_9 _) ((OpI.ldzx (.inl rfl)).at _) (by decide) <|
  .cons (p1_13 _) ((OpI.st (.inr (.inr (.inl rfl)))).at _) (by decide) <|
  .cons (p1_15 _) ((OpI.mov (.i 7183264) (.inr rfl)).at _) (by decide) <|
  .cons (p1_22 _) ((OpI.ldzx (.inl rfl)).at _) (by decide) <|
  .cons (p1_26 _) ((OpI.st (.inr (.inl rfl))).at _) (by decide) <|
  .cons (p1_30 _) ((OpI.xor (.r 0) (.inl rfl)).at _) (by decide) <|
  .cons (p1_32 _) ((OpI.sti (.inr (.inr (.inr rfl)))).at _) (by decide) <|
  .nil 39

/-- The stretch at `56`. -/
def p2 : List Byte := [
  0xb8, 0x57, 0x00, 0x07, 0x80]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 2147942487)] 5) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 0 (.i 2147942487)]

theorem b2 (prof : Profile) : Blk prof p2 0 5 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 2147942487) (.inl rfl)) (by decide) <|
  .nil 5

end FV7z.Gpi
