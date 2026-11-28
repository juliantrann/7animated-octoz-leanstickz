import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `do_tunable_update_val` (PLAN.md G3, startup)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 7) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Dtu
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0x8b, 0x47, 0x08, 0x83, 0xf8, 0x03]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .mov 32 [gr 32 0, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl
theorem p0_3 : ∀ feat, Dec feat p0 3 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 3)] 3) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.ld 32 0 (some 7) none 1 8,
  Op.cmp 32 0 (.i 3)]

theorem b0 (prof : Profile) : Blk prof p0 0 6 o0 :=
  .cons (p0_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p0_3 _) (OpI.cmp (.i 3) (.inl rfl)) (by decide) <|
  .nil 6

def j0 : List Byte := [0x74, 0x28]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `8`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x16, 0x83, 0xf8, 0x01]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 2, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .cmp 32 [gr 32 0, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 2 (some 6) none 1 0,
  Op.cmp 32 0 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 6 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 6

def j1 : List Byte := [0x74, 0x02]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 2] 2) := by dec_rfl

def j2 : List Byte := [0x76, 0x26]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 6) 64 [.rel 38] 2) := by dec_rfl

/-- The stretch at `18`. -/
def p2 : List Byte := [
  0x48, 0x3b, 0x57, 0x10]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 64 [gr 64 2, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpm 64 2 (some 7) none 1 16]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 4

def j3 : List Byte := [0x72, 0x1c]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 2) 64 [.rel 28] 2) := by dec_rfl

/-- The stretch at `24`. -/
def p3 : List Byte := [
  0x48, 0x3b, 0x57, 0x18]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 64 [gr 64 2, .mem (mg (some 7) none 1 24 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpm 64 2 (some 7) none 1 24]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.cmpm (.inr rfl)) (by decide) <|
  .nil 4

def j4 : List Byte := [0x77, 0x16]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 7) 64 [.rel 22] 2) := by dec_rfl

/-- The stretch at `30`. -/
def p4 : List Byte := [
  0x48, 0x89, 0x57, 0x20, 0xc6, 0x47, 0x28, 0x01]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), gr 64 2] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 40 8), .imm 8 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.st 64 (some 7) none 1 32 2,
  Op.sti 8 (some 7) none 1 40 1]

theorem b4 (prof : Profile) : Blk prof p4 0 8 o4 :=
  .cons (p4_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_4 _) (OpI.sti (.inl rfl)) (by decide) <|
  .nil 8

/-- The stretch at `48`. -/
def p5 : List Byte := [
  0x48, 0x89, 0x77, 0x20]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 32 64), gr 64 6] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 64 (some 7) none 1 32 6]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 4

def j5 : List Byte := [0x7c, 0xf6]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 12) 64 [.rel 18446744073709551606] 2) := by dec_rfl

def j6 : List Byte := [0x7f, 0xf0]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk (.jcc 15) 64 [.rel 18446744073709551600] 2) := by dec_rfl

end FV7z.Dtu
