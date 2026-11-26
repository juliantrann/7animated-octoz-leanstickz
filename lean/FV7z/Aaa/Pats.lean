import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWildcard::CItem::AreAllAllowed` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 6 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Aaa
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0x7f, 0x11, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 17 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 8 (some 7) none 1 17 0]

theorem b0 (prof : Profile) : Blk prof p0 0 8 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 8

def j0 : List Byte := [0x74, 0x12]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl

/-- The stretch at `10`. -/
def p1 : List Byte := [
  0x80, 0x7f, 0x12, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 18 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmi 8 (some 7) none 1 18 0]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j1 : List Byte := [0x74, 0x0c]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 12] 2) := by dec_rfl

/-- The stretch at `16`. -/
def p2 : List Byte := [
  0x80, 0x7f, 0x13, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 19 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 8 (some 7) none 1 19 0]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x74, 0x06]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `22`. -/
def p3 : List Byte := [
  0x83, 0x7f, 0x08, 0x01]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 32 [.mem (mg (some 7) none 1 8 32), .imm 32 1] 4) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpmi 32 (some 7) none 1 8 1]

theorem b3 (prof : Profile) : Blk prof p3 0 4 o3 :=
  .cons (p3_0 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .nil 4

def j3 : List Byte := [0x74, 0x04]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl

/-- The stretch at `28`. -/
def p4 : List Byte := [
  0x31, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.xor 32 0 (.r 0)]

theorem b4 (prof : Profile) : Blk prof p4 0 2 o4 :=
  .cons (p4_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 2

/-- The stretch at `32`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x07, 0x48, 0x8d, 0x35, 0x1f, 0xb3, 0x29, 0x00, 0x48, 0x8b, 0x00, 0x48, 0x8b, 0x38]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .lea 64 [gr 64 6, .mem (mrip 2732831 0)] 7) := by dec_rfl
theorem p5_10 : ∀ feat, Dec feat p5 10 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl
theorem p5_13 : ∀ feat, Dec feat p5 13 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 0) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 0 (some 7) none 1 0,
  Op.mov 64 6 (.i 7265497),
  Op.ld 64 0 (some 0) none 1 0,
  Op.ld 64 7 (some 0) none 1 0]

theorem b5 (prof : Profile) : BlkA prof p5 (0x4529b0 : Addr) 0 16 o5 :=
  .cons (p5_0 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p5_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p5_10 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .cons (p5_13 _) ((OpI.ld (.inr rfl)).at _) (by decide) <|
  .nil 16

end FV7z.Aaa
