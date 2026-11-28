import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NWindows::NFile::NFind::CDirEntry::IsDots() const` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 4) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ids
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x31, 0xc0, 0xf6, 0x47, 0x08, 0xfb]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p0_6 : ∀ feat, Dec feat p0 6 (FV7z.mk .test 8 [.mem (mg (some 7) none 1 8 8), .imm 8 251] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.xor 32 0 (.r 0),
  Op.testmi 8 (some 7) none 1 8 251]

theorem b0 (prof : Profile) : Blk prof p0 0 10 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p0_6 _) (OpI.testmi8) (by decide) <|
  .nil 10

def j0 : List Byte := [0x75, 0x0b]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 11] 2) := by dec_rfl

/-- The stretch at `12`. -/
def p1 : List Byte := [
  0x8b, 0x57, 0x18, 0x8d, 0x4a, 0xff, 0x83, 0xf9, 0x01]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 32 [gr 32 2, .mem (mg (some 7) none 1 24 32)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 32 [gr 32 1, .mem (mg (some 2) none 1 18446744073709551615 0)] 3) := by dec_rfl
theorem p1_6 : ∀ feat, Dec feat p1 6 (FV7z.mk .cmp 32 [gr 32 1, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 32 2 (some 7) none 1 24,
  Op.lea 32 1 (some 2) none 1 18446744073709551615,
  Op.cmp 32 1 (.i 1)]

theorem b1 (prof : Profile) : Blk prof p1 0 9 o1 :=
  .cons (p1_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inl rfl)) (by decide) <|
  .cons (p1_6 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 9

def j1 : List Byte := [0x76, 0x09]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 6) 64 [.rel 9] 2) := by dec_rfl

/-- The stretch at `32`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0x4f, 0x10, 0x80, 0x39, 0x2e]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 1, .mem (mg (some 7) none 1 16 64)] 4) := by dec_rfl
theorem p2_4 : ∀ feat, Dec feat p2 4 (FV7z.mk .cmp 8 [.mem (mg (some 1) none 1 0 8), .imm 8 46] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 1 (some 7) none 1 16,
  Op.cmpmi 8 (some 1) none 1 0 46]

theorem b2 (prof : Profile) : Blk prof p2 0 7 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 7

def j2 : List Byte := [0x75, 0xee]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551598] 2) := by dec_rfl

/-- The stretch at `41`. -/
def p3 : List Byte := [
  0xb8, 0x01, 0x00, 0x00, 0x00, 0x83, 0xfa, 0x01]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .cmp 32 [gr 32 2, Src.opd 32 (.i 1)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.mov 32 0 (.i 1),
  Op.cmp 32 2 (.i 1)]

theorem b3 (prof : Profile) : Blk prof p3 0 8 o3 :=
  .cons (p3_0 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (p3_5 _) (OpI.cmp (.i 1) (.inl rfl)) (by decide) <|
  .nil 8

def j3 : List Byte := [0x74, 0xe4]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551588] 2) := by dec_rfl

/-- The stretch at `51`. -/
def p4 : List Byte := [
  0x80, 0x79, 0x01, 0x2e, 0x0f, 0x94, 0xc0]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .cmp 8 [.mem (mg (some 1) none 1 1 8), .imm 8 46] 4) := by dec_rfl
theorem p4_4 : ∀ feat, Dec feat p4 4 (FV7z.mk (.setcc 4) 8 [gr 8 0] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.cmpmi 8 (some 1) none 1 1 46,
  Op.setcc 4 0]

theorem b4 (prof : Profile) : Blk prof p4 0 7 o4 :=
  .cons (p4_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .cons (p4_4 _) (OpI.setcc) (by decide) <|
  .nil 7

end FV7z.Ids
