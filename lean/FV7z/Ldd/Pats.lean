import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `NCompress::NLzma::CDecoder::~CDecoder` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 5 of them) and each distinct jump (`j*`, 1) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ldd
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0x98, 0xc4, 0x78, 0x00, 0x48, 0xc7, 0xc6, 0xe0, 0x7a,
  0x77, 0x00, 0x53, 0x48, 0x89, 0xfb, 0x48, 0x83, 0xef, 0x80, 0x48, 0x8d, 0x50, 0x10, 0x48, 0x89,
  0x57, 0x80, 0x48, 0x8d, 0x90, 0x88, 0x00, 0x00, 0x00, 0x48, 0x89, 0x57, 0x88, 0x48, 0x8d, 0x90,
  0xb8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x57, 0x90, 0x48, 0x8d, 0x90, 0xe8, 0x00, 0x00, 0x00, 0x48,
  0x89, 0x57, 0x98, 0x48, 0x8d, 0x90, 0x18, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57, 0xa0, 0x48, 0x8d,
  0x90, 0x50, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57, 0xa8, 0x48, 0x8d, 0x90, 0x88, 0x01, 0x00, 0x00,
  0x48, 0x05, 0xb8, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57, 0xb0, 0x48, 0x89, 0x47, 0xb8]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7914648)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .mov 64 [gr 64 6, Src.opd 64 (.i 7830240)] 7) := by dec_rfl
theorem p0_18 : ∀ feat, Dec feat p0 18 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .sub 64 [gr 64 7, Src.opd 64 (.i 18446744073709551488)] 4) := by dec_rfl
theorem p0_26 : ∀ feat, Dec feat p0 26 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 16 0)] 4) := by dec_rfl
theorem p0_30 : ∀ feat, Dec feat p0 30 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551488 64), gr 64 2] 4) := by dec_rfl
theorem p0_34 : ∀ feat, Dec feat p0 34 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 136 0)] 7) := by dec_rfl
theorem p0_41 : ∀ feat, Dec feat p0 41 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551496 64), gr 64 2] 4) := by dec_rfl
theorem p0_45 : ∀ feat, Dec feat p0 45 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 184 0)] 7) := by dec_rfl
theorem p0_52 : ∀ feat, Dec feat p0 52 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551504 64), gr 64 2] 4) := by dec_rfl
theorem p0_56 : ∀ feat, Dec feat p0 56 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 232 0)] 7) := by dec_rfl
theorem p0_63 : ∀ feat, Dec feat p0 63 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551512 64), gr 64 2] 4) := by dec_rfl
theorem p0_67 : ∀ feat, Dec feat p0 67 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 280 0)] 7) := by dec_rfl
theorem p0_74 : ∀ feat, Dec feat p0 74 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551520 64), gr 64 2] 4) := by dec_rfl
theorem p0_78 : ∀ feat, Dec feat p0 78 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 336 0)] 7) := by dec_rfl
theorem p0_85 : ∀ feat, Dec feat p0 85 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551528 64), gr 64 2] 4) := by dec_rfl
theorem p0_89 : ∀ feat, Dec feat p0 89 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 392 0)] 7) := by dec_rfl
theorem p0_96 : ∀ feat, Dec feat p0 96 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 440)] 6) := by dec_rfl
theorem p0_102 : ∀ feat, Dec feat p0 102 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551536 64), gr 64 2] 4) := by dec_rfl
theorem p0_106 : ∀ feat, Dec feat p0 106 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551544 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 7914648),
  Op.mov 64 6 (.i 7830240),
  Op.push 3,
  Op.mov 64 3 (.r 7),
  Op.sub 64 7 (.i 18446744073709551488),
  Op.lea 64 2 (some 0) none 1 16,
  Op.st 64 (some 7) none 1 18446744073709551488 2,
  Op.lea 64 2 (some 0) none 1 136,
  Op.st 64 (some 7) none 1 18446744073709551496 2,
  Op.lea 64 2 (some 0) none 1 184,
  Op.st 64 (some 7) none 1 18446744073709551504 2,
  Op.lea 64 2 (some 0) none 1 232,
  Op.st 64 (some 7) none 1 18446744073709551512 2,
  Op.lea 64 2 (some 0) none 1 280,
  Op.st 64 (some 7) none 1 18446744073709551520 2,
  Op.lea 64 2 (some 0) none 1 336,
  Op.st 64 (some 7) none 1 18446744073709551528 2,
  Op.lea 64 2 (some 0) none 1 392,
  Op.add 64 0 (.i 440),
  Op.st 64 (some 7) none 1 18446744073709551536 2,
  Op.st 64 (some 7) none 1 18446744073709551544 0]

theorem b0 (prof : Profile) : Blk prof p0 0 110 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7914648) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.mov (.i 7830240) (.inr rfl)) (by decide) <|
  .cons (p0_18 _) (OpI.push) (by decide) <|
  .cons (p0_19 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p0_22 _) (OpI.sub (.i 18446744073709551488) (.inr rfl)) (by decide) <|
  .cons (p0_26 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_30 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_34 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_41 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_45 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_52 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_56 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_63 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_67 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_74 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_78 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_85 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_89 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_96 _) (OpI.add (.i 440) (.inr rfl)) (by decide) <|
  .cons (p0_102 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p0_106 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 110

/-- The stretch at `115`. -/
def p1 : List Byte := [
  0x48, 0x8b, 0x7b, 0x60]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 96 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ld 64 7 (some 3) none 1 96]

theorem b1 (prof : Profile) : Blk prof p1 0 4 o1 :=
  .cons (p1_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `124`. -/
def p2 : List Byte := [
  0x48, 0x8b, 0xbb, 0x00, 0x01, 0x00, 0x00, 0x48, 0x85, 0xff]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 3) none 1 256 64)] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .test 64 [gr 64 7, Src.opd 64 (.r 7)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.ld 64 7 (some 3) none 1 256,
  Op.test 64 7 (.r 7)]

theorem b2 (prof : Profile) : Blk prof p2 0 10 o2 :=
  .cons (p2_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p2_7 _) (OpI.test (.r 7) (.inr rfl)) (by decide) <|
  .nil 10

def j0 : List Byte := [0x74, 0x06]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 4) 64 [.rel 6] 2) := by dec_rfl

/-- The stretch at `136`. -/
def p3 : List Byte := [
  0x48, 0x8b, 0x07]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 0 64)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.ld 64 0 (some 7) none 1 0]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 3

/-- The stretch at `142`. -/
def p4 : List Byte := [
  0x5b]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.pop 3]

theorem b4 (prof : Profile) : Blk prof p4 0 1 o4 :=
  .cons (p4_0 _) (OpI.pop) (by decide) <|
  .nil 1

end FV7z.Ldd
