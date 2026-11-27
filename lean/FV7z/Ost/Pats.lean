import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps20
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `COpenCallbackConsole::Open_SetTotal` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 10 of them) and each distinct jump (`j*`, 8) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Ost
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x80, 0xbf, 0xf9, 0x00, 0x00, 0x00, 0x00]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 249 8), .imm 8 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.cmpmi 8 (some 7) none 1 249 0]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 11

def j0 : List Byte := [0x75, 0x2f]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 5) 64 [.rel 47] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x48, 0x83, 0x7f, 0x40, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .cmp 64 [.mem (mg (some 7) none 1 64 64), .imm 64 0] 5) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.cmpmi 64 (some 7) none 1 64 0]

theorem b1 (prof : Profile) : Blk prof p1 0 5 o1 :=
  .cons (p1_0 _) (OpI.cmpmi64) (by decide) <|
  .nil 5

def j1 : List Byte := [0x74, 0x28]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk (.jcc 4) 64 [.rel 40] 2) := by dec_rfl

/-- The stretch at `20`. -/
def p2 : List Byte := [
  0x80, 0x7f, 0x48, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .cmp 8 [.mem (mg (some 7) none 1 72 8), .imm 8 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.cmpmi 8 (some 7) none 1 72 0]

theorem b2 (prof : Profile) : Blk prof p2 0 4 o2 :=
  .cons (p2_0 _) (OpI.cmpmi (.inl rfl)) (by decide) <|
  .nil 4

def j2 : List Byte := [0x75, 0x22]
theorem j2_0 : ∀ feat, Dec feat j2 0 (FV7z.mk (.jcc 5) 64 [.rel 34] 2) := by dec_rfl

/-- The stretch at `26`. -/
def p3 : List Byte := [
  0x48, 0x85, 0xf6]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.test 64 6 (.r 6)]

theorem b3 (prof : Profile) : Blk prof p3 0 3 o3 :=
  .cons (p3_0 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .nil 3

def j3 : List Byte := [0x74, 0x31]
theorem j3_0 : ∀ feat, Dec feat j3 0 (FV7z.mk (.jcc 4) 64 [.rel 49] 2) := by dec_rfl

/-- The stretch at `31`. -/
def p4 : List Byte := [
  0x48, 0x8b, 0x06, 0xc6, 0x87, 0xf8, 0x00, 0x00, 0x00, 0x01, 0x48, 0x89, 0x47, 0x10, 0x48, 0x85,
  0xd2]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 6) none 1 0 64)] 3) := by dec_rfl
theorem p4_3 : ∀ feat, Dec feat p4 3 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 248 8), .imm 8 1] 7) := by dec_rfl
theorem p4_10 : ∀ feat, Dec feat p4 10 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), gr 64 0] 4) := by dec_rfl
theorem p4_14 : ∀ feat, Dec feat p4 14 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ld 64 0 (some 6) none 1 0,
  Op.sti 8 (some 7) none 1 248 1,
  Op.st 64 (some 7) none 1 16 0,
  Op.test 64 2 (.r 2)]

theorem b4 (prof : Profile) : Blk prof p4 0 17 o4 :=
  .cons (p4_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p4_3 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p4_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_14 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 17

def j4 : List Byte := [0x74, 0x0a]
theorem j4_0 : ∀ feat, Dec feat j4 0 (FV7z.mk (.jcc 4) 64 [.rel 10] 2) := by dec_rfl

/-- The stretch at `50`. -/
def p5 : List Byte := [
  0x48, 0x8b, 0x02, 0x48, 0x89, 0x87, 0xf0, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p5_3 : ∀ feat, Dec feat p5 3 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 240 64), gr 64 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ld 64 0 (some 2) none 1 0,
  Op.st 64 (some 7) none 1 240 0]

theorem b5 (prof : Profile) : Blk prof p5 0 10 o5 :=
  .cons (p5_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p5_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 10

/-- The stretch at `60`. -/
def p6 : List Byte := [
  0x48, 0xc7, 0xc0, 0x88, 0xf0, 0x79, 0x00, 0x83, 0x38, 0x01, 0x19, 0xc0, 0xf7, 0xd0, 0x25, 0x04,
  0x40, 0x00, 0x80]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7991432)] 7) := by dec_rfl
theorem p6_7 : ∀ feat, Dec feat p6 7 (FV7z.mk .cmp 32 [.mem (mg (some 0) none 1 0 32), .imm 32 1] 3) := by dec_rfl
theorem p6_10 : ∀ feat, Dec feat p6 10 (FV7z.mk .sbb 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p6_12 : ∀ feat, Dec feat p6 12 (FV7z.mk .not 32 [gr 32 0] 2) := by dec_rfl
theorem p6_14 : ∀ feat, Dec feat p6 14 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 2147500036)] 5) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.mov 64 0 (.i 7991432),
  Op.cmpmi 32 (some 0) none 1 0 1,
  Op.sbb 32 0 (.r 0),
  Op.not32 0,
  Op.and 32 0 (.i 2147500036)]

theorem b6 (prof : Profile) : Blk prof p6 0 19 o6 :=
  .cons (p6_0 _) (OpI.mov (.i 7991432) (.inr rfl)) (by decide) <|
  .cons (p6_7 _) (OpI.cmpmi (.inr rfl)) (by decide) <|
  .cons (p6_10 _) (OpI.sbb (.r 0) (.inl rfl)) (by decide) <|
  .cons (p6_12 _) (OpI.not32) (by decide) <|
  .cons (p6_14 _) (OpI.and (.i 2147500036) (.inl rfl)) (by decide) <|
  .nil 19

/-- The stretch at `80`. -/
def p7 : List Byte := [
  0xc6, 0x87, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x48, 0x85, 0xd2]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 248 8), .imm 8 0] 7) := by dec_rfl
theorem p7_7 : ∀ feat, Dec feat p7 7 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.sti 8 (some 7) none 1 248 0,
  Op.test 64 2 (.r 2)]

theorem b7 (prof : Profile) : Blk prof p7 0 10 o7 :=
  .cons (p7_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p7_7 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 10

def j5 : List Byte := [0x74, 0x14]
theorem j5_0 : ∀ feat, Dec feat j5 0 (FV7z.mk (.jcc 4) 64 [.rel 20] 2) := by dec_rfl

/-- The stretch at `92`. -/
def p8 : List Byte := [
  0x48, 0x8b, 0x02, 0x48, 0x89, 0x87, 0xf0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x47, 0x10]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 2) none 1 0 64)] 3) := by dec_rfl
theorem p8_3 : ∀ feat, Dec feat p8 3 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 240 64), gr 64 0] 7) := by dec_rfl
theorem p8_10 : ∀ feat, Dec feat p8 10 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.ld 64 0 (some 2) none 1 0,
  Op.st 64 (some 7) none 1 240 0,
  Op.st 64 (some 7) none 1 16 0]

theorem b8 (prof : Profile) : Blk prof p8 0 14 o8 :=
  .cons (p8_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p8_3 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 14

def j6 : List Byte := [0xeb, 0xd0]
theorem j6_0 : ∀ feat, Dec feat j6 0 (FV7z.mk .jmp 64 [.rel 18446744073709551568] 2) := by dec_rfl

/-- The stretch at `112`. -/
def p9 : List Byte := [
  0x48, 0x8b, 0x87, 0xf0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x47, 0x10]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .mov 64 [gr 64 0, .mem (mg (some 7) none 1 240 64)] 7) := by dec_rfl
theorem p9_7 : ∀ feat, Dec feat p9 7 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 16 64), gr 64 0] 4) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ld 64 0 (some 7) none 1 240,
  Op.st 64 (some 7) none 1 16 0]

theorem b9 (prof : Profile) : Blk prof p9 0 11 o9 :=
  .cons (p9_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .cons (p9_7 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 11

def j7 : List Byte := [0xeb, 0xbf]
theorem j7_0 : ∀ feat, Dec feat j7 0 (FV7z.mk .jmp 64 [.rel 18446744073709551551] 2) := by dec_rfl

end FV7z.Ost
