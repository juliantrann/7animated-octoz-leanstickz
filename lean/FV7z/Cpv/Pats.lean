import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps27
import FV7z.Lemmas.CmpMi16
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `ConvertPropVariantToShortString` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 12 of them) and each distinct jump (`j*`, 2) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Cpv
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xc6, 0x06, 0x00, 0x66, 0x83, 0x3f, 0x40]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), .imm 8 0] 3) := by dec_rfl
theorem p0_7 : ∀ feat, Dec feat p0 7 (FV7z.mk .cmp 16 [.mem (mg (some 7) none 1 0 16), .imm 16 64] 4) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.sti 8 (some 6) none 1 0 0,
  Op.cmpmi 16 (some 7) none 1 0 64]

theorem b0 (prof : Profile) : Blk prof p0 0 11 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p0_7 _) (OpI.cmpmi16) (by decide) <|
  .nil 11

def j0 : List Byte := [0x77, 0x23]
theorem j0_0 : ∀ feat, Dec feat j0 0 (FV7z.mk (.jcc 7) 64 [.rel 35] 2) := by dec_rfl

/-- The stretch at `13`. -/
def p1 : List Byte := [
  0x0f, 0xb7, 0x07, 0x48, 0x8d, 0x15, 0x49, 0x1a, 0x28, 0x00, 0x48, 0x63, 0x04, 0x82, 0x48, 0x01,
  0xd0]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .movzx 32 [gr 32 0, .mem (mg (some 7) none 1 0 16)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 64 [gr 64 2, .mem (mrip 2628169 0)] 7) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .movsxd 64 [gr 64 0, .mem (mg (some 2) (some 0) 4 0 32)] 4) := by dec_rfl
theorem p1_14 : ∀ feat, Dec feat p1 14 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.ldzx 16 0 (some 7) none 1 0,
  Op.mov 64 2 (.i 7181680),
  Op.ldsx 0 (some 2) (some 0) 4 0,
  Op.add 64 0 (.r 2)]

theorem b1 (prof : Profile) : BlkA prof p1 (0x457b1d : Addr) 0 17 o1 :=
  .cons (p1_0 _) ((OpI.ldzx (.inr rfl)).at _) (by decide) <|
  .cons (p1_3 _) (OpIA.lea_rip (by decide)) (by decide) <|
  .cons (p1_10 _) ((OpI.ldsx).at _) (by decide) <|
  .cons (p1_14 _) ((OpI.add (.r 2) (.inr rfl)).at _) (by decide) <|
  .nil 17

def j1 : List Byte := [0x3e, 0xff, 0xe0]
theorem j1_0 : ∀ feat, Dec feat j1 0 (FV7z.mk .jmp 64 [gr 64 0] 3) := by dec_rfl

/-- The stretch at `48`. -/
def p2 : List Byte := [
  0xb8, 0x3f, 0x3a, 0x00, 0x00, 0x48, 0x83, 0xc6, 0x02, 0x66, 0x89, 0x46, 0xfe, 0x0f, 0xb7, 0x3f]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 32 [gr 32 0, Src.opd 32 (.i 14911)] 5) := by dec_rfl
theorem p2_5 : ∀ feat, Dec feat p2 5 (FV7z.mk .add 64 [gr 64 6, Src.opd 64 (.i 2)] 4) := by dec_rfl
theorem p2_9 : ∀ feat, Dec feat p2 9 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 18446744073709551614 16), gr 16 0] 4) := by dec_rfl
theorem p2_13 : ∀ feat, Dec feat p2 13 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 7) none 1 0 16)] 3) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.mov 32 0 (.i 14911),
  Op.add 64 6 (.i 2),
  Op.st 16 (some 6) none 1 18446744073709551614 0,
  Op.ldzx 16 7 (some 7) none 1 0]

theorem b2 (prof : Profile) : Blk prof p2 0 16 o2 :=
  .cons (p2_0 _) (OpI.mov (.i 14911) (.inl rfl)) (by decide) <|
  .cons (p2_5 _) (OpI.add (.i 2) (.inr rfl)) (by decide) <|
  .cons (p2_9 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p2_13 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 16

/-- The stretch at `72`. -/
def p3 : List Byte := [
  0x66, 0x83, 0x7f, 0x08, 0x01, 0xc6, 0x46, 0x01, 0x00, 0x19, 0xc0, 0x83, 0xe0, 0x02, 0x83, 0xc0,
  0x2b, 0x88, 0x06]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .cmp 16 [.mem (mg (some 7) none 1 8 16), .imm 16 1] 5) := by dec_rfl
theorem p3_5 : ∀ feat, Dec feat p3 5 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 1 8), .imm 8 0] 4) := by dec_rfl
theorem p3_9 : ∀ feat, Dec feat p3 9 (FV7z.mk .sbb 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p3_11 : ∀ feat, Dec feat p3 11 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 2)] 3) := by dec_rfl
theorem p3_14 : ∀ feat, Dec feat p3 14 (FV7z.mk .add 32 [gr 32 0, Src.opd 32 (.i 43)] 3) := by dec_rfl
theorem p3_17 : ∀ feat, Dec feat p3 17 (FV7z.mk .mov 8 [.mem (mg (some 6) none 1 0 8), gr 8 0] 2) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.cmpmi 16 (some 7) none 1 8 1,
  Op.sti 8 (some 6) none 1 1 0,
  Op.sbb 32 0 (.r 0),
  Op.and 32 0 (.i 2),
  Op.add 32 0 (.i 43),
  Op.st 8 (some 6) none 1 0 0]

theorem b3 (prof : Profile) : Blk prof p3 0 19 o3 :=
  .cons (p3_0 _) (OpI.cmpmi16) (by decide) <|
  .cons (p3_5 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p3_9 _) (OpI.sbb (.r 0) (.inl rfl)) (by decide) <|
  .cons (p3_11 _) (OpI.and (.i 2) (.inl rfl)) (by decide) <|
  .cons (p3_14 _) (OpI.add (.i 43) (.inl rfl)) (by decide) <|
  .cons (p3_17 _) (OpI.st (.inl rfl)) (by decide) <|
  .nil 19

/-- The stretch at `96`. -/
def p4 : List Byte := [
  0x0f, 0xb6, 0x7f, 0x08]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 7) none 1 8 8)] 4) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.ldzx 8 7 (some 7) none 1 8]

theorem b4 (prof : Profile) : Blk prof p4 0 4 o4 :=
  .cons (p4_0 _) (OpI.ldzx (.inl rfl)) (by decide) <|
  .nil 4

/-- The stretch at `112`. -/
def p5 : List Byte := [
  0x0f, 0xb7, 0x7f, 0x08]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .movzx 32 [gr 32 7, .mem (mg (some 7) none 1 8 16)] 4) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.ldzx 16 7 (some 7) none 1 8]

theorem b5 (prof : Profile) : Blk prof p5 0 4 o5 :=
  .cons (p5_0 _) (OpI.ldzx (.inr rfl)) (by decide) <|
  .nil 4

/-- The stretch at `128`. -/
def p6 : List Byte := [
  0x8b, 0x7f, 0x08]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .mov 32 [gr 32 7, .mem (mg (some 7) none 1 8 32)] 3) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.ld 32 7 (some 7) none 1 8]

theorem b6 (prof : Profile) : Blk prof p6 0 3 o6 :=
  .cons (p6_0 _) (OpI.ld (.inl rfl)) (by decide) <|
  .nil 3

/-- The stretch at `144`. -/
def p7 : List Byte := [
  0x48, 0x63, 0x7f, 0x08]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .movsxd 64 [gr 64 7, .mem (mg (some 7) none 1 8 32)] 4) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.ldsx 7 (some 7) none 1 8]

theorem b7 (prof : Profile) : Blk prof p7 0 4 o7 :=
  .cons (p7_0 _) (OpI.ldsx) (by decide) <|
  .nil 4

/-- The stretch at `160`. -/
def p8 : List Byte := [
  0xba, 0x3f, 0x00, 0x00, 0x00, 0x66, 0x89, 0x16]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 32 [gr 32 2, Src.opd 32 (.i 63)] 5) := by dec_rfl
theorem p8_5 : ∀ feat, Dec feat p8 5 (FV7z.mk .mov 16 [.mem (mg (some 6) none 1 0 16), gr 16 2] 3) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.mov 32 2 (.i 63),
  Op.st 16 (some 6) none 1 0 2]

theorem b8 (prof : Profile) : Blk prof p8 0 8 o8 :=
  .cons (p8_0 _) (OpI.mov (.i 63) (.inl rfl)) (by decide) <|
  .cons (p8_5 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 8

/-- The stretch at `176`. -/
def p9 : List Byte := [
  0x48, 0x0f, 0xbf, 0x7f, 0x08]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .movsx 64 [gr 64 7, .mem (mg (some 7) none 1 8 16)] 5) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.ldsxw 7 (some 7) none 1 8]

theorem b9 (prof : Profile) : Blk prof p9 0 5 o9 :=
  .cons (p9_0 _) (OpI.ldsxw) (by decide) <|
  .nil 5

/-- The stretch at `192`. -/
def p10 : List Byte := [
  0x48, 0x83, 0xc7, 0x08, 0x31, 0xd2]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 8)] 4) := by dec_rfl
theorem p10_4 : ∀ feat, Dec feat p10 4 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.add 64 7 (.i 8),
  Op.xor 32 2 (.r 2)]

theorem b10 (prof : Profile) : Blk prof p10 0 6 o10 :=
  .cons (p10_0 _) (OpI.add (.i 8) (.inr rfl)) (by decide) <|
  .cons (p10_4 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .nil 6

/-- The stretch at `208`. -/
def p11 : List Byte := [
  0x48, 0x8b, 0x7f, 0x08]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [gr 64 7, .mem (mg (some 7) none 1 8 64)] 4) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.ld 64 7 (some 7) none 1 8]

theorem b11 (prof : Profile) : Blk prof p11 0 4 o11 :=
  .cons (p11_0 _) (OpI.ld (.inr rfl)) (by decide) <|
  .nil 4

end FV7z.Cpv
