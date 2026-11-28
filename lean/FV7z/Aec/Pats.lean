import FV7z.Lemmas.Sp
import FV7z.Lemmas.BlkOps2
/-!
# The stretches of straight-line code of `CArchiveExtractCallback::CArchiveExtractCallback` (PLAN.md §M, M1)

Each distinct stretch between labels and jumps (`p*`, 21 of them) and each distinct jump (`j*`, 0) as its own
list of bytes: what the model's decoder makes of its instructions on every processor, whatever bytes follow
(`Leaf.Dec`, by evaluation), their effects (`o*`, `Op`s of `BlkOps.lean`), and the stretch as a `Blk`. Generated from
the decoder's own output (`decshow`) by `tools/blk_gen.py`.
-/
namespace FV7z.Aec
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The stretch at `0`. -/
def p0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xc7, 0xc0, 0xd8, 0xeb, 0x78, 0x00, 0x41, 0x56, 0x41, 0x55, 0x48,
  0x8d, 0x50, 0x10, 0x41, 0x54, 0x55, 0x53]

theorem p0_0 : ∀ feat, Dec feat p0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem p0_4 : ∀ feat, Dec feat p0 4 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 7924696)] 7) := by dec_rfl
theorem p0_11 : ∀ feat, Dec feat p0 11 (FV7z.mk .push 64 [gr 64 14] 2) := by dec_rfl
theorem p0_13 : ∀ feat, Dec feat p0 13 (FV7z.mk .push 64 [gr 64 13] 2) := by dec_rfl
theorem p0_15 : ∀ feat, Dec feat p0 15 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 16 0)] 4) := by dec_rfl
theorem p0_19 : ∀ feat, Dec feat p0 19 (FV7z.mk .push 64 [gr 64 12] 2) := by dec_rfl
theorem p0_21 : ∀ feat, Dec feat p0 21 (FV7z.mk .push 64 [gr 64 5] 1) := by dec_rfl
theorem p0_22 : ∀ feat, Dec feat p0 22 (FV7z.mk .push 64 [gr 64 3] 1) := by dec_rfl

/-- What the stretch does. -/
def o0 : List Op := [
  Op.nop,
  Op.mov 64 0 (.i 7924696),
  Op.push 14,
  Op.push 13,
  Op.lea 64 2 (some 0) none 1 16,
  Op.push 12,
  Op.push 5,
  Op.push 3]

theorem b0 (prof : Profile) : Blk prof p0 0 23 o0 :=
  .cons (p0_0 _) (OpI.endbr) (by decide) <|
  .cons (p0_4 _) (OpI.mov (.i 7924696) (.inr rfl)) (by decide) <|
  .cons (p0_11 _) (OpI.push) (by decide) <|
  .cons (p0_13 _) (OpI.push) (by decide) <|
  .cons (p0_15 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p0_19 _) (OpI.push) (by decide) <|
  .cons (p0_21 _) (OpI.push) (by decide) <|
  .cons (p0_22 _) (OpI.push) (by decide) <|
  .nil 23

/-- The stretch at `23`. -/
def p1 : List Byte := [
  0x48, 0x89, 0xfb, 0x48, 0x8d, 0xbf, 0xa0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x97, 0x60, 0xff, 0xff,
  0xff, 0x48, 0x8d, 0x90, 0x98, 0x00, 0x00, 0x00, 0x48, 0x89, 0x97, 0x68, 0xff, 0xff, 0xff, 0x48,
  0x8d, 0x90, 0xc8, 0x00, 0x00, 0x00]

theorem p1_0 : ∀ feat, Dec feat p1 0 (FV7z.mk .mov 64 [gr 64 3, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem p1_3 : ∀ feat, Dec feat p1 3 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 7) none 1 160 0)] 7) := by dec_rfl
theorem p1_10 : ∀ feat, Dec feat p1 10 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551456 64), gr 64 2] 7) := by dec_rfl
theorem p1_17 : ∀ feat, Dec feat p1 17 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 152 0)] 7) := by dec_rfl
theorem p1_24 : ∀ feat, Dec feat p1 24 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551464 64), gr 64 2] 7) := by dec_rfl
theorem p1_31 : ∀ feat, Dec feat p1 31 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 200 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o1 : List Op := [
  Op.mov 64 3 (.r 7),
  Op.lea 64 7 (some 7) none 1 160,
  Op.st 64 (some 7) none 1 18446744073709551456 2,
  Op.lea 64 2 (some 0) none 1 152,
  Op.st 64 (some 7) none 1 18446744073709551464 2,
  Op.lea 64 2 (some 0) none 1 200]

theorem b1 (prof : Profile) : Blk prof p1 0 38 o1 :=
  .cons (p1_0 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (p1_3 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_10 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_17 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p1_24 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p1_31 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 38

/-- The stretch at `61`. -/
def p2 : List Byte := [
  0x48, 0x89, 0x97, 0x70, 0xff, 0xff, 0xff, 0x48, 0x8d, 0x90, 0xf8, 0x00, 0x00, 0x00, 0x48, 0x89,
  0x97, 0x78, 0xff, 0xff, 0xff, 0x48, 0x8d, 0x90, 0x28, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57, 0x80,
  0x48, 0x8d, 0x90, 0x60, 0x01, 0x00, 0x00]

theorem p2_0 : ∀ feat, Dec feat p2 0 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551472 64), gr 64 2] 7) := by dec_rfl
theorem p2_7 : ∀ feat, Dec feat p2 7 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 248 0)] 7) := by dec_rfl
theorem p2_14 : ∀ feat, Dec feat p2 14 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551480 64), gr 64 2] 7) := by dec_rfl
theorem p2_21 : ∀ feat, Dec feat p2 21 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 296 0)] 7) := by dec_rfl
theorem p2_28 : ∀ feat, Dec feat p2 28 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551488 64), gr 64 2] 4) := by dec_rfl
theorem p2_32 : ∀ feat, Dec feat p2 32 (FV7z.mk .lea 64 [gr 64 2, .mem (mg (some 0) none 1 352 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o2 : List Op := [
  Op.st 64 (some 7) none 1 18446744073709551472 2,
  Op.lea 64 2 (some 0) none 1 248,
  Op.st 64 (some 7) none 1 18446744073709551480 2,
  Op.lea 64 2 (some 0) none 1 296,
  Op.st 64 (some 7) none 1 18446744073709551488 2,
  Op.lea 64 2 (some 0) none 1 352]

theorem b2 (prof : Profile) : Blk prof p2 0 39 o2 :=
  .cons (p2_0 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_14 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_21 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p2_28 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p2_32 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 39

/-- The stretch at `100`. -/
def p3 : List Byte := [
  0x48, 0x05, 0x90, 0x01, 0x00, 0x00, 0x48, 0x89, 0x57, 0x88, 0x31, 0xd2, 0x48, 0x89, 0x47, 0x90,
  0x48, 0xb8, 0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x01, 0x00, 0xc7, 0x47, 0x98, 0x00, 0x00, 0x00,
  0x00]

theorem p3_0 : ∀ feat, Dec feat p3 0 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 400)] 6) := by dec_rfl
theorem p3_6 : ∀ feat, Dec feat p3 6 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551496 64), gr 64 2] 4) := by dec_rfl
theorem p3_10 : ∀ feat, Dec feat p3 10 (FV7z.mk .xor 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem p3_12 : ∀ feat, Dec feat p3 12 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551504 64), gr 64 0] 4) := by dec_rfl
theorem p3_16 : ∀ feat, Dec feat p3 16 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.i 281479271743488)] 10) := by dec_rfl
theorem p3_26 : ∀ feat, Dec feat p3 26 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 18446744073709551512 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o3 : List Op := [
  Op.add 64 0 (.i 400),
  Op.st 64 (some 7) none 1 18446744073709551496 2,
  Op.xor 32 2 (.r 2),
  Op.st 64 (some 7) none 1 18446744073709551504 0,
  Op.mov 64 0 (.i 281479271743488),
  Op.sti 32 (some 7) none 1 18446744073709551512 0]

theorem b3 (prof : Profile) : Blk prof p3 0 33 o3 :=
  .cons (p3_0 _) (OpI.add (.i 400) (.inr rfl)) (by decide) <|
  .cons (p3_6 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_10 _) (OpI.xor (.r 2) (.inl rfl)) (by decide) <|
  .cons (p3_12 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p3_16 _) (OpI.mov (.i 281479271743488) (.inr rfl)) (by decide) <|
  .cons (p3_26 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 33

/-- The stretch at `133`. -/
def p4 : List Byte := [
  0xc7, 0x47, 0xb8, 0x05, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0xc0, 0xff, 0xff, 0xff, 0xff, 0xc6,
  0x47, 0x9f, 0x00, 0x48, 0xc7, 0x47, 0xa0, 0x00, 0x00, 0x00, 0x00, 0x48, 0x89, 0x47, 0xa8, 0xc7,
  0x47, 0xb0, 0x00, 0x00, 0x00, 0x00]

theorem p4_0 : ∀ feat, Dec feat p4 0 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 18446744073709551544 32), .imm 32 5] 7) := by dec_rfl
theorem p4_7 : ∀ feat, Dec feat p4 7 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551552 64), .imm 64 18446744073709551615] 8) := by dec_rfl
theorem p4_15 : ∀ feat, Dec feat p4 15 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 18446744073709551519 8), .imm 8 0] 4) := by dec_rfl
theorem p4_19 : ∀ feat, Dec feat p4 19 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551520 64), .imm 64 0] 8) := by dec_rfl
theorem p4_27 : ∀ feat, Dec feat p4 27 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551528 64), gr 64 0] 4) := by dec_rfl
theorem p4_31 : ∀ feat, Dec feat p4 31 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 18446744073709551536 32), .imm 32 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o4 : List Op := [
  Op.sti 32 (some 7) none 1 18446744073709551544 5,
  Op.sti 64 (some 7) none 1 18446744073709551552 18446744073709551615,
  Op.sti 8 (some 7) none 1 18446744073709551519 0,
  Op.sti 64 (some 7) none 1 18446744073709551520 0,
  Op.st 64 (some 7) none 1 18446744073709551528 0,
  Op.sti 32 (some 7) none 1 18446744073709551536 0]

theorem b4 (prof : Profile) : Blk prof p4 0 38 o4 :=
  .cons (p4_0 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p4_7 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_15 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p4_19 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_27 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p4_31 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 38

/-- The stretch at `171`. -/
def p5 : List Byte := [
  0x66, 0x89, 0x57, 0xb4, 0xc6, 0x47, 0xd3, 0x00, 0x48, 0xc7, 0x47, 0xe0, 0x00, 0x00, 0x00, 0x00,
  0x48, 0xc7, 0x47, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x47, 0xf8, 0x00, 0x00, 0x00, 0x00]

theorem p5_0 : ∀ feat, Dec feat p5 0 (FV7z.mk .mov 16 [.mem (mg (some 7) none 1 18446744073709551540 16), gr 16 2] 4) := by dec_rfl
theorem p5_4 : ∀ feat, Dec feat p5 4 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 18446744073709551571 8), .imm 8 0] 4) := by dec_rfl
theorem p5_8 : ∀ feat, Dec feat p5 8 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551584 64), .imm 64 0] 8) := by dec_rfl
theorem p5_16 : ∀ feat, Dec feat p5 16 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551600 64), .imm 64 0] 8) := by dec_rfl
theorem p5_24 : ∀ feat, Dec feat p5 24 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 18446744073709551608 64), .imm 64 0] 8) := by dec_rfl

/-- What the stretch does. -/
def o5 : List Op := [
  Op.st 16 (some 7) none 1 18446744073709551540 2,
  Op.sti 8 (some 7) none 1 18446744073709551571 0,
  Op.sti 64 (some 7) none 1 18446744073709551584 0,
  Op.sti 64 (some 7) none 1 18446744073709551600 0,
  Op.sti 64 (some 7) none 1 18446744073709551608 0]

theorem b5 (prof : Profile) : Blk prof p5 0 32 o5 :=
  .cons (p5_0 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .cons (p5_4 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p5_8 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_16 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p5_24 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 32

/-- The stretch at `208`. -/
def p6 : List Byte := [
  0x48, 0x8d, 0xbb, 0xb0, 0x00, 0x00, 0x00]

theorem p6_0 : ∀ feat, Dec feat p6 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 176 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o6 : List Op := [
  Op.lea 64 7 (some 3) none 1 176]

theorem b6 (prof : Profile) : Blk prof p6 0 7 o6 :=
  .cons (p6_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `220`. -/
def p7 : List Byte := [
  0x48, 0xc7, 0x83, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x8d, 0xa3, 0xd0, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x83, 0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4c, 0x89, 0xe7]

theorem p7_0 : ∀ feat, Dec feat p7 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 192 64), .imm 64 0] 11) := by dec_rfl
theorem p7_11 : ∀ feat, Dec feat p7 11 (FV7z.mk .lea 64 [gr 64 12, .mem (mg (some 3) none 1 208 0)] 7) := by dec_rfl
theorem p7_18 : ∀ feat, Dec feat p7 18 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 200 64), .imm 64 0] 11) := by dec_rfl
theorem p7_29 : ∀ feat, Dec feat p7 29 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 12)] 3) := by dec_rfl

/-- What the stretch does. -/
def o7 : List Op := [
  Op.sti 64 (some 3) none 1 192 0,
  Op.lea 64 12 (some 3) none 1 208,
  Op.sti 64 (some 3) none 1 200 0,
  Op.mov 64 7 (.r 12)]

theorem b7 (prof : Profile) : Blk prof p7 0 32 o7 :=
  .cons (p7_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p7_18 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p7_29 _) (OpI.mov (.r 12) (.inr rfl)) (by decide) <|
  .nil 32

/-- The stretch at `257`. -/
def p8 : List Byte := [
  0x48, 0xc7, 0x83, 0xe0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xbb, 0xf0, 0x00,
  0x00, 0x00, 0x48, 0xc7, 0x83, 0xe8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p8_0 : ∀ feat, Dec feat p8 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 224 64), .imm 64 0] 11) := by dec_rfl
theorem p8_11 : ∀ feat, Dec feat p8 11 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 240 0)] 7) := by dec_rfl
theorem p8_18 : ∀ feat, Dec feat p8 18 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 232 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o8 : List Op := [
  Op.sti 64 (some 3) none 1 224 0,
  Op.lea 64 7 (some 3) none 1 240,
  Op.sti 64 (some 3) none 1 232 0]

theorem b8 (prof : Profile) : Blk prof p8 0 29 o8 :=
  .cons (p8_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p8_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p8_18 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 29

/-- The stretch at `291`. -/
def p9 : List Byte := [
  0x48, 0x8d, 0xbb, 0x00, 0x01, 0x00, 0x00]

theorem p9_0 : ∀ feat, Dec feat p9 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 256 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o9 : List Op := [
  Op.lea 64 7 (some 3) none 1 256]

theorem b9 (prof : Profile) : Blk prof p9 0 7 o9 :=
  .cons (p9_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `303`. -/
def p10 : List Byte := [
  0xc6, 0x83, 0x11, 0x01, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xbb, 0x20, 0x01, 0x00, 0x00, 0xc6, 0x83,
  0x18, 0x01, 0x00, 0x00, 0x00, 0xc7, 0x83, 0x1c, 0x01, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff]

theorem p10_0 : ∀ feat, Dec feat p10 0 (FV7z.mk .mov 8 [.mem (mg (some 3) none 1 273 8), .imm 8 0] 7) := by dec_rfl
theorem p10_7 : ∀ feat, Dec feat p10 7 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 288 0)] 7) := by dec_rfl
theorem p10_14 : ∀ feat, Dec feat p10 14 (FV7z.mk .mov 8 [.mem (mg (some 3) none 1 280 8), .imm 8 0] 7) := by dec_rfl
theorem p10_21 : ∀ feat, Dec feat p10 21 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 284 32), .imm 32 4294967295] 10) := by dec_rfl

/-- What the stretch does. -/
def o10 : List Op := [
  Op.sti 8 (some 3) none 1 273 0,
  Op.lea 64 7 (some 3) none 1 288,
  Op.sti 8 (some 3) none 1 280 0,
  Op.sti 32 (some 3) none 1 284 4294967295]

theorem b10 (prof : Profile) : Blk prof p10 0 31 o10 :=
  .cons (p10_0 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p10_7 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p10_14 _) (OpI.sti (.inl rfl)) (by decide) <|
  .cons (p10_21 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 31

/-- The stretch at `339`. -/
def p11 : List Byte := [
  0x48, 0xc7, 0x83, 0x30, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xbb, 0x68, 0x01,
  0x00, 0x00, 0x48, 0xc7, 0x83, 0x38, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83,
  0x40, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0x48, 0x01, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0xc7, 0x83, 0x50, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p11_0 : ∀ feat, Dec feat p11 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 304 64), .imm 64 0] 11) := by dec_rfl
theorem p11_11 : ∀ feat, Dec feat p11 11 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 360 0)] 7) := by dec_rfl
theorem p11_18 : ∀ feat, Dec feat p11 18 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 312 64), .imm 64 0] 11) := by dec_rfl
theorem p11_29 : ∀ feat, Dec feat p11 29 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 320 64), .imm 64 0] 11) := by dec_rfl
theorem p11_40 : ∀ feat, Dec feat p11 40 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 328 64), .imm 64 0] 11) := by dec_rfl
theorem p11_51 : ∀ feat, Dec feat p11 51 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 336 32), .imm 32 0] 10) := by dec_rfl

/-- What the stretch does. -/
def o11 : List Op := [
  Op.sti 64 (some 3) none 1 304 0,
  Op.lea 64 7 (some 3) none 1 360,
  Op.sti 64 (some 3) none 1 312 0,
  Op.sti 64 (some 3) none 1 320 0,
  Op.sti 64 (some 3) none 1 328 0,
  Op.sti 32 (some 3) none 1 336 0]

theorem b11 (prof : Profile) : Blk prof p11 0 61 o11 :=
  .cons (p11_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_11 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p11_18 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_29 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_40 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p11_51 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .nil 61

/-- The stretch at `405`. -/
def p12 : List Byte := [
  0x48, 0x8d, 0xbb, 0x80, 0x01, 0x00, 0x00]

theorem p12_0 : ∀ feat, Dec feat p12 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 384 0)] 7) := by dec_rfl

/-- What the stretch does. -/
def o12 : List Op := [
  Op.lea 64 7 (some 3) none 1 384]

theorem b12 (prof : Profile) : Blk prof p12 0 7 o12 :=
  .cons (p12_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 7

/-- The stretch at `417`. -/
def p13 : List Byte := [
  0x48, 0xc7, 0x83, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xbf, 0x38, 0x00, 0x00, 0x00,
  0x48, 0xc7, 0x83, 0xc0, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0xc8, 0x01,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0xd8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x48, 0xc7, 0x83, 0xe8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p13_0 : ∀ feat, Dec feat p13 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 440 64), .imm 64 0] 11) := by dec_rfl
theorem p13_11 : ∀ feat, Dec feat p13 11 (FV7z.mk .mov 32 [gr 32 7, Src.opd 32 (.i 56)] 5) := by dec_rfl
theorem p13_16 : ∀ feat, Dec feat p13 16 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 448 64), .imm 64 0] 11) := by dec_rfl
theorem p13_27 : ∀ feat, Dec feat p13 27 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 456 64), .imm 64 0] 11) := by dec_rfl
theorem p13_38 : ∀ feat, Dec feat p13 38 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 472 64), .imm 64 0] 11) := by dec_rfl
theorem p13_49 : ∀ feat, Dec feat p13 49 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 488 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o13 : List Op := [
  Op.sti 64 (some 3) none 1 440 0,
  Op.mov 32 7 (.i 56),
  Op.sti 64 (some 3) none 1 448 0,
  Op.sti 64 (some 3) none 1 456 0,
  Op.sti 64 (some 3) none 1 472 0,
  Op.sti 64 (some 3) none 1 488 0]

theorem b13 (prof : Profile) : Blk prof p13 0 60 o13 :=
  .cons (p13_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p13_11 _) (OpI.mov (.i 56) (.inl rfl)) (by decide) <|
  .cons (p13_16 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p13_27 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p13_38 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p13_49 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 60

/-- The stretch at `477`. -/
def p14 : List Byte := [
  0x48, 0xc7, 0x83, 0xf8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0x00, 0x02,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0x18, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x48, 0xc7, 0x83, 0x20, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p14_0 : ∀ feat, Dec feat p14 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 504 64), .imm 64 0] 11) := by dec_rfl
theorem p14_11 : ∀ feat, Dec feat p14 11 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 512 64), .imm 64 0] 11) := by dec_rfl
theorem p14_22 : ∀ feat, Dec feat p14 22 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 536 64), .imm 64 0] 11) := by dec_rfl
theorem p14_33 : ∀ feat, Dec feat p14 33 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 544 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o14 : List Op := [
  Op.sti 64 (some 3) none 1 504 0,
  Op.sti 64 (some 3) none 1 512 0,
  Op.sti 64 (some 3) none 1 536 0,
  Op.sti 64 (some 3) none 1 544 0]

theorem b14 (prof : Profile) : Blk prof p14 0 44 o14 :=
  .cons (p14_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p14_11 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p14_22 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p14_33 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 44

/-- The stretch at `526`. -/
def p15 : List Byte := [
  0x48, 0x89, 0xc7, 0x48, 0x89, 0xc5]

theorem p15_0 : ∀ feat, Dec feat p15 0 (FV7z.mk .mov 64 [gr 64 7, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem p15_3 : ∀ feat, Dec feat p15 3 (FV7z.mk .mov 64 [gr 64 5, Src.opd 64 (.r 0)] 3) := by dec_rfl

/-- What the stretch does. -/
def o15 : List Op := [
  Op.mov 64 7 (.r 0),
  Op.mov 64 5 (.r 0)]

theorem b15 (prof : Profile) : Blk prof p15 0 6 o15 :=
  .cons (p15_0 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .cons (p15_3 _) (OpI.mov (.r 0) (.inr rfl)) (by decide) <|
  .nil 6

/-- The stretch at `541`. -/
def p16 : List Byte := [
  0x48, 0x8d, 0xbb, 0x58, 0x02, 0x00, 0x00, 0x48, 0x89, 0xab, 0x28, 0x02, 0x00, 0x00]

theorem p16_0 : ∀ feat, Dec feat p16 0 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 600 0)] 7) := by dec_rfl
theorem p16_7 : ∀ feat, Dec feat p16 7 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 552 64), gr 64 5] 7) := by dec_rfl

/-- What the stretch does. -/
def o16 : List Op := [
  Op.lea 64 7 (some 3) none 1 600,
  Op.st 64 (some 3) none 1 552 5]

theorem b16 (prof : Profile) : Blk prof p16 0 14 o16 :=
  .cons (p16_0 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p16_7 _) (OpI.st (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 14

/-- The stretch at `560`. -/
def p17 : List Byte := [
  0x31, 0xc0, 0x48, 0xc7, 0x83, 0x68, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0x8d, 0xbb,
  0xa0, 0x02, 0x00, 0x00, 0x48, 0xc7, 0x83, 0x70, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48,
  0xc7, 0x83, 0x78, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0x80, 0x02, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00]

theorem p17_0 : ∀ feat, Dec feat p17 0 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem p17_2 : ∀ feat, Dec feat p17 2 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 616 64), .imm 64 0] 11) := by dec_rfl
theorem p17_13 : ∀ feat, Dec feat p17 13 (FV7z.mk .lea 64 [gr 64 7, .mem (mg (some 3) none 1 672 0)] 7) := by dec_rfl
theorem p17_20 : ∀ feat, Dec feat p17 20 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 624 64), .imm 64 0] 11) := by dec_rfl
theorem p17_31 : ∀ feat, Dec feat p17 31 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 632 64), .imm 64 0] 11) := by dec_rfl
theorem p17_42 : ∀ feat, Dec feat p17 42 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 640 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o17 : List Op := [
  Op.xor 32 0 (.r 0),
  Op.sti 64 (some 3) none 1 616 0,
  Op.lea 64 7 (some 3) none 1 672,
  Op.sti 64 (some 3) none 1 624 0,
  Op.sti 64 (some 3) none 1 632 0,
  Op.sti 64 (some 3) none 1 640 0]

theorem b17 (prof : Profile) : Blk prof p17 0 53 o17 :=
  .cons (p17_0 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .cons (p17_2 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p17_13 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (p17_20 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p17_31 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p17_42 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 53

/-- The stretch at `613`. -/
def p18 : List Byte := [
  0x48, 0xc7, 0x83, 0x88, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0x90, 0x02,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc7, 0x83, 0x98, 0x02, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00,
  0x66, 0x89, 0x83, 0x9c, 0x02, 0x00, 0x00]

theorem p18_0 : ∀ feat, Dec feat p18 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 648 64), .imm 64 0] 11) := by dec_rfl
theorem p18_11 : ∀ feat, Dec feat p18 11 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 656 64), .imm 64 0] 11) := by dec_rfl
theorem p18_22 : ∀ feat, Dec feat p18 22 (FV7z.mk .mov 32 [.mem (mg (some 3) none 1 664 32), .imm 32 1] 10) := by dec_rfl
theorem p18_32 : ∀ feat, Dec feat p18 32 (FV7z.mk .mov 16 [.mem (mg (some 3) none 1 668 16), gr 16 0] 7) := by dec_rfl

/-- What the stretch does. -/
def o18 : List Op := [
  Op.sti 64 (some 3) none 1 648 0,
  Op.sti 64 (some 3) none 1 656 0,
  Op.sti 32 (some 3) none 1 664 1,
  Op.st 16 (some 3) none 1 668 0]

theorem b18 (prof : Profile) : Blk prof p18 0 39 o18 :=
  .cons (p18_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p18_11 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p18_22 _) (OpI.sti (.inr (.inr (.inl rfl)))) (by decide) <|
  .cons (p18_32 _) (OpI.st (.inr (.inl rfl))) (by decide) <|
  .nil 39

/-- The stretch at `657`. -/
def p19 : List Byte := [
  0x48, 0xc7, 0x83, 0xb0, 0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x83, 0xb8, 0x02,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

theorem p19_0 : ∀ feat, Dec feat p19 0 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 688 64), .imm 64 0] 11) := by dec_rfl
theorem p19_11 : ∀ feat, Dec feat p19 11 (FV7z.mk .mov 64 [.mem (mg (some 3) none 1 696 64), .imm 64 0] 11) := by dec_rfl

/-- What the stretch does. -/
def o19 : List Op := [
  Op.sti 64 (some 3) none 1 688 0,
  Op.sti 64 (some 3) none 1 696 0]

theorem b19 (prof : Profile) : Blk prof p19 0 22 o19 :=
  .cons (p19_0 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .cons (p19_11 _) (OpI.sti (.inr (.inr (.inr rfl)))) (by decide) <|
  .nil 22

/-- The stretch at `679`. -/
def p20 : List Byte := [
  0x5b, 0x5d, 0x41, 0x5c, 0x41, 0x5d, 0x41, 0x5e]

theorem p20_0 : ∀ feat, Dec feat p20 0 (FV7z.mk .pop 64 [gr 64 3] 1) := by dec_rfl
theorem p20_1 : ∀ feat, Dec feat p20 1 (FV7z.mk .pop 64 [gr 64 5] 1) := by dec_rfl
theorem p20_2 : ∀ feat, Dec feat p20 2 (FV7z.mk .pop 64 [gr 64 12] 2) := by dec_rfl
theorem p20_4 : ∀ feat, Dec feat p20 4 (FV7z.mk .pop 64 [gr 64 13] 2) := by dec_rfl
theorem p20_6 : ∀ feat, Dec feat p20 6 (FV7z.mk .pop 64 [gr 64 14] 2) := by dec_rfl

/-- What the stretch does. -/
def o20 : List Op := [
  Op.pop 3,
  Op.pop 5,
  Op.pop 12,
  Op.pop 13,
  Op.pop 14]

theorem b20 (prof : Profile) : Blk prof p20 0 8 o20 :=
  .cons (p20_0 _) (OpI.pop) (by decide) <|
  .cons (p20_1 _) (OpI.pop) (by decide) <|
  .cons (p20_2 _) (OpI.pop) (by decide) <|
  .cons (p20_4 _) (OpI.pop) (by decide) <|
  .cons (p20_6 _) (OpI.pop) (by decide) <|
  .nil 8

end FV7z.Aec
