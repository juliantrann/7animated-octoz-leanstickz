import ZellicX86.Spec.Executable
import FV7z.Image
import FV7z.Glibc.Avx2Pick
import FV7z.Glibc.BitPick
import FV7z.Glibc.UnalignedSsse3
import FV7z.Glibc.StrCaseCmp
import FV7z.Glibc.Avx2Bit
import FV7z.Glibc.StrNCmp
import FV7z.Glibc.Wmemset
import FV7z.Glibc.Memmove
import FV7z.Glibc.Memset
import FV7z.Glibc.MemcmpRes
/-!
# The IFUNC resolvers of `7zzs` 26.06, byte by byte (PLAN.md G2, "Dispatch theo CPUID")

For each resolver: its bytes (`rADDR`), that the file holds them at its address (`_pin`), what they decode to on every
processor (`_dK`, the `K`-th byte), all written by `lake exe resgen` (`Tools/ResGen.lean`) and checked by Lean; then
the shape of resolver it is, with where its operands point (`_shape`, by `decide`), and what it returns (`_holds`).
-/
namespace FV7z.Glibc.Res
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- The 53 bytes of `7zzs` at `0x636090`. -/
def r636090 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0x91, 0xea, 0x16, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0xd7, 0xe9, 0x01, 0x00, 0x48, 0x8d, 0x05, 0x10, 0xe6, 0x01, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r636090_pin : Exe.bytesAt V2606.zzs.blob 0x636090 53 = some r636090 := by decide +kernel

theorem r636090_length : r636090.length = 53 := rfl

theorem r636090_d0 : ∀ feat, Dec feat r636090 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636090_d4 : ∀ feat, Dec feat r636090 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r636090_d14 : ∀ feat, Dec feat r636090 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r636090_d24 : ∀ feat, Dec feat r636090 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1501841 64)] 7) := by intro feat f; rfl
theorem r636090_d31 : ∀ feat, Dec feat r636090 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r636090_d34 : ∀ feat, Dec feat r636090 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 125399 0)] 7) := by intro feat f; rfl
theorem r636090_d41 : ∀ feat, Dec feat r636090 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 124432 0)] 7) := by intro feat f; rfl
theorem r636090_d48 : ∀ feat, Dec feat r636090 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636090_d52 : ∀ feat, Dec feat r636090 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636090_shape : Avx2Pick.Shape r636090 0x636090 0x6546d0 0x654a90 :=
  ⟨rfl, r636090_d0, r636090_d4, r636090_d14, ⟨_, r636090_d24, by decide⟩, r636090_d31, ⟨_, r636090_d34, by decide⟩, ⟨_, r636090_d41, by decide⟩,
    r636090_d48, r636090_d52⟩

theorem r636090_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x636090 r636090) : ImplementsCall prof 0x636090 L (resolverK prof [(0x6546d0, []), (0x654a90, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r636090_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x6a1250`. -/
def r6a1250 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0xd1, 0x38, 0x10, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0x27, 0x0f, 0x00, 0x00, 0x48, 0x8d, 0x05, 0x80, 0x0c, 0x00, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r6a1250_pin : Exe.bytesAt V2606.zzs.blob 0x6a1250 53 = some r6a1250 := by decide +kernel

theorem r6a1250_length : r6a1250.length = 53 := rfl

theorem r6a1250_d0 : ∀ feat, Dec feat r6a1250 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6a1250_d4 : ∀ feat, Dec feat r6a1250 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r6a1250_d14 : ∀ feat, Dec feat r6a1250 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r6a1250_d24 : ∀ feat, Dec feat r6a1250 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1063121 64)] 7) := by intro feat f; rfl
theorem r6a1250_d31 : ∀ feat, Dec feat r6a1250 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r6a1250_d34 : ∀ feat, Dec feat r6a1250 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 3879 0)] 7) := by intro feat f; rfl
theorem r6a1250_d41 : ∀ feat, Dec feat r6a1250 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 3200 0)] 7) := by intro feat f; rfl
theorem r6a1250_d48 : ∀ feat, Dec feat r6a1250 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6a1250_d52 : ∀ feat, Dec feat r6a1250 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6a1250_shape : Avx2Pick.Shape r6a1250 0x6a1250 0x6a1f00 0x6a21a0 :=
  ⟨rfl, r6a1250_d0, r6a1250_d4, r6a1250_d14, ⟨_, r6a1250_d24, by decide⟩, r6a1250_d31, ⟨_, r6a1250_d34, by decide⟩, ⟨_, r6a1250_d41, by decide⟩,
    r6a1250_d48, r6a1250_d52⟩

theorem r6a1250_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x6a1250 r6a1250) : ImplementsCall prof 0x6a1250 L (resolverK prof [(0x6a1f00, []), (0x6a21a0, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r6a1250_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x6a1290`. -/
def r6a1290 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0x91, 0x38, 0x10, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0x77, 0x09, 0x00, 0x00, 0x48, 0x8d, 0x05, 0x40, 0x06, 0x00, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r6a1290_pin : Exe.bytesAt V2606.zzs.blob 0x6a1290 53 = some r6a1290 := by decide +kernel

theorem r6a1290_length : r6a1290.length = 53 := rfl

theorem r6a1290_d0 : ∀ feat, Dec feat r6a1290 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6a1290_d4 : ∀ feat, Dec feat r6a1290 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r6a1290_d14 : ∀ feat, Dec feat r6a1290 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r6a1290_d24 : ∀ feat, Dec feat r6a1290 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1063057 64)] 7) := by intro feat f; rfl
theorem r6a1290_d31 : ∀ feat, Dec feat r6a1290 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r6a1290_d34 : ∀ feat, Dec feat r6a1290 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 2423 0)] 7) := by intro feat f; rfl
theorem r6a1290_d41 : ∀ feat, Dec feat r6a1290 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 1600 0)] 7) := by intro feat f; rfl
theorem r6a1290_d48 : ∀ feat, Dec feat r6a1290 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6a1290_d52 : ∀ feat, Dec feat r6a1290 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6a1290_shape : Avx2Pick.Shape r6a1290 0x6a1290 0x6a1900 0x6a1c30 :=
  ⟨rfl, r6a1290_d0, r6a1290_d4, r6a1290_d14, ⟨_, r6a1290_d24, by decide⟩, r6a1290_d31, ⟨_, r6a1290_d34, by decide⟩, ⟨_, r6a1290_d41, by decide⟩,
    r6a1290_d48, r6a1290_d52⟩

theorem r6a1290_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x6a1290 r6a1290) : ImplementsCall prof 0x6a1290 L (resolverK prof [(0x6a1900, []), (0x6a1c30, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r6a1290_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x637440`. -/
def r637440 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0xe1, 0xd6, 0x16, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0xa7, 0x7c, 0x00, 0x00, 0x48, 0x8d, 0x05, 0xc0, 0x77, 0x00, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r637440_pin : Exe.bytesAt V2606.zzs.blob 0x637440 53 = some r637440 := by decide +kernel

theorem r637440_length : r637440.length = 53 := rfl

theorem r637440_d0 : ∀ feat, Dec feat r637440 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r637440_d4 : ∀ feat, Dec feat r637440 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r637440_d14 : ∀ feat, Dec feat r637440 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r637440_d24 : ∀ feat, Dec feat r637440 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1496801 64)] 7) := by intro feat f; rfl
theorem r637440_d31 : ∀ feat, Dec feat r637440 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r637440_d34 : ∀ feat, Dec feat r637440 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 31911 0)] 7) := by intro feat f; rfl
theorem r637440_d41 : ∀ feat, Dec feat r637440 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 30656 0)] 7) := by intro feat f; rfl
theorem r637440_d48 : ∀ feat, Dec feat r637440 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r637440_d52 : ∀ feat, Dec feat r637440 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r637440_shape : Avx2Pick.Shape r637440 0x637440 0x63ec30 0x63f110 :=
  ⟨rfl, r637440_d0, r637440_d4, r637440_d14, ⟨_, r637440_d24, by decide⟩, r637440_d31, ⟨_, r637440_d34, by decide⟩, ⟨_, r637440_d41, by decide⟩,
    r637440_d48, r637440_d52⟩

theorem r637440_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x637440 r637440) : ImplementsCall prof 0x637440 L (resolverK prof [(0x63ec30, []), (0x63f110, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r637440_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x6369b0`. -/
def r6369b0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0x71, 0xe1, 0x16, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0x67, 0x84, 0x00, 0x00, 0x48, 0x8d, 0x05, 0x20, 0x7f, 0x00, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r6369b0_pin : Exe.bytesAt V2606.zzs.blob 0x6369b0 53 = some r6369b0 := by decide +kernel

theorem r6369b0_length : r6369b0.length = 53 := rfl

theorem r6369b0_d0 : ∀ feat, Dec feat r6369b0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6369b0_d4 : ∀ feat, Dec feat r6369b0 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r6369b0_d14 : ∀ feat, Dec feat r6369b0 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r6369b0_d24 : ∀ feat, Dec feat r6369b0 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1499505 64)] 7) := by intro feat f; rfl
theorem r6369b0_d31 : ∀ feat, Dec feat r6369b0 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r6369b0_d34 : ∀ feat, Dec feat r6369b0 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 33895 0)] 7) := by intro feat f; rfl
theorem r6369b0_d41 : ∀ feat, Dec feat r6369b0 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 32544 0)] 7) := by intro feat f; rfl
theorem r6369b0_d48 : ∀ feat, Dec feat r6369b0 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6369b0_d52 : ∀ feat, Dec feat r6369b0 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6369b0_shape : Avx2Pick.Shape r6369b0 0x6369b0 0x63e900 0x63ee40 :=
  ⟨rfl, r6369b0_d0, r6369b0_d4, r6369b0_d14, ⟨_, r6369b0_d24, by decide⟩, r6369b0_d31, ⟨_, r6369b0_d34, by decide⟩, ⟨_, r6369b0_d41, by decide⟩,
    r6369b0_d48, r6369b0_d52⟩

theorem r6369b0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x6369b0 r6369b0) : ImplementsCall prof 0x6369b0 L (resolverK prof [(0x63e900, []), (0x63ee40, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r6369b0_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x65d1f0`. -/
def r65d1f0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0x31, 0x79, 0x14, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0xd7, 0x1b, 0x00, 0x00, 0x48, 0x8d, 0x05, 0x00, 0x0f, 0x00, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r65d1f0_pin : Exe.bytesAt V2606.zzs.blob 0x65d1f0 53 = some r65d1f0 := by decide +kernel

theorem r65d1f0_length : r65d1f0.length = 53 := rfl

theorem r65d1f0_d0 : ∀ feat, Dec feat r65d1f0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r65d1f0_d4 : ∀ feat, Dec feat r65d1f0 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r65d1f0_d14 : ∀ feat, Dec feat r65d1f0 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r65d1f0_d24 : ∀ feat, Dec feat r65d1f0 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1341745 64)] 7) := by intro feat f; rfl
theorem r65d1f0_d31 : ∀ feat, Dec feat r65d1f0 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r65d1f0_d34 : ∀ feat, Dec feat r65d1f0 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 7127 0)] 7) := by intro feat f; rfl
theorem r65d1f0_d41 : ∀ feat, Dec feat r65d1f0 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 3840 0)] 7) := by intro feat f; rfl
theorem r65d1f0_d48 : ∀ feat, Dec feat r65d1f0 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r65d1f0_d52 : ∀ feat, Dec feat r65d1f0 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r65d1f0_shape : Avx2Pick.Shape r65d1f0 0x65d1f0 0x65e120 0x65edf0 :=
  ⟨rfl, r65d1f0_d0, r65d1f0_d4, r65d1f0_d14, ⟨_, r65d1f0_d24, by decide⟩, r65d1f0_d31, ⟨_, r65d1f0_d34, by decide⟩, ⟨_, r65d1f0_d41, by decide⟩,
    r65d1f0_d48, r65d1f0_d52⟩

theorem r65d1f0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x65d1f0 r65d1f0) : ImplementsCall prof 0x65d1f0 L (resolverK prof [(0x65e120, []), (0x65edf0, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r65d1f0_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x6360d0`. -/
def r6360d0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0x51, 0xea, 0x16, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0x37, 0xeb, 0x01, 0x00, 0x48, 0x8d, 0x05, 0x70, 0xe7, 0x01, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r6360d0_pin : Exe.bytesAt V2606.zzs.blob 0x6360d0 53 = some r6360d0 := by decide +kernel

theorem r6360d0_length : r6360d0.length = 53 := rfl

theorem r6360d0_d0 : ∀ feat, Dec feat r6360d0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6360d0_d4 : ∀ feat, Dec feat r6360d0 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r6360d0_d14 : ∀ feat, Dec feat r6360d0 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r6360d0_d24 : ∀ feat, Dec feat r6360d0 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1501777 64)] 7) := by intro feat f; rfl
theorem r6360d0_d31 : ∀ feat, Dec feat r6360d0 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r6360d0_d34 : ∀ feat, Dec feat r6360d0 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 125751 0)] 7) := by intro feat f; rfl
theorem r6360d0_d41 : ∀ feat, Dec feat r6360d0 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 124784 0)] 7) := by intro feat f; rfl
theorem r6360d0_d48 : ∀ feat, Dec feat r6360d0 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6360d0_d52 : ∀ feat, Dec feat r6360d0 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6360d0_shape : Avx2Pick.Shape r6360d0 0x6360d0 0x654870 0x654c30 :=
  ⟨rfl, r6360d0_d0, r6360d0_d4, r6360d0_d14, ⟨_, r6360d0_d24, by decide⟩, r6360d0_d31, ⟨_, r6360d0_d34, by decide⟩, ⟨_, r6360d0_d41, by decide⟩,
    r6360d0_d48, r6360d0_d52⟩

theorem r6360d0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x6360d0 r6360d0) : ImplementsCall prof 0x6360d0 L (resolverK prof [(0x654870, []), (0x654c30, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r6360d0_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x637480`. -/
def r637480 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0xa1, 0xd6, 0x16, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0x67, 0xcb, 0x01, 0x00, 0x48, 0x8d, 0x05, 0x20, 0xc7, 0x01, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r637480_pin : Exe.bytesAt V2606.zzs.blob 0x637480 53 = some r637480 := by decide +kernel

theorem r637480_length : r637480.length = 53 := rfl

theorem r637480_d0 : ∀ feat, Dec feat r637480 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r637480_d4 : ∀ feat, Dec feat r637480 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r637480_d14 : ∀ feat, Dec feat r637480 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r637480_d24 : ∀ feat, Dec feat r637480 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1496737 64)] 7) := by intro feat f; rfl
theorem r637480_d31 : ∀ feat, Dec feat r637480 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r637480_d34 : ∀ feat, Dec feat r637480 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 117607 0)] 7) := by intro feat f; rfl
theorem r637480_d41 : ∀ feat, Dec feat r637480 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 116512 0)] 7) := by intro feat f; rfl
theorem r637480_d48 : ∀ feat, Dec feat r637480 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r637480_d52 : ∀ feat, Dec feat r637480 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r637480_shape : Avx2Pick.Shape r637480 0x637480 0x653bd0 0x654010 :=
  ⟨rfl, r637480_d0, r637480_d4, r637480_d14, ⟨_, r637480_d24, by decide⟩, r637480_d31, ⟨_, r637480_d34, by decide⟩, ⟨_, r637480_d41, by decide⟩,
    r637480_d48, r637480_d52⟩

theorem r637480_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x637480 r637480) : ImplementsCall prof 0x637480 L (resolverK prof [(0x653bd0, []), (0x654010, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r637480_shape L prof hc hin

/-- The 53 bytes of `7zzs` at `0x636170`. -/
def r636170 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0xb8,
  0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23, 0x05, 0xb1, 0xe9, 0x16, 0x00, 0x48,
  0x39, 0xd0, 0x48, 0x8d, 0x15, 0x67, 0xe3, 0x01, 0x00, 0x48, 0x8d, 0x05, 0x60, 0xe0, 0x01, 0x00,
  0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r636170_pin : Exe.bytesAt V2606.zzs.blob 0x636170 53 = some r636170 := by decide +kernel

theorem r636170_length : r636170.length = 53 := rfl

theorem r636170_d0 : ∀ feat, Dec feat r636170 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636170_d4 : ∀ feat, Dec feat r636170 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r636170_d14 : ∀ feat, Dec feat r636170 14 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r636170_d24 : ∀ feat, Dec feat r636170 24 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1501617 64)] 7) := by intro feat f; rfl
theorem r636170_d31 : ∀ feat, Dec feat r636170 31 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r636170_d34 : ∀ feat, Dec feat r636170 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 123751 0)] 7) := by intro feat f; rfl
theorem r636170_d41 : ∀ feat, Dec feat r636170 41 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 122976 0)] 7) := by intro feat f; rfl
theorem r636170_d48 : ∀ feat, Dec feat r636170 48 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636170_d52 : ∀ feat, Dec feat r636170 52 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636170_shape : Avx2Pick.Shape r636170 0x636170 0x654200 0x654500 :=
  ⟨rfl, r636170_d0, r636170_d4, r636170_d14, ⟨_, r636170_d24, by decide⟩, r636170_d31, ⟨_, r636170_d34, by decide⟩, ⟨_, r636170_d41, by decide⟩,
    r636170_d48, r636170_d52⟩

theorem r636170_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x636170 r636170) : ImplementsCall prof 0x636170 L (resolverK prof [(0x654200, []), (0x654500, [Features.avx, Features.avx2])]) :=
  Avx2Pick.holds r636170_shape L prof hc hin

/-- The 30 bytes of `7zzs` at `0x6652e0`. -/
def r6652e0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xf6, 0x05, 0xff, 0xf7, 0x13, 0x00, 0x80, 0x48, 0x8d, 0x15, 0x8e, 0xff,
  0xff, 0xff, 0x48, 0x8d, 0x05, 0x47, 0xff, 0xff, 0xff, 0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r6652e0_pin : Exe.bytesAt V2606.zzs.blob 0x6652e0 30 = some r6652e0 := by decide +kernel

theorem r6652e0_length : r6652e0.length = 30 := rfl

theorem r6652e0_d0 : ∀ feat, Dec feat r6652e0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6652e0_d4 : ∀ feat, Dec feat r6652e0 4 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1308671 8), .imm 8 128] 7) := by intro feat f; rfl
theorem r6652e0_d11 : ∀ feat, Dec feat r6652e0 11 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 18446744073709551502 0)] 7) := by intro feat f; rfl
theorem r6652e0_d18 : ∀ feat, Dec feat r6652e0 18 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709551431 0)] 7) := by intro feat f; rfl
theorem r6652e0_d25 : ∀ feat, Dec feat r6652e0 25 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6652e0_d29 : ∀ feat, Dec feat r6652e0 29 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6652e0_shape : BitPick.Shape r6652e0 0x6652e0 10 7 4 0x665280 0x665240 :=
  ⟨rfl, r6652e0_d0, ⟨_, _, r6652e0_d4, by decide, by decide⟩, by decide, by decide, ⟨_, r6652e0_d11, by decide⟩,
    ⟨_, r6652e0_d18, by decide⟩, r6652e0_d25, r6652e0_d29⟩

theorem r6652e0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x6652e0 r6652e0) : ImplementsCall prof 0x6652e0 L (resolverK prof [(0x665280, []), (0x665240, [Features.popcnt])]) :=
  BitPick.holds r6652e0_shape (Or.inr ⟨rfl, rfl, rfl⟩)
    (fun _ _ hc _ h b => by simp only [List.mem_singleton, forall_eq]; exact (feat_of_ecx1 hc h).2.2.2.2.2 b) L prof hc hch hin

/-- The 30 bytes of `7zzs` at `0x6c7320`. -/
def r6c7320 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xf6, 0x05, 0xbf, 0xd7, 0x0d, 0x00, 0x10, 0x48, 0x8d, 0x15, 0xae, 0x03,
  0x00, 0x00, 0x48, 0x8d, 0x05, 0xb7, 0x01, 0x00, 0x00, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r6c7320_pin : Exe.bytesAt V2606.zzs.blob 0x6c7320 30 = some r6c7320 := by decide +kernel

theorem r6c7320_length : r6c7320.length = 30 := rfl

theorem r6c7320_d0 : ∀ feat, Dec feat r6c7320 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6c7320_d4 : ∀ feat, Dec feat r6c7320 4 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 907199 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r6c7320_d11 : ∀ feat, Dec feat r6c7320 11 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 942 0)] 7) := by intro feat f; rfl
theorem r6c7320_d18 : ∀ feat, Dec feat r6c7320 18 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 439 0)] 7) := by intro feat f; rfl
theorem r6c7320_d25 : ∀ feat, Dec feat r6c7320 25 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6c7320_d29 : ∀ feat, Dec feat r6c7320 29 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6c7320_shape : BitPick.Shape r6c7320 0x6c7320 10 4 5 0x6c76e0 0x6c74f0 :=
  ⟨rfl, r6c7320_d0, ⟨_, _, r6c7320_d4, by decide, by decide⟩, by decide, by decide, ⟨_, r6c7320_d11, by decide⟩,
    ⟨_, r6c7320_d18, by decide⟩, r6c7320_d25, r6c7320_d29⟩

theorem r6c7320_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x6c7320 r6c7320) : ImplementsCall prof 0x6c7320 L (resolverK prof [(0x6c74f0, []), (0x6c76e0, [Features.sse42, Features.ssse3])]) :=
  BitPick.holds r6c7320_shape (Or.inl ⟨rfl, rfl, rfl⟩)
    (fun _ _ hc hch h b => by have h42 := (feat_of_ecx1 hc h).2.2.1 b; simp [h42, hch.ssse3 h42]) L prof hc hch hin

/-- The 30 bytes of `7zzs` at `0x6c7300`. -/
def r6c7300 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xf6, 0x05, 0xdf, 0xd7, 0x0d, 0x00, 0x10, 0x48, 0x8d, 0x15, 0x8e, 0x02,
  0x00, 0x00, 0x48, 0x8d, 0x05, 0x27, 0x01, 0x00, 0x00, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r6c7300_pin : Exe.bytesAt V2606.zzs.blob 0x6c7300 30 = some r6c7300 := by decide +kernel

theorem r6c7300_length : r6c7300.length = 30 := rfl

theorem r6c7300_d0 : ∀ feat, Dec feat r6c7300 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6c7300_d4 : ∀ feat, Dec feat r6c7300 4 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 907231 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r6c7300_d11 : ∀ feat, Dec feat r6c7300 11 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 654 0)] 7) := by intro feat f; rfl
theorem r6c7300_d18 : ∀ feat, Dec feat r6c7300 18 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 295 0)] 7) := by intro feat f; rfl
theorem r6c7300_d25 : ∀ feat, Dec feat r6c7300 25 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6c7300_d29 : ∀ feat, Dec feat r6c7300 29 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6c7300_shape : BitPick.Shape r6c7300 0x6c7300 10 4 5 0x6c75a0 0x6c7440 :=
  ⟨rfl, r6c7300_d0, ⟨_, _, r6c7300_d4, by decide, by decide⟩, by decide, by decide, ⟨_, r6c7300_d11, by decide⟩,
    ⟨_, r6c7300_d18, by decide⟩, r6c7300_d25, r6c7300_d29⟩

theorem r6c7300_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x6c7300 r6c7300) : ImplementsCall prof 0x6c7300 L (resolverK prof [(0x6c7440, []), (0x6c75a0, [Features.sse42, Features.ssse3])]) :=
  BitPick.holds r6c7300_shape (Or.inl ⟨rfl, rfl, rfl⟩)
    (fun _ _ hc hch h b => by have h42 := (feat_of_ecx1 hc h).2.2.1 b; simp [h42, hch.ssse3 h42]) L prof hc hch hin

/-- The 30 bytes of `7zzs` at `0x635db0`. -/
def r635db0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xf6, 0x05, 0x2f, 0xed, 0x16, 0x00, 0x10, 0x48, 0x8d, 0x15, 0x3e, 0x57,
  0x02, 0x00, 0x48, 0x8d, 0x05, 0x87, 0x56, 0x02, 0x00, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r635db0_pin : Exe.bytesAt V2606.zzs.blob 0x635db0 30 = some r635db0 := by decide +kernel

theorem r635db0_length : r635db0.length = 30 := rfl

theorem r635db0_d0 : ∀ feat, Dec feat r635db0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r635db0_d4 : ∀ feat, Dec feat r635db0 4 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1502511 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r635db0_d11 : ∀ feat, Dec feat r635db0 11 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 153406 0)] 7) := by intro feat f; rfl
theorem r635db0_d18 : ∀ feat, Dec feat r635db0 18 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 153223 0)] 7) := by intro feat f; rfl
theorem r635db0_d25 : ∀ feat, Dec feat r635db0 25 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r635db0_d29 : ∀ feat, Dec feat r635db0 29 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r635db0_shape : BitPick.Shape r635db0 0x635db0 10 4 5 0x65b500 0x65b450 :=
  ⟨rfl, r635db0_d0, ⟨_, _, r635db0_d4, by decide, by decide⟩, by decide, by decide, ⟨_, r635db0_d11, by decide⟩,
    ⟨_, r635db0_d18, by decide⟩, r635db0_d25, r635db0_d29⟩

theorem r635db0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x635db0 r635db0) : ImplementsCall prof 0x635db0 L (resolverK prof [(0x65b450, []), (0x65b500, [Features.sse42, Features.ssse3])]) :=
  BitPick.holds r635db0_shape (Or.inl ⟨rfl, rfl, rfl⟩)
    (fun _ _ hc hch h b => by have h42 := (feat_of_ecx1 hc h).2.2.1 b; simp [h42, hch.ssse3 h42]) L prof hc hch hin

/-- The 30 bytes of `7zzs` at `0x636990`. -/
def r636990 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0xf6, 0x05, 0xa9, 0xe1, 0x16, 0x00, 0x10, 0x48, 0x8d, 0x15, 0x9e, 0xfc,
  0xff, 0xff, 0x48, 0x8d, 0x05, 0x07, 0x46, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r636990_pin : Exe.bytesAt V2606.zzs.blob 0x636990 30 = some r636990 := by decide +kernel

theorem r636990_length : r636990.length = 30 := rfl

theorem r636990_d0 : ∀ feat, Dec feat r636990 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636990_d4 : ∀ feat, Dec feat r636990 4 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1499561 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r636990_d11 : ∀ feat, Dec feat r636990 11 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 18446744073709550750 0)] 7) := by intro feat f; rfl
theorem r636990_d18 : ∀ feat, Dec feat r636990 18 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 148999 0)] 7) := by intro feat f; rfl
theorem r636990_d25 : ∀ feat, Dec feat r636990 25 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636990_d29 : ∀ feat, Dec feat r636990 29 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636990_shape : BitPick.Shape r636990 0x636990 100 4 4 0x636640 0x65afb0 :=
  ⟨rfl, r636990_d0, ⟨_, _, r636990_d4, by decide, by decide⟩, by decide, by decide, ⟨_, r636990_d11, by decide⟩,
    ⟨_, r636990_d18, by decide⟩, r636990_d25, r636990_d29⟩

theorem r636990_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x636990 r636990) : ImplementsCall prof 0x636990 L (resolverK prof [(0x636640, []), (0x65afb0, [])]) :=
  BitPick.holds r636990_shape (Or.inr ⟨rfl, rfl, rfl⟩)
    (fun _ _ _ _ _ _ => by simp) L prof hc hch hin

/-- The 85 bytes of `7zzs` at `0x635cf0`. -/
def r635cf0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23,
  0x15, 0x3b, 0xee, 0x16, 0x00, 0x48, 0xb9, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x05, 0xca, 0x42, 0x00, 0x00, 0x48, 0x39, 0xca, 0x74, 0x29, 0x48, 0x8d, 0x05, 0x9e, 0x2d,
  0x00, 0x00, 0xf6, 0x05, 0x1b, 0xee, 0x16, 0x00, 0x10, 0x75, 0x19, 0xf6, 0x05, 0xb7, 0xed, 0x16,
  0x00, 0x02, 0x48, 0x8d, 0x05, 0x37, 0x19, 0x00, 0x00, 0x48, 0x8d, 0x15, 0x30, 0x30, 0x00, 0x00,
  0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r635cf0_pin : Exe.bytesAt V2606.zzs.blob 0x635cf0 85 = some r635cf0 := by decide +kernel

theorem r635cf0_length : r635cf0.length = 85 := rfl

theorem r635cf0_d0 : ∀ feat, Dec feat r635cf0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r635cf0_d4 : ∀ feat, Dec feat r635cf0 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r635cf0_d14 : ∀ feat, Dec feat r635cf0 14 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, .mem (mrip 1502779 64)] 7) := by intro feat f; rfl
theorem r635cf0_d21 : ∀ feat, Dec feat r635cf0 21 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r635cf0_d31 : ∀ feat, Dec feat r635cf0 31 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 17098 0)] 7) := by intro feat f; rfl
theorem r635cf0_d38 : ∀ feat, Dec feat r635cf0 38 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, gr 64 1] 3) := by intro feat f; rfl
theorem r635cf0_d41 : ∀ feat, Dec feat r635cf0 41 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 41] 2) := by intro feat f; rfl
theorem r635cf0_d43 : ∀ feat, Dec feat r635cf0 43 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 11678 0)] 7) := by intro feat f; rfl
theorem r635cf0_d50 : ∀ feat, Dec feat r635cf0 50 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1502747 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r635cf0_d57 : ∀ feat, Dec feat r635cf0 57 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 25] 2) := by intro feat f; rfl
theorem r635cf0_d59 : ∀ feat, Dec feat r635cf0 59 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1502647 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r635cf0_d66 : ∀ feat, Dec feat r635cf0 66 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 6455 0)] 7) := by intro feat f; rfl
theorem r635cf0_d73 : ∀ feat, Dec feat r635cf0 73 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 12336 0)] 7) := by intro feat f; rfl
theorem r635cf0_d80 : ∀ feat, Dec feat r635cf0 80 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r635cf0_d84 : ∀ feat, Dec feat r635cf0 84 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r635cf0_shape : UnalignedSsse3.Shape r635cf0 0x635cf0 0x639fe0 0x638ac0 0x637670 0x638d70 :=
  ⟨rfl, r635cf0_d0, r635cf0_d4, ⟨_, r635cf0_d14, by decide⟩, r635cf0_d21, ⟨_, r635cf0_d31, by decide⟩, r635cf0_d38, r635cf0_d41,
    ⟨_, r635cf0_d43, by decide⟩, ⟨_, r635cf0_d50, by decide⟩, r635cf0_d57, ⟨_, r635cf0_d59, by decide⟩, ⟨_, r635cf0_d66, by decide⟩,
    ⟨_, r635cf0_d73, by decide⟩, r635cf0_d80, r635cf0_d84⟩

theorem r635cf0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x635cf0 r635cf0) : ImplementsCall prof 0x635cf0 L (resolverK prof [(0x637670, []), (0x638ac0, []), (0x638d70, [Features.ssse3]), (0x639fe0, [Features.avx, Features.avx2])]) :=
  UnalignedSsse3.holds r635cf0_shape L prof hc hin

/-- The 85 bytes of `7zzs` at `0x6cd120`. -/
def r6cd120 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23,
  0x15, 0x0b, 0x7a, 0x0d, 0x00, 0x48, 0xb9, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x05, 0x9a, 0x00, 0x00, 0x00, 0x48, 0x39, 0xca, 0x74, 0x29, 0x48, 0x8d, 0x05, 0x6e, 0x35,
  0x00, 0x00, 0xf6, 0x05, 0xeb, 0x79, 0x0d, 0x00, 0x10, 0x75, 0x19, 0xf6, 0x05, 0x87, 0x79, 0x0d,
  0x00, 0x02, 0x48, 0x8d, 0x05, 0x17, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x15, 0xd0, 0x09, 0x00, 0x00,
  0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r6cd120_pin : Exe.bytesAt V2606.zzs.blob 0x6cd120 85 = some r6cd120 := by decide +kernel

theorem r6cd120_length : r6cd120.length = 85 := rfl

theorem r6cd120_d0 : ∀ feat, Dec feat r6cd120 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6cd120_d4 : ∀ feat, Dec feat r6cd120 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r6cd120_d14 : ∀ feat, Dec feat r6cd120 14 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, .mem (mrip 883211 64)] 7) := by intro feat f; rfl
theorem r6cd120_d21 : ∀ feat, Dec feat r6cd120 21 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r6cd120_d31 : ∀ feat, Dec feat r6cd120 31 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 154 0)] 7) := by intro feat f; rfl
theorem r6cd120_d38 : ∀ feat, Dec feat r6cd120 38 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, gr 64 1] 3) := by intro feat f; rfl
theorem r6cd120_d41 : ∀ feat, Dec feat r6cd120 41 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 41] 2) := by intro feat f; rfl
theorem r6cd120_d43 : ∀ feat, Dec feat r6cd120 43 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 13678 0)] 7) := by intro feat f; rfl
theorem r6cd120_d50 : ∀ feat, Dec feat r6cd120 50 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 883179 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r6cd120_d57 : ∀ feat, Dec feat r6cd120 57 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 25] 2) := by intro feat f; rfl
theorem r6cd120_d59 : ∀ feat, Dec feat r6cd120 59 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 883079 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r6cd120_d66 : ∀ feat, Dec feat r6cd120 66 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 23 0)] 7) := by intro feat f; rfl
theorem r6cd120_d73 : ∀ feat, Dec feat r6cd120 73 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 2512 0)] 7) := by intro feat f; rfl
theorem r6cd120_d80 : ∀ feat, Dec feat r6cd120 80 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6cd120_d84 : ∀ feat, Dec feat r6cd120 84 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6cd120_shape : UnalignedSsse3.Shape r6cd120 0x6cd120 0x6cd1e0 0x6d06c0 0x6cd180 0x6cdb40 :=
  ⟨rfl, r6cd120_d0, r6cd120_d4, ⟨_, r6cd120_d14, by decide⟩, r6cd120_d21, ⟨_, r6cd120_d31, by decide⟩, r6cd120_d38, r6cd120_d41,
    ⟨_, r6cd120_d43, by decide⟩, ⟨_, r6cd120_d50, by decide⟩, r6cd120_d57, ⟨_, r6cd120_d59, by decide⟩, ⟨_, r6cd120_d66, by decide⟩,
    ⟨_, r6cd120_d73, by decide⟩, r6cd120_d80, r6cd120_d84⟩

theorem r6cd120_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x6cd120 r6cd120) : ImplementsCall prof 0x6cd120 L (resolverK prof [(0x6cd180, []), (0x6d06c0, []), (0x6cdb40, [Features.ssse3]), (0x6cd1e0, [Features.avx, Features.avx2])]) :=
  UnalignedSsse3.holds r6cd120_shape L prof hc hin

/-- The 85 bytes of `7zzs` at `0x635d50`. -/
def r635d50 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23,
  0x15, 0xdb, 0xed, 0x16, 0x00, 0x48, 0xb9, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x05, 0xda, 0xf1, 0x01, 0x00, 0x48, 0x39, 0xca, 0x74, 0x29, 0x48, 0x8d, 0x05, 0xfe, 0x26,
  0x02, 0x00, 0xf6, 0x05, 0xbb, 0xed, 0x16, 0x00, 0x10, 0x75, 0x19, 0xf6, 0x05, 0x57, 0xed, 0x16,
  0x00, 0x02, 0x48, 0x8d, 0x05, 0x47, 0xf5, 0x01, 0x00, 0x48, 0x8d, 0x15, 0x20, 0xf7, 0x01, 0x00,
  0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r635d50_pin : Exe.bytesAt V2606.zzs.blob 0x635d50 85 = some r635d50 := by decide +kernel

theorem r635d50_length : r635d50.length = 85 := rfl

theorem r635d50_d0 : ∀ feat, Dec feat r635d50 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r635d50_d4 : ∀ feat, Dec feat r635d50 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r635d50_d14 : ∀ feat, Dec feat r635d50 14 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, .mem (mrip 1502683 64)] 7) := by intro feat f; rfl
theorem r635d50_d21 : ∀ feat, Dec feat r635d50 21 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r635d50_d31 : ∀ feat, Dec feat r635d50 31 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 127450 0)] 7) := by intro feat f; rfl
theorem r635d50_d38 : ∀ feat, Dec feat r635d50 38 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, gr 64 1] 3) := by intro feat f; rfl
theorem r635d50_d41 : ∀ feat, Dec feat r635d50 41 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 41] 2) := by intro feat f; rfl
theorem r635d50_d43 : ∀ feat, Dec feat r635d50 43 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 141054 0)] 7) := by intro feat f; rfl
theorem r635d50_d50 : ∀ feat, Dec feat r635d50 50 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1502651 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r635d50_d57 : ∀ feat, Dec feat r635d50 57 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 25] 2) := by intro feat f; rfl
theorem r635d50_d59 : ∀ feat, Dec feat r635d50 59 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1502551 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r635d50_d66 : ∀ feat, Dec feat r635d50 66 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 128327 0)] 7) := by intro feat f; rfl
theorem r635d50_d73 : ∀ feat, Dec feat r635d50 73 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 128800 0)] 7) := by intro feat f; rfl
theorem r635d50_d80 : ∀ feat, Dec feat r635d50 80 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r635d50_d84 : ∀ feat, Dec feat r635d50 84 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r635d50_shape : UnalignedSsse3.Shape r635d50 0x635d50 0x654f50 0x658480 0x6552e0 0x6554c0 :=
  ⟨rfl, r635d50_d0, r635d50_d4, ⟨_, r635d50_d14, by decide⟩, r635d50_d21, ⟨_, r635d50_d31, by decide⟩, r635d50_d38, r635d50_d41,
    ⟨_, r635d50_d43, by decide⟩, ⟨_, r635d50_d50, by decide⟩, r635d50_d57, ⟨_, r635d50_d59, by decide⟩, ⟨_, r635d50_d66, by decide⟩,
    ⟨_, r635d50_d73, by decide⟩, r635d50_d80, r635d50_d84⟩

theorem r635d50_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x635d50 r635d50) : ImplementsCall prof 0x635d50 L (resolverK prof [(0x6552e0, []), (0x658480, []), (0x6554c0, [Features.ssse3]), (0x654f50, [Features.avx, Features.avx2])]) :=
  UnalignedSsse3.holds r635d50_shape L prof hc hin

/-- The 85 bytes of `7zzs` at `0x636c80`. -/
def r636c80 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23,
  0x15, 0xab, 0xde, 0x16, 0x00, 0x48, 0xb9, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x05, 0xca, 0x24, 0x02, 0x00, 0x48, 0x39, 0xca, 0x74, 0x29, 0x48, 0x8d, 0x05, 0xfe, 0x1d,
  0x02, 0x00, 0xf6, 0x05, 0x8b, 0xde, 0x16, 0x00, 0x10, 0x75, 0x19, 0xf6, 0x05, 0x27, 0xde, 0x16,
  0x00, 0x02, 0x48, 0x8d, 0x05, 0x07, 0xe7, 0x01, 0x00, 0x48, 0x8d, 0x15, 0xa0, 0xff, 0x01, 0x00,
  0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r636c80_pin : Exe.bytesAt V2606.zzs.blob 0x636c80 85 = some r636c80 := by decide +kernel

theorem r636c80_length : r636c80.length = 85 := rfl

theorem r636c80_d0 : ∀ feat, Dec feat r636c80 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636c80_d4 : ∀ feat, Dec feat r636c80 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r636c80_d14 : ∀ feat, Dec feat r636c80 14 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, .mem (mrip 1498795 64)] 7) := by intro feat f; rfl
theorem r636c80_d21 : ∀ feat, Dec feat r636c80 21 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r636c80_d31 : ∀ feat, Dec feat r636c80 31 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 140490 0)] 7) := by intro feat f; rfl
theorem r636c80_d38 : ∀ feat, Dec feat r636c80 38 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, gr 64 1] 3) := by intro feat f; rfl
theorem r636c80_d41 : ∀ feat, Dec feat r636c80 41 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 41] 2) := by intro feat f; rfl
theorem r636c80_d43 : ∀ feat, Dec feat r636c80 43 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 138750 0)] 7) := by intro feat f; rfl
theorem r636c80_d50 : ∀ feat, Dec feat r636c80 50 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498763 8), .imm 8 16] 7) := by intro feat f; rfl
theorem r636c80_d57 : ∀ feat, Dec feat r636c80 57 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 25] 2) := by intro feat f; rfl
theorem r636c80_d59 : ∀ feat, Dec feat r636c80 59 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498663 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636c80_d66 : ∀ feat, Dec feat r636c80 66 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 124679 0)] 7) := by intro feat f; rfl
theorem r636c80_d73 : ∀ feat, Dec feat r636c80 73 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 130976 0)] 7) := by intro feat f; rfl
theorem r636c80_d80 : ∀ feat, Dec feat r636c80 80 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636c80_d84 : ∀ feat, Dec feat r636c80 84 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636c80_shape : UnalignedSsse3.Shape r636c80 0x636c80 0x659170 0x658ab0 0x6553d0 0x656c70 :=
  ⟨rfl, r636c80_d0, r636c80_d4, ⟨_, r636c80_d14, by decide⟩, r636c80_d21, ⟨_, r636c80_d31, by decide⟩, r636c80_d38, r636c80_d41,
    ⟨_, r636c80_d43, by decide⟩, ⟨_, r636c80_d50, by decide⟩, r636c80_d57, ⟨_, r636c80_d59, by decide⟩, ⟨_, r636c80_d66, by decide⟩,
    ⟨_, r636c80_d73, by decide⟩, r636c80_d80, r636c80_d84⟩

theorem r636c80_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x636c80 r636c80) : ImplementsCall prof 0x636c80 L (resolverK prof [(0x6553d0, []), (0x658ab0, []), (0x656c70, [Features.ssse3]), (0x659170, [Features.avx, Features.avx2])]) :=
  UnalignedSsse3.holds r636c80_shape L prof hc hin

/-- The 72 bytes of `7zzs` at `0x6c7340`. -/
def r6c7340 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x05, 0xd5, 0xaf, 0xf8, 0xff, 0xf6, 0x05, 0xee, 0xd7, 0x0d,
  0x00, 0x01, 0x75, 0x33, 0x8b, 0x15, 0x8e, 0xd7, 0x0d, 0x00, 0xf7, 0xc2, 0x00, 0x00, 0x10, 0x00,
  0x74, 0x10, 0x48, 0x8d, 0x05, 0x07, 0x94, 0xf8, 0xff, 0xf6, 0x05, 0xd4, 0xd7, 0x0d, 0x00, 0x80,
  0x74, 0x15, 0x80, 0xe6, 0x02, 0x48, 0x8d, 0x05, 0x44, 0x50, 0xf8, 0xff, 0x48, 0x8d, 0x15, 0x8d,
  0x72, 0xf8, 0xff, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r6c7340_pin : Exe.bytesAt V2606.zzs.blob 0x6c7340 72 = some r6c7340 := by decide +kernel

theorem r6c7340_length : r6c7340.length = 72 := rfl

theorem r6c7340_d0 : ∀ feat, Dec feat r6c7340 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6c7340_d4 : ∀ feat, Dec feat r6c7340 4 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709072341 0)] 7) := by intro feat f; rfl
theorem r6c7340_d11 : ∀ feat, Dec feat r6c7340 11 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 907246 8), .imm 8 1] 7) := by intro feat f; rfl
theorem r6c7340_d18 : ∀ feat, Dec feat r6c7340 18 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 51] 2) := by intro feat f; rfl
theorem r6c7340_d20 : ∀ feat, Dec feat r6c7340 20 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 907150 32)] 6) := by intro feat f; rfl
theorem r6c7340_d26 : ∀ feat, Dec feat r6c7340 26 (FV7z.mk (ZellicX86.Decode.Mn.test) 32 [gr 32 2, .imm 32 1048576] 6) := by intro feat f; rfl
theorem r6c7340_d32 : ∀ feat, Dec feat r6c7340 32 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 16] 2) := by intro feat f; rfl
theorem r6c7340_d34 : ∀ feat, Dec feat r6c7340 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709065223 0)] 7) := by intro feat f; rfl
theorem r6c7340_d41 : ∀ feat, Dec feat r6c7340 41 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 907220 8), .imm 8 128] 7) := by intro feat f; rfl
theorem r6c7340_d48 : ∀ feat, Dec feat r6c7340 48 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 21] 2) := by intro feat f; rfl
theorem r6c7340_d50 : ∀ feat, Dec feat r6c7340 50 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 2] 3) := by intro feat f; rfl
theorem r6c7340_d53 : ∀ feat, Dec feat r6c7340 53 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709047876 0)] 7) := by intro feat f; rfl
theorem r6c7340_d60 : ∀ feat, Dec feat r6c7340 60 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 18446744073709056653 0)] 7) := by intro feat f; rfl
theorem r6c7340_d67 : ∀ feat, Dec feat r6c7340 67 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6c7340_d71 : ∀ feat, Dec feat r6c7340 71 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6c7340_shape : StrCaseCmp.Shape r6c7340 0x6c7340 0x652320 0x650770 0x64c3c0 0x64e610 :=
  ⟨rfl, r6c7340_d0, ⟨_, r6c7340_d4, by decide⟩, ⟨_, r6c7340_d11, by decide⟩, r6c7340_d18, ⟨_, r6c7340_d20, by decide⟩, r6c7340_d26, r6c7340_d32,
    ⟨_, r6c7340_d34, by decide⟩, ⟨_, r6c7340_d41, by decide⟩, r6c7340_d48, r6c7340_d50, ⟨_, r6c7340_d53, by decide⟩, ⟨_, r6c7340_d60, by decide⟩,
    r6c7340_d67, r6c7340_d71⟩

theorem r6c7340_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x6c7340 r6c7340) : ImplementsCall prof 0x6c7340 L (resolverK prof [(0x64c3c0, []), (0x64e610, [Features.ssse3]), (0x650770, [Features.sse42, Features.ssse3]), (0x652320, [Features.avx])]) :=
  StrCaseCmp.holds r6c7340_shape L prof hc hch hin

/-- The 72 bytes of `7zzs` at `0x6c7390`. -/
def r6c7390 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x05, 0xb9, 0x84, 0xfd, 0xff, 0xf6, 0x05, 0x9e, 0xd7, 0x0d,
  0x00, 0x01, 0x75, 0x33, 0x8b, 0x15, 0x3e, 0xd7, 0x0d, 0x00, 0xf7, 0xc2, 0x00, 0x00, 0x10, 0x00,
  0x74, 0x10, 0x48, 0x8d, 0x05, 0xcb, 0x64, 0xfd, 0xff, 0xf6, 0x05, 0x84, 0xd7, 0x0d, 0x00, 0x80,
  0x74, 0x15, 0x80, 0xe6, 0x02, 0x48, 0x8d, 0x05, 0xf4, 0x18, 0xfd, 0xff, 0x48, 0x8d, 0x15, 0x4d,
  0x3f, 0xfd, 0xff, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r6c7390_pin : Exe.bytesAt V2606.zzs.blob 0x6c7390 72 = some r6c7390 := by decide +kernel

theorem r6c7390_length : r6c7390.length = 72 := rfl

theorem r6c7390_d0 : ∀ feat, Dec feat r6c7390 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6c7390_d4 : ∀ feat, Dec feat r6c7390 4 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709388985 0)] 7) := by intro feat f; rfl
theorem r6c7390_d11 : ∀ feat, Dec feat r6c7390 11 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 907166 8), .imm 8 1] 7) := by intro feat f; rfl
theorem r6c7390_d18 : ∀ feat, Dec feat r6c7390 18 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 51] 2) := by intro feat f; rfl
theorem r6c7390_d20 : ∀ feat, Dec feat r6c7390 20 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 907070 32)] 6) := by intro feat f; rfl
theorem r6c7390_d26 : ∀ feat, Dec feat r6c7390 26 (FV7z.mk (ZellicX86.Decode.Mn.test) 32 [gr 32 2, .imm 32 1048576] 6) := by intro feat f; rfl
theorem r6c7390_d32 : ∀ feat, Dec feat r6c7390 32 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 16] 2) := by intro feat f; rfl
theorem r6c7390_d34 : ∀ feat, Dec feat r6c7390 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709380811 0)] 7) := by intro feat f; rfl
theorem r6c7390_d41 : ∀ feat, Dec feat r6c7390 41 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 907140 8), .imm 8 128] 7) := by intro feat f; rfl
theorem r6c7390_d48 : ∀ feat, Dec feat r6c7390 48 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 21] 2) := by intro feat f; rfl
theorem r6c7390_d50 : ∀ feat, Dec feat r6c7390 50 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 2] 3) := by intro feat f; rfl
theorem r6c7390_d53 : ∀ feat, Dec feat r6c7390 53 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709361396 0)] 7) := by intro feat f; rfl
theorem r6c7390_d60 : ∀ feat, Dec feat r6c7390 60 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 18446744073709371213 0)] 7) := by intro feat f; rfl
theorem r6c7390_d67 : ∀ feat, Dec feat r6c7390 67 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r6c7390_d71 : ∀ feat, Dec feat r6c7390 71 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6c7390_shape : StrCaseCmp.Shape r6c7390 0x6c7390 0x69f854 0x69d884 0x698cc0 0x69b320 :=
  ⟨rfl, r6c7390_d0, ⟨_, r6c7390_d4, by decide⟩, ⟨_, r6c7390_d11, by decide⟩, r6c7390_d18, ⟨_, r6c7390_d20, by decide⟩, r6c7390_d26, r6c7390_d32,
    ⟨_, r6c7390_d34, by decide⟩, ⟨_, r6c7390_d41, by decide⟩, r6c7390_d48, r6c7390_d50, ⟨_, r6c7390_d53, by decide⟩, ⟨_, r6c7390_d60, by decide⟩,
    r6c7390_d67, r6c7390_d71⟩

theorem r6c7390_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x6c7390 r6c7390) : ImplementsCall prof 0x6c7390 L (resolverK prof [(0x698cc0, []), (0x69b320, [Features.ssse3]), (0x69d884, [Features.sse42, Features.ssse3]), (0x69f854, [Features.avx])]) :=
  StrCaseCmp.holds r6c7390_shape L prof hc hch hin

/-- The 72 bytes of `7zzs` at `0x636ce0`. -/
def r636ce0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x05, 0x49, 0xb6, 0x01, 0x00, 0xf6, 0x05, 0x4e, 0xde, 0x16,
  0x00, 0x01, 0x75, 0x33, 0x8b, 0x15, 0xee, 0xdd, 0x16, 0x00, 0xf7, 0xc2, 0x00, 0x00, 0x10, 0x00,
  0x74, 0x10, 0x48, 0x8d, 0x05, 0x7b, 0x9a, 0x01, 0x00, 0xf6, 0x05, 0x34, 0xde, 0x16, 0x00, 0x80,
  0x74, 0x15, 0x80, 0xe6, 0x02, 0x48, 0x8d, 0x05, 0xc4, 0x56, 0x01, 0x00, 0x48, 0x8d, 0x15, 0x0d,
  0x79, 0x01, 0x00, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r636ce0_pin : Exe.bytesAt V2606.zzs.blob 0x636ce0 72 = some r636ce0 := by decide +kernel

theorem r636ce0_length : r636ce0.length = 72 := rfl

theorem r636ce0_d0 : ∀ feat, Dec feat r636ce0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636ce0_d4 : ∀ feat, Dec feat r636ce0 4 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 112201 0)] 7) := by intro feat f; rfl
theorem r636ce0_d11 : ∀ feat, Dec feat r636ce0 11 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498702 8), .imm 8 1] 7) := by intro feat f; rfl
theorem r636ce0_d18 : ∀ feat, Dec feat r636ce0 18 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 51] 2) := by intro feat f; rfl
theorem r636ce0_d20 : ∀ feat, Dec feat r636ce0 20 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 1498606 32)] 6) := by intro feat f; rfl
theorem r636ce0_d26 : ∀ feat, Dec feat r636ce0 26 (FV7z.mk (ZellicX86.Decode.Mn.test) 32 [gr 32 2, .imm 32 1048576] 6) := by intro feat f; rfl
theorem r636ce0_d32 : ∀ feat, Dec feat r636ce0 32 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 16] 2) := by intro feat f; rfl
theorem r636ce0_d34 : ∀ feat, Dec feat r636ce0 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 105083 0)] 7) := by intro feat f; rfl
theorem r636ce0_d41 : ∀ feat, Dec feat r636ce0 41 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498676 8), .imm 8 128] 7) := by intro feat f; rfl
theorem r636ce0_d48 : ∀ feat, Dec feat r636ce0 48 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 21] 2) := by intro feat f; rfl
theorem r636ce0_d50 : ∀ feat, Dec feat r636ce0 50 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 2] 3) := by intro feat f; rfl
theorem r636ce0_d53 : ∀ feat, Dec feat r636ce0 53 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 87748 0)] 7) := by intro feat f; rfl
theorem r636ce0_d60 : ∀ feat, Dec feat r636ce0 60 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 96525 0)] 7) := by intro feat f; rfl
theorem r636ce0_d67 : ∀ feat, Dec feat r636ce0 67 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636ce0_d71 : ∀ feat, Dec feat r636ce0 71 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636ce0_shape : StrCaseCmp.Shape r636ce0 0x636ce0 0x652334 0x650784 0x64c3e0 0x64e630 :=
  ⟨rfl, r636ce0_d0, ⟨_, r636ce0_d4, by decide⟩, ⟨_, r636ce0_d11, by decide⟩, r636ce0_d18, ⟨_, r636ce0_d20, by decide⟩, r636ce0_d26, r636ce0_d32,
    ⟨_, r636ce0_d34, by decide⟩, ⟨_, r636ce0_d41, by decide⟩, r636ce0_d48, r636ce0_d50, ⟨_, r636ce0_d53, by decide⟩, ⟨_, r636ce0_d60, by decide⟩,
    r636ce0_d67, r636ce0_d71⟩

theorem r636ce0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x636ce0 r636ce0) : ImplementsCall prof 0x636ce0 L (resolverK prof [(0x64c3e0, []), (0x64e630, [Features.ssse3]), (0x650784, [Features.sse42, Features.ssse3]), (0x652334, [Features.avx])]) :=
  StrCaseCmp.holds r636ce0_shape L prof hc hch hin

/-- The 72 bytes of `7zzs` at `0x698c50`. -/
def r698c50 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8d, 0x05, 0xe5, 0x6b, 0x00, 0x00, 0xf6, 0x05, 0xde, 0xbe, 0x10,
  0x00, 0x01, 0x75, 0x33, 0x8b, 0x15, 0x7e, 0xbe, 0x10, 0x00, 0xf7, 0xc2, 0x00, 0x00, 0x10, 0x00,
  0x74, 0x10, 0x48, 0x8d, 0x05, 0xf7, 0x4b, 0x00, 0x00, 0xf6, 0x05, 0xc4, 0xbe, 0x10, 0x00, 0x80,
  0x74, 0x15, 0x80, 0xe6, 0x02, 0x48, 0x8d, 0x05, 0x14, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x15, 0x6d,
  0x26, 0x00, 0x00, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r698c50_pin : Exe.bytesAt V2606.zzs.blob 0x698c50 72 = some r698c50 := by decide +kernel

theorem r698c50_length : r698c50.length = 72 := rfl

theorem r698c50_d0 : ∀ feat, Dec feat r698c50 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r698c50_d4 : ∀ feat, Dec feat r698c50 4 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 27621 0)] 7) := by intro feat f; rfl
theorem r698c50_d11 : ∀ feat, Dec feat r698c50 11 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1097438 8), .imm 8 1] 7) := by intro feat f; rfl
theorem r698c50_d18 : ∀ feat, Dec feat r698c50 18 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 51] 2) := by intro feat f; rfl
theorem r698c50_d20 : ∀ feat, Dec feat r698c50 20 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 1097342 32)] 6) := by intro feat f; rfl
theorem r698c50_d26 : ∀ feat, Dec feat r698c50 26 (FV7z.mk (ZellicX86.Decode.Mn.test) 32 [gr 32 2, .imm 32 1048576] 6) := by intro feat f; rfl
theorem r698c50_d32 : ∀ feat, Dec feat r698c50 32 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 16] 2) := by intro feat f; rfl
theorem r698c50_d34 : ∀ feat, Dec feat r698c50 34 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 19447 0)] 7) := by intro feat f; rfl
theorem r698c50_d41 : ∀ feat, Dec feat r698c50 41 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1097412 8), .imm 8 128] 7) := by intro feat f; rfl
theorem r698c50_d48 : ∀ feat, Dec feat r698c50 48 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 21] 2) := by intro feat f; rfl
theorem r698c50_d50 : ∀ feat, Dec feat r698c50 50 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 2] 3) := by intro feat f; rfl
theorem r698c50_d53 : ∀ feat, Dec feat r698c50 53 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 20 0)] 7) := by intro feat f; rfl
theorem r698c50_d60 : ∀ feat, Dec feat r698c50 60 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 9837 0)] 7) := by intro feat f; rfl
theorem r698c50_d67 : ∀ feat, Dec feat r698c50 67 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r698c50_d71 : ∀ feat, Dec feat r698c50 71 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r698c50_shape : StrCaseCmp.Shape r698c50 0x698c50 0x69f840 0x69d870 0x698ca0 0x69b300 :=
  ⟨rfl, r698c50_d0, ⟨_, r698c50_d4, by decide⟩, ⟨_, r698c50_d11, by decide⟩, r698c50_d18, ⟨_, r698c50_d20, by decide⟩, r698c50_d26, r698c50_d32,
    ⟨_, r698c50_d34, by decide⟩, ⟨_, r698c50_d41, by decide⟩, r698c50_d48, r698c50_d50, ⟨_, r698c50_d53, by decide⟩, ⟨_, r698c50_d60, by decide⟩,
    r698c50_d67, r698c50_d71⟩

theorem r698c50_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x698c50 r698c50) : ImplementsCall prof 0x698c50 L (resolverK prof [(0x698ca0, []), (0x69b300, [Features.ssse3]), (0x69d870, [Features.sse42, Features.ssse3]), (0x69f840, [Features.avx])]) :=
  StrCaseCmp.holds r698c50_shape L prof hc hch hin

/-- The 69 bytes of `7zzs` at `0x65d650`. -/
def r65d650 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23,
  0x15, 0xdb, 0x74, 0x14, 0x00, 0x48, 0xb9, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x05, 0x2a, 0x1e, 0x00, 0x00, 0x48, 0x39, 0xca, 0x74, 0x19, 0xf6, 0x05, 0x68, 0x74, 0x14,
  0x00, 0x08, 0x48, 0x8d, 0x05, 0xd7, 0x1d, 0x00, 0x00, 0x48, 0x8d, 0x15, 0xb0, 0x1b, 0x00, 0x00,
  0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r65d650_pin : Exe.bytesAt V2606.zzs.blob 0x65d650 69 = some r65d650 := by decide +kernel

theorem r65d650_length : r65d650.length = 69 := rfl

theorem r65d650_d0 : ∀ feat, Dec feat r65d650 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r65d650_d4 : ∀ feat, Dec feat r65d650 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r65d650_d14 : ∀ feat, Dec feat r65d650 14 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, .mem (mrip 1340635 64)] 7) := by intro feat f; rfl
theorem r65d650_d21 : ∀ feat, Dec feat r65d650 21 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r65d650_d31 : ∀ feat, Dec feat r65d650 31 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 7722 0)] 7) := by intro feat f; rfl
theorem r65d650_d38 : ∀ feat, Dec feat r65d650 38 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, gr 64 1] 3) := by intro feat f; rfl
theorem r65d650_d41 : ∀ feat, Dec feat r65d650 41 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 25] 2) := by intro feat f; rfl
theorem r65d650_d43 : ∀ feat, Dec feat r65d650 43 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1340520 8), .imm 8 8] 7) := by intro feat f; rfl
theorem r65d650_d50 : ∀ feat, Dec feat r65d650 50 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 7639 0)] 7) := by intro feat f; rfl
theorem r65d650_d57 : ∀ feat, Dec feat r65d650 57 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 7088 0)] 7) := by intro feat f; rfl
theorem r65d650_d64 : ∀ feat, Dec feat r65d650 64 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r65d650_d68 : ∀ feat, Dec feat r65d650 68 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r65d650_shape : Avx2Bit.Shape r65d650 0x65d650 10 3 0x65f4a0 0x65f240 0x65f460 :=
  ⟨rfl, r65d650_d0, r65d650_d4, ⟨_, r65d650_d14, by decide⟩, r65d650_d21, ⟨_, r65d650_d31, by decide⟩, r65d650_d38, r65d650_d41,
    ⟨_, _, r65d650_d43, by decide, by decide⟩, by decide, by decide, ⟨_, r65d650_d50, by decide⟩, ⟨_, r65d650_d57, by decide⟩,
    r65d650_d64, r65d650_d68⟩

theorem r65d650_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x65d650 r65d650) : ImplementsCall prof 0x65d650 L (resolverK prof [(0x65f460, []), (0x65f240, [Features.sse41]), (0x65f4a0, [Features.avx, Features.avx2])]) :=
  Avx2Bit.holds r65d650_shape
    (fun _ _ hc _ h b => by simp only [List.mem_singleton, forall_eq]; exact (feat_of_ecx1 hc h).2.1 b) L prof hc hch hin

/-- The 69 bytes of `7zzs` at `0x635ca0`. -/
def r635ca0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23,
  0x15, 0x8b, 0xee, 0x16, 0x00, 0x48, 0xb9, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x05, 0x1a, 0xe1, 0x01, 0x00, 0x48, 0x39, 0xca, 0x74, 0x19, 0xf6, 0x05, 0x72, 0xee, 0x16,
  0x00, 0x40, 0x48, 0x8d, 0x05, 0xc7, 0xdc, 0x01, 0x00, 0x48, 0x8d, 0x15, 0x40, 0x38, 0x02, 0x00,
  0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r635ca0_pin : Exe.bytesAt V2606.zzs.blob 0x635ca0 69 = some r635ca0 := by decide +kernel

theorem r635ca0_length : r635ca0.length = 69 := rfl

theorem r635ca0_d0 : ∀ feat, Dec feat r635ca0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r635ca0_d4 : ∀ feat, Dec feat r635ca0 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r635ca0_d14 : ∀ feat, Dec feat r635ca0 14 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, .mem (mrip 1502859 64)] 7) := by intro feat f; rfl
theorem r635ca0_d21 : ∀ feat, Dec feat r635ca0 21 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r635ca0_d31 : ∀ feat, Dec feat r635ca0 31 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 123162 0)] 7) := by intro feat f; rfl
theorem r635ca0_d38 : ∀ feat, Dec feat r635ca0 38 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, gr 64 1] 3) := by intro feat f; rfl
theorem r635ca0_d41 : ∀ feat, Dec feat r635ca0 41 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 25] 2) := by intro feat f; rfl
theorem r635ca0_d43 : ∀ feat, Dec feat r635ca0 43 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1502834 8), .imm 8 64] 7) := by intro feat f; rfl
theorem r635ca0_d50 : ∀ feat, Dec feat r635ca0 50 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 122055 0)] 7) := by intro feat f; rfl
theorem r635ca0_d57 : ∀ feat, Dec feat r635ca0 57 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 145472 0)] 7) := by intro feat f; rfl
theorem r635ca0_d64 : ∀ feat, Dec feat r635ca0 64 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r635ca0_d68 : ∀ feat, Dec feat r635ca0 68 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r635ca0_shape : Avx2Bit.Shape r635ca0 0x635ca0 100 6 0x653de0 0x659520 0x6539a0 :=
  ⟨rfl, r635ca0_d0, r635ca0_d4, ⟨_, r635ca0_d14, by decide⟩, r635ca0_d21, ⟨_, r635ca0_d31, by decide⟩, r635ca0_d38, r635ca0_d41,
    ⟨_, _, r635ca0_d43, by decide, by decide⟩, by decide, by decide, ⟨_, r635ca0_d50, by decide⟩, ⟨_, r635ca0_d57, by decide⟩,
    r635ca0_d64, r635ca0_d68⟩

theorem r635ca0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x635ca0 r635ca0) : ImplementsCall prof 0x635ca0 L (resolverK prof [(0x6539a0, []), (0x659520, []), (0x653de0, [Features.avx, Features.avx2])]) :=
  Avx2Bit.holds r635ca0_shape
    (fun _ _ _ _ _ _ => by simp) L prof hc hch hin

/-- The 95 bytes of `7zzs` at `0x636110`. -/
def r636110 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0xba, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0x23,
  0x15, 0x1b, 0xea, 0x16, 0x00, 0x48, 0xb9, 0x02, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48,
  0x8d, 0x05, 0x9a, 0x82, 0x00, 0x00, 0x48, 0x39, 0xca, 0x74, 0x33, 0x8b, 0x15, 0xa7, 0xe9, 0x16,
  0x00, 0xf7, 0xc2, 0x00, 0x00, 0x10, 0x00, 0x74, 0x10, 0x48, 0x8d, 0x05, 0xa0, 0x72, 0x00, 0x00,
  0xf6, 0x05, 0xed, 0xe9, 0x16, 0x00, 0x80, 0x74, 0x15, 0x80, 0xe6, 0x02, 0x48, 0x8d, 0x05, 0xbd,
  0x42, 0x00, 0x00, 0x48, 0x8d, 0x15, 0x16, 0x5b, 0x00, 0x00, 0x48, 0x0f, 0x45, 0xc2, 0xc3]

theorem r636110_pin : Exe.bytesAt V2606.zzs.blob 0x636110 95 = some r636110 := by decide +kernel

theorem r636110_length : r636110.length = 95 := rfl

theorem r636110_d0 : ∀ feat, Dec feat r636110 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636110_d4 : ∀ feat, Dec feat r636110 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r636110_d14 : ∀ feat, Dec feat r636110 14 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, .mem (mrip 1501723 64)] 7) := by intro feat f; rfl
theorem r636110_d21 : ∀ feat, Dec feat r636110 21 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r636110_d31 : ∀ feat, Dec feat r636110 31 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 33434 0)] 7) := by intro feat f; rfl
theorem r636110_d38 : ∀ feat, Dec feat r636110 38 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, gr 64 1] 3) := by intro feat f; rfl
theorem r636110_d41 : ∀ feat, Dec feat r636110 41 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 51] 2) := by intro feat f; rfl
theorem r636110_d43 : ∀ feat, Dec feat r636110 43 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 1501607 32)] 6) := by intro feat f; rfl
theorem r636110_d49 : ∀ feat, Dec feat r636110 49 (FV7z.mk (ZellicX86.Decode.Mn.test) 32 [gr 32 2, .imm 32 1048576] 6) := by intro feat f; rfl
theorem r636110_d55 : ∀ feat, Dec feat r636110 55 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 16] 2) := by intro feat f; rfl
theorem r636110_d57 : ∀ feat, Dec feat r636110 57 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 29344 0)] 7) := by intro feat f; rfl
theorem r636110_d64 : ∀ feat, Dec feat r636110 64 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1501677 8), .imm 8 128] 7) := by intro feat f; rfl
theorem r636110_d71 : ∀ feat, Dec feat r636110 71 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 21] 2) := by intro feat f; rfl
theorem r636110_d73 : ∀ feat, Dec feat r636110 73 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 2] 3) := by intro feat f; rfl
theorem r636110_d76 : ∀ feat, Dec feat r636110 76 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 17085 0)] 7) := by intro feat f; rfl
theorem r636110_d83 : ∀ feat, Dec feat r636110 83 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 23318 0)] 7) := by intro feat f; rfl
theorem r636110_d90 : ∀ feat, Dec feat r636110 90 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636110_d94 : ∀ feat, Dec feat r636110 94 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636110_shape : StrNCmp.Shape r636110 0x636110 0x63e3d0 0x63d3f0 0x63a420 0x63bc80 :=
  ⟨rfl, r636110_d0, r636110_d4, ⟨_, r636110_d14, by decide⟩, r636110_d21, ⟨_, r636110_d31, by decide⟩, r636110_d38, r636110_d41,
    ⟨_, r636110_d43, by decide⟩, r636110_d49, r636110_d55, ⟨_, r636110_d57, by decide⟩, ⟨_, r636110_d64, by decide⟩, r636110_d71, r636110_d73,
    ⟨_, r636110_d76, by decide⟩, ⟨_, r636110_d83, by decide⟩, r636110_d90, r636110_d94⟩

theorem r636110_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x636110 r636110) : ImplementsCall prof 0x636110 L (resolverK prof [(0x63a420, []), (0x63bc80, [Features.ssse3]), (0x63d3f0, [Features.sse42, Features.ssse3]), (0x63e3d0, [Features.avx, Features.avx2])]) :=
  StrNCmp.holds r636110_shape L prof hc hch hin

/-- The 85 bytes of `7zzs` at `0x6c7810`. -/
def r6c7810 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x8b, 0x15, 0x25, 0xd3, 0x0d, 0x00, 0x4c, 0x8d, 0x05, 0x0e, 0x4e,
  0xf9, 0xff, 0x48, 0xb8, 0x02, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x48, 0xb9, 0x02, 0x00,
  0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x48, 0x21, 0xd0, 0x48, 0x39, 0xc8, 0x75, 0x23, 0x48, 0xb8,
  0x04, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00, 0x4c, 0x8d, 0x05, 0xe1, 0x50, 0xf9, 0xff, 0x48,
  0x21, 0xc2, 0x48, 0x8d, 0x05, 0x57, 0x4f, 0xf9, 0xff, 0x48, 0x83, 0xfa, 0x04, 0x4c, 0x0f, 0x45,
  0xc0, 0x4c, 0x89, 0xc0, 0xc3]

theorem r6c7810_pin : Exe.bytesAt V2606.zzs.blob 0x6c7810 85 = some r6c7810 := by decide +kernel

theorem r6c7810_length : r6c7810.length = 85 := rfl

theorem r6c7810_d0 : ∀ feat, Dec feat r6c7810 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r6c7810_d4 : ∀ feat, Dec feat r6c7810 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 2, .mem (mrip 906021 64)] 7) := by intro feat f; rfl
theorem r6c7810_d11 : ∀ feat, Dec feat r6c7810 11 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 8, .mem (mrip 18446744073709112846 0)] 7) := by intro feat f; rfl
theorem r6c7810_d18 : ∀ feat, Dec feat r6c7810 18 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 9895604649986] 10) := by intro feat f; rfl
theorem r6c7810_d28 : ∀ feat, Dec feat r6c7810 28 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 1, .imm 64 1099511627778] 10) := by intro feat f; rfl
theorem r6c7810_d38 : ∀ feat, Dec feat r6c7810 38 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, gr 64 2] 3) := by intro feat f; rfl
theorem r6c7810_d41 : ∀ feat, Dec feat r6c7810 41 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, gr 64 1] 3) := by intro feat f; rfl
theorem r6c7810_d44 : ∀ feat, Dec feat r6c7810 44 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 35] 2) := by intro feat f; rfl
theorem r6c7810_d46 : ∀ feat, Dec feat r6c7810 46 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 70368744177668] 10) := by intro feat f; rfl
theorem r6c7810_d56 : ∀ feat, Dec feat r6c7810 56 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 8, .mem (mrip 18446744073709113569 0)] 7) := by intro feat f; rfl
theorem r6c7810_d63 : ∀ feat, Dec feat r6c7810 63 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 2, gr 64 0] 3) := by intro feat f; rfl
theorem r6c7810_d66 : ∀ feat, Dec feat r6c7810 66 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 18446744073709113175 0)] 7) := by intro feat f; rfl
theorem r6c7810_d73 : ∀ feat, Dec feat r6c7810 73 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 2, .imm 64 4] 4) := by intro feat f; rfl
theorem r6c7810_d77 : ∀ feat, Dec feat r6c7810 77 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 8, gr 64 0] 4) := by intro feat f; rfl
theorem r6c7810_d81 : ∀ feat, Dec feat r6c7810 81 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, gr 64 8] 3) := by intro feat f; rfl
theorem r6c7810_d84 : ∀ feat, Dec feat r6c7810 84 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r6c7810_shape : Wmemset.Shape r6c7810 0x6c7810 0x65c630 0x65c7b0 0x65c930 :=
  ⟨rfl, r6c7810_d0, ⟨_, r6c7810_d4, by decide⟩, ⟨_, r6c7810_d11, by decide⟩, r6c7810_d18, r6c7810_d28, r6c7810_d38, r6c7810_d41, r6c7810_d44,
    r6c7810_d46, ⟨_, r6c7810_d56, by decide⟩, r6c7810_d63, ⟨_, r6c7810_d66, by decide⟩, r6c7810_d73, r6c7810_d77, r6c7810_d81, r6c7810_d84⟩

theorem r6c7810_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x6c7810 r6c7810) : ImplementsCall prof 0x6c7810 L (resolverK prof [(0x65c630, []), (0x65c7b0, [Features.avx, Features.avx2]), (0x65c930, [Features.avx, Features.avx2, Features.avx512f])]) :=
  Wmemset.holds r6c7810_shape L prof hc hin

/-- The 186 bytes of `7zzs` at `0x636bc0`. -/
def r636bc0 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x15, 0x7a, 0xdf, 0x16, 0x00, 0x48, 0x8d, 0x05, 0x4f, 0x4d, 0x02,
  0x00, 0xf6, 0xc6, 0x30, 0x75, 0x5d, 0x48, 0xb8, 0x04, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00,
  0x48, 0x23, 0x05, 0x59, 0xdf, 0x16, 0x00, 0x48, 0x83, 0xf8, 0x04, 0x74, 0x4b, 0xf6, 0xc6, 0x01,
  0x74, 0x1e, 0xf6, 0x05, 0xfc, 0xde, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0xa0, 0x50, 0x02, 0x00,
  0x48, 0x8d, 0x05, 0xe9, 0x50, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3, 0x0f, 0x1f, 0x40, 0x00,
  0xf6, 0x05, 0xd2, 0xde, 0x16, 0x00, 0x02, 0x74, 0x47, 0xf6, 0xc2, 0x20, 0x75, 0x42, 0x83, 0xe2,
  0x08, 0x48, 0x8d, 0x05, 0x68, 0xa4, 0x00, 0x00, 0x48, 0x8d, 0x15, 0xf1, 0xf9, 0x00, 0x00, 0x48,
  0x0f, 0x45, 0xc2, 0xc3, 0x0f, 0x1f, 0x40, 0x00, 0x48, 0x8d, 0x05, 0x21, 0x50, 0x01, 0x00, 0x80,
  0xe6, 0x08, 0x75, 0xef, 0xf6, 0x05, 0xaa, 0xde, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0x8e, 0x54,
  0x02, 0x00, 0x48, 0x8d, 0x05, 0xd7, 0x54, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3, 0x66, 0x90,
  0xf6, 0x05, 0x8e, 0xde, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0x62, 0x4c, 0x02, 0x00, 0x48, 0x8d,
  0x05, 0x1b, 0x4d, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r636bc0_pin : Exe.bytesAt V2606.zzs.blob 0x636bc0 186 = some r636bc0 := by decide +kernel

theorem r636bc0_length : r636bc0.length = 186 := rfl

theorem r636bc0_d0 : ∀ feat, Dec feat r636bc0 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636bc0_d4 : ∀ feat, Dec feat r636bc0 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 1499002 32)] 6) := by intro feat f; rfl
theorem r636bc0_d10 : ∀ feat, Dec feat r636bc0 10 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 150863 0)] 7) := by intro feat f; rfl
theorem r636bc0_d17 : ∀ feat, Dec feat r636bc0 17 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gh 2, .imm 8 48] 3) := by intro feat f; rfl
theorem r636bc0_d20 : ∀ feat, Dec feat r636bc0 20 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 93] 2) := by intro feat f; rfl
theorem r636bc0_d22 : ∀ feat, Dec feat r636bc0 22 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 70368744177668] 10) := by intro feat f; rfl
theorem r636bc0_d32 : ∀ feat, Dec feat r636bc0 32 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1498969 64)] 7) := by intro feat f; rfl
theorem r636bc0_d39 : ∀ feat, Dec feat r636bc0 39 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, .imm 64 4] 4) := by intro feat f; rfl
theorem r636bc0_d43 : ∀ feat, Dec feat r636bc0 43 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 75] 2) := by intro feat f; rfl
theorem r636bc0_d45 : ∀ feat, Dec feat r636bc0 45 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gh 2, .imm 8 1] 3) := by intro feat f; rfl
theorem r636bc0_d48 : ∀ feat, Dec feat r636bc0 48 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 30] 2) := by intro feat f; rfl
theorem r636bc0_d50 : ∀ feat, Dec feat r636bc0 50 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498876 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636bc0_d57 : ∀ feat, Dec feat r636bc0 57 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 151712 0)] 7) := by intro feat f; rfl
theorem r636bc0_d64 : ∀ feat, Dec feat r636bc0 64 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 151785 0)] 7) := by intro feat f; rfl
theorem r636bc0_d71 : ∀ feat, Dec feat r636bc0 71 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636bc0_d75 : ∀ feat, Dec feat r636bc0 75 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636bc0_d76 : ∀ feat, Dec feat r636bc0 76 (FV7z.mk (ZellicX86.Decode.Mn.nop) 32 [.mem (mbd 0 0 32)] 4) := by intro feat f; rfl
theorem r636bc0_d80 : ∀ feat, Dec feat r636bc0 80 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498834 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636bc0_d87 : ∀ feat, Dec feat r636bc0 87 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 71] 2) := by intro feat f; rfl
theorem r636bc0_d89 : ∀ feat, Dec feat r636bc0 89 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gr 8 2, .imm 8 32] 3) := by intro feat f; rfl
theorem r636bc0_d92 : ∀ feat, Dec feat r636bc0 92 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 66] 2) := by intro feat f; rfl
theorem r636bc0_d94 : ∀ feat, Dec feat r636bc0 94 (FV7z.mk (ZellicX86.Decode.Mn.and) 32 [gr 32 2, .imm 32 8] 3) := by intro feat f; rfl
theorem r636bc0_d97 : ∀ feat, Dec feat r636bc0 97 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 42088 0)] 7) := by intro feat f; rfl
theorem r636bc0_d104 : ∀ feat, Dec feat r636bc0 104 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 63985 0)] 7) := by intro feat f; rfl
theorem r636bc0_d111 : ∀ feat, Dec feat r636bc0 111 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636bc0_d115 : ∀ feat, Dec feat r636bc0 115 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636bc0_d116 : ∀ feat, Dec feat r636bc0 116 (FV7z.mk (ZellicX86.Decode.Mn.nop) 32 [.mem (mbd 0 0 32)] 4) := by intro feat f; rfl
theorem r636bc0_d120 : ∀ feat, Dec feat r636bc0 120 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 86049 0)] 7) := by intro feat f; rfl
theorem r636bc0_d127 : ∀ feat, Dec feat r636bc0 127 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 8] 3) := by intro feat f; rfl
theorem r636bc0_d130 : ∀ feat, Dec feat r636bc0 130 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 18446744073709551599] 2) := by intro feat f; rfl
theorem r636bc0_d132 : ∀ feat, Dec feat r636bc0 132 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498794 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636bc0_d139 : ∀ feat, Dec feat r636bc0 139 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 152718 0)] 7) := by intro feat f; rfl
theorem r636bc0_d146 : ∀ feat, Dec feat r636bc0 146 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 152791 0)] 7) := by intro feat f; rfl
theorem r636bc0_d153 : ∀ feat, Dec feat r636bc0 153 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636bc0_d157 : ∀ feat, Dec feat r636bc0 157 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636bc0_d158 : ∀ feat, Dec feat r636bc0 158 (FV7z.mk (ZellicX86.Decode.Mn.nop) 16 [] 2) := by intro feat f; rfl
theorem r636bc0_d160 : ∀ feat, Dec feat r636bc0 160 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498766 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636bc0_d167 : ∀ feat, Dec feat r636bc0 167 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 150626 0)] 7) := by intro feat f; rfl
theorem r636bc0_d174 : ∀ feat, Dec feat r636bc0 174 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 150811 0)] 7) := by intro feat f; rfl
theorem r636bc0_d181 : ∀ feat, Dec feat r636bc0 181 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636bc0_d185 : ∀ feat, Dec feat r636bc0 185 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636bc0_shape : Memmove.Shape r636bc0 0x636bc0 ⟨0x65b920, 0x65bca0, 0x65bcf0, 0x641090, 0x646620, 0x64bc60, 0x65c0e0, 0x65c130, 0x65b8d0, 0x65b990⟩ :=
  ⟨rfl, r636bc0_d0, ⟨_, r636bc0_d4, by decide⟩, ⟨_, r636bc0_d10, by decide⟩, r636bc0_d17, r636bc0_d20, r636bc0_d22, ⟨_, r636bc0_d32, by decide⟩, r636bc0_d39, r636bc0_d43, r636bc0_d45, r636bc0_d48, ⟨_, r636bc0_d50, by decide⟩, ⟨_, r636bc0_d57, by decide⟩, ⟨_, r636bc0_d64, by decide⟩, r636bc0_d71, r636bc0_d75, ⟨_, r636bc0_d80, by decide⟩, r636bc0_d87, r636bc0_d89, r636bc0_d92, r636bc0_d94, ⟨_, r636bc0_d97, by decide⟩, ⟨_, r636bc0_d104, by decide⟩, r636bc0_d111, r636bc0_d115, ⟨_, r636bc0_d120, by decide⟩, r636bc0_d127, r636bc0_d130, ⟨_, r636bc0_d132, by decide⟩, ⟨_, r636bc0_d139, by decide⟩, ⟨_, r636bc0_d146, by decide⟩, r636bc0_d153, r636bc0_d157, ⟨_, r636bc0_d160, by decide⟩, ⟨_, r636bc0_d167, by decide⟩, ⟨_, r636bc0_d174, by decide⟩, r636bc0_d181, r636bc0_d185⟩

theorem r636bc0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x636bc0 r636bc0) : ImplementsCall prof 0x636bc0 L (resolverK prof [(0x65b920, []), (0x65b8d0, []), (0x65b990, []), (0x641090, [Features.ssse3, Features.sse3]), (0x646620, [Features.ssse3, Features.sse3]), (0x65bca0, [Features.avx, Features.avx2]), (0x65bcf0, [Features.avx, Features.avx2]), (0x64bc60, [Features.avx, Features.avx2, Features.avx512f]), (0x65c0e0, [Features.avx, Features.avx2, Features.avx512f]), (0x65c130, [Features.avx, Features.avx2, Features.avx512f])]) :=
  Memmove.holds r636bc0_shape L prof hc hch hin

/-- The 186 bytes of `7zzs` at `0x636d30`. -/
def r636d30 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x15, 0x0a, 0xde, 0x16, 0x00, 0x48, 0x8d, 0x05, 0x0f, 0x4c, 0x02,
  0x00, 0xf6, 0xc6, 0x30, 0x75, 0x5d, 0x48, 0xb8, 0x04, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00,
  0x48, 0x23, 0x05, 0xe9, 0xdd, 0x16, 0x00, 0x48, 0x83, 0xf8, 0x04, 0x74, 0x4b, 0xf6, 0xc6, 0x01,
  0x74, 0x1e, 0xf6, 0x05, 0x8c, 0xdd, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0x40, 0x4f, 0x02, 0x00,
  0x48, 0x8d, 0x05, 0x89, 0x4f, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3, 0x0f, 0x1f, 0x40, 0x00,
  0xf6, 0x05, 0x62, 0xdd, 0x16, 0x00, 0x02, 0x74, 0x47, 0xf6, 0xc2, 0x20, 0x75, 0x42, 0x83, 0xe2,
  0x08, 0x48, 0x8d, 0x05, 0x18, 0xa3, 0x00, 0x00, 0x48, 0x8d, 0x15, 0xa1, 0xf8, 0x00, 0x00, 0x48,
  0x0f, 0x45, 0xc2, 0xc3, 0x0f, 0x1f, 0x40, 0x00, 0x48, 0x8d, 0x05, 0xd1, 0x4e, 0x01, 0x00, 0x80,
  0xe6, 0x08, 0x75, 0xef, 0xf6, 0x05, 0x3a, 0xdd, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0x2e, 0x53,
  0x02, 0x00, 0x48, 0x8d, 0x05, 0x77, 0x53, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3, 0x66, 0x90,
  0xf6, 0x05, 0x1e, 0xdd, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0x02, 0x4b, 0x02, 0x00, 0x48, 0x8d,
  0x05, 0xbb, 0x4b, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r636d30_pin : Exe.bytesAt V2606.zzs.blob 0x636d30 186 = some r636d30 := by decide +kernel

theorem r636d30_length : r636d30.length = 186 := rfl

theorem r636d30_d0 : ∀ feat, Dec feat r636d30 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636d30_d4 : ∀ feat, Dec feat r636d30 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 1498634 32)] 6) := by intro feat f; rfl
theorem r636d30_d10 : ∀ feat, Dec feat r636d30 10 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 150543 0)] 7) := by intro feat f; rfl
theorem r636d30_d17 : ∀ feat, Dec feat r636d30 17 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gh 2, .imm 8 48] 3) := by intro feat f; rfl
theorem r636d30_d20 : ∀ feat, Dec feat r636d30 20 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 93] 2) := by intro feat f; rfl
theorem r636d30_d22 : ∀ feat, Dec feat r636d30 22 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 70368744177668] 10) := by intro feat f; rfl
theorem r636d30_d32 : ∀ feat, Dec feat r636d30 32 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1498601 64)] 7) := by intro feat f; rfl
theorem r636d30_d39 : ∀ feat, Dec feat r636d30 39 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, .imm 64 4] 4) := by intro feat f; rfl
theorem r636d30_d43 : ∀ feat, Dec feat r636d30 43 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 75] 2) := by intro feat f; rfl
theorem r636d30_d45 : ∀ feat, Dec feat r636d30 45 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gh 2, .imm 8 1] 3) := by intro feat f; rfl
theorem r636d30_d48 : ∀ feat, Dec feat r636d30 48 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 30] 2) := by intro feat f; rfl
theorem r636d30_d50 : ∀ feat, Dec feat r636d30 50 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498508 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636d30_d57 : ∀ feat, Dec feat r636d30 57 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 151360 0)] 7) := by intro feat f; rfl
theorem r636d30_d64 : ∀ feat, Dec feat r636d30 64 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 151433 0)] 7) := by intro feat f; rfl
theorem r636d30_d71 : ∀ feat, Dec feat r636d30 71 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636d30_d75 : ∀ feat, Dec feat r636d30 75 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636d30_d76 : ∀ feat, Dec feat r636d30 76 (FV7z.mk (ZellicX86.Decode.Mn.nop) 32 [.mem (mbd 0 0 32)] 4) := by intro feat f; rfl
theorem r636d30_d80 : ∀ feat, Dec feat r636d30 80 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498466 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636d30_d87 : ∀ feat, Dec feat r636d30 87 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 71] 2) := by intro feat f; rfl
theorem r636d30_d89 : ∀ feat, Dec feat r636d30 89 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gr 8 2, .imm 8 32] 3) := by intro feat f; rfl
theorem r636d30_d92 : ∀ feat, Dec feat r636d30 92 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 66] 2) := by intro feat f; rfl
theorem r636d30_d94 : ∀ feat, Dec feat r636d30 94 (FV7z.mk (ZellicX86.Decode.Mn.and) 32 [gr 32 2, .imm 32 8] 3) := by intro feat f; rfl
theorem r636d30_d97 : ∀ feat, Dec feat r636d30 97 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 41752 0)] 7) := by intro feat f; rfl
theorem r636d30_d104 : ∀ feat, Dec feat r636d30 104 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 63649 0)] 7) := by intro feat f; rfl
theorem r636d30_d111 : ∀ feat, Dec feat r636d30 111 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636d30_d115 : ∀ feat, Dec feat r636d30 115 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636d30_d116 : ∀ feat, Dec feat r636d30 116 (FV7z.mk (ZellicX86.Decode.Mn.nop) 32 [.mem (mbd 0 0 32)] 4) := by intro feat f; rfl
theorem r636d30_d120 : ∀ feat, Dec feat r636d30 120 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 85713 0)] 7) := by intro feat f; rfl
theorem r636d30_d127 : ∀ feat, Dec feat r636d30 127 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 8] 3) := by intro feat f; rfl
theorem r636d30_d130 : ∀ feat, Dec feat r636d30 130 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 18446744073709551599] 2) := by intro feat f; rfl
theorem r636d30_d132 : ∀ feat, Dec feat r636d30 132 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498426 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636d30_d139 : ∀ feat, Dec feat r636d30 139 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 152366 0)] 7) := by intro feat f; rfl
theorem r636d30_d146 : ∀ feat, Dec feat r636d30 146 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 152439 0)] 7) := by intro feat f; rfl
theorem r636d30_d153 : ∀ feat, Dec feat r636d30 153 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636d30_d157 : ∀ feat, Dec feat r636d30 157 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636d30_d158 : ∀ feat, Dec feat r636d30 158 (FV7z.mk (ZellicX86.Decode.Mn.nop) 16 [] 2) := by intro feat f; rfl
theorem r636d30_d160 : ∀ feat, Dec feat r636d30 160 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498398 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636d30_d167 : ∀ feat, Dec feat r636d30 167 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 150274 0)] 7) := by intro feat f; rfl
theorem r636d30_d174 : ∀ feat, Dec feat r636d30 174 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 150459 0)] 7) := by intro feat f; rfl
theorem r636d30_d181 : ∀ feat, Dec feat r636d30 181 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636d30_d185 : ∀ feat, Dec feat r636d30 185 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636d30_shape : Memmove.Shape r636d30 0x636d30 ⟨0x65b950, 0x65bcb0, 0x65bd00, 0x6410b0, 0x646640, 0x64bc80, 0x65c0f0, 0x65c140, 0x65b8e0, 0x65b9a0⟩ :=
  ⟨rfl, r636d30_d0, ⟨_, r636d30_d4, by decide⟩, ⟨_, r636d30_d10, by decide⟩, r636d30_d17, r636d30_d20, r636d30_d22, ⟨_, r636d30_d32, by decide⟩, r636d30_d39, r636d30_d43, r636d30_d45, r636d30_d48, ⟨_, r636d30_d50, by decide⟩, ⟨_, r636d30_d57, by decide⟩, ⟨_, r636d30_d64, by decide⟩, r636d30_d71, r636d30_d75, ⟨_, r636d30_d80, by decide⟩, r636d30_d87, r636d30_d89, r636d30_d92, r636d30_d94, ⟨_, r636d30_d97, by decide⟩, ⟨_, r636d30_d104, by decide⟩, r636d30_d111, r636d30_d115, ⟨_, r636d30_d120, by decide⟩, r636d30_d127, r636d30_d130, ⟨_, r636d30_d132, by decide⟩, ⟨_, r636d30_d139, by decide⟩, ⟨_, r636d30_d146, by decide⟩, r636d30_d153, r636d30_d157, ⟨_, r636d30_d160, by decide⟩, ⟨_, r636d30_d167, by decide⟩, ⟨_, r636d30_d174, by decide⟩, r636d30_d181, r636d30_d185⟩

theorem r636d30_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x636d30 r636d30) : ImplementsCall prof 0x636d30 L (resolverK prof [(0x65b950, []), (0x65b8e0, []), (0x65b9a0, []), (0x6410b0, [Features.ssse3, Features.sse3]), (0x646640, [Features.ssse3, Features.sse3]), (0x65bcb0, [Features.avx, Features.avx2]), (0x65bd00, [Features.avx, Features.avx2]), (0x64bc80, [Features.avx, Features.avx2, Features.avx512f]), (0x65c0f0, [Features.avx, Features.avx2, Features.avx512f]), (0x65c140, [Features.avx, Features.avx2, Features.avx512f])]) :=
  Memmove.holds r636d30_shape L prof hc hch hin

/-- The 186 bytes of `7zzs` at `0x636a60`. -/
def r636a60 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x15, 0xda, 0xe0, 0x16, 0x00, 0x48, 0x8d, 0x05, 0xdf, 0x4e, 0x02,
  0x00, 0xf6, 0xc6, 0x30, 0x75, 0x5d, 0x48, 0xb8, 0x04, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00,
  0x48, 0x23, 0x05, 0xb9, 0xe0, 0x16, 0x00, 0x48, 0x83, 0xf8, 0x04, 0x74, 0x4b, 0xf6, 0xc6, 0x01,
  0x74, 0x1e, 0xf6, 0x05, 0x5c, 0xe0, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0x10, 0x52, 0x02, 0x00,
  0x48, 0x8d, 0x05, 0x59, 0x52, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3, 0x0f, 0x1f, 0x40, 0x00,
  0xf6, 0x05, 0x32, 0xe0, 0x16, 0x00, 0x02, 0x74, 0x47, 0xf6, 0xc2, 0x20, 0x75, 0x42, 0x83, 0xe2,
  0x08, 0x48, 0x8d, 0x05, 0xc8, 0xcf, 0x00, 0x00, 0x48, 0x8d, 0x15, 0x61, 0x26, 0x01, 0x00, 0x48,
  0x0f, 0x45, 0xc2, 0xc3, 0x0f, 0x1f, 0x40, 0x00, 0x48, 0x8d, 0x05, 0xa1, 0x51, 0x01, 0x00, 0x80,
  0xe6, 0x08, 0x75, 0xef, 0xf6, 0x05, 0x0a, 0xe0, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0xfe, 0x55,
  0x02, 0x00, 0x48, 0x8d, 0x05, 0x47, 0x56, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3, 0x66, 0x90,
  0xf6, 0x05, 0xee, 0xdf, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0xd2, 0x4d, 0x02, 0x00, 0x48, 0x8d,
  0x05, 0x8b, 0x4e, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r636a60_pin : Exe.bytesAt V2606.zzs.blob 0x636a60 186 = some r636a60 := by decide +kernel

theorem r636a60_length : r636a60.length = 186 := rfl

theorem r636a60_d0 : ∀ feat, Dec feat r636a60 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636a60_d4 : ∀ feat, Dec feat r636a60 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 1499354 32)] 6) := by intro feat f; rfl
theorem r636a60_d10 : ∀ feat, Dec feat r636a60 10 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 151263 0)] 7) := by intro feat f; rfl
theorem r636a60_d17 : ∀ feat, Dec feat r636a60 17 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gh 2, .imm 8 48] 3) := by intro feat f; rfl
theorem r636a60_d20 : ∀ feat, Dec feat r636a60 20 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 93] 2) := by intro feat f; rfl
theorem r636a60_d22 : ∀ feat, Dec feat r636a60 22 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 70368744177668] 10) := by intro feat f; rfl
theorem r636a60_d32 : ∀ feat, Dec feat r636a60 32 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1499321 64)] 7) := by intro feat f; rfl
theorem r636a60_d39 : ∀ feat, Dec feat r636a60 39 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, .imm 64 4] 4) := by intro feat f; rfl
theorem r636a60_d43 : ∀ feat, Dec feat r636a60 43 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 75] 2) := by intro feat f; rfl
theorem r636a60_d45 : ∀ feat, Dec feat r636a60 45 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gh 2, .imm 8 1] 3) := by intro feat f; rfl
theorem r636a60_d48 : ∀ feat, Dec feat r636a60 48 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 30] 2) := by intro feat f; rfl
theorem r636a60_d50 : ∀ feat, Dec feat r636a60 50 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1499228 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636a60_d57 : ∀ feat, Dec feat r636a60 57 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 152080 0)] 7) := by intro feat f; rfl
theorem r636a60_d64 : ∀ feat, Dec feat r636a60 64 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 152153 0)] 7) := by intro feat f; rfl
theorem r636a60_d71 : ∀ feat, Dec feat r636a60 71 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636a60_d75 : ∀ feat, Dec feat r636a60 75 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636a60_d76 : ∀ feat, Dec feat r636a60 76 (FV7z.mk (ZellicX86.Decode.Mn.nop) 32 [.mem (mbd 0 0 32)] 4) := by intro feat f; rfl
theorem r636a60_d80 : ∀ feat, Dec feat r636a60 80 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1499186 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636a60_d87 : ∀ feat, Dec feat r636a60 87 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 71] 2) := by intro feat f; rfl
theorem r636a60_d89 : ∀ feat, Dec feat r636a60 89 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gr 8 2, .imm 8 32] 3) := by intro feat f; rfl
theorem r636a60_d92 : ∀ feat, Dec feat r636a60 92 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 66] 2) := by intro feat f; rfl
theorem r636a60_d94 : ∀ feat, Dec feat r636a60 94 (FV7z.mk (ZellicX86.Decode.Mn.and) 32 [gr 32 2, .imm 32 8] 3) := by intro feat f; rfl
theorem r636a60_d97 : ∀ feat, Dec feat r636a60 97 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 53192 0)] 7) := by intro feat f; rfl
theorem r636a60_d104 : ∀ feat, Dec feat r636a60 104 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 75361 0)] 7) := by intro feat f; rfl
theorem r636a60_d111 : ∀ feat, Dec feat r636a60 111 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636a60_d115 : ∀ feat, Dec feat r636a60 115 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636a60_d116 : ∀ feat, Dec feat r636a60 116 (FV7z.mk (ZellicX86.Decode.Mn.nop) 32 [.mem (mbd 0 0 32)] 4) := by intro feat f; rfl
theorem r636a60_d120 : ∀ feat, Dec feat r636a60 120 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 86433 0)] 7) := by intro feat f; rfl
theorem r636a60_d127 : ∀ feat, Dec feat r636a60 127 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 8] 3) := by intro feat f; rfl
theorem r636a60_d130 : ∀ feat, Dec feat r636a60 130 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 18446744073709551599] 2) := by intro feat f; rfl
theorem r636a60_d132 : ∀ feat, Dec feat r636a60 132 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1499146 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636a60_d139 : ∀ feat, Dec feat r636a60 139 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 153086 0)] 7) := by intro feat f; rfl
theorem r636a60_d146 : ∀ feat, Dec feat r636a60 146 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 153159 0)] 7) := by intro feat f; rfl
theorem r636a60_d153 : ∀ feat, Dec feat r636a60 153 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636a60_d157 : ∀ feat, Dec feat r636a60 157 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636a60_d158 : ∀ feat, Dec feat r636a60 158 (FV7z.mk (ZellicX86.Decode.Mn.nop) 16 [] 2) := by intro feat f; rfl
theorem r636a60_d160 : ∀ feat, Dec feat r636a60 160 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1499118 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636a60_d167 : ∀ feat, Dec feat r636a60 167 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 150994 0)] 7) := by intro feat f; rfl
theorem r636a60_d174 : ∀ feat, Dec feat r636a60 174 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 151179 0)] 7) := by intro feat f; rfl
theorem r636a60_d181 : ∀ feat, Dec feat r636a60 181 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636a60_d185 : ∀ feat, Dec feat r636a60 185 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636a60_shape : Memmove.Shape r636a60 0x636a60 ⟨0x65b950, 0x65bcb0, 0x65bd00, 0x643a90, 0x649130, 0x64bc80, 0x65c0f0, 0x65c140, 0x65b8e0, 0x65b9a0⟩ :=
  ⟨rfl, r636a60_d0, ⟨_, r636a60_d4, by decide⟩, ⟨_, r636a60_d10, by decide⟩, r636a60_d17, r636a60_d20, r636a60_d22, ⟨_, r636a60_d32, by decide⟩, r636a60_d39, r636a60_d43, r636a60_d45, r636a60_d48, ⟨_, r636a60_d50, by decide⟩, ⟨_, r636a60_d57, by decide⟩, ⟨_, r636a60_d64, by decide⟩, r636a60_d71, r636a60_d75, ⟨_, r636a60_d80, by decide⟩, r636a60_d87, r636a60_d89, r636a60_d92, r636a60_d94, ⟨_, r636a60_d97, by decide⟩, ⟨_, r636a60_d104, by decide⟩, r636a60_d111, r636a60_d115, ⟨_, r636a60_d120, by decide⟩, r636a60_d127, r636a60_d130, ⟨_, r636a60_d132, by decide⟩, ⟨_, r636a60_d139, by decide⟩, ⟨_, r636a60_d146, by decide⟩, r636a60_d153, r636a60_d157, ⟨_, r636a60_d160, by decide⟩, ⟨_, r636a60_d167, by decide⟩, ⟨_, r636a60_d174, by decide⟩, r636a60_d181, r636a60_d185⟩

theorem r636a60_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x636a60 r636a60) : ImplementsCall prof 0x636a60 L (resolverK prof [(0x65b950, []), (0x65b8e0, []), (0x65b9a0, []), (0x643a90, [Features.ssse3, Features.sse3]), (0x649130, [Features.ssse3, Features.sse3]), (0x65bcb0, [Features.avx, Features.avx2]), (0x65bd00, [Features.avx, Features.avx2]), (0x64bc80, [Features.avx, Features.avx2, Features.avx512f]), (0x65c0f0, [Features.avx, Features.avx2, Features.avx512f]), (0x65c140, [Features.avx, Features.avx2, Features.avx512f])]) :=
  Memmove.holds r636a60_shape L prof hc hch hin

/-- The 158 bytes of `7zzs` at `0x636b20`. -/
def r636b20 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x8b, 0x15, 0x1a, 0xe0, 0x16, 0x00, 0x48, 0x8d, 0x05, 0x6f, 0x5b, 0x02,
  0x00, 0xf6, 0xc6, 0x10, 0x75, 0x5e, 0x48, 0xb8, 0x04, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x00,
  0x48, 0x23, 0x05, 0xf9, 0xdf, 0x16, 0x00, 0x48, 0x83, 0xf8, 0x04, 0x74, 0x4b, 0x8b, 0x05, 0xa1,
  0xdf, 0x16, 0x00, 0x25, 0x00, 0x02, 0x00, 0x00, 0xf6, 0x05, 0xe1, 0xdf, 0x16, 0x00, 0x02, 0x74,
  0x1f, 0x85, 0xc0, 0x48, 0x8d, 0x15, 0x66, 0x5c, 0x02, 0x00, 0x48, 0x8d, 0x05, 0xaf, 0x5c, 0x02,
  0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x85, 0xc0, 0x48, 0x8d, 0x15, 0x37, 0x5b, 0x02, 0x00, 0x48, 0x8d, 0x05, 0xc0, 0x5a, 0x02, 0x00,
  0x48, 0x0f, 0x45, 0xc2, 0xc3, 0x0f, 0x1f, 0x00, 0x48, 0x8d, 0x05, 0xb1, 0x4a, 0x02, 0x00, 0x80,
  0xe6, 0x08, 0x75, 0xf0, 0xf6, 0x05, 0x4a, 0xdf, 0x16, 0x00, 0x02, 0x48, 0x8d, 0x15, 0x9e, 0x5d,
  0x02, 0x00, 0x48, 0x8d, 0x05, 0xf7, 0x5d, 0x02, 0x00, 0x48, 0x0f, 0x44, 0xc2, 0xc3]

theorem r636b20_pin : Exe.bytesAt V2606.zzs.blob 0x636b20 158 = some r636b20 := by decide +kernel

theorem r636b20_length : r636b20.length = 158 := rfl

theorem r636b20_d0 : ∀ feat, Dec feat r636b20 0 (FV7z.mk (ZellicX86.Decode.Mn.endbr64) 32 [] 4) := by intro feat f; rfl
theorem r636b20_d4 : ∀ feat, Dec feat r636b20 4 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 2, .mem (mrip 1499162 32)] 6) := by intro feat f; rfl
theorem r636b20_d10 : ∀ feat, Dec feat r636b20 10 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 154479 0)] 7) := by intro feat f; rfl
theorem r636b20_d17 : ∀ feat, Dec feat r636b20 17 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [gh 2, .imm 8 16] 3) := by intro feat f; rfl
theorem r636b20_d20 : ∀ feat, Dec feat r636b20 20 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 94] 2) := by intro feat f; rfl
theorem r636b20_d22 : ∀ feat, Dec feat r636b20 22 (FV7z.mk (ZellicX86.Decode.Mn.mov) 64 [gr 64 0, .imm 64 70368744177668] 10) := by intro feat f; rfl
theorem r636b20_d32 : ∀ feat, Dec feat r636b20 32 (FV7z.mk (ZellicX86.Decode.Mn.and) 64 [gr 64 0, .mem (mrip 1499129 64)] 7) := by intro feat f; rfl
theorem r636b20_d39 : ∀ feat, Dec feat r636b20 39 (FV7z.mk (ZellicX86.Decode.Mn.cmp) 64 [gr 64 0, .imm 64 4] 4) := by intro feat f; rfl
theorem r636b20_d43 : ∀ feat, Dec feat r636b20 43 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 75] 2) := by intro feat f; rfl
theorem r636b20_d45 : ∀ feat, Dec feat r636b20 45 (FV7z.mk (ZellicX86.Decode.Mn.mov) 32 [gr 32 0, .mem (mrip 1499041 32)] 6) := by intro feat f; rfl
theorem r636b20_d51 : ∀ feat, Dec feat r636b20 51 (FV7z.mk (ZellicX86.Decode.Mn.and) 32 [gr 32 0, .imm 32 512] 5) := by intro feat f; rfl
theorem r636b20_d56 : ∀ feat, Dec feat r636b20 56 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1499105 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636b20_d63 : ∀ feat, Dec feat r636b20 63 (FV7z.mk (ZellicX86.Decode.Mn.jcc 4) 64 [.rel 31] 2) := by intro feat f; rfl
theorem r636b20_d65 : ∀ feat, Dec feat r636b20 65 (FV7z.mk (ZellicX86.Decode.Mn.test) 32 [gr 32 0, gr 32 0] 2) := by intro feat f; rfl
theorem r636b20_d67 : ∀ feat, Dec feat r636b20 67 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 154726 0)] 7) := by intro feat f; rfl
theorem r636b20_d74 : ∀ feat, Dec feat r636b20 74 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 154799 0)] 7) := by intro feat f; rfl
theorem r636b20_d81 : ∀ feat, Dec feat r636b20 81 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636b20_d85 : ∀ feat, Dec feat r636b20 85 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636b20_d86 : ∀ feat, Dec feat r636b20 86 (FV7z.mk (ZellicX86.Decode.Mn.nop) 16 [.mem ({ seg := none, base := some 0, index := some 0, scale := 1, disp := 0, ripRel := false, addr32 := false, width := 16 })] 10) := by intro feat f; rfl
theorem r636b20_d96 : ∀ feat, Dec feat r636b20 96 (FV7z.mk (ZellicX86.Decode.Mn.test) 32 [gr 32 0, gr 32 0] 2) := by intro feat f; rfl
theorem r636b20_d98 : ∀ feat, Dec feat r636b20 98 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 154423 0)] 7) := by intro feat f; rfl
theorem r636b20_d105 : ∀ feat, Dec feat r636b20 105 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 154304 0)] 7) := by intro feat f; rfl
theorem r636b20_d112 : ∀ feat, Dec feat r636b20 112 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 5) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636b20_d116 : ∀ feat, Dec feat r636b20 116 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl
theorem r636b20_d117 : ∀ feat, Dec feat r636b20 117 (FV7z.mk (ZellicX86.Decode.Mn.nop) 32 [.mem (mbd 0 0 32)] 3) := by intro feat f; rfl
theorem r636b20_d120 : ∀ feat, Dec feat r636b20 120 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 150193 0)] 7) := by intro feat f; rfl
theorem r636b20_d127 : ∀ feat, Dec feat r636b20 127 (FV7z.mk (ZellicX86.Decode.Mn.and) 8 [gh 2, .imm 8 8] 3) := by intro feat f; rfl
theorem r636b20_d130 : ∀ feat, Dec feat r636b20 130 (FV7z.mk (ZellicX86.Decode.Mn.jcc 5) 64 [.rel 18446744073709551600] 2) := by intro feat f; rfl
theorem r636b20_d132 : ∀ feat, Dec feat r636b20 132 (FV7z.mk (ZellicX86.Decode.Mn.test) 8 [.mem (mrip 1498954 8), .imm 8 2] 7) := by intro feat f; rfl
theorem r636b20_d139 : ∀ feat, Dec feat r636b20 139 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 2, .mem (mrip 155038 0)] 7) := by intro feat f; rfl
theorem r636b20_d146 : ∀ feat, Dec feat r636b20 146 (FV7z.mk (ZellicX86.Decode.Mn.lea) 64 [gr 64 0, .mem (mrip 155127 0)] 7) := by intro feat f; rfl
theorem r636b20_d153 : ∀ feat, Dec feat r636b20 153 (FV7z.mk (ZellicX86.Decode.Mn.cmovcc 4) 64 [gr 64 0, gr 64 2] 4) := by intro feat f; rfl
theorem r636b20_d157 : ∀ feat, Dec feat r636b20 157 (FV7z.mk (ZellicX86.Decode.Mn.ret) 64 [] 1) := by intro feat f; rfl

theorem r636b20_shape : Memset.Shape r636b20 0x636b20 ⟨0x65c6a0, 0x65c7d0, 0x65c820, 0x65c6c0, 0x65c650, 0x65b650, 0x65c950, 0x65c9b0⟩ :=
  ⟨rfl, r636b20_d0, ⟨_, r636b20_d4, by decide⟩, ⟨_, r636b20_d10, by decide⟩, r636b20_d17, r636b20_d20, r636b20_d22, ⟨_, r636b20_d32, by decide⟩, r636b20_d39, r636b20_d43, ⟨_, r636b20_d45, by decide⟩, r636b20_d51, ⟨_, r636b20_d56, by decide⟩, r636b20_d63, r636b20_d65, ⟨_, r636b20_d67, by decide⟩, ⟨_, r636b20_d74, by decide⟩, r636b20_d81, r636b20_d85, r636b20_d96, ⟨_, r636b20_d98, by decide⟩, ⟨_, r636b20_d105, by decide⟩, r636b20_d112, r636b20_d116, ⟨_, r636b20_d120, by decide⟩, r636b20_d127, r636b20_d130, ⟨_, r636b20_d132, by decide⟩, ⟨_, r636b20_d139, by decide⟩, ⟨_, r636b20_d146, by decide⟩, r636b20_d153, r636b20_d157⟩

theorem r636b20_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (hch : Chain prof)
    (hin : CodeIn L 0x636b20 r636b20) : ImplementsCall prof 0x636b20 L (resolverK prof [(0x65c6a0, []), (0x65c6c0, []), (0x65c650, []), (0x65c7d0, [Features.avx, Features.avx2]), (0x65c820, [Features.avx, Features.avx2]), (0x65b650, [Features.avx, Features.avx2, Features.avx512f]), (0x65c950, [Features.avx, Features.avx2, Features.avx512f]), (0x65c9b0, [Features.avx, Features.avx2, Features.avx512f])]) :=
  Memset.holds r636b20_shape L prof hc hch hin


theorem r6369f0_pin : Exe.bytesAt V2606.zzs.blob 0x6369f0 105 = some IfMemcmp.code := IfMemcmp.pin

theorem r6369f0_holds (L : List (Addr × List Byte)) (prof : Profile) (hc : prof.Consistent) (_ : Chain prof)
    (hin : CodeIn L 0x6369f0 IfMemcmp.code) : ImplementsCall prof 0x6369f0 L (resolverK prof [(0x63f260, []), (0x659840, [Features.ssse3]), (0x63fa40, [Features.sse41]), (0x63f660, [Features.avx, Features.avx2, Features.movbe])]) :=
  IfMemcmp.holds' L prof hc hin


end FV7z.Glibc.Res
