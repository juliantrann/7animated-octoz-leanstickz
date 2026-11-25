import FV7z.Lemmas.Sse2b
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.RepMovsb
import FV7z.Lemmas.StoreX
/-!
# The code of glibc's `memmove`/`memcpy`/`mempcpy` variants without AVX (PLAN.md M, the PLT contracts of
`launch_to_main`)

glibc 2.31's `memmove-vec-unaligned-erms.S` with SSE2 vectors, `[0x65b8d0, 0x65bcb0)` in `7zzs` (`mc2`), the code the
IFUNC resolvers of `memmove` (`0x636a60`), `memcpy` (`0x636d30`) and `mempcpy` (`0x636bc0`) share on a processor
without AVX2 or SSSE3: at `+0` `__mempcpy_sse2_unaligned`, `+16` `__memmove_sse2_unaligned` (= `__memcpy_…`), `+80`
`__mempcpy_erms`, `+128` `__memmove_erms`, `+192` `__mempcpy_sse2_unaligned_erms`, `+208`
`__memmove_sse2_unaligned_erms`; the `__…_chk` entries (`+64`, `+112`) jump to `__chk_fail` when the size exceeds
the object's. What each instruction decodes to on every processor (`d<offset>`, by evaluation), from the decoder's
output (`decshow`).
-/
namespace FV7z.Memcpy
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The bytes of `memmove`'s variants without AVX. -/
def mc2 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x01, 0xd0, 0xeb, 0x0b, 0x0f, 0x1f, 0x40, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x83, 0xfa, 0x10, 0x0f, 0x82, 0xfa, 0x00, 0x00,
  0x00, 0x48, 0x83, 0xfa, 0x20, 0x0f, 0x87, 0x3f, 0x01, 0x00, 0x00, 0x0f, 0x10, 0x06, 0x0f, 0x10,
  0x4c, 0x16, 0xf0, 0x0f, 0x11, 0x07, 0x0f, 0x11, 0x4c, 0x17, 0xf0, 0xc3, 0x0f, 0x1f, 0x40, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x39, 0xd1, 0x0f, 0x82, 0x73, 0xde, 0x00, 0x00, 0x0f, 0x1f, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x85, 0xd2, 0x74, 0x45, 0x48, 0x01, 0xd0, 0xeb,
  0x2b, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x40, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x39, 0xd1, 0x0f, 0x82, 0x43, 0xde, 0x00, 0x00, 0x0f, 0x1f, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x85, 0xd2, 0x74, 0x15, 0x48, 0x89, 0xd1, 0x48,
  0x39, 0xf7, 0x72, 0x0b, 0x74, 0x0b, 0x48, 0x8d, 0x14, 0x0e, 0x48, 0x39, 0xd7, 0x72, 0x03, 0xf3,
  0xa4, 0xc3, 0x48, 0x8d, 0x7c, 0x0f, 0xff, 0x48, 0x8d, 0x74, 0x0e, 0xff, 0xfd, 0xf3, 0xa4, 0xfc,
  0xc3, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x40, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x01, 0xd0, 0xeb, 0x0b, 0x0f, 0x1f, 0x40, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x83, 0xfa, 0x10, 0x72, 0x3e, 0x48, 0x83, 0xfa,
  0x20, 0x77, 0x7e, 0x0f, 0x10, 0x06, 0x0f, 0x10, 0x4c, 0x16, 0xf0, 0x0f, 0x11, 0x07, 0x0f, 0x11,
  0x4c, 0x17, 0xf0, 0xc3, 0x48, 0x3b, 0x15, 0x5d, 0xca, 0x14, 0x00, 0x0f, 0x83, 0xe2, 0x00, 0x00,
  0x00, 0x48, 0x39, 0xf7, 0x72, 0x0f, 0x74, 0x12, 0x4c, 0x8d, 0x0c, 0x16, 0x4c, 0x39, 0xcf, 0x0f,
  0x82, 0x63, 0x01, 0x00, 0x00, 0x48, 0x89, 0xd1, 0xf3, 0xa4, 0xc3, 0x80, 0xfa, 0x08, 0x73, 0x12,
  0x80, 0xfa, 0x04, 0x73, 0x1e, 0x80, 0xfa, 0x01, 0x77, 0x26, 0x72, 0x05, 0x0f, 0xb6, 0x0e, 0x88,
  0x0f, 0xc3, 0x48, 0x8b, 0x4c, 0x16, 0xf8, 0x48, 0x8b, 0x36, 0x48, 0x89, 0x4c, 0x17, 0xf8, 0x48,
  0x89, 0x37, 0xc3, 0x8b, 0x4c, 0x16, 0xfc, 0x8b, 0x36, 0x89, 0x4c, 0x17, 0xfc, 0x89, 0x37, 0xc3,
  0x0f, 0xb7, 0x4c, 0x16, 0xfe, 0x0f, 0xb7, 0x36, 0x66, 0x89, 0x4c, 0x17, 0xfe, 0x66, 0x89, 0x37,
  0xc3, 0x48, 0x81, 0xfa, 0x00, 0x08, 0x00, 0x00, 0x77, 0x8a, 0x48, 0x81, 0xfa, 0x80, 0x00, 0x00,
  0x00, 0x77, 0x70, 0x48, 0x83, 0xfa, 0x40, 0x72, 0x47, 0x0f, 0x10, 0x06, 0x0f, 0x10, 0x4e, 0x10,
  0x0f, 0x10, 0x56, 0x20, 0x0f, 0x10, 0x5e, 0x30, 0x0f, 0x10, 0x64, 0x16, 0xf0, 0x0f, 0x10, 0x6c,
  0x16, 0xe0, 0x0f, 0x10, 0x74, 0x16, 0xd0, 0x0f, 0x10, 0x7c, 0x16, 0xc0, 0x0f, 0x11, 0x07, 0x0f,
  0x11, 0x4f, 0x10, 0x0f, 0x11, 0x57, 0x20, 0x0f, 0x11, 0x5f, 0x30, 0x0f, 0x11, 0x64, 0x17, 0xf0,
  0x0f, 0x11, 0x6c, 0x17, 0xe0, 0x0f, 0x11, 0x74, 0x17, 0xd0, 0x0f, 0x11, 0x7c, 0x17, 0xc0, 0xc3,
  0x0f, 0x10, 0x06, 0x0f, 0x10, 0x4e, 0x10, 0x0f, 0x10, 0x54, 0x16, 0xf0, 0x0f, 0x10, 0x5c, 0x16,
  0xe0, 0x0f, 0x11, 0x07, 0x0f, 0x11, 0x4f, 0x10, 0x0f, 0x11, 0x54, 0x17, 0xf0, 0x0f, 0x11, 0x5c,
  0x17, 0xe0, 0xc3, 0x48, 0x39, 0xf7, 0x0f, 0x87, 0x8c, 0x00, 0x00, 0x00, 0x0f, 0x84, 0x28, 0xff,
  0xff, 0xff, 0x0f, 0x10, 0x26, 0x0f, 0x10, 0x6c, 0x16, 0xf0, 0x0f, 0x10, 0x74, 0x16, 0xe0, 0x0f,
  0x10, 0x7c, 0x16, 0xd0, 0x44, 0x0f, 0x10, 0x44, 0x16, 0xc0, 0x49, 0x89, 0xfb, 0x48, 0x8d, 0x4c,
  0x17, 0xf0, 0x49, 0x89, 0xf8, 0x49, 0x83, 0xe0, 0x0f, 0x49, 0x83, 0xe8, 0x10, 0x4c, 0x29, 0xc6,
  0x4c, 0x29, 0xc7, 0x4c, 0x01, 0xc2, 0x48, 0x3b, 0x15, 0x2b, 0xc9, 0x14, 0x00, 0x0f, 0x87, 0xcc,
  0x00, 0x00, 0x00, 0x0f, 0x10, 0x06, 0x0f, 0x10, 0x4e, 0x10, 0x0f, 0x10, 0x56, 0x20, 0x0f, 0x10,
  0x5e, 0x30, 0x48, 0x83, 0xc6, 0x40, 0x48, 0x83, 0xea, 0x40, 0x0f, 0x29, 0x07, 0x0f, 0x29, 0x4f,
  0x10, 0x0f, 0x29, 0x57, 0x20, 0x0f, 0x29, 0x5f, 0x30, 0x48, 0x83, 0xc7, 0x40, 0x48, 0x83, 0xfa,
  0x40, 0x77, 0xd0, 0x0f, 0x11, 0x29, 0x0f, 0x11, 0x71, 0xf0, 0x0f, 0x11, 0x79, 0xe0, 0x44, 0x0f,
  0x11, 0x41, 0xd0, 0x41, 0x0f, 0x11, 0x23, 0xc3, 0x0f, 0x10, 0x26, 0x0f, 0x10, 0x6e, 0x10, 0x0f,
  0x10, 0x76, 0x20, 0x0f, 0x10, 0x7e, 0x30, 0x44, 0x0f, 0x10, 0x44, 0x16, 0xf0, 0x4c, 0x8d, 0x5c,
  0x17, 0xf0, 0x48, 0x8d, 0x4c, 0x16, 0xf0, 0x4d, 0x89, 0xd9, 0x4d, 0x89, 0xd8, 0x49, 0x83, 0xe0,
  0x0f, 0x4c, 0x29, 0xc1, 0x4d, 0x29, 0xc1, 0x4c, 0x29, 0xc2, 0x48, 0x3b, 0x15, 0xa7, 0xc8, 0x14,
  0x00, 0x0f, 0x87, 0xaf, 0x00, 0x00, 0x00, 0x0f, 0x10, 0x01, 0x0f, 0x10, 0x49, 0xf0, 0x0f, 0x10,
  0x51, 0xe0, 0x0f, 0x10, 0x59, 0xd0, 0x48, 0x83, 0xe9, 0x40, 0x48, 0x83, 0xea, 0x40, 0x41, 0x0f,
  0x29, 0x01, 0x41, 0x0f, 0x29, 0x49, 0xf0, 0x41, 0x0f, 0x29, 0x51, 0xe0, 0x41, 0x0f, 0x29, 0x59,
  0xd0, 0x49, 0x83, 0xe9, 0x40, 0x48, 0x83, 0xfa, 0x40, 0x77, 0xcc, 0x0f, 0x11, 0x27, 0x0f, 0x11,
  0x6f, 0x10, 0x0f, 0x11, 0x77, 0x20, 0x0f, 0x11, 0x7f, 0x30, 0x45, 0x0f, 0x11, 0x03, 0xc3, 0x4c,
  0x8d, 0x14, 0x17, 0x4c, 0x39, 0xd6, 0x0f, 0x82, 0x27, 0xff, 0xff, 0xff, 0x0f, 0x18, 0x8e, 0x80,
  0x00, 0x00, 0x00, 0x0f, 0x18, 0x8e, 0xc0, 0x00, 0x00, 0x00, 0x0f, 0x10, 0x06, 0x0f, 0x10, 0x4e,
  0x10, 0x0f, 0x10, 0x56, 0x20, 0x0f, 0x10, 0x5e, 0x30, 0x48, 0x83, 0xc6, 0x40, 0x48, 0x83, 0xea,
  0x40, 0x66, 0x0f, 0xe7, 0x07, 0x66, 0x0f, 0xe7, 0x4f, 0x10, 0x66, 0x0f, 0xe7, 0x57, 0x20, 0x66,
  0x0f, 0xe7, 0x5f, 0x30, 0x48, 0x83, 0xc7, 0x40, 0x48, 0x83, 0xfa, 0x40, 0x77, 0xbe, 0x0f, 0xae,
  0xf8, 0x0f, 0x11, 0x29, 0x0f, 0x11, 0x71, 0xf0, 0x0f, 0x11, 0x79, 0xe0, 0x44, 0x0f, 0x11, 0x41,
  0xd0, 0x41, 0x0f, 0x11, 0x23, 0xc3, 0x4c, 0x8d, 0x14, 0x11, 0x4d, 0x39, 0xd1, 0x0f, 0x82, 0x44,
  0xff, 0xff, 0xff, 0x0f, 0x18, 0x49, 0x80, 0x0f, 0x18, 0x89, 0x40, 0xff, 0xff, 0xff, 0x0f, 0x10,
  0x01, 0x0f, 0x10, 0x49, 0xf0, 0x0f, 0x10, 0x51, 0xe0, 0x0f, 0x10, 0x59, 0xd0, 0x48, 0x83, 0xe9,
  0x40, 0x48, 0x83, 0xea, 0x40, 0x66, 0x41, 0x0f, 0xe7, 0x01, 0x66, 0x41, 0x0f, 0xe7, 0x49, 0xf0,
  0x66, 0x41, 0x0f, 0xe7, 0x51, 0xe0, 0x66, 0x41, 0x0f, 0xe7, 0x59, 0xd0, 0x49, 0x83, 0xe9, 0x40,
  0x48, 0x83, 0xfa, 0x40, 0x77, 0xbd, 0x0f, 0xae, 0xf8, 0x0f, 0x11, 0x27, 0x0f, 0x11, 0x6f, 0x10,
  0x0f, 0x11, 0x77, 0x20, 0x0f, 0x11, 0x7f, 0x30, 0x45, 0x0f, 0x11, 0x03, 0xc3, 0x0f, 0x1f, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x89, 0xf8, 0x48, 0x01, 0xd0, 0xeb, 0x0b, 0x0f, 0x1f, 0x40, 0x00]

theorem mc2_length : mc2.length = 992 := rfl

theorem d0 : ∀ feat, Dec feat mc2 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d4 : ∀ feat, Dec feat mc2 4 (FV7z.mk .mov 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d7 : ∀ feat, Dec feat mc2 7 (FV7z.mk .add 64 [gr 64 0, gr 64 2] 3) := by dec_rfl
theorem d10 : ∀ feat, Dec feat mc2 10 (FV7z.mk .jmp 64 [.rel 11] 2) := by dec_rfl
theorem d16 : ∀ feat, Dec feat mc2 16 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d20 : ∀ feat, Dec feat mc2 20 (FV7z.mk .mov 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d23 : ∀ feat, Dec feat mc2 23 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 16] 4) := by dec_rfl
theorem d27 : ∀ feat, Dec feat mc2 27 (FV7z.mk (.jcc 2) 64 [.rel 250] 6) := by dec_rfl
theorem d33 : ∀ feat, Dec feat mc2 33 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 32] 4) := by dec_rfl
theorem d37 : ∀ feat, Dec feat mc2 37 (FV7z.mk (.jcc 7) 64 [.rel 319] 6) := by dec_rfl
theorem d43 : ∀ feat, Dec feat mc2 43 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d46 : ∀ feat, Dec feat mc2 46
    (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbi 6 2 18446744073709551600 128)] 5) := by dec_rfl
theorem d51 : ∀ feat, Dec feat mc2 51 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 0 128), .xmm 0] 3) := by dec_rfl
theorem d54 : ∀ feat, Dec feat mc2 54
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 1] 5) := by dec_rfl
theorem d59 : ∀ feat, Dec feat mc2 59 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d64 : ∀ feat, Dec feat mc2 64 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d68 : ∀ feat, Dec feat mc2 68 (FV7z.mk .cmp 64 [gr 64 1, gr 64 2] 3) := by dec_rfl
theorem d71 : ∀ feat, Dec feat mc2 71 (FV7z.mk (.jcc 2) 64 [.rel 56947] 6) := by dec_rfl
theorem d80 : ∀ feat, Dec feat mc2 80 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d84 : ∀ feat, Dec feat mc2 84 (FV7z.mk .mov 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d87 : ∀ feat, Dec feat mc2 87 (FV7z.mk .test 64 [gr 64 2, gr 64 2] 3) := by dec_rfl
theorem d90 : ∀ feat, Dec feat mc2 90 (FV7z.mk (.jcc 4) 64 [.rel 69] 2) := by dec_rfl
theorem d92 : ∀ feat, Dec feat mc2 92 (FV7z.mk .add 64 [gr 64 0, gr 64 2] 3) := by dec_rfl
theorem d95 : ∀ feat, Dec feat mc2 95 (FV7z.mk .jmp 64 [.rel 43] 2) := by dec_rfl
theorem d112 : ∀ feat, Dec feat mc2 112 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d116 : ∀ feat, Dec feat mc2 116 (FV7z.mk .cmp 64 [gr 64 1, gr 64 2] 3) := by dec_rfl
theorem d119 : ∀ feat, Dec feat mc2 119 (FV7z.mk (.jcc 2) 64 [.rel 56899] 6) := by dec_rfl
theorem d128 : ∀ feat, Dec feat mc2 128 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d132 : ∀ feat, Dec feat mc2 132 (FV7z.mk .mov 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d135 : ∀ feat, Dec feat mc2 135 (FV7z.mk .test 64 [gr 64 2, gr 64 2] 3) := by dec_rfl
theorem d138 : ∀ feat, Dec feat mc2 138 (FV7z.mk (.jcc 4) 64 [.rel 21] 2) := by dec_rfl
theorem d140 : ∀ feat, Dec feat mc2 140 (FV7z.mk .mov 64 [gr 64 1, gr 64 2] 3) := by dec_rfl
theorem d143 : ∀ feat, Dec feat mc2 143 (FV7z.mk .cmp 64 [gr 64 7, gr 64 6] 3) := by dec_rfl
theorem d146 : ∀ feat, Dec feat mc2 146 (FV7z.mk (.jcc 2) 64 [.rel 11] 2) := by dec_rfl
theorem d148 : ∀ feat, Dec feat mc2 148 (FV7z.mk (.jcc 4) 64 [.rel 11] 2) := by dec_rfl
theorem d150 : ∀ feat, Dec feat mc2 150 (FV7z.mk .lea 64 [gr 64 2, .mem (mbi 6 1 0 0)] 4) := by dec_rfl
theorem d154 : ∀ feat, Dec feat mc2 154 (FV7z.mk .cmp 64 [gr 64 7, gr 64 2] 3) := by dec_rfl
theorem d157 : ∀ feat, Dec feat mc2 157 (FV7z.mk (.jcc 2) 64 [.rel 3] 2) := by dec_rfl
theorem d159 : ∀ feat, Dec feat mc2 159 (repMovsb 2) := by dec_rfl
theorem d161 : ∀ feat, Dec feat mc2 161 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d162 : ∀ feat, Dec feat mc2 162
    (FV7z.mk .lea 64 [gr 64 7, .mem (mbi 7 1 18446744073709551615 0)] 5) := by dec_rfl
theorem d167 : ∀ feat, Dec feat mc2 167
    (FV7z.mk .lea 64 [gr 64 6, .mem (mbi 6 1 18446744073709551615 0)] 5) := by dec_rfl
theorem d172 : ∀ feat, Dec feat mc2 172 (FV7z.mk (.str (.std)) 32 [] 1) := by dec_rfl
theorem d173 : ∀ feat, Dec feat mc2 173 (repMovsb 2) := by dec_rfl
theorem d175 : ∀ feat, Dec feat mc2 175 (FV7z.mk (.str (.cld)) 32 [] 1) := by dec_rfl
theorem d176 : ∀ feat, Dec feat mc2 176 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d192 : ∀ feat, Dec feat mc2 192 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d196 : ∀ feat, Dec feat mc2 196 (FV7z.mk .mov 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d199 : ∀ feat, Dec feat mc2 199 (FV7z.mk .add 64 [gr 64 0, gr 64 2] 3) := by dec_rfl
theorem d202 : ∀ feat, Dec feat mc2 202 (FV7z.mk .jmp 64 [.rel 11] 2) := by dec_rfl
theorem d208 : ∀ feat, Dec feat mc2 208 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d212 : ∀ feat, Dec feat mc2 212 (FV7z.mk .mov 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d215 : ∀ feat, Dec feat mc2 215 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 16] 4) := by dec_rfl
theorem d219 : ∀ feat, Dec feat mc2 219 (FV7z.mk (.jcc 2) 64 [.rel 62] 2) := by dec_rfl
theorem d221 : ∀ feat, Dec feat mc2 221 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 32] 4) := by dec_rfl
theorem d225 : ∀ feat, Dec feat mc2 225 (FV7z.mk (.jcc 7) 64 [.rel 126] 2) := by dec_rfl
theorem d227 : ∀ feat, Dec feat mc2 227 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d230 : ∀ feat, Dec feat mc2 230
    (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbi 6 2 18446744073709551600 128)] 5) := by dec_rfl
theorem d235 : ∀ feat, Dec feat mc2 235 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 0 128), .xmm 0] 3) := by dec_rfl
theorem d238 : ∀ feat, Dec feat mc2 238
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 1] 5) := by dec_rfl
theorem d243 : ∀ feat, Dec feat mc2 243 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d244 : ∀ feat, Dec feat mc2 244 (FV7z.mk .cmp 64 [gr 64 2, .mem (mrip 1362525 64)] 7) := by dec_rfl
theorem d251 : ∀ feat, Dec feat mc2 251 (FV7z.mk (.jcc 3) 64 [.rel 226] 6) := by dec_rfl
theorem d257 : ∀ feat, Dec feat mc2 257 (FV7z.mk .cmp 64 [gr 64 7, gr 64 6] 3) := by dec_rfl
theorem d260 : ∀ feat, Dec feat mc2 260 (FV7z.mk (.jcc 2) 64 [.rel 15] 2) := by dec_rfl
theorem d262 : ∀ feat, Dec feat mc2 262 (FV7z.mk (.jcc 4) 64 [.rel 18] 2) := by dec_rfl
theorem d264 : ∀ feat, Dec feat mc2 264 (FV7z.mk .lea 64 [gr 64 9, .mem (mbi 6 2 0 0)] 4) := by dec_rfl
theorem d268 : ∀ feat, Dec feat mc2 268 (FV7z.mk .cmp 64 [gr 64 7, gr 64 9] 3) := by dec_rfl
theorem d271 : ∀ feat, Dec feat mc2 271 (FV7z.mk (.jcc 2) 64 [.rel 355] 6) := by dec_rfl
theorem d277 : ∀ feat, Dec feat mc2 277 (FV7z.mk .mov 64 [gr 64 1, gr 64 2] 3) := by dec_rfl
theorem d280 : ∀ feat, Dec feat mc2 280 (repMovsb 2) := by dec_rfl
theorem d282 : ∀ feat, Dec feat mc2 282 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d283 : ∀ feat, Dec feat mc2 283 (FV7z.mk .cmp 8 [gr 8 2, .imm 8 8] 3) := by dec_rfl
theorem d286 : ∀ feat, Dec feat mc2 286 (FV7z.mk (.jcc 3) 64 [.rel 18] 2) := by dec_rfl
theorem d288 : ∀ feat, Dec feat mc2 288 (FV7z.mk .cmp 8 [gr 8 2, .imm 8 4] 3) := by dec_rfl
theorem d291 : ∀ feat, Dec feat mc2 291 (FV7z.mk (.jcc 3) 64 [.rel 30] 2) := by dec_rfl
theorem d293 : ∀ feat, Dec feat mc2 293 (FV7z.mk .cmp 8 [gr 8 2, .imm 8 1] 3) := by dec_rfl
theorem d296 : ∀ feat, Dec feat mc2 296 (FV7z.mk (.jcc 7) 64 [.rel 38] 2) := by dec_rfl
theorem d298 : ∀ feat, Dec feat mc2 298 (FV7z.mk (.jcc 2) 64 [.rel 5] 2) := by dec_rfl
theorem d300 : ∀ feat, Dec feat mc2 300 (FV7z.mk .movzx 32 [gr 32 1, .mem (mbd 6 0 8)] 3) := by dec_rfl
theorem d303 : ∀ feat, Dec feat mc2 303 (FV7z.mk .mov 8 [.mem (mbd 7 0 8), gr 8 1] 2) := by dec_rfl
theorem d305 : ∀ feat, Dec feat mc2 305 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d306 : ∀ feat, Dec feat mc2 306
    (FV7z.mk .mov 64 [gr 64 1, .mem (mbi 6 2 18446744073709551608 64)] 5) := by dec_rfl
theorem d311 : ∀ feat, Dec feat mc2 311 (FV7z.mk .mov 64 [gr 64 6, .mem (mbd 6 0 64)] 3) := by dec_rfl
theorem d314 : ∀ feat, Dec feat mc2 314
    (FV7z.mk .mov 64 [.mem (mbi 7 2 18446744073709551608 64), gr 64 1] 5) := by dec_rfl
theorem d319 : ∀ feat, Dec feat mc2 319 (FV7z.mk .mov 64 [.mem (mbd 7 0 64), gr 64 6] 3) := by dec_rfl
theorem d322 : ∀ feat, Dec feat mc2 322 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d323 : ∀ feat, Dec feat mc2 323
    (FV7z.mk .mov 32 [gr 32 1, .mem (mbi 6 2 18446744073709551612 32)] 4) := by dec_rfl
theorem d327 : ∀ feat, Dec feat mc2 327 (FV7z.mk .mov 32 [gr 32 6, .mem (mbd 6 0 32)] 2) := by dec_rfl
theorem d329 : ∀ feat, Dec feat mc2 329
    (FV7z.mk .mov 32 [.mem (mbi 7 2 18446744073709551612 32), gr 32 1] 4) := by dec_rfl
theorem d333 : ∀ feat, Dec feat mc2 333 (FV7z.mk .mov 32 [.mem (mbd 7 0 32), gr 32 6] 2) := by dec_rfl
theorem d335 : ∀ feat, Dec feat mc2 335 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d336 : ∀ feat, Dec feat mc2 336
    (FV7z.mk .movzx 32 [gr 32 1, .mem (mbi 6 2 18446744073709551614 16)] 5) := by dec_rfl
theorem d341 : ∀ feat, Dec feat mc2 341 (FV7z.mk .movzx 32 [gr 32 6, .mem (mbd 6 0 16)] 3) := by dec_rfl
theorem d344 : ∀ feat, Dec feat mc2 344
    (FV7z.mk .mov 16 [.mem (mbi 7 2 18446744073709551614 16), gr 16 1] 5) := by dec_rfl
theorem d349 : ∀ feat, Dec feat mc2 349 (FV7z.mk .mov 16 [.mem (mbd 7 0 16), gr 16 6] 3) := by dec_rfl
theorem d352 : ∀ feat, Dec feat mc2 352 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d353 : ∀ feat, Dec feat mc2 353 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 2048] 7) := by dec_rfl
theorem d360 : ∀ feat, Dec feat mc2 360 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551498] 2) := by dec_rfl
theorem d362 : ∀ feat, Dec feat mc2 362 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 128] 7) := by dec_rfl
theorem d369 : ∀ feat, Dec feat mc2 369 (FV7z.mk (.jcc 7) 64 [.rel 112] 2) := by dec_rfl
theorem d371 : ∀ feat, Dec feat mc2 371 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d375 : ∀ feat, Dec feat mc2 375 (FV7z.mk (.jcc 2) 64 [.rel 71] 2) := by dec_rfl
theorem d377 : ∀ feat, Dec feat mc2 377 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d380 : ∀ feat, Dec feat mc2 380 (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbd 6 16 128)] 4) := by dec_rfl
theorem d384 : ∀ feat, Dec feat mc2 384 (FV7z.mk (.sse (.movups)) 32 [.xmm 2, .mem (mbd 6 32 128)] 4) := by dec_rfl
theorem d388 : ∀ feat, Dec feat mc2 388 (FV7z.mk (.sse (.movups)) 32 [.xmm 3, .mem (mbd 6 48 128)] 4) := by dec_rfl
theorem d392 : ∀ feat, Dec feat mc2 392
    (FV7z.mk (.sse (.movups)) 32 [.xmm 4, .mem (mbi 6 2 18446744073709551600 128)] 5) := by dec_rfl
theorem d397 : ∀ feat, Dec feat mc2 397
    (FV7z.mk (.sse (.movups)) 32 [.xmm 5, .mem (mbi 6 2 18446744073709551584 128)] 5) := by dec_rfl
theorem d402 : ∀ feat, Dec feat mc2 402
    (FV7z.mk (.sse (.movups)) 32 [.xmm 6, .mem (mbi 6 2 18446744073709551568 128)] 5) := by dec_rfl
theorem d407 : ∀ feat, Dec feat mc2 407
    (FV7z.mk (.sse (.movups)) 32 [.xmm 7, .mem (mbi 6 2 18446744073709551552 128)] 5) := by dec_rfl
theorem d412 : ∀ feat, Dec feat mc2 412 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 0 128), .xmm 0] 3) := by dec_rfl
theorem d415 : ∀ feat, Dec feat mc2 415 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 16 128), .xmm 1] 4) := by dec_rfl
theorem d419 : ∀ feat, Dec feat mc2 419 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 32 128), .xmm 2] 4) := by dec_rfl
theorem d423 : ∀ feat, Dec feat mc2 423 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 48 128), .xmm 3] 4) := by dec_rfl
theorem d427 : ∀ feat, Dec feat mc2 427
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 4] 5) := by dec_rfl
theorem d432 : ∀ feat, Dec feat mc2 432
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551584 128), .xmm 5] 5) := by dec_rfl
theorem d437 : ∀ feat, Dec feat mc2 437
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551568 128), .xmm 6] 5) := by dec_rfl
theorem d442 : ∀ feat, Dec feat mc2 442
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551552 128), .xmm 7] 5) := by dec_rfl
theorem d447 : ∀ feat, Dec feat mc2 447 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d448 : ∀ feat, Dec feat mc2 448 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d451 : ∀ feat, Dec feat mc2 451 (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbd 6 16 128)] 4) := by dec_rfl
theorem d455 : ∀ feat, Dec feat mc2 455
    (FV7z.mk (.sse (.movups)) 32 [.xmm 2, .mem (mbi 6 2 18446744073709551600 128)] 5) := by dec_rfl
theorem d460 : ∀ feat, Dec feat mc2 460
    (FV7z.mk (.sse (.movups)) 32 [.xmm 3, .mem (mbi 6 2 18446744073709551584 128)] 5) := by dec_rfl
theorem d465 : ∀ feat, Dec feat mc2 465 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 0 128), .xmm 0] 3) := by dec_rfl
theorem d468 : ∀ feat, Dec feat mc2 468 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 16 128), .xmm 1] 4) := by dec_rfl
theorem d472 : ∀ feat, Dec feat mc2 472
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 2] 5) := by dec_rfl
theorem d477 : ∀ feat, Dec feat mc2 477
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551584 128), .xmm 3] 5) := by dec_rfl
theorem d482 : ∀ feat, Dec feat mc2 482 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d483 : ∀ feat, Dec feat mc2 483 (FV7z.mk .cmp 64 [gr 64 7, gr 64 6] 3) := by dec_rfl
theorem d486 : ∀ feat, Dec feat mc2 486 (FV7z.mk (.jcc 7) 64 [.rel 140] 6) := by dec_rfl
theorem d492 : ∀ feat, Dec feat mc2 492 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551400] 6) := by dec_rfl
theorem d498 : ∀ feat, Dec feat mc2 498 (FV7z.mk (.sse (.movups)) 32 [.xmm 4, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d501 : ∀ feat, Dec feat mc2 501
    (FV7z.mk (.sse (.movups)) 32 [.xmm 5, .mem (mbi 6 2 18446744073709551600 128)] 5) := by dec_rfl
theorem d506 : ∀ feat, Dec feat mc2 506
    (FV7z.mk (.sse (.movups)) 32 [.xmm 6, .mem (mbi 6 2 18446744073709551584 128)] 5) := by dec_rfl
theorem d511 : ∀ feat, Dec feat mc2 511
    (FV7z.mk (.sse (.movups)) 32 [.xmm 7, .mem (mbi 6 2 18446744073709551568 128)] 5) := by dec_rfl
theorem d516 : ∀ feat, Dec feat mc2 516
    (FV7z.mk (.sse (.movups)) 32 [.xmm 8, .mem (mbi 6 2 18446744073709551552 128)] 6) := by dec_rfl
theorem d522 : ∀ feat, Dec feat mc2 522 (FV7z.mk .mov 64 [gr 64 11, gr 64 7] 3) := by dec_rfl
theorem d525 : ∀ feat, Dec feat mc2 525
    (FV7z.mk .lea 64 [gr 64 1, .mem (mbi 7 2 18446744073709551600 0)] 5) := by dec_rfl
theorem d530 : ∀ feat, Dec feat mc2 530 (FV7z.mk .mov 64 [gr 64 8, gr 64 7] 3) := by dec_rfl
theorem d533 : ∀ feat, Dec feat mc2 533 (FV7z.mk .and 64 [gr 64 8, .imm 64 15] 4) := by dec_rfl
theorem d537 : ∀ feat, Dec feat mc2 537 (FV7z.mk .sub 64 [gr 64 8, .imm 64 16] 4) := by dec_rfl
theorem d541 : ∀ feat, Dec feat mc2 541 (FV7z.mk .sub 64 [gr 64 6, gr 64 8] 3) := by dec_rfl
theorem d544 : ∀ feat, Dec feat mc2 544 (FV7z.mk .sub 64 [gr 64 7, gr 64 8] 3) := by dec_rfl
theorem d547 : ∀ feat, Dec feat mc2 547 (FV7z.mk .add 64 [gr 64 2, gr 64 8] 3) := by dec_rfl
theorem d550 : ∀ feat, Dec feat mc2 550 (FV7z.mk .cmp 64 [gr 64 2, .mem (mrip 1362219 64)] 7) := by dec_rfl
theorem d557 : ∀ feat, Dec feat mc2 557 (FV7z.mk (.jcc 7) 64 [.rel 204] 6) := by dec_rfl
theorem d563 : ∀ feat, Dec feat mc2 563 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d566 : ∀ feat, Dec feat mc2 566 (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbd 6 16 128)] 4) := by dec_rfl
theorem d570 : ∀ feat, Dec feat mc2 570 (FV7z.mk (.sse (.movups)) 32 [.xmm 2, .mem (mbd 6 32 128)] 4) := by dec_rfl
theorem d574 : ∀ feat, Dec feat mc2 574 (FV7z.mk (.sse (.movups)) 32 [.xmm 3, .mem (mbd 6 48 128)] 4) := by dec_rfl
theorem d578 : ∀ feat, Dec feat mc2 578 (FV7z.mk .add 64 [gr 64 6, .imm 64 64] 4) := by dec_rfl
theorem d582 : ∀ feat, Dec feat mc2 582 (FV7z.mk .sub 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d586 : ∀ feat, Dec feat mc2 586 (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 7 0 128), .xmm 0] 3) := by dec_rfl
theorem d589 : ∀ feat, Dec feat mc2 589 (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 7 16 128), .xmm 1] 4) := by dec_rfl
theorem d593 : ∀ feat, Dec feat mc2 593 (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 7 32 128), .xmm 2] 4) := by dec_rfl
theorem d597 : ∀ feat, Dec feat mc2 597 (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 7 48 128), .xmm 3] 4) := by dec_rfl
theorem d601 : ∀ feat, Dec feat mc2 601 (FV7z.mk .add 64 [gr 64 7, .imm 64 64] 4) := by dec_rfl
theorem d605 : ∀ feat, Dec feat mc2 605 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d609 : ∀ feat, Dec feat mc2 609 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551568] 2) := by dec_rfl
theorem d611 : ∀ feat, Dec feat mc2 611 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 0 128), .xmm 5] 3) := by dec_rfl
theorem d614 : ∀ feat, Dec feat mc2 614
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 18446744073709551600 128), .xmm 6] 4) := by dec_rfl
theorem d618 : ∀ feat, Dec feat mc2 618
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 18446744073709551584 128), .xmm 7] 4) := by dec_rfl
theorem d622 : ∀ feat, Dec feat mc2 622
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 18446744073709551568 128), .xmm 8] 5) := by dec_rfl
theorem d627 : ∀ feat, Dec feat mc2 627 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 11 0 128), .xmm 4] 4) := by dec_rfl
theorem d631 : ∀ feat, Dec feat mc2 631 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d632 : ∀ feat, Dec feat mc2 632 (FV7z.mk (.sse (.movups)) 32 [.xmm 4, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d635 : ∀ feat, Dec feat mc2 635 (FV7z.mk (.sse (.movups)) 32 [.xmm 5, .mem (mbd 6 16 128)] 4) := by dec_rfl
theorem d639 : ∀ feat, Dec feat mc2 639 (FV7z.mk (.sse (.movups)) 32 [.xmm 6, .mem (mbd 6 32 128)] 4) := by dec_rfl
theorem d643 : ∀ feat, Dec feat mc2 643 (FV7z.mk (.sse (.movups)) 32 [.xmm 7, .mem (mbd 6 48 128)] 4) := by dec_rfl
theorem d647 : ∀ feat, Dec feat mc2 647
    (FV7z.mk (.sse (.movups)) 32 [.xmm 8, .mem (mbi 6 2 18446744073709551600 128)] 6) := by dec_rfl
theorem d653 : ∀ feat, Dec feat mc2 653
    (FV7z.mk .lea 64 [gr 64 11, .mem (mbi 7 2 18446744073709551600 0)] 5) := by dec_rfl
theorem d658 : ∀ feat, Dec feat mc2 658
    (FV7z.mk .lea 64 [gr 64 1, .mem (mbi 6 2 18446744073709551600 0)] 5) := by dec_rfl
theorem d663 : ∀ feat, Dec feat mc2 663 (FV7z.mk .mov 64 [gr 64 9, gr 64 11] 3) := by dec_rfl
theorem d666 : ∀ feat, Dec feat mc2 666 (FV7z.mk .mov 64 [gr 64 8, gr 64 11] 3) := by dec_rfl
theorem d669 : ∀ feat, Dec feat mc2 669 (FV7z.mk .and 64 [gr 64 8, .imm 64 15] 4) := by dec_rfl
theorem d673 : ∀ feat, Dec feat mc2 673 (FV7z.mk .sub 64 [gr 64 1, gr 64 8] 3) := by dec_rfl
theorem d676 : ∀ feat, Dec feat mc2 676 (FV7z.mk .sub 64 [gr 64 9, gr 64 8] 3) := by dec_rfl
theorem d679 : ∀ feat, Dec feat mc2 679 (FV7z.mk .sub 64 [gr 64 2, gr 64 8] 3) := by dec_rfl
theorem d682 : ∀ feat, Dec feat mc2 682 (FV7z.mk .cmp 64 [gr 64 2, .mem (mrip 1362087 64)] 7) := by dec_rfl
theorem d689 : ∀ feat, Dec feat mc2 689 (FV7z.mk (.jcc 7) 64 [.rel 175] 6) := by dec_rfl
theorem d695 : ∀ feat, Dec feat mc2 695 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 1 0 128)] 3) := by dec_rfl
theorem d698 : ∀ feat, Dec feat mc2 698
    (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbd 1 18446744073709551600 128)] 4) := by dec_rfl
theorem d702 : ∀ feat, Dec feat mc2 702
    (FV7z.mk (.sse (.movups)) 32 [.xmm 2, .mem (mbd 1 18446744073709551584 128)] 4) := by dec_rfl
theorem d706 : ∀ feat, Dec feat mc2 706
    (FV7z.mk (.sse (.movups)) 32 [.xmm 3, .mem (mbd 1 18446744073709551568 128)] 4) := by dec_rfl
theorem d710 : ∀ feat, Dec feat mc2 710 (FV7z.mk .sub 64 [gr 64 1, .imm 64 64] 4) := by dec_rfl
theorem d714 : ∀ feat, Dec feat mc2 714 (FV7z.mk .sub 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d718 : ∀ feat, Dec feat mc2 718 (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 9 0 128), .xmm 0] 4) := by dec_rfl
theorem d722 : ∀ feat, Dec feat mc2 722
    (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 9 18446744073709551600 128), .xmm 1] 5) := by dec_rfl
theorem d727 : ∀ feat, Dec feat mc2 727
    (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 9 18446744073709551584 128), .xmm 2] 5) := by dec_rfl
theorem d732 : ∀ feat, Dec feat mc2 732
    (FV7z.mk (.sse (.movaps)) 32 [.mem (mbd 9 18446744073709551568 128), .xmm 3] 5) := by dec_rfl
theorem d737 : ∀ feat, Dec feat mc2 737 (FV7z.mk .sub 64 [gr 64 9, .imm 64 64] 4) := by dec_rfl
theorem d741 : ∀ feat, Dec feat mc2 741 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d745 : ∀ feat, Dec feat mc2 745 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551564] 2) := by dec_rfl
theorem d747 : ∀ feat, Dec feat mc2 747 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 0 128), .xmm 4] 3) := by dec_rfl
theorem d750 : ∀ feat, Dec feat mc2 750 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 16 128), .xmm 5] 4) := by dec_rfl
theorem d754 : ∀ feat, Dec feat mc2 754 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 32 128), .xmm 6] 4) := by dec_rfl
theorem d758 : ∀ feat, Dec feat mc2 758 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 48 128), .xmm 7] 4) := by dec_rfl
theorem d762 : ∀ feat, Dec feat mc2 762 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 11 0 128), .xmm 8] 4) := by dec_rfl
theorem d766 : ∀ feat, Dec feat mc2 766 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d767 : ∀ feat, Dec feat mc2 767 (FV7z.mk .lea 64 [gr 64 10, .mem (mbi 7 2 0 0)] 4) := by dec_rfl
theorem d771 : ∀ feat, Dec feat mc2 771 (FV7z.mk .cmp 64 [gr 64 6, gr 64 10] 3) := by dec_rfl
theorem d774 : ∀ feat, Dec feat mc2 774 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551399] 6) := by dec_rfl
theorem d780 : ∀ feat, Dec feat mc2 780 (FV7z.mk (.prefetch 1) 32 [.mem (mbd 6 128 0)] 7) := by dec_rfl
theorem d787 : ∀ feat, Dec feat mc2 787 (FV7z.mk (.prefetch 1) 32 [.mem (mbd 6 192 0)] 7) := by dec_rfl
theorem d794 : ∀ feat, Dec feat mc2 794 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 6 0 128)] 3) := by dec_rfl
theorem d797 : ∀ feat, Dec feat mc2 797 (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbd 6 16 128)] 4) := by dec_rfl
theorem d801 : ∀ feat, Dec feat mc2 801 (FV7z.mk (.sse (.movups)) 32 [.xmm 2, .mem (mbd 6 32 128)] 4) := by dec_rfl
theorem d805 : ∀ feat, Dec feat mc2 805 (FV7z.mk (.sse (.movups)) 32 [.xmm 3, .mem (mbd 6 48 128)] 4) := by dec_rfl
theorem d809 : ∀ feat, Dec feat mc2 809 (FV7z.mk .add 64 [gr 64 6, .imm 64 64] 4) := by dec_rfl
theorem d813 : ∀ feat, Dec feat mc2 813 (FV7z.mk .sub 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d817 : ∀ feat, Dec feat mc2 817 (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 7 0 128), .xmm 0] 4) := by dec_rfl
theorem d821 : ∀ feat, Dec feat mc2 821 (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 7 16 128), .xmm 1] 5) := by dec_rfl
theorem d826 : ∀ feat, Dec feat mc2 826 (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 7 32 128), .xmm 2] 5) := by dec_rfl
theorem d831 : ∀ feat, Dec feat mc2 831 (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 7 48 128), .xmm 3] 5) := by dec_rfl
theorem d836 : ∀ feat, Dec feat mc2 836 (FV7z.mk .add 64 [gr 64 7, .imm 64 64] 4) := by dec_rfl
theorem d840 : ∀ feat, Dec feat mc2 840 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d844 : ∀ feat, Dec feat mc2 844 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551550] 2) := by dec_rfl
theorem d846 : ∀ feat, Dec feat mc2 846 (FV7z.mk .sfence 32 [] 3) := by dec_rfl
theorem d849 : ∀ feat, Dec feat mc2 849 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 0 128), .xmm 5] 3) := by dec_rfl
theorem d852 : ∀ feat, Dec feat mc2 852
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 18446744073709551600 128), .xmm 6] 4) := by dec_rfl
theorem d856 : ∀ feat, Dec feat mc2 856
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 18446744073709551584 128), .xmm 7] 4) := by dec_rfl
theorem d860 : ∀ feat, Dec feat mc2 860
    (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 1 18446744073709551568 128), .xmm 8] 5) := by dec_rfl
theorem d865 : ∀ feat, Dec feat mc2 865 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 11 0 128), .xmm 4] 4) := by dec_rfl
theorem d869 : ∀ feat, Dec feat mc2 869 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d870 : ∀ feat, Dec feat mc2 870 (FV7z.mk .lea 64 [gr 64 10, .mem (mbi 1 2 0 0)] 4) := by dec_rfl
theorem d874 : ∀ feat, Dec feat mc2 874 (FV7z.mk .cmp 64 [gr 64 9, gr 64 10] 3) := by dec_rfl
theorem d877 : ∀ feat, Dec feat mc2 877 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551428] 6) := by dec_rfl
theorem d883 : ∀ feat, Dec feat mc2 883 (FV7z.mk (.prefetch 1) 32 [.mem (mbd 1 18446744073709551488 0)] 4) := by dec_rfl
theorem d887 : ∀ feat, Dec feat mc2 887 (FV7z.mk (.prefetch 1) 32 [.mem (mbd 1 18446744073709551424 0)] 7) := by dec_rfl
theorem d894 : ∀ feat, Dec feat mc2 894 (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 1 0 128)] 3) := by dec_rfl
theorem d897 : ∀ feat, Dec feat mc2 897
    (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbd 1 18446744073709551600 128)] 4) := by dec_rfl
theorem d901 : ∀ feat, Dec feat mc2 901
    (FV7z.mk (.sse (.movups)) 32 [.xmm 2, .mem (mbd 1 18446744073709551584 128)] 4) := by dec_rfl
theorem d905 : ∀ feat, Dec feat mc2 905
    (FV7z.mk (.sse (.movups)) 32 [.xmm 3, .mem (mbd 1 18446744073709551568 128)] 4) := by dec_rfl
theorem d909 : ∀ feat, Dec feat mc2 909 (FV7z.mk .sub 64 [gr 64 1, .imm 64 64] 4) := by dec_rfl
theorem d913 : ∀ feat, Dec feat mc2 913 (FV7z.mk .sub 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d917 : ∀ feat, Dec feat mc2 917 (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 9 0 128), .xmm 0] 5) := by dec_rfl
theorem d922 : ∀ feat, Dec feat mc2 922
    (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 9 18446744073709551600 128), .xmm 1] 6) := by dec_rfl
theorem d928 : ∀ feat, Dec feat mc2 928
    (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 9 18446744073709551584 128), .xmm 2] 6) := by dec_rfl
theorem d934 : ∀ feat, Dec feat mc2 934
    (FV7z.mk (.sse (.movntdq)) 16 [.mem (mbd 9 18446744073709551568 128), .xmm 3] 6) := by dec_rfl
theorem d940 : ∀ feat, Dec feat mc2 940 (FV7z.mk .sub 64 [gr 64 9, .imm 64 64] 4) := by dec_rfl
theorem d944 : ∀ feat, Dec feat mc2 944 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d948 : ∀ feat, Dec feat mc2 948 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551549] 2) := by dec_rfl
theorem d950 : ∀ feat, Dec feat mc2 950 (FV7z.mk .sfence 32 [] 3) := by dec_rfl
theorem d953 : ∀ feat, Dec feat mc2 953 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 0 128), .xmm 4] 3) := by dec_rfl
theorem d956 : ∀ feat, Dec feat mc2 956 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 16 128), .xmm 5] 4) := by dec_rfl
theorem d960 : ∀ feat, Dec feat mc2 960 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 32 128), .xmm 6] 4) := by dec_rfl
theorem d964 : ∀ feat, Dec feat mc2 964 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 48 128), .xmm 7] 4) := by dec_rfl
theorem d968 : ∀ feat, Dec feat mc2 968 (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 11 0 128), .xmm 8] 4) := by dec_rfl
theorem d972 : ∀ feat, Dec feat mc2 972 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d976 : ∀ feat, Dec feat mc2 976 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d980 : ∀ feat, Dec feat mc2 980 (FV7z.mk .mov 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d983 : ∀ feat, Dec feat mc2 983 (FV7z.mk .add 64 [gr 64 0, gr 64 2] 3) := by dec_rfl
theorem d986 : ∀ feat, Dec feat mc2 986 (FV7z.mk .jmp 64 [.rel 11] 2) := by dec_rfl

end FV7z.Memcpy
