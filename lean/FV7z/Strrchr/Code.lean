import FV7z.Lemmas.Sse2b
import FV7z.Lemmas.BlkOps3
import FV7z.Lemmas.BlkOps2
/-!
# The code of `__strrchr_sse2` (PLAN.md G2, the PLT contracts of `launch_to_main`)

glibc 2.31's `__strrchr_sse2` (`sysdeps/x86_64/multiarch/strrchr-sse2.S`, `strrchr.S`) at `0x654200` in `7zzs`, the
variant of `strrchr` that the IFUNC resolver picks on a processor without AVX2: its bytes (`sr2`), what each
instruction decodes to on every processor (`d<offset>`, by evaluation), and its straight-line stretches as `BlkV`s
(`b<start>`), in pieces of at most 6 instructions. Generated from the decoder's output (`decshow`) by
`tools/strrchr_gen.py`.
-/
namespace FV7z.Strrchr
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The bytes of `__strrchr_sse2`. -/
def sr2 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x66, 0x0f, 0x6e, 0xce, 0x48, 0x89, 0xf8, 0x25, 0xff, 0x0f, 0x00, 0x00,
  0x66, 0x0f, 0x60, 0xc9, 0x48, 0x3d, 0xc0, 0x0f, 0x00, 0x00, 0x66, 0x0f, 0x61, 0xc9, 0x66, 0x0f,
  0x70, 0xc9, 0x00, 0x0f, 0x87, 0x07, 0x02, 0x00, 0x00, 0xf3, 0x0f, 0x6f, 0x07, 0x66, 0x0f, 0xef,
  0xd2, 0x66, 0x0f, 0x6f, 0xd8, 0x66, 0x0f, 0x74, 0xc1, 0x66, 0x0f, 0x74, 0xda, 0x66, 0x0f, 0xd7,
  0xc8, 0x66, 0x0f, 0xd7, 0xd3, 0x48, 0x85, 0xd2, 0x74, 0x26, 0x48, 0x8d, 0x42, 0xff, 0x48, 0x31,
  0xd0, 0x48, 0x21, 0xc8, 0x0f, 0x84, 0xc6, 0x01, 0x00, 0x00, 0x48, 0x0f, 0xbd, 0xc0, 0x48, 0x01,
  0xf8, 0xc3, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x00,
  0xf3, 0x0f, 0x6f, 0x67, 0x10, 0x66, 0x0f, 0x6f, 0xec, 0xf3, 0x0f, 0x6f, 0x5f, 0x20, 0x66, 0x0f,
  0x74, 0xe1, 0x66, 0x0f, 0x74, 0xea, 0xf3, 0x0f, 0x6f, 0x47, 0x30, 0x66, 0x0f, 0xd7, 0xd5, 0x66,
  0x0f, 0x6f, 0xeb, 0x66, 0x0f, 0x74, 0xd9, 0x66, 0x0f, 0x74, 0xea, 0x66, 0x0f, 0x74, 0xd0, 0x48,
  0xc1, 0xe2, 0x10, 0x66, 0x44, 0x0f, 0xd7, 0xc3, 0x66, 0x0f, 0xd7, 0xc5, 0x66, 0x0f, 0xd7, 0xf2,
  0x49, 0xc1, 0xe0, 0x20, 0x48, 0xc1, 0xe0, 0x20, 0x66, 0x0f, 0x74, 0xc1, 0x48, 0x09, 0xd0, 0x48,
  0x89, 0xf2, 0x66, 0x0f, 0xd7, 0xf4, 0x48, 0xc1, 0xe2, 0x30, 0x48, 0xc1, 0xe6, 0x10, 0x4c, 0x09,
  0xc6, 0x48, 0x09, 0xce, 0x66, 0x0f, 0xd7, 0xc8, 0x48, 0xc1, 0xe1, 0x30, 0x48, 0x09, 0xce, 0x48,
  0x09, 0xd0, 0x74, 0x1c, 0x48, 0x8d, 0x48, 0xff, 0x48, 0x31, 0xc1, 0x48, 0x21, 0xce, 0x0f, 0x84,
  0x2c, 0x01, 0x00, 0x00, 0x48, 0x0f, 0xbd, 0xf6, 0x48, 0x8d, 0x04, 0x37, 0xc3, 0x0f, 0x1f, 0x00,
  0x48, 0x85, 0xf6, 0x48, 0x89, 0xf9, 0x0f, 0x84, 0x04, 0x01, 0x00, 0x00, 0x48, 0x83, 0xc7, 0x40,
  0x66, 0x0f, 0xef, 0xff, 0x48, 0x83, 0xe7, 0xc0, 0xeb, 0x15, 0x66, 0x0f, 0x1f, 0x44, 0x00, 0x00,
  0x48, 0x85, 0xd2, 0x48, 0x0f, 0x45, 0xf2, 0x48, 0x0f, 0x45, 0xcf, 0x48, 0x83, 0xc7, 0x40, 0x66,
  0x0f, 0x6f, 0x5f, 0x20, 0x66, 0x0f, 0xef, 0xf6, 0x66, 0x0f, 0x6f, 0x57, 0x30, 0x66, 0x0f, 0x6f,
  0xc3, 0x66, 0x0f, 0x6f, 0x67, 0x10, 0x66, 0x0f, 0xda, 0xc2, 0x66, 0x0f, 0x6f, 0x2f, 0x66, 0x0f,
  0xda, 0xc4, 0x66, 0x0f, 0xda, 0xc5, 0x66, 0x0f, 0x74, 0xc7, 0x66, 0x0f, 0xd7, 0xc0, 0x66, 0x0f,
  0x6f, 0xc5, 0x66, 0x0f, 0x74, 0xc1, 0x66, 0x44, 0x0f, 0xd7, 0xc8, 0x66, 0x0f, 0x6f, 0xc4, 0x66,
  0x0f, 0x74, 0xc1, 0x66, 0x0f, 0xd7, 0xd0, 0x66, 0x0f, 0x6f, 0xc3, 0x66, 0x0f, 0x74, 0xc1, 0x48,
  0xc1, 0xe2, 0x10, 0x66, 0x44, 0x0f, 0xd7, 0xd0, 0x66, 0x0f, 0x6f, 0xc2, 0x66, 0x0f, 0x74, 0xc1,
  0x49, 0xc1, 0xe2, 0x20, 0x4c, 0x09, 0xd2, 0x66, 0x44, 0x0f, 0xd7, 0xc0, 0x4c, 0x09, 0xca, 0x49,
  0xc1, 0xe0, 0x30, 0x4c, 0x09, 0xc2, 0x85, 0xc0, 0x0f, 0x84, 0x72, 0xff, 0xff, 0xff, 0x66, 0x0f,
  0x74, 0xe6, 0x66, 0x0f, 0x74, 0xde, 0x66, 0x0f, 0x74, 0xee, 0x66, 0x0f, 0xd7, 0xc4, 0x66, 0x44,
  0x0f, 0xd7, 0xd3, 0x66, 0x0f, 0x74, 0xd6, 0x66, 0x44, 0x0f, 0xd7, 0xcd, 0x49, 0xc1, 0xe2, 0x20,
  0x48, 0xc1, 0xe0, 0x10, 0x66, 0x44, 0x0f, 0xd7, 0xc2, 0x4c, 0x09, 0xd0, 0x4c, 0x09, 0xc8, 0x49,
  0xc1, 0xe0, 0x30, 0x4c, 0x09, 0xc0, 0x4c, 0x8d, 0x40, 0xff, 0x49, 0x31, 0xc0, 0x4c, 0x21, 0xc2,
  0x48, 0x0f, 0x45, 0xcf, 0x48, 0x0f, 0x45, 0xf2, 0x48, 0x0f, 0xbd, 0xf6, 0x48, 0x8d, 0x04, 0x31,
  0xc3, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x1f, 0x40, 0x00,
  0xbe, 0x01, 0x00, 0x00, 0x00, 0x31, 0xc9, 0xe9, 0xf0, 0xfe, 0xff, 0xff, 0x0f, 0x1f, 0x40, 0x00,
  0x31, 0xc0, 0xc3, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x66, 0x90,
  0x48, 0x89, 0xf8, 0x66, 0x0f, 0xef, 0xc0, 0x48, 0x83, 0xe0, 0xc0, 0xf3, 0x0f, 0x6f, 0x28, 0x66,
  0x0f, 0x6f, 0xf5, 0xf3, 0x0f, 0x6f, 0x60, 0x10, 0x66, 0x0f, 0x74, 0xe9, 0x66, 0x0f, 0x74, 0xf0,
  0xf3, 0x0f, 0x6f, 0x58, 0x20, 0x66, 0x0f, 0xd7, 0xf6, 0x66, 0x0f, 0x6f, 0xf4, 0xf3, 0x0f, 0x6f,
  0x50, 0x30, 0x66, 0x0f, 0x74, 0xe1, 0x66, 0x0f, 0x74, 0xf0, 0x66, 0x0f, 0xd7, 0xd6, 0x66, 0x0f,
  0x6f, 0xf3, 0x66, 0x0f, 0x74, 0xd9, 0x66, 0x0f, 0x74, 0xf0, 0x66, 0x0f, 0x74, 0xc2, 0x48, 0xc1,
  0xe2, 0x10, 0x66, 0x44, 0x0f, 0xd7, 0xcb, 0x66, 0x44, 0x0f, 0xd7, 0xc6, 0x66, 0x0f, 0xd7, 0xc8,
  0x49, 0xc1, 0xe1, 0x20, 0x49, 0xc1, 0xe0, 0x20, 0x66, 0x0f, 0x74, 0xd1, 0x4c, 0x09, 0xc2, 0x48,
  0xc1, 0xe1, 0x30, 0x66, 0x44, 0x0f, 0xd7, 0xc5, 0x48, 0x09, 0xf2, 0x66, 0x0f, 0xd7, 0xf4, 0x48,
  0x09, 0xca, 0x66, 0x0f, 0xd7, 0xca, 0x48, 0xc1, 0xe6, 0x10, 0x48, 0xc1, 0xe1, 0x30, 0x4c, 0x09,
  0xce, 0x4c, 0x09, 0xc6, 0x48, 0x09, 0xce, 0x89, 0xf9, 0x29, 0xc1, 0x48, 0xd3, 0xea, 0x48, 0xd3,
  0xee, 0x48, 0x85, 0xd2, 0x0f, 0x84, 0x26, 0xfe, 0xff, 0xff, 0x48, 0x8d, 0x42, 0xff, 0x48, 0x31,
  0xd0, 0x48, 0x21, 0xc6, 0x0f, 0x84, 0x36, 0xff, 0xff, 0xff, 0x48, 0x0f, 0xbd, 0xc6, 0x48, 0x01,
  0xf8, 0xc3]

theorem sr2_length : sr2.length = 754 := rfl

theorem d0 : ∀ feat, Dec feat sr2 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d4 : ∀ feat, Dec feat sr2 4 (FV7z.mk (.sse .movd) 16 [.xmm 1, gr 32 6] 4) := by dec_rfl
theorem d8 : ∀ feat, Dec feat sr2 8 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d11 : ∀ feat, Dec feat sr2 11 (FV7z.mk .and 32 [gr 32 0, Src.opd 32 (.i 4095)] 5) := by dec_rfl
theorem d16 : ∀ feat, Dec feat sr2 16 (FV7z.mk (.sse .punpcklbw) 16 [.xmm 1, .xmm 1] 4) := by dec_rfl
theorem d20 : ∀ feat, Dec feat sr2 20 (FV7z.mk .cmp 64 [gr 64 0, Src.opd 64 (.i 4032)] 6) := by dec_rfl
theorem d26 : ∀ feat, Dec feat sr2 26 (FV7z.mk (.sse .punpcklwd) 16 [.xmm 1, .xmm 1] 4) := by dec_rfl
theorem d30 : ∀ feat, Dec feat sr2 30 (FV7z.mk (.sse .pshufd) 16 [.xmm 1, .xmm 1, .imm 8 0] 5) := by dec_rfl
theorem d35 : ∀ feat, Dec feat sr2 35 (FV7z.mk (.jcc 7) 64 [.rel 519] 6) := by dec_rfl
theorem d41 : ∀ feat, Dec feat sr2 41 (FV7z.mk (.sse .movdqu) 32 [.xmm 0, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d45 : ∀ feat, Dec feat sr2 45 (FV7z.mk (.sse .pxor) 16 [.xmm 2, .xmm 2] 4) := by dec_rfl
theorem d49 : ∀ feat, Dec feat sr2 49 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .xmm 0] 4) := by dec_rfl
theorem d53 : ∀ feat, Dec feat sr2 53 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d57 : ∀ feat, Dec feat sr2 57 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 3, .xmm 2] 4) := by dec_rfl
theorem d61 : ∀ feat, Dec feat sr2 61 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 1, .xmm 0] 4) := by dec_rfl
theorem d65 : ∀ feat, Dec feat sr2 65 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 3] 4) := by dec_rfl
theorem d69 : ∀ feat, Dec feat sr2 69 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d72 : ∀ feat, Dec feat sr2 72 (FV7z.mk (.jcc 4) 64 [.rel 38] 2) := by dec_rfl
theorem d74 : ∀ feat, Dec feat sr2 74
    (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem d78 : ∀ feat, Dec feat sr2 78 (FV7z.mk .xor 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d81 : ∀ feat, Dec feat sr2 81 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d84 : ∀ feat, Dec feat sr2 84 (FV7z.mk (.jcc 4) 64 [.rel 454] 6) := by dec_rfl
theorem d90 : ∀ feat, Dec feat sr2 90 (FV7z.mk (.bit (BitMn.bsr)) 64 [gr 64 0, gr 64 0] 4) := by dec_rfl
theorem d94 : ∀ feat, Dec feat sr2 94 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d97 : ∀ feat, Dec feat sr2 97 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d112 : ∀ feat, Dec feat sr2 112 (FV7z.mk (.sse .movdqu) 32 [.xmm 4, .mem (mbd 7 16 128)] 5) := by dec_rfl
theorem d117 : ∀ feat, Dec feat sr2 117 (FV7z.mk (.sse .movdqa) 16 [.xmm 5, .xmm 4] 4) := by dec_rfl
theorem d121 : ∀ feat, Dec feat sr2 121 (FV7z.mk (.sse .movdqu) 32 [.xmm 3, .mem (mbd 7 32 128)] 5) := by dec_rfl
theorem d126 : ∀ feat, Dec feat sr2 126 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 4, .xmm 1] 4) := by dec_rfl
theorem d130 : ∀ feat, Dec feat sr2 130 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 5, .xmm 2] 4) := by dec_rfl
theorem d134 : ∀ feat, Dec feat sr2 134 (FV7z.mk (.sse .movdqu) 32 [.xmm 0, .mem (mbd 7 48 128)] 5) := by dec_rfl
theorem d139 : ∀ feat, Dec feat sr2 139 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 5] 4) := by dec_rfl
theorem d143 : ∀ feat, Dec feat sr2 143 (FV7z.mk (.sse .movdqa) 16 [.xmm 5, .xmm 3] 4) := by dec_rfl
theorem d147 : ∀ feat, Dec feat sr2 147 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 3, .xmm 1] 4) := by dec_rfl
theorem d151 : ∀ feat, Dec feat sr2 151 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 5, .xmm 2] 4) := by dec_rfl
theorem d155 : ∀ feat, Dec feat sr2 155 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 0] 4) := by dec_rfl
theorem d159 : ∀ feat, Dec feat sr2 159 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d163 : ∀ feat, Dec feat sr2 163 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 3] 5) := by dec_rfl
theorem d168 : ∀ feat, Dec feat sr2 168 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 0, .xmm 5] 4) := by dec_rfl
theorem d172 : ∀ feat, Dec feat sr2 172 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 6, .xmm 2] 4) := by dec_rfl
theorem d176 : ∀ feat, Dec feat sr2 176 (FV7z.mk .shl 64 [gr 64 8, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d180 : ∀ feat, Dec feat sr2 180 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d184 : ∀ feat, Dec feat sr2 184 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d188 : ∀ feat, Dec feat sr2 188 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d191 : ∀ feat, Dec feat sr2 191 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem d194 : ∀ feat, Dec feat sr2 194 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 6, .xmm 4] 4) := by dec_rfl
theorem d198 : ∀ feat, Dec feat sr2 198 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 48)] 4) := by dec_rfl
theorem d202 : ∀ feat, Dec feat sr2 202 (FV7z.mk .shl 64 [gr 64 6, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d206 : ∀ feat, Dec feat sr2 206 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d209 : ∀ feat, Dec feat sr2 209 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d212 : ∀ feat, Dec feat sr2 212 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 1, .xmm 0] 4) := by dec_rfl
theorem d216 : ∀ feat, Dec feat sr2 216 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 48)] 4) := by dec_rfl
theorem d220 : ∀ feat, Dec feat sr2 220 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d223 : ∀ feat, Dec feat sr2 223 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d226 : ∀ feat, Dec feat sr2 226 (FV7z.mk (.jcc 4) 64 [.rel 28] 2) := by dec_rfl
theorem d228 : ∀ feat, Dec feat sr2 228
    (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem d232 : ∀ feat, Dec feat sr2 232 (FV7z.mk .xor 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem d235 : ∀ feat, Dec feat sr2 235 (FV7z.mk .and 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d238 : ∀ feat, Dec feat sr2 238 (FV7z.mk (.jcc 4) 64 [.rel 300] 6) := by dec_rfl
theorem d244 : ∀ feat, Dec feat sr2 244 (FV7z.mk (.bit (BitMn.bsr)) 64 [gr 64 6, gr 64 6] 4) := by dec_rfl
theorem d248 : ∀ feat, Dec feat sr2 248 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 7) (some 6) 1 0 0)] 4) := by dec_rfl
theorem d252 : ∀ feat, Dec feat sr2 252 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d256 : ∀ feat, Dec feat sr2 256 (FV7z.mk .test 64 [gr 64 6, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem d259 : ∀ feat, Dec feat sr2 259 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d262 : ∀ feat, Dec feat sr2 262 (FV7z.mk (.jcc 4) 64 [.rel 260] 6) := by dec_rfl
theorem d268 : ∀ feat, Dec feat sr2 268 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 64)] 4) := by dec_rfl
theorem d272 : ∀ feat, Dec feat sr2 272 (FV7z.mk (.sse .pxor) 16 [.xmm 7, .xmm 7] 4) := by dec_rfl
theorem d276 : ∀ feat, Dec feat sr2 276
    (FV7z.mk .and 64 [gr 64 7, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem d280 : ∀ feat, Dec feat sr2 280 (FV7z.mk .jmp 64 [.rel 21] 2) := by dec_rfl
theorem d288 : ∀ feat, Dec feat sr2 288 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d291 : ∀ feat, Dec feat sr2 291 (FV7z.mk (.cmovcc 5) 64 [gr 64 6, gr 64 2] 4) := by dec_rfl
theorem d295 : ∀ feat, Dec feat sr2 295 (FV7z.mk (.cmovcc 5) 64 [gr 64 1, gr 64 7] 4) := by dec_rfl
theorem d299 : ∀ feat, Dec feat sr2 299 (FV7z.mk .add 64 [gr 64 7, Src.opd 64 (.i 64)] 4) := by dec_rfl
theorem d303 : ∀ feat, Dec feat sr2 303 (FV7z.mk (.sse .movdqa) 16 [.xmm 3, .mem (mbd 7 32 128)] 5) := by dec_rfl
theorem d308 : ∀ feat, Dec feat sr2 308 (FV7z.mk (.sse .pxor) 16 [.xmm 6, .xmm 6] 4) := by dec_rfl
theorem d312 : ∀ feat, Dec feat sr2 312 (FV7z.mk (.sse .movdqa) 16 [.xmm 2, .mem (mbd 7 48 128)] 5) := by dec_rfl
theorem d317 : ∀ feat, Dec feat sr2 317 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d321 : ∀ feat, Dec feat sr2 321 (FV7z.mk (.sse .movdqa) 16 [.xmm 4, .mem (mbd 7 16 128)] 5) := by dec_rfl
theorem d326 : ∀ feat, Dec feat sr2 326 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .xmm 2] 4) := by dec_rfl
theorem d330 : ∀ feat, Dec feat sr2 330 (FV7z.mk (.sse .movdqa) 16 [.xmm 5, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d334 : ∀ feat, Dec feat sr2 334 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .xmm 4] 4) := by dec_rfl
theorem d338 : ∀ feat, Dec feat sr2 338 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .xmm 5] 4) := by dec_rfl
theorem d342 : ∀ feat, Dec feat sr2 342 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 7] 4) := by dec_rfl
theorem d346 : ∀ feat, Dec feat sr2 346 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 0, .xmm 0] 4) := by dec_rfl
theorem d350 : ∀ feat, Dec feat sr2 350 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .xmm 5] 4) := by dec_rfl
theorem d354 : ∀ feat, Dec feat sr2 354 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d358 : ∀ feat, Dec feat sr2 358 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 0] 5) := by dec_rfl
theorem d363 : ∀ feat, Dec feat sr2 363 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .xmm 4] 4) := by dec_rfl
theorem d367 : ∀ feat, Dec feat sr2 367 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d371 : ∀ feat, Dec feat sr2 371 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d375 : ∀ feat, Dec feat sr2 375 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d379 : ∀ feat, Dec feat sr2 379 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d383 : ∀ feat, Dec feat sr2 383 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d387 : ∀ feat, Dec feat sr2 387 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 10, .xmm 0] 5) := by dec_rfl
theorem d392 : ∀ feat, Dec feat sr2 392 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .xmm 2] 4) := by dec_rfl
theorem d396 : ∀ feat, Dec feat sr2 396 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 1] 4) := by dec_rfl
theorem d400 : ∀ feat, Dec feat sr2 400 (FV7z.mk .shl 64 [gr 64 10, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d404 : ∀ feat, Dec feat sr2 404 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem d407 : ∀ feat, Dec feat sr2 407 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 0] 5) := by dec_rfl
theorem d412 : ∀ feat, Dec feat sr2 412 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d415 : ∀ feat, Dec feat sr2 415 (FV7z.mk .shl 64 [gr 64 8, Src.opd 8 (.i 48)] 4) := by dec_rfl
theorem d419 : ∀ feat, Dec feat sr2 419 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d422 : ∀ feat, Dec feat sr2 422 (FV7z.mk .test 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem d424 : ∀ feat, Dec feat sr2 424 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551474] 6) := by dec_rfl
theorem d430 : ∀ feat, Dec feat sr2 430 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 4, .xmm 6] 4) := by dec_rfl
theorem d434 : ∀ feat, Dec feat sr2 434 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 3, .xmm 6] 4) := by dec_rfl
theorem d438 : ∀ feat, Dec feat sr2 438 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 5, .xmm 6] 4) := by dec_rfl
theorem d442 : ∀ feat, Dec feat sr2 442 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 0, .xmm 4] 4) := by dec_rfl
theorem d446 : ∀ feat, Dec feat sr2 446 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 10, .xmm 3] 5) := by dec_rfl
theorem d451 : ∀ feat, Dec feat sr2 451 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 6] 4) := by dec_rfl
theorem d455 : ∀ feat, Dec feat sr2 455 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 5] 5) := by dec_rfl
theorem d460 : ∀ feat, Dec feat sr2 460 (FV7z.mk .shl 64 [gr 64 10, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d464 : ∀ feat, Dec feat sr2 464 (FV7z.mk .shl 64 [gr 64 0, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d468 : ∀ feat, Dec feat sr2 468 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 2] 5) := by dec_rfl
theorem d473 : ∀ feat, Dec feat sr2 473 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.r 10)] 3) := by dec_rfl
theorem d476 : ∀ feat, Dec feat sr2 476 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d479 : ∀ feat, Dec feat sr2 479 (FV7z.mk .shl 64 [gr 64 8, Src.opd 8 (.i 48)] 4) := by dec_rfl
theorem d483 : ∀ feat, Dec feat sr2 483 (FV7z.mk .or 64 [gr 64 0, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d486 : ∀ feat, Dec feat sr2 486
    (FV7z.mk .lea 64 [gr 64 8, .mem (mg (some 0) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem d490 : ∀ feat, Dec feat sr2 490 (FV7z.mk .xor 64 [gr 64 8, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem d493 : ∀ feat, Dec feat sr2 493 (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d496 : ∀ feat, Dec feat sr2 496 (FV7z.mk (.cmovcc 5) 64 [gr 64 1, gr 64 7] 4) := by dec_rfl
theorem d500 : ∀ feat, Dec feat sr2 500 (FV7z.mk (.cmovcc 5) 64 [gr 64 6, gr 64 2] 4) := by dec_rfl
theorem d504 : ∀ feat, Dec feat sr2 504 (FV7z.mk (.bit (BitMn.bsr)) 64 [gr 64 6, gr 64 6] 4) := by dec_rfl
theorem d508 : ∀ feat, Dec feat sr2 508 (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 1) (some 6) 1 0 0)] 4) := by dec_rfl
theorem d512 : ∀ feat, Dec feat sr2 512 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d528 : ∀ feat, Dec feat sr2 528 (FV7z.mk .mov 32 [gr 32 6, Src.opd 32 (.i 1)] 5) := by dec_rfl
theorem d533 : ∀ feat, Dec feat sr2 533 (FV7z.mk .xor 32 [gr 32 1, Src.opd 32 (.r 1)] 2) := by dec_rfl
theorem d535 : ∀ feat, Dec feat sr2 535 (FV7z.mk .jmp 64 [.rel 18446744073709551344] 5) := by dec_rfl
theorem d544 : ∀ feat, Dec feat sr2 544 (FV7z.mk .xor 32 [gr 32 0, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem d546 : ∀ feat, Dec feat sr2 546 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d560 : ∀ feat, Dec feat sr2 560 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d563 : ∀ feat, Dec feat sr2 563 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d567 : ∀ feat, Dec feat sr2 567
    (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem d571 : ∀ feat, Dec feat sr2 571 (FV7z.mk (.sse .movdqu) 32 [.xmm 5, .mem (mbd 0 0 128)] 4) := by dec_rfl
theorem d575 : ∀ feat, Dec feat sr2 575 (FV7z.mk (.sse .movdqa) 16 [.xmm 6, .xmm 5] 4) := by dec_rfl
theorem d579 : ∀ feat, Dec feat sr2 579 (FV7z.mk (.sse .movdqu) 32 [.xmm 4, .mem (mbd 0 16 128)] 5) := by dec_rfl
theorem d584 : ∀ feat, Dec feat sr2 584 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 5, .xmm 1] 4) := by dec_rfl
theorem d588 : ∀ feat, Dec feat sr2 588 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 6, .xmm 0] 4) := by dec_rfl
theorem d592 : ∀ feat, Dec feat sr2 592 (FV7z.mk (.sse .movdqu) 32 [.xmm 3, .mem (mbd 0 32 128)] 5) := by dec_rfl
theorem d597 : ∀ feat, Dec feat sr2 597 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 6, .xmm 6] 4) := by dec_rfl
theorem d601 : ∀ feat, Dec feat sr2 601 (FV7z.mk (.sse .movdqa) 16 [.xmm 6, .xmm 4] 4) := by dec_rfl
theorem d605 : ∀ feat, Dec feat sr2 605 (FV7z.mk (.sse .movdqu) 32 [.xmm 2, .mem (mbd 0 48 128)] 5) := by dec_rfl
theorem d610 : ∀ feat, Dec feat sr2 610 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 4, .xmm 1] 4) := by dec_rfl
theorem d614 : ∀ feat, Dec feat sr2 614 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 6, .xmm 0] 4) := by dec_rfl
theorem d618 : ∀ feat, Dec feat sr2 618 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 6] 4) := by dec_rfl
theorem d622 : ∀ feat, Dec feat sr2 622 (FV7z.mk (.sse .movdqa) 16 [.xmm 6, .xmm 3] 4) := by dec_rfl
theorem d626 : ∀ feat, Dec feat sr2 626 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 3, .xmm 1] 4) := by dec_rfl
theorem d630 : ∀ feat, Dec feat sr2 630 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 6, .xmm 0] 4) := by dec_rfl
theorem d634 : ∀ feat, Dec feat sr2 634 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 2] 4) := by dec_rfl
theorem d638 : ∀ feat, Dec feat sr2 638 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d642 : ∀ feat, Dec feat sr2 642 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 9, .xmm 3] 5) := by dec_rfl
theorem d647 : ∀ feat, Dec feat sr2 647 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 6] 5) := by dec_rfl
theorem d652 : ∀ feat, Dec feat sr2 652 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 1, .xmm 0] 4) := by dec_rfl
theorem d656 : ∀ feat, Dec feat sr2 656 (FV7z.mk .shl 64 [gr 64 9, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d660 : ∀ feat, Dec feat sr2 660 (FV7z.mk .shl 64 [gr 64 8, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d664 : ∀ feat, Dec feat sr2 664 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .xmm 1] 4) := by dec_rfl
theorem d668 : ∀ feat, Dec feat sr2 668 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d671 : ∀ feat, Dec feat sr2 671 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 48)] 4) := by dec_rfl
theorem d675 : ∀ feat, Dec feat sr2 675 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 5] 5) := by dec_rfl
theorem d680 : ∀ feat, Dec feat sr2 680 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem d683 : ∀ feat, Dec feat sr2 683 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 6, .xmm 4] 4) := by dec_rfl
theorem d687 : ∀ feat, Dec feat sr2 687 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d690 : ∀ feat, Dec feat sr2 690 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 1, .xmm 2] 4) := by dec_rfl
theorem d694 : ∀ feat, Dec feat sr2 694 (FV7z.mk .shl 64 [gr 64 6, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d698 : ∀ feat, Dec feat sr2 698 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 48)] 4) := by dec_rfl
theorem d702 : ∀ feat, Dec feat sr2 702 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.r 9)] 3) := by dec_rfl
theorem d705 : ∀ feat, Dec feat sr2 705 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d708 : ∀ feat, Dec feat sr2 708 (FV7z.mk .or 64 [gr 64 6, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d711 : ∀ feat, Dec feat sr2 711 (FV7z.mk .mov 32 [gr 32 1, Src.opd 32 (.r 7)] 2) := by dec_rfl
theorem d713 : ∀ feat, Dec feat sr2 713 (FV7z.mk .sub 32 [gr 32 1, Src.opd 32 (.r 0)] 2) := by dec_rfl
theorem d715 : ∀ feat, Dec feat sr2 715 (FV7z.mk .shr 64 [gr 64 2, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d718 : ∀ feat, Dec feat sr2 718 (FV7z.mk .shr 64 [gr 64 6, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d721 : ∀ feat, Dec feat sr2 721 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d724 : ∀ feat, Dec feat sr2 724 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551142] 6) := by dec_rfl
theorem d730 : ∀ feat, Dec feat sr2 730
    (FV7z.mk .lea 64 [gr 64 0, .mem (mg (some 2) none 1 18446744073709551615 0)] 4) := by dec_rfl
theorem d734 : ∀ feat, Dec feat sr2 734 (FV7z.mk .xor 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d737 : ∀ feat, Dec feat sr2 737 (FV7z.mk .and 64 [gr 64 6, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem d740 : ∀ feat, Dec feat sr2 740 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551414] 6) := by dec_rfl
theorem d746 : ∀ feat, Dec feat sr2 746 (FV7z.mk (.bit (BitMn.bsr)) 64 [gr 64 0, gr 64 6] 4) := by dec_rfl
theorem d750 : ∀ feat, Dec feat sr2 750 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d753 : ∀ feat, Dec feat sr2 753 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-- The stretch from `0` to `26`. -/
def o0 : List VOp := [
  VOp.op Op.nop,
  VOp.movd 1 6,
  VOp.op (Op.mov 64 0 (.r 7)),
  VOp.op (Op.and 32 0 (.i 4095)),
  VOp.punpcklbw 1 1,
  VOp.op (Op.cmp 64 0 (.i 4032))]

theorem b0 (prof : Profile) : BlkV prof sr2 0 26 o0 :=
  .cons (d0 _) (OpI.endbr) (by decide) <|
  .cons (d4 _) (VOpI.movd) (by decide) <|
  .cons (d8 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (d11 _) (OpI.and (.i 4095) (.inl rfl)) (by decide) <|
  .cons (d16 _) (VOpI.punpcklbw) (by decide) <|
  .cons (d20 _) (OpI.cmp (.i 4032) (.inr rfl)) (by decide) <|
  .nil 26

/-- The stretch from `26` to `35`. -/
def o26 : List VOp := [
  VOp.punpcklwd 1 1,
  VOp.pshufd 1 1 0]

theorem b26 (prof : Profile) : BlkV prof sr2 26 35 o26 :=
  .cons (d26 _) (VOpI.punpcklwd) (by decide) <|
  .cons (d30 _) (VOpI.pshufd) (by decide) <|
  .nil 35

/-- The stretch from `41` to `65`. -/
def o41 : List VOp := [
  VOp.movdqu_m 0 7 0,
  VOp.pxor 2 2,
  VOp.movdqa 3 0,
  VOp.pcmpeqb 0 1,
  VOp.pcmpeqb 3 2,
  VOp.pmovmskb 1 0]

theorem b41 (prof : Profile) : BlkV prof sr2 41 65 o41 :=
  .cons (d41 _) (VOpI.movdqu_m) (by decide) <|
  .cons (d45 _) (VOpI.pxor) (by decide) <|
  .cons (d49 _) (VOpI.movdqa) (by decide) <|
  .cons (d53 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d57 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d61 _) (VOpI.pmovmskb) (by decide) <|
  .nil 65

/-- The stretch from `65` to `72`. -/
def o65 : List VOp := [
  VOp.pmovmskb 2 3,
  VOp.op (Op.test 64 2 (.r 2))]

theorem b65 (prof : Profile) : BlkV prof sr2 65 72 o65 :=
  .cons (d65 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d69 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 72

/-- The stretch from `74` to `84`. -/
def o74 : List VOp := [
  VOp.op (Op.lea 64 0 (some 2) none 1 18446744073709551615),
  VOp.op (Op.xor 64 0 (.r 2)),
  VOp.op (Op.and 64 0 (.r 1))]

theorem b74 (prof : Profile) : BlkV prof sr2 74 84 o74 :=
  .cons (d74 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (d78 _) (OpI.xor (.r 2) (.inr rfl)) (by decide) <|
  .cons (d81 _) (OpI.and (.r 1) (.inr rfl)) (by decide) <|
  .nil 84

/-- The stretch from `94` to `97`. -/
def o94 : List VOp := [
  VOp.op (Op.add 64 0 (.r 7))]

theorem b94 (prof : Profile) : BlkV prof sr2 94 97 o94 :=
  .cons (d94 _) (OpI.add (.r 7) (.inr rfl)) (by decide) <|
  .nil 97

/-- The stretch from `112` to `139`. -/
def o112 : List VOp := [
  VOp.movdqu_m 4 7 16,
  VOp.movdqa 5 4,
  VOp.movdqu_m 3 7 32,
  VOp.pcmpeqb 4 1,
  VOp.pcmpeqb 5 2,
  VOp.movdqu_m 0 7 48]

theorem b112 (prof : Profile) : BlkV prof sr2 112 139 o112 :=
  .cons (d112 _) (VOpI.movdqu_m) (by decide) <|
  .cons (d117 _) (VOpI.movdqa) (by decide) <|
  .cons (d121 _) (VOpI.movdqu_m) (by decide) <|
  .cons (d126 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d130 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d134 _) (VOpI.movdqu_m) (by decide) <|
  .nil 139

/-- The stretch from `139` to `163`. -/
def o139 : List VOp := [
  VOp.pmovmskb 2 5,
  VOp.movdqa 5 3,
  VOp.pcmpeqb 3 1,
  VOp.pcmpeqb 5 2,
  VOp.pcmpeqb 2 0,
  VOp.op (Op.shl64 2 (.i 16))]

theorem b139 (prof : Profile) : BlkV prof sr2 139 163 o139 :=
  .cons (d139 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d143 _) (VOpI.movdqa) (by decide) <|
  .cons (d147 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d151 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d155 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d159 _) (OpI.shl64 (.i 16)) (by decide) <|
  .nil 163

/-- The stretch from `163` to `188`. -/
def o163 : List VOp := [
  VOp.pmovmskb 8 3,
  VOp.pmovmskb 0 5,
  VOp.pmovmskb 6 2,
  VOp.op (Op.shl64 8 (.i 32)),
  VOp.op (Op.shl64 0 (.i 32)),
  VOp.pcmpeqb 0 1]

theorem b163 (prof : Profile) : BlkV prof sr2 163 188 o163 :=
  .cons (d163 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d168 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d172 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d176 _) (OpI.shl64 (.i 32)) (by decide) <|
  .cons (d180 _) (OpI.shl64 (.i 32)) (by decide) <|
  .cons (d184 _) (VOpI.pcmpeqb) (by decide) <|
  .nil 188

/-- The stretch from `188` to `209`. -/
def o188 : List VOp := [
  VOp.op (Op.or 64 0 (.r 2)),
  VOp.op (Op.mov 64 2 (.r 6)),
  VOp.pmovmskb 6 4,
  VOp.op (Op.shl64 2 (.i 48)),
  VOp.op (Op.shl64 6 (.i 16)),
  VOp.op (Op.or 64 6 (.r 8))]

theorem b188 (prof : Profile) : BlkV prof sr2 188 209 o188 :=
  .cons (d188 _) (OpI.or (.r 2) (.inr rfl)) (by decide) <|
  .cons (d191 _) (OpI.mov (.r 6) (.inr rfl)) (by decide) <|
  .cons (d194 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d198 _) (OpI.shl64 (.i 48)) (by decide) <|
  .cons (d202 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d206 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .nil 209

/-- The stretch from `209` to `226`. -/
def o209 : List VOp := [
  VOp.op (Op.or 64 6 (.r 1)),
  VOp.pmovmskb 1 0,
  VOp.op (Op.shl64 1 (.i 48)),
  VOp.op (Op.or 64 6 (.r 1)),
  VOp.op (Op.or 64 0 (.r 2))]

theorem b209 (prof : Profile) : BlkV prof sr2 209 226 o209 :=
  .cons (d209 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (d212 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d216 _) (OpI.shl64 (.i 48)) (by decide) <|
  .cons (d220 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (d223 _) (OpI.or (.r 2) (.inr rfl)) (by decide) <|
  .nil 226

/-- The stretch from `228` to `238`. -/
def o228 : List VOp := [
  VOp.op (Op.lea 64 1 (some 0) none 1 18446744073709551615),
  VOp.op (Op.xor 64 1 (.r 0)),
  VOp.op (Op.and 64 6 (.r 1))]

theorem b228 (prof : Profile) : BlkV prof sr2 228 238 o228 :=
  .cons (d228 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (d232 _) (OpI.xor (.r 0) (.inr rfl)) (by decide) <|
  .cons (d235 _) (OpI.and (.r 1) (.inr rfl)) (by decide) <|
  .nil 238

/-- The stretch from `248` to `252`. -/
def o248 : List VOp := [
  VOp.op (Op.lea 64 0 (some 7) (some 6) 1 0)]

theorem b248 (prof : Profile) : BlkV prof sr2 248 252 o248 :=
  .cons (d248 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 252

/-- The stretch from `256` to `262`. -/
def o256 : List VOp := [
  VOp.op (Op.test 64 6 (.r 6)),
  VOp.op (Op.mov 64 1 (.r 7))]

theorem b256 (prof : Profile) : BlkV prof sr2 256 262 o256 :=
  .cons (d256 _) (OpI.test (.r 6) (.inr rfl)) (by decide) <|
  .cons (d259 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .nil 262

/-- The stretch from `268` to `280`. -/
def o268 : List VOp := [
  VOp.op (Op.add 64 7 (.i 64)),
  VOp.pxor 7 7,
  VOp.op (Op.and 64 7 (.i 18446744073709551552))]

theorem b268 (prof : Profile) : BlkV prof sr2 268 280 o268 :=
  .cons (d268 _) (OpI.add (.i 64) (.inr rfl)) (by decide) <|
  .cons (d272 _) (VOpI.pxor) (by decide) <|
  .cons (d276 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by decide) <|
  .nil 280

/-- The stretch from `288` to `303`. -/
def o288 : List VOp := [
  VOp.op (Op.test 64 2 (.r 2)),
  VOp.op (Op.cmov64 5 6 2),
  VOp.op (Op.cmov64 5 1 7),
  VOp.op (Op.add 64 7 (.i 64))]

theorem b288 (prof : Profile) : BlkV prof sr2 288 303 o288 :=
  .cons (d288 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .cons (d291 _) (OpI.cmov64) (by decide) <|
  .cons (d295 _) (OpI.cmov64) (by decide) <|
  .cons (d299 _) (OpI.add (.i 64) (.inr rfl)) (by decide) <|
  .nil 303

/-- The stretch from `303` to `330`. -/
def o303 : List VOp := [
  VOp.movdqa_m 3 7 32,
  VOp.pxor 6 6,
  VOp.movdqa_m 2 7 48,
  VOp.movdqa 0 3,
  VOp.movdqa_m 4 7 16,
  VOp.pminub 0 2]

theorem b303 (prof : Profile) : BlkV prof sr2 303 330 o303 :=
  .cons (d303 _) (VOpI.movdqa_m) (by decide) <|
  .cons (d308 _) (VOpI.pxor) (by decide) <|
  .cons (d312 _) (VOpI.movdqa_m) (by decide) <|
  .cons (d317 _) (VOpI.movdqa) (by decide) <|
  .cons (d321 _) (VOpI.movdqa_m) (by decide) <|
  .cons (d326 _) (VOpI.pminub) (by decide) <|
  .nil 330

/-- The stretch from `330` to `354`. -/
def o330 : List VOp := [
  VOp.movdqa_m 5 7 0,
  VOp.pminub 0 4,
  VOp.pminub 0 5,
  VOp.pcmpeqb 0 7,
  VOp.pmovmskb 0 0,
  VOp.movdqa 0 5]

theorem b330 (prof : Profile) : BlkV prof sr2 330 354 o330 :=
  .cons (d330 _) (VOpI.movdqa_m) (by decide) <|
  .cons (d334 _) (VOpI.pminub) (by decide) <|
  .cons (d338 _) (VOpI.pminub) (by decide) <|
  .cons (d342 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d346 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d350 _) (VOpI.movdqa) (by decide) <|
  .nil 354

/-- The stretch from `354` to `379`. -/
def o354 : List VOp := [
  VOp.pcmpeqb 0 1,
  VOp.pmovmskb 9 0,
  VOp.movdqa 0 4,
  VOp.pcmpeqb 0 1,
  VOp.pmovmskb 2 0,
  VOp.movdqa 0 3]

theorem b354 (prof : Profile) : BlkV prof sr2 354 379 o354 :=
  .cons (d354 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d358 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d363 _) (VOpI.movdqa) (by decide) <|
  .cons (d367 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d371 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d375 _) (VOpI.movdqa) (by decide) <|
  .nil 379

/-- The stretch from `379` to `404`. -/
def o379 : List VOp := [
  VOp.pcmpeqb 0 1,
  VOp.op (Op.shl64 2 (.i 16)),
  VOp.pmovmskb 10 0,
  VOp.movdqa 0 2,
  VOp.pcmpeqb 0 1,
  VOp.op (Op.shl64 10 (.i 32))]

theorem b379 (prof : Profile) : BlkV prof sr2 379 404 o379 :=
  .cons (d379 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d383 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d387 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d392 _) (VOpI.movdqa) (by decide) <|
  .cons (d396 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d400 _) (OpI.shl64 (.i 32)) (by decide) <|
  .nil 404

/-- The stretch from `404` to `424`. -/
def o404 : List VOp := [
  VOp.op (Op.or 64 2 (.r 10)),
  VOp.pmovmskb 8 0,
  VOp.op (Op.or 64 2 (.r 9)),
  VOp.op (Op.shl64 8 (.i 48)),
  VOp.op (Op.or 64 2 (.r 8)),
  VOp.op (Op.test 32 0 (.r 0))]

theorem b404 (prof : Profile) : BlkV prof sr2 404 424 o404 :=
  .cons (d404 _) (OpI.or (.r 10) (.inr rfl)) (by decide) <|
  .cons (d407 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d412 _) (OpI.or (.r 9) (.inr rfl)) (by decide) <|
  .cons (d415 _) (OpI.shl64 (.i 48)) (by decide) <|
  .cons (d419 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d422 _) (OpI.test (.r 0) (.inl rfl)) (by decide) <|
  .nil 424

/-- The stretch from `430` to `455`. -/
def o430 : List VOp := [
  VOp.pcmpeqb 4 6,
  VOp.pcmpeqb 3 6,
  VOp.pcmpeqb 5 6,
  VOp.pmovmskb 0 4,
  VOp.pmovmskb 10 3,
  VOp.pcmpeqb 2 6]

theorem b430 (prof : Profile) : BlkV prof sr2 430 455 o430 :=
  .cons (d430 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d434 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d438 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d442 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d446 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d451 _) (VOpI.pcmpeqb) (by decide) <|
  .nil 455

/-- The stretch from `455` to `479`. -/
def o455 : List VOp := [
  VOp.pmovmskb 9 5,
  VOp.op (Op.shl64 10 (.i 32)),
  VOp.op (Op.shl64 0 (.i 16)),
  VOp.pmovmskb 8 2,
  VOp.op (Op.or 64 0 (.r 10)),
  VOp.op (Op.or 64 0 (.r 9))]

theorem b455 (prof : Profile) : BlkV prof sr2 455 479 o455 :=
  .cons (d455 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d460 _) (OpI.shl64 (.i 32)) (by decide) <|
  .cons (d464 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d468 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d473 _) (OpI.or (.r 10) (.inr rfl)) (by decide) <|
  .cons (d476 _) (OpI.or (.r 9) (.inr rfl)) (by decide) <|
  .nil 479

/-- The stretch from `479` to `500`. -/
def o479 : List VOp := [
  VOp.op (Op.shl64 8 (.i 48)),
  VOp.op (Op.or 64 0 (.r 8)),
  VOp.op (Op.lea 64 8 (some 0) none 1 18446744073709551615),
  VOp.op (Op.xor 64 8 (.r 0)),
  VOp.op (Op.and 64 2 (.r 8)),
  VOp.op (Op.cmov64 5 1 7)]

theorem b479 (prof : Profile) : BlkV prof sr2 479 500 o479 :=
  .cons (d479 _) (OpI.shl64 (.i 48)) (by decide) <|
  .cons (d483 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d486 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (d490 _) (OpI.xor (.r 0) (.inr rfl)) (by decide) <|
  .cons (d493 _) (OpI.and (.r 8) (.inr rfl)) (by decide) <|
  .cons (d496 _) (OpI.cmov64) (by decide) <|
  .nil 500

/-- The stretch from `500` to `504`. -/
def o500 : List VOp := [
  VOp.op (Op.cmov64 5 6 2)]

theorem b500 (prof : Profile) : BlkV prof sr2 500 504 o500 :=
  .cons (d500 _) (OpI.cmov64) (by decide) <|
  .nil 504

/-- The stretch from `508` to `512`. -/
def o508 : List VOp := [
  VOp.op (Op.lea 64 0 (some 1) (some 6) 1 0)]

theorem b508 (prof : Profile) : BlkV prof sr2 508 512 o508 :=
  .cons (d508 _) (OpI.lea (.inr rfl)) (by decide) <|
  .nil 512

/-- The stretch from `528` to `535`. -/
def o528 : List VOp := [
  VOp.op (Op.mov 32 6 (.i 1)),
  VOp.op (Op.xor 32 1 (.r 1))]

theorem b528 (prof : Profile) : BlkV prof sr2 528 535 o528 :=
  .cons (d528 _) (OpI.mov (.i 1) (.inl rfl)) (by decide) <|
  .cons (d533 _) (OpI.xor (.r 1) (.inl rfl)) (by decide) <|
  .nil 535

/-- The stretch from `544` to `546`. -/
def o544 : List VOp := [
  VOp.op (Op.xor 32 0 (.r 0))]

theorem b544 (prof : Profile) : BlkV prof sr2 544 546 o544 :=
  .cons (d544 _) (OpI.xor (.r 0) (.inl rfl)) (by decide) <|
  .nil 546

/-- The stretch from `560` to `584`. -/
def o560 : List VOp := [
  VOp.op (Op.mov 64 0 (.r 7)),
  VOp.pxor 0 0,
  VOp.op (Op.and 64 0 (.i 18446744073709551552)),
  VOp.movdqu_m 5 0 0,
  VOp.movdqa 6 5,
  VOp.movdqu_m 4 0 16]

theorem b560 (prof : Profile) : BlkV prof sr2 560 584 o560 :=
  .cons (d560 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (d563 _) (VOpI.pxor) (by decide) <|
  .cons (d567 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by decide) <|
  .cons (d571 _) (VOpI.movdqu_m) (by decide) <|
  .cons (d575 _) (VOpI.movdqa) (by decide) <|
  .cons (d579 _) (VOpI.movdqu_m) (by decide) <|
  .nil 584

/-- The stretch from `584` to `610`. -/
def o584 : List VOp := [
  VOp.pcmpeqb 5 1,
  VOp.pcmpeqb 6 0,
  VOp.movdqu_m 3 0 32,
  VOp.pmovmskb 6 6,
  VOp.movdqa 6 4,
  VOp.movdqu_m 2 0 48]

theorem b584 (prof : Profile) : BlkV prof sr2 584 610 o584 :=
  .cons (d584 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d588 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d592 _) (VOpI.movdqu_m) (by decide) <|
  .cons (d597 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d601 _) (VOpI.movdqa) (by decide) <|
  .cons (d605 _) (VOpI.movdqu_m) (by decide) <|
  .nil 610

/-- The stretch from `610` to `634`. -/
def o610 : List VOp := [
  VOp.pcmpeqb 4 1,
  VOp.pcmpeqb 6 0,
  VOp.pmovmskb 2 6,
  VOp.movdqa 6 3,
  VOp.pcmpeqb 3 1,
  VOp.pcmpeqb 6 0]

theorem b610 (prof : Profile) : BlkV prof sr2 610 634 o610 :=
  .cons (d610 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d614 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d618 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d622 _) (VOpI.movdqa) (by decide) <|
  .cons (d626 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d630 _) (VOpI.pcmpeqb) (by decide) <|
  .nil 634

/-- The stretch from `634` to `660`. -/
def o634 : List VOp := [
  VOp.pcmpeqb 0 2,
  VOp.op (Op.shl64 2 (.i 16)),
  VOp.pmovmskb 9 3,
  VOp.pmovmskb 8 6,
  VOp.pmovmskb 1 0,
  VOp.op (Op.shl64 9 (.i 32))]

theorem b634 (prof : Profile) : BlkV prof sr2 634 660 o634 :=
  .cons (d634 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d638 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d642 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d647 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d652 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d656 _) (OpI.shl64 (.i 32)) (by decide) <|
  .nil 660

/-- The stretch from `660` to `683`. -/
def o660 : List VOp := [
  VOp.op (Op.shl64 8 (.i 32)),
  VOp.pcmpeqb 2 1,
  VOp.op (Op.or 64 2 (.r 8)),
  VOp.op (Op.shl64 1 (.i 48)),
  VOp.pmovmskb 8 5,
  VOp.op (Op.or 64 2 (.r 6))]

theorem b660 (prof : Profile) : BlkV prof sr2 660 683 o660 :=
  .cons (d660 _) (OpI.shl64 (.i 32)) (by decide) <|
  .cons (d664 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d668 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d671 _) (OpI.shl64 (.i 48)) (by decide) <|
  .cons (d675 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d680 _) (OpI.or (.r 6) (.inr rfl)) (by decide) <|
  .nil 683

/-- The stretch from `683` to `705`. -/
def o683 : List VOp := [
  VOp.pmovmskb 6 4,
  VOp.op (Op.or 64 2 (.r 1)),
  VOp.pmovmskb 1 2,
  VOp.op (Op.shl64 6 (.i 16)),
  VOp.op (Op.shl64 1 (.i 48)),
  VOp.op (Op.or 64 6 (.r 9))]

theorem b683 (prof : Profile) : BlkV prof sr2 683 705 o683 :=
  .cons (d683 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d687 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (d690 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d694 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d698 _) (OpI.shl64 (.i 48)) (by decide) <|
  .cons (d702 _) (OpI.or (.r 9) (.inr rfl)) (by decide) <|
  .nil 705

/-- The stretch from `705` to `721`. -/
def o705 : List VOp := [
  VOp.op (Op.or 64 6 (.r 8)),
  VOp.op (Op.or 64 6 (.r 1)),
  VOp.op (Op.mov 32 1 (.r 7)),
  VOp.op (Op.sub 32 1 (.r 0)),
  VOp.op (Op.shr64 2 (.r 1)),
  VOp.op (Op.shr64 6 (.r 1))]

theorem b705 (prof : Profile) : BlkV prof sr2 705 721 o705 :=
  .cons (d705 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d708 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (d711 _) (OpI.mov (.r 7) (.inl rfl)) (by decide) <|
  .cons (d713 _) (OpI.sub (.r 0) (.inl rfl)) (by decide) <|
  .cons (d715 _) (OpI.shr64 (.r 1)) (by decide) <|
  .cons (d718 _) (OpI.shr64 (.r 1)) (by decide) <|
  .nil 721

/-- The stretch from `721` to `724`. -/
def o721 : List VOp := [
  VOp.op (Op.test 64 2 (.r 2))]

theorem b721 (prof : Profile) : BlkV prof sr2 721 724 o721 :=
  .cons (d721 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 724

/-- The stretch from `730` to `740`. -/
def o730 : List VOp := [
  VOp.op (Op.lea 64 0 (some 2) none 1 18446744073709551615),
  VOp.op (Op.xor 64 0 (.r 2)),
  VOp.op (Op.and 64 6 (.r 0))]

theorem b730 (prof : Profile) : BlkV prof sr2 730 740 o730 :=
  .cons (d730 _) (OpI.lea (.inr rfl)) (by decide) <|
  .cons (d734 _) (OpI.xor (.r 2) (.inr rfl)) (by decide) <|
  .cons (d737 _) (OpI.and (.r 0) (.inr rfl)) (by decide) <|
  .nil 740

/-- The stretch from `750` to `753`. -/
def o750 : List VOp := [
  VOp.op (Op.add 64 0 (.r 7))]

theorem b750 (prof : Profile) : BlkV prof sr2 750 753 o750 :=
  .cons (d750 _) (OpI.add (.r 7) (.inr rfl)) (by decide) <|
  .nil 753

end FV7z.Strrchr
