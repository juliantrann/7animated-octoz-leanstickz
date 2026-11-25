import FV7z.Lemmas.Sse2
import FV7z.Lemmas.BlkOps3
import FV7z.Lemmas.BlkOps2
/-!
# The code of `__strlen_sse2` (PLAN.md G2, the PLT contracts of `launch_to_main`)

glibc 2.31's `__strlen_sse2` (`sysdeps/x86_64/multiarch/strlen-sse2.S`, `strlen-vec.S`) at `0x6546d0` in `7zzs`, the
variant of `strlen` that the IFUNC resolver picks on a processor without AVX2: its bytes (`sl2`), what each instruction
decodes to on every processor (`d<offset>`, by evaluation), and its straight-line stretches as `BlkV`s
(`b<start>`). Generated from the decoder's output (`decshow`) by `tools/strlen_gen.py`.
-/
namespace FV7z.Strlen
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The bytes of `__strlen_sse2`. -/
def sl2 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x66, 0x0f, 0xef, 0xc0, 0x66, 0x0f, 0xef, 0xc9, 0x66, 0x0f, 0xef, 0xd2,
  0x66, 0x0f, 0xef, 0xdb, 0x48, 0x89, 0xf8, 0x48, 0x89, 0xf9, 0x48, 0x81, 0xe1, 0xff, 0x0f, 0x00,
  0x00, 0x48, 0x81, 0xf9, 0xcf, 0x0f, 0x00, 0x00, 0x77, 0x66, 0xf3, 0x0f, 0x6f, 0x20, 0x66, 0x0f,
  0x74, 0xe0, 0x66, 0x0f, 0xd7, 0xd4, 0x85, 0xd2, 0x74, 0x04, 0x0f, 0xbc, 0xc2, 0xc3, 0x48, 0x83,
  0xe0, 0xf0, 0x66, 0x0f, 0x74, 0x48, 0x10, 0x66, 0x0f, 0x74, 0x50, 0x20, 0x66, 0x0f, 0x74, 0x58,
  0x30, 0x66, 0x0f, 0xd7, 0xd1, 0x66, 0x44, 0x0f, 0xd7, 0xc2, 0x66, 0x0f, 0xd7, 0xcb, 0x48, 0xc1,
  0xe2, 0x10, 0x48, 0xc1, 0xe1, 0x10, 0x4c, 0x09, 0xc1, 0x48, 0xc1, 0xe1, 0x20, 0x48, 0x09, 0xca,
  0x48, 0x89, 0xf9, 0x48, 0x31, 0xc1, 0x48, 0x83, 0xe0, 0xc0, 0x48, 0xd3, 0xfa, 0x48, 0x85, 0xd2,
  0x74, 0x7e, 0x48, 0x0f, 0xbc, 0xc2, 0xc3, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x83, 0xe0, 0xc0, 0x66, 0x0f, 0x74, 0x00, 0x66, 0x0f, 0x74, 0x48, 0x10, 0x66, 0x0f, 0x74,
  0x50, 0x20, 0x66, 0x0f, 0x74, 0x58, 0x30, 0x66, 0x0f, 0xd7, 0xf0, 0x66, 0x0f, 0xd7, 0xd1, 0x66,
  0x44, 0x0f, 0xd7, 0xc2, 0x66, 0x0f, 0xd7, 0xcb, 0x48, 0xc1, 0xe2, 0x10, 0x48, 0xc1, 0xe1, 0x10,
  0x48, 0x09, 0xf2, 0x4c, 0x09, 0xc1, 0x48, 0xc1, 0xe1, 0x20, 0x48, 0x09, 0xca, 0x48, 0x89, 0xf9,
  0x48, 0x31, 0xc1, 0x48, 0x83, 0xe0, 0xc0, 0x48, 0xd3, 0xfa, 0x48, 0x85, 0xd2, 0x74, 0x11, 0x48,
  0x0f, 0xbc, 0xc2, 0xc3, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x90,
  0x66, 0x0f, 0xef, 0xc9, 0x66, 0x0f, 0xef, 0xd2, 0x66, 0x0f, 0xef, 0xdb, 0x0f, 0x1f, 0x40, 0x00,
  0x66, 0x0f, 0x6f, 0x40, 0x40, 0x66, 0x0f, 0xda, 0x40, 0x50, 0x66, 0x0f, 0xda, 0x40, 0x60, 0x66,
  0x0f, 0xda, 0x40, 0x70, 0x66, 0x0f, 0x74, 0xc3, 0x66, 0x0f, 0xd7, 0xd0, 0x85, 0xd2, 0x75, 0x30,
  0x48, 0x83, 0xe8, 0x80, 0x66, 0x0f, 0x6f, 0x00, 0x66, 0x0f, 0xda, 0x40, 0x10, 0x66, 0x0f, 0xda,
  0x40, 0x20, 0x66, 0x0f, 0xda, 0x40, 0x30, 0x66, 0x0f, 0x74, 0xc3, 0x66, 0x0f, 0xd7, 0xd0, 0x85,
  0xd2, 0x75, 0x11, 0xeb, 0xbb, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x48, 0x83, 0xc0, 0x40, 0x66, 0x0f, 0xef, 0xc0, 0x66, 0x0f, 0x74, 0x00, 0x66, 0x0f, 0x74, 0x48,
  0x10, 0x66, 0x0f, 0x74, 0x50, 0x20, 0x66, 0x0f, 0x74, 0x58, 0x30, 0x66, 0x0f, 0xd7, 0xf0, 0x66,
  0x0f, 0xd7, 0xd1, 0x66, 0x44, 0x0f, 0xd7, 0xc2, 0x66, 0x0f, 0xd7, 0xcb, 0x48, 0xc1, 0xe2, 0x10,
  0x48, 0xc1, 0xe1, 0x10, 0x48, 0x09, 0xf2, 0x4c, 0x09, 0xc1, 0x48, 0xc1, 0xe1, 0x20, 0x48, 0x09,
  0xca, 0x48, 0x0f, 0xbc, 0xd2, 0x48, 0x01, 0xd0, 0x48, 0x29, 0xf8, 0xc3]

theorem sl2_length : sl2.length = 412 := rfl

theorem d0 : ∀ feat, Dec feat sl2 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d4 : ∀ feat, Dec feat sl2 4 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d8 : ∀ feat, Dec feat sl2 8 (FV7z.mk (.sse .pxor) 16 [.xmm 1, .xmm 1] 4) := by dec_rfl
theorem d12 : ∀ feat, Dec feat sl2 12 (FV7z.mk (.sse .pxor) 16 [.xmm 2, .xmm 2] 4) := by dec_rfl
theorem d16 : ∀ feat, Dec feat sl2 16 (FV7z.mk (.sse .pxor) 16 [.xmm 3, .xmm 3] 4) := by dec_rfl
theorem d20 : ∀ feat, Dec feat sl2 20 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d23 : ∀ feat, Dec feat sl2 23 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d26 : ∀ feat, Dec feat sl2 26 (FV7z.mk .and 64 [gr 64 1, Src.opd 64 (.i 4095)] 7) := by dec_rfl
theorem d33 : ∀ feat, Dec feat sl2 33 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.i 4047)] 7) := by dec_rfl
theorem d40 : ∀ feat, Dec feat sl2 40 (FV7z.mk (.jcc 7) 64 [.rel 102] 2) := by dec_rfl
theorem d42 : ∀ feat, Dec feat sl2 42 (FV7z.mk (.sse .movdqu) 32 [.xmm 4, .mem (mbd 0 0 128)] 4) := by dec_rfl
theorem d46 : ∀ feat, Dec feat sl2 46 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 4, .xmm 0] 4) := by dec_rfl
theorem d50 : ∀ feat, Dec feat sl2 50 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 4] 4) := by dec_rfl
theorem d54 : ∀ feat, Dec feat sl2 54 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem d56 : ∀ feat, Dec feat sl2 56 (FV7z.mk (.jcc 4) 64 [.rel 4] 2) := by dec_rfl
theorem d58 : ∀ feat, Dec feat sl2 58 (FV7z.mk (.bit (BitMn.bsf)) 32 [gr 32 0, gr 32 2] 3) := by dec_rfl
theorem d61 : ∀ feat, Dec feat sl2 61 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d62 : ∀ feat, Dec feat sl2 62 (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551600)] 4) := by dec_rfl
theorem d66 : ∀ feat, Dec feat sl2 66 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .mem (mbd 0 16 128)] 5) := by dec_rfl
theorem d71 : ∀ feat, Dec feat sl2 71 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .mem (mbd 0 32 128)] 5) := by dec_rfl
theorem d76 : ∀ feat, Dec feat sl2 76 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 3, .mem (mbd 0 48 128)] 5) := by dec_rfl
theorem d81 : ∀ feat, Dec feat sl2 81 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d85 : ∀ feat, Dec feat sl2 85 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 2] 5) := by dec_rfl
theorem d90 : ∀ feat, Dec feat sl2 90 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 1, .xmm 3] 4) := by dec_rfl
theorem d94 : ∀ feat, Dec feat sl2 94 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d98 : ∀ feat, Dec feat sl2 98 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d102 : ∀ feat, Dec feat sl2 102 (FV7z.mk .or 64 [gr 64 1, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d105 : ∀ feat, Dec feat sl2 105 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d109 : ∀ feat, Dec feat sl2 109 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d112 : ∀ feat, Dec feat sl2 112 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d115 : ∀ feat, Dec feat sl2 115 (FV7z.mk .xor 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem d118 : ∀ feat, Dec feat sl2 118
    (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem d122 : ∀ feat, Dec feat sl2 122 (FV7z.mk .sar 64 [gr 64 2, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d125 : ∀ feat, Dec feat sl2 125 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d128 : ∀ feat, Dec feat sl2 128 (FV7z.mk (.jcc 4) 64 [.rel 126] 2) := by dec_rfl
theorem d130 : ∀ feat, Dec feat sl2 130 (FV7z.mk (.bit (BitMn.bsf)) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem d134 : ∀ feat, Dec feat sl2 134 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d144 : ∀ feat, Dec feat sl2 144
    (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem d148 : ∀ feat, Dec feat sl2 148 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .mem (mbd 0 0 128)] 4) := by dec_rfl
theorem d152 : ∀ feat, Dec feat sl2 152 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .mem (mbd 0 16 128)] 5) := by dec_rfl
theorem d157 : ∀ feat, Dec feat sl2 157 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .mem (mbd 0 32 128)] 5) := by dec_rfl
theorem d162 : ∀ feat, Dec feat sl2 162 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 3, .mem (mbd 0 48 128)] 5) := by dec_rfl
theorem d167 : ∀ feat, Dec feat sl2 167 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 6, .xmm 0] 4) := by dec_rfl
theorem d171 : ∀ feat, Dec feat sl2 171 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d175 : ∀ feat, Dec feat sl2 175 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 2] 5) := by dec_rfl
theorem d180 : ∀ feat, Dec feat sl2 180 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 1, .xmm 3] 4) := by dec_rfl
theorem d184 : ∀ feat, Dec feat sl2 184 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d188 : ∀ feat, Dec feat sl2 188 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d192 : ∀ feat, Dec feat sl2 192 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem d195 : ∀ feat, Dec feat sl2 195 (FV7z.mk .or 64 [gr 64 1, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d198 : ∀ feat, Dec feat sl2 198 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d202 : ∀ feat, Dec feat sl2 202 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d205 : ∀ feat, Dec feat sl2 205 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d208 : ∀ feat, Dec feat sl2 208 (FV7z.mk .xor 64 [gr 64 1, Src.opd 64 (.r 0)] 3) := by dec_rfl
theorem d211 : ∀ feat, Dec feat sl2 211
    (FV7z.mk .and 64 [gr 64 0, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem d215 : ∀ feat, Dec feat sl2 215 (FV7z.mk .sar 64 [gr 64 2, Src.opd 8 (.r 1)] 3) := by dec_rfl
theorem d218 : ∀ feat, Dec feat sl2 218 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d221 : ∀ feat, Dec feat sl2 221 (FV7z.mk (.jcc 4) 64 [.rel 17] 2) := by dec_rfl
theorem d223 : ∀ feat, Dec feat sl2 223 (FV7z.mk (.bit (BitMn.bsf)) 64 [gr 64 0, gr 64 2] 4) := by dec_rfl
theorem d227 : ∀ feat, Dec feat sl2 227 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d240 : ∀ feat, Dec feat sl2 240 (FV7z.mk (.sse .pxor) 16 [.xmm 1, .xmm 1] 4) := by dec_rfl
theorem d244 : ∀ feat, Dec feat sl2 244 (FV7z.mk (.sse .pxor) 16 [.xmm 2, .xmm 2] 4) := by dec_rfl
theorem d248 : ∀ feat, Dec feat sl2 248 (FV7z.mk (.sse .pxor) 16 [.xmm 3, .xmm 3] 4) := by dec_rfl
theorem d252 : ∀ feat, Dec feat sl2 252 (FV7z.mk .nop 32 [.mem (mg (some 0) none 1 0 32)] 4) := by dec_rfl
theorem d256 : ∀ feat, Dec feat sl2 256 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .mem (mbd 0 64 128)] 5) := by dec_rfl
theorem d261 : ∀ feat, Dec feat sl2 261 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .mem (mbd 0 80 128)] 5) := by dec_rfl
theorem d266 : ∀ feat, Dec feat sl2 266 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .mem (mbd 0 96 128)] 5) := by dec_rfl
theorem d271 : ∀ feat, Dec feat sl2 271 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .mem (mbd 0 112 128)] 5) := by dec_rfl
theorem d276 : ∀ feat, Dec feat sl2 276 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d280 : ∀ feat, Dec feat sl2 280 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d284 : ∀ feat, Dec feat sl2 284 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem d286 : ∀ feat, Dec feat sl2 286 (FV7z.mk (.jcc 5) 64 [.rel 48] 2) := by dec_rfl
theorem d288 : ∀ feat, Dec feat sl2 288
    (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.i 18446744073709551488)] 4) := by dec_rfl
theorem d292 : ∀ feat, Dec feat sl2 292 (FV7z.mk (.sse .movdqa) 16 [.xmm 0, .mem (mbd 0 0 128)] 4) := by dec_rfl
theorem d296 : ∀ feat, Dec feat sl2 296 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .mem (mbd 0 16 128)] 5) := by dec_rfl
theorem d301 : ∀ feat, Dec feat sl2 301 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .mem (mbd 0 32 128)] 5) := by dec_rfl
theorem d306 : ∀ feat, Dec feat sl2 306 (FV7z.mk (.sse (.pminu 8)) 16 [.xmm 0, .mem (mbd 0 48 128)] 5) := by dec_rfl
theorem d311 : ∀ feat, Dec feat sl2 311 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .xmm 3] 4) := by dec_rfl
theorem d315 : ∀ feat, Dec feat sl2 315 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 0] 4) := by dec_rfl
theorem d319 : ∀ feat, Dec feat sl2 319 (FV7z.mk .test 32 [gr 32 2, Src.opd 32 (.r 2)] 2) := by dec_rfl
theorem d321 : ∀ feat, Dec feat sl2 321 (FV7z.mk (.jcc 5) 64 [.rel 17] 2) := by dec_rfl
theorem d323 : ∀ feat, Dec feat sl2 323 (FV7z.mk .jmp 64 [.rel 18446744073709551547] 2) := by dec_rfl
theorem d336 : ∀ feat, Dec feat sl2 336 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.i 64)] 4) := by dec_rfl
theorem d340 : ∀ feat, Dec feat sl2 340 (FV7z.mk (.sse .pxor) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d344 : ∀ feat, Dec feat sl2 344 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 0, .mem (mbd 0 0 128)] 4) := by dec_rfl
theorem d348 : ∀ feat, Dec feat sl2 348 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 1, .mem (mbd 0 16 128)] 5) := by dec_rfl
theorem d353 : ∀ feat, Dec feat sl2 353 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 2, .mem (mbd 0 32 128)] 5) := by dec_rfl
theorem d358 : ∀ feat, Dec feat sl2 358 (FV7z.mk (.sse .pcmpeqb) 16 [.xmm 3, .mem (mbd 0 48 128)] 5) := by dec_rfl
theorem d363 : ∀ feat, Dec feat sl2 363 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 6, .xmm 0] 4) := by dec_rfl
theorem d367 : ∀ feat, Dec feat sl2 367 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 2, .xmm 1] 4) := by dec_rfl
theorem d371 : ∀ feat, Dec feat sl2 371 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 8, .xmm 2] 5) := by dec_rfl
theorem d376 : ∀ feat, Dec feat sl2 376 (FV7z.mk (.sse .pmovmskb) 16 [gr 32 1, .xmm 3] 4) := by dec_rfl
theorem d380 : ∀ feat, Dec feat sl2 380 (FV7z.mk .shl 64 [gr 64 2, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d384 : ∀ feat, Dec feat sl2 384 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 16)] 4) := by dec_rfl
theorem d388 : ∀ feat, Dec feat sl2 388 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 6)] 3) := by dec_rfl
theorem d391 : ∀ feat, Dec feat sl2 391 (FV7z.mk .or 64 [gr 64 1, Src.opd 64 (.r 8)] 3) := by dec_rfl
theorem d394 : ∀ feat, Dec feat sl2 394 (FV7z.mk .shl 64 [gr 64 1, Src.opd 8 (.i 32)] 4) := by dec_rfl
theorem d398 : ∀ feat, Dec feat sl2 398 (FV7z.mk .or 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d401 : ∀ feat, Dec feat sl2 401 (FV7z.mk (.bit (BitMn.bsf)) 64 [gr 64 2, gr 64 2] 4) := by dec_rfl
theorem d405 : ∀ feat, Dec feat sl2 405 (FV7z.mk .add 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d408 : ∀ feat, Dec feat sl2 408 (FV7z.mk .sub 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d411 : ∀ feat, Dec feat sl2 411 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-- The stretch from `0` to `40`. -/
def o0 : List VOp := [
  VOp.op Op.nop,
  VOp.pxor 0 0,
  VOp.pxor 1 1,
  VOp.pxor 2 2,
  VOp.pxor 3 3,
  VOp.op (Op.mov 64 0 (.r 7)),
  VOp.op (Op.mov 64 1 (.r 7)),
  VOp.op (Op.and 64 1 (.i 4095)),
  VOp.op (Op.cmp 64 1 (.i 4047))]

theorem b0 (prof : Profile) : BlkV prof sl2 0 40 o0 :=
  .cons (d0 _) (OpI.endbr) (by decide) <|
  .cons (d4 _) (VOpI.pxor) (by decide) <|
  .cons (d8 _) (VOpI.pxor) (by decide) <|
  .cons (d12 _) (VOpI.pxor) (by decide) <|
  .cons (d16 _) (VOpI.pxor) (by decide) <|
  .cons (d20 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (d23 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (d26 _) (OpI.and (.i 4095) (.inr rfl)) (by decide) <|
  .cons (d33 _) (OpI.cmp (.i 4047) (.inr rfl)) (by decide) <|
  .nil 40

/-- The stretch from `42` to `56`. -/
def o42 : List VOp := [
  VOp.movdqu_m 4 0 0,
  VOp.pcmpeqb 4 0,
  VOp.pmovmskb 2 4,
  VOp.op (Op.test 32 2 (.r 2))]

theorem b42 (prof : Profile) : BlkV prof sl2 42 56 o42 :=
  .cons (d42 _) (VOpI.movdqu_m) (by decide) <|
  .cons (d46 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d50 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d54 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 56

/-- The stretch from `62` to `66`. -/
def o62 : List VOp := [
  VOp.op (Op.and 64 0 (.i 18446744073709551600))]

theorem b62 (prof : Profile) : BlkV prof sl2 62 66 o62 :=
  .cons (d62 _) (OpI.and (.i 18446744073709551600) (.inr rfl)) (by decide) <|
  .nil 66

/-- The stretch from `66` to `128`. -/
def o66 : List VOp := [
  VOp.pcmpeqb_m 1 0 16,
  VOp.pcmpeqb_m 2 0 32,
  VOp.pcmpeqb_m 3 0 48,
  VOp.pmovmskb 2 1,
  VOp.pmovmskb 8 2,
  VOp.pmovmskb 1 3,
  VOp.op (Op.shl64 2 (.i 16)),
  VOp.op (Op.shl64 1 (.i 16)),
  VOp.op (Op.or 64 1 (.r 8)),
  VOp.op (Op.shl64 1 (.i 32)),
  VOp.op (Op.or 64 2 (.r 1)),
  VOp.op (Op.mov 64 1 (.r 7)),
  VOp.op (Op.xor 64 1 (.r 0)),
  VOp.op (Op.and 64 0 (.i 18446744073709551552)),
  VOp.op (Op.sar64 2 (.r 1)),
  VOp.op (Op.test 64 2 (.r 2))]

theorem b66 (prof : Profile) : BlkV prof sl2 66 128 o66 :=
  .cons (d66 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d71 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d76 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d81 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d85 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d90 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d94 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d98 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d102 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d105 _) (OpI.shl64 (.i 32)) (by decide) <|
  .cons (d109 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (d112 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (d115 _) (OpI.xor (.r 0) (.inr rfl)) (by decide) <|
  .cons (d118 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by decide) <|
  .cons (d122 _) (OpI.sar64 (.r 1)) (by decide) <|
  .cons (d125 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 128

/-- The stretch from `144` to `148`. -/
def o144 : List VOp := [
  VOp.op (Op.and 64 0 (.i 18446744073709551552))]

theorem b144 (prof : Profile) : BlkV prof sl2 144 148 o144 :=
  .cons (d144 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by decide) <|
  .nil 148

/-- The stretch from `148` to `221`. -/
def o148 : List VOp := [
  VOp.pcmpeqb_m 0 0 0,
  VOp.pcmpeqb_m 1 0 16,
  VOp.pcmpeqb_m 2 0 32,
  VOp.pcmpeqb_m 3 0 48,
  VOp.pmovmskb 6 0,
  VOp.pmovmskb 2 1,
  VOp.pmovmskb 8 2,
  VOp.pmovmskb 1 3,
  VOp.op (Op.shl64 2 (.i 16)),
  VOp.op (Op.shl64 1 (.i 16)),
  VOp.op (Op.or 64 2 (.r 6)),
  VOp.op (Op.or 64 1 (.r 8)),
  VOp.op (Op.shl64 1 (.i 32)),
  VOp.op (Op.or 64 2 (.r 1)),
  VOp.op (Op.mov 64 1 (.r 7)),
  VOp.op (Op.xor 64 1 (.r 0)),
  VOp.op (Op.and 64 0 (.i 18446744073709551552)),
  VOp.op (Op.sar64 2 (.r 1)),
  VOp.op (Op.test 64 2 (.r 2))]

theorem b148 (prof : Profile) : BlkV prof sl2 148 221 o148 :=
  .cons (d148 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d152 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d157 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d162 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d167 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d171 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d175 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d180 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d184 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d188 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d192 _) (OpI.or (.r 6) (.inr rfl)) (by decide) <|
  .cons (d195 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d198 _) (OpI.shl64 (.i 32)) (by decide) <|
  .cons (d202 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (d205 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (d208 _) (OpI.xor (.r 0) (.inr rfl)) (by decide) <|
  .cons (d211 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by decide) <|
  .cons (d215 _) (OpI.sar64 (.r 1)) (by decide) <|
  .cons (d218 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 221

/-- The stretch from `240` to `256`. -/
def o240 : List VOp := [
  VOp.pxor 1 1,
  VOp.pxor 2 2,
  VOp.pxor 3 3,
  VOp.op Op.nop]

theorem b240 (prof : Profile) : BlkV prof sl2 240 256 o240 :=
  .cons (d240 _) (VOpI.pxor) (by decide) <|
  .cons (d244 _) (VOpI.pxor) (by decide) <|
  .cons (d248 _) (VOpI.pxor) (by decide) <|
  .cons (d252 _) OpI.nop (by decide) <|
  .nil 256

/-- The stretch from `256` to `286`. -/
def o256 : List VOp := [
  VOp.movdqa_m 0 0 64,
  VOp.pminub_m 0 0 80,
  VOp.pminub_m 0 0 96,
  VOp.pminub_m 0 0 112,
  VOp.pcmpeqb 0 3,
  VOp.pmovmskb 2 0,
  VOp.op (Op.test 32 2 (.r 2))]

theorem b256 (prof : Profile) : BlkV prof sl2 256 286 o256 :=
  .cons (d256 _) (VOpI.movdqa_m) (by decide) <|
  .cons (d261 _) (VOpI.pminub_m) (by decide) <|
  .cons (d266 _) (VOpI.pminub_m) (by decide) <|
  .cons (d271 _) (VOpI.pminub_m) (by decide) <|
  .cons (d276 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d280 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d284 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 286

/-- The stretch from `288` to `292`. -/
def o288 : List VOp := [
  VOp.op (Op.sub 64 0 (.i 18446744073709551488))]

theorem b288 (prof : Profile) : BlkV prof sl2 288 292 o288 :=
  .cons (d288 _) (OpI.sub (.i 18446744073709551488) (.inr rfl)) (by decide) <|
  .nil 292

/-- The stretch from `292` to `321`. -/
def o292 : List VOp := [
  VOp.movdqa_m 0 0 0,
  VOp.pminub_m 0 0 16,
  VOp.pminub_m 0 0 32,
  VOp.pminub_m 0 0 48,
  VOp.pcmpeqb 0 3,
  VOp.pmovmskb 2 0,
  VOp.op (Op.test 32 2 (.r 2))]

theorem b292 (prof : Profile) : BlkV prof sl2 292 321 o292 :=
  .cons (d292 _) (VOpI.movdqa_m) (by decide) <|
  .cons (d296 _) (VOpI.pminub_m) (by decide) <|
  .cons (d301 _) (VOpI.pminub_m) (by decide) <|
  .cons (d306 _) (VOpI.pminub_m) (by decide) <|
  .cons (d311 _) (VOpI.pcmpeqb) (by decide) <|
  .cons (d315 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d319 _) (OpI.test (.r 2) (.inl rfl)) (by decide) <|
  .nil 321

/-- The stretch from `336` to `340`. -/
def o336 : List VOp := [
  VOp.op (Op.add 64 0 (.i 64))]

theorem b336 (prof : Profile) : BlkV prof sl2 336 340 o336 :=
  .cons (d336 _) (OpI.add (.i 64) (.inr rfl)) (by decide) <|
  .nil 340

/-- The stretch from `340` to `401`. -/
def o340 : List VOp := [
  VOp.pxor 0 0,
  VOp.pcmpeqb_m 0 0 0,
  VOp.pcmpeqb_m 1 0 16,
  VOp.pcmpeqb_m 2 0 32,
  VOp.pcmpeqb_m 3 0 48,
  VOp.pmovmskb 6 0,
  VOp.pmovmskb 2 1,
  VOp.pmovmskb 8 2,
  VOp.pmovmskb 1 3,
  VOp.op (Op.shl64 2 (.i 16)),
  VOp.op (Op.shl64 1 (.i 16)),
  VOp.op (Op.or 64 2 (.r 6)),
  VOp.op (Op.or 64 1 (.r 8)),
  VOp.op (Op.shl64 1 (.i 32)),
  VOp.op (Op.or 64 2 (.r 1))]

theorem b340 (prof : Profile) : BlkV prof sl2 340 401 o340 :=
  .cons (d340 _) (VOpI.pxor) (by decide) <|
  .cons (d344 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d348 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d353 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d358 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d363 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d367 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d371 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d376 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d380 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d384 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d388 _) (OpI.or (.r 6) (.inr rfl)) (by decide) <|
  .cons (d391 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d394 _) (OpI.shl64 (.i 32)) (by decide) <|
  .cons (d398 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .nil 401

/-- The stretch from `405` to `411`. -/
def o405 : List VOp := [
  VOp.op (Op.add 64 0 (.r 2)),
  VOp.op (Op.sub 64 0 (.r 7))]

theorem b405 (prof : Profile) : BlkV prof sl2 405 411 o405 :=
  .cons (d405 _) (OpI.add (.r 2) (.inr rfl)) (by decide) <|
  .cons (d408 _) (OpI.sub (.r 7) (.inr rfl)) (by decide) <|
  .nil 411

end FV7z.Strlen
