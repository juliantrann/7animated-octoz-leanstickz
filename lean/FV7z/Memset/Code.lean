import FV7z.Lemmas.Sse2b
import FV7z.Lemmas.BlkOps14
import FV7z.Lemmas.RepStosb
import FV7z.Lemmas.StoreX
/-!
# The code of glibc's `memset` variants without AVX (PLAN.md M, the PLT contracts of `launch_to_main`)

glibc 2.31's `memset-vec-unaligned-erms.S` with SSE2 vectors, `[0x65c650, 0x65c7a7)` in `7zzs` (`ms2`): at `+0`
`__memset_sse2_unaligned`, at `+80` `__memset_erms`, at `+112` `__memset_sse2_unaligned_erms`, the three variants that
the IFUNC resolver at `0x636b20` may pick on a processor without AVX2. What each instruction decodes to on every
processor (`d<offset>`, by evaluation) and straight-line stretches as `BlkV`s (`b<start>`). From the decoder's output
(`decshow`). The stores of `xmm0` and the jumps are steps of their own (`Lemmas/StoreX.lean`).
-/
namespace FV7z.Memset
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (intro feat f; rfl))

/-- The bytes of `memset`'s variants without AVX. -/
def ms2 : List Byte := [
  0xf3, 0x0f, 0x1e, 0xfa, 0x66, 0x0f, 0x6e, 0xc6, 0x48, 0x89, 0xf8, 0x66, 0x0f, 0x60, 0xc0, 0x66,
  0x0f, 0x61, 0xc0, 0x66, 0x0f, 0x70, 0xc0, 0x00, 0x48, 0x83, 0xfa, 0x10, 0x0f, 0x82, 0x03, 0x01,
  0x00, 0x00, 0x48, 0x83, 0xfa, 0x20, 0x0f, 0x87, 0x80, 0x00, 0x00, 0x00, 0xf3, 0x0f, 0x7f, 0x44,
  0x17, 0xf0, 0xf3, 0x0f, 0x7f, 0x07, 0xc3, 0x66, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x39, 0xd1, 0x0f, 0x82, 0xf3, 0xd0, 0x00, 0x00, 0x0f, 0x1f, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x48, 0x85, 0xd2, 0x75, 0x04, 0x48, 0x89, 0xf8, 0xc3, 0x48, 0x89, 0xd1,
  0x40, 0x0f, 0xb6, 0xc6, 0x48, 0x89, 0xfa, 0xf3, 0xaa, 0x48, 0x89, 0xd0, 0xc3, 0x0f, 0x1f, 0x00,
  0xf3, 0x0f, 0x1e, 0xfa, 0x66, 0x0f, 0x6e, 0xc6, 0x48, 0x89, 0xf8, 0x66, 0x0f, 0x60, 0xc0, 0x66,
  0x0f, 0x61, 0xc0, 0x66, 0x0f, 0x70, 0xc0, 0x00, 0x48, 0x83, 0xfa, 0x10, 0x0f, 0x82, 0x93, 0x00,
  0x00, 0x00, 0x48, 0x83, 0xfa, 0x20, 0x77, 0x0b, 0xf3, 0x0f, 0x7f, 0x44, 0x17, 0xf0, 0xf3, 0x0f,
  0x7f, 0x07, 0xc3, 0x48, 0x81, 0xfa, 0x00, 0x08, 0x00, 0x00, 0x77, 0xb1, 0x48, 0x83, 0xfa, 0x40,
  0x77, 0x16, 0xf3, 0x0f, 0x7f, 0x07, 0xf3, 0x0f, 0x7f, 0x47, 0x10, 0xf3, 0x0f, 0x7f, 0x44, 0x17,
  0xf0, 0xf3, 0x0f, 0x7f, 0x44, 0x17, 0xe0, 0xc3, 0x48, 0x8d, 0x4f, 0x40, 0xf3, 0x0f, 0x7f, 0x07,
  0x48, 0x83, 0xe1, 0xc0, 0xf3, 0x0f, 0x7f, 0x44, 0x17, 0xf0, 0xf3, 0x0f, 0x7f, 0x47, 0x10, 0xf3,
  0x0f, 0x7f, 0x44, 0x17, 0xe0, 0xf3, 0x0f, 0x7f, 0x47, 0x20, 0xf3, 0x0f, 0x7f, 0x44, 0x17, 0xd0,
  0xf3, 0x0f, 0x7f, 0x47, 0x30, 0xf3, 0x0f, 0x7f, 0x44, 0x17, 0xc0, 0x48, 0x01, 0xfa, 0x48, 0x83,
  0xe2, 0xc0, 0x48, 0x39, 0xd1, 0x74, 0xc0, 0x66, 0x0f, 0x7f, 0x01, 0x66, 0x0f, 0x7f, 0x41, 0x10,
  0x66, 0x0f, 0x7f, 0x41, 0x20, 0x66, 0x0f, 0x7f, 0x41, 0x30, 0x48, 0x83, 0xc1, 0x40, 0x48, 0x39,
  0xca, 0x75, 0xe4, 0xf3, 0xc3, 0x66, 0x48, 0x0f, 0x7e, 0xc1, 0x80, 0xfa, 0x08, 0x73, 0x0f, 0x80,
  0xfa, 0x04, 0x73, 0x13, 0x80, 0xfa, 0x01, 0x77, 0x15, 0x72, 0x02, 0x88, 0x0f, 0xc3, 0x48, 0x89,
  0x4c, 0x17, 0xf8, 0x48, 0x89, 0x0f, 0xc3, 0x89, 0x4c, 0x17, 0xfc, 0x89, 0x0f, 0xc3, 0x66, 0x89,
  0x4c, 0x17, 0xfe, 0x66, 0x89, 0x0f, 0xc3]

theorem ms2_length : ms2.length = 343 := rfl

theorem d80 : ∀ feat, Dec feat ms2 80 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d84 : ∀ feat, Dec feat ms2 84 (FV7z.mk .test 64 [gr 64 2, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d87 : ∀ feat, Dec feat ms2 87 (FV7z.mk (.jcc 5) 64 [.rel 4] 2) := by dec_rfl
theorem d89 : ∀ feat, Dec feat ms2 89 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d92 : ∀ feat, Dec feat ms2 92 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d93 : ∀ feat, Dec feat ms2 93 (FV7z.mk .mov 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d96 : ∀ feat, Dec feat ms2 96 (FV7z.mk .movzx 32 [gr 32 0, gr 8 6] 4) := by dec_rfl
theorem d100 : ∀ feat, Dec feat ms2 100 (FV7z.mk .mov 64 [gr 64 2, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d103 : ∀ feat, Dec feat ms2 103 (repStosb 2) := by dec_rfl
theorem d105 : ∀ feat, Dec feat ms2 105 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d108 : ∀ feat, Dec feat ms2 108 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-- The stretch from `80` to `87`. -/
def o80 : List VOp := [
  VOp.op Op.nop,
  VOp.op (Op.test 64 2 (.r 2))]

theorem b80 (prof : Profile) : BlkV prof ms2 80 87 o80 :=
  .cons (d80 _) (OpI.endbr) (by rw [ms2_length]; decide) <|
  .cons (d84 _) (OpI.test (.r 2) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 87

/-- The stretch from `89` to `92`. -/
def o89 : List VOp := [
  VOp.op (Op.mov 64 0 (.r 7))]

theorem b89 (prof : Profile) : BlkV prof ms2 89 92 o89 :=
  .cons (d89 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 92

/-- The stretch from `93` to `103`. -/
def o93 : List VOp := [
  VOp.op (Op.mov 64 1 (.r 2)),
  VOp.op (Op.zxr 0 6),
  VOp.op (Op.mov 64 2 (.r 7))]

theorem b93 (prof : Profile) : BlkV prof ms2 93 103 o93 :=
  .cons (d93 _) (OpI.mov (.r 2) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .cons (d96 _) (OpI.zxr) (by rw [ms2_length]; decide) <|
  .cons (d100 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 103

/-- The stretch from `105` to `108`. -/
def o105 : List VOp := [
  VOp.op (Op.mov 64 0 (.r 2))]

theorem b105 (prof : Profile) : BlkV prof ms2 105 108 o105 :=
  .cons (d105 _) (OpI.mov (.r 2) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 108

/-! ## `__memset_sse2_unaligned(_erms)` -/

theorem d0 : ∀ feat, Dec feat ms2 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d4 : ∀ feat, Dec feat ms2 4 (FV7z.mk (.sse (.movd)) 16 [.xmm 0, gr 32 6] 4) := by dec_rfl
theorem d8 : ∀ feat, Dec feat ms2 8 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d11 : ∀ feat, Dec feat ms2 11 (FV7z.mk (.sse (.punpcklbw)) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d15 : ∀ feat, Dec feat ms2 15 (FV7z.mk (.sse (.punpcklwd)) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d19 : ∀ feat, Dec feat ms2 19 (FV7z.mk (.sse (.pshufd)) 16 [.xmm 0, .xmm 0, .imm 8 0] 5) := by dec_rfl
theorem d24 : ∀ feat, Dec feat ms2 24 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d28 : ∀ feat, Dec feat ms2 28 (FV7z.mk (.jcc 2) 64 [.rel 259] 6) := by dec_rfl
theorem d34 : ∀ feat, Dec feat ms2 34 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem d38 : ∀ feat, Dec feat ms2 38 (FV7z.mk (.jcc 7) 64 [.rel 128] 6) := by dec_rfl
theorem d44 : ∀ feat, Dec feat ms2 44
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 0] 6) := by dec_rfl
theorem d50 : ∀ feat, Dec feat ms2 50 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 0 128), .xmm 0] 4) := by dec_rfl
theorem d54 : ∀ feat, Dec feat ms2 54 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d112 : ∀ feat, Dec feat ms2 112 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d116 : ∀ feat, Dec feat ms2 116 (FV7z.mk (.sse (.movd)) 16 [.xmm 0, gr 32 6] 4) := by dec_rfl
theorem d120 : ∀ feat, Dec feat ms2 120 (FV7z.mk .mov 64 [gr 64 0, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d123 : ∀ feat, Dec feat ms2 123 (FV7z.mk (.sse (.punpcklbw)) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d127 : ∀ feat, Dec feat ms2 127 (FV7z.mk (.sse (.punpcklwd)) 16 [.xmm 0, .xmm 0] 4) := by dec_rfl
theorem d131 : ∀ feat, Dec feat ms2 131 (FV7z.mk (.sse (.pshufd)) 16 [.xmm 0, .xmm 0, .imm 8 0] 5) := by dec_rfl
theorem d136 : ∀ feat, Dec feat ms2 136 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 16)] 4) := by dec_rfl
theorem d140 : ∀ feat, Dec feat ms2 140 (FV7z.mk (.jcc 2) 64 [.rel 147] 6) := by dec_rfl
theorem d146 : ∀ feat, Dec feat ms2 146 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 32)] 4) := by dec_rfl
theorem d150 : ∀ feat, Dec feat ms2 150 (FV7z.mk (.jcc 7) 64 [.rel 11] 2) := by dec_rfl
theorem d152 : ∀ feat, Dec feat ms2 152
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 0] 6) := by dec_rfl
theorem d158 : ∀ feat, Dec feat ms2 158 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 0 128), .xmm 0] 4) := by dec_rfl
theorem d162 : ∀ feat, Dec feat ms2 162 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d163 : ∀ feat, Dec feat ms2 163 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 2048)] 7) := by dec_rfl
theorem d170 : ∀ feat, Dec feat ms2 170 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709551537] 2) := by dec_rfl
theorem d172 : ∀ feat, Dec feat ms2 172 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.i 64)] 4) := by dec_rfl
theorem d176 : ∀ feat, Dec feat ms2 176 (FV7z.mk (.jcc 7) 64 [.rel 22] 2) := by dec_rfl
theorem d178 : ∀ feat, Dec feat ms2 178 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 0 128), .xmm 0] 4) := by dec_rfl
theorem d182 : ∀ feat, Dec feat ms2 182 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 16 128), .xmm 0] 5) := by dec_rfl
theorem d187 : ∀ feat, Dec feat ms2 187
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 0] 6) := by dec_rfl
theorem d193 : ∀ feat, Dec feat ms2 193
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551584 128), .xmm 0] 6) := by dec_rfl
theorem d199 : ∀ feat, Dec feat ms2 199 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d200 : ∀ feat, Dec feat ms2 200 (FV7z.mk .lea 64 [gr 64 1, .mem (mg (some 7) none 1 64 0)] 4) := by dec_rfl
theorem d204 : ∀ feat, Dec feat ms2 204 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 0 128), .xmm 0] 4) := by dec_rfl
theorem d208 : ∀ feat, Dec feat ms2 208
    (FV7z.mk .and 64 [gr 64 1, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem d212 : ∀ feat, Dec feat ms2 212
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 0] 6) := by dec_rfl
theorem d218 : ∀ feat, Dec feat ms2 218 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 16 128), .xmm 0] 5) := by dec_rfl
theorem d223 : ∀ feat, Dec feat ms2 223
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551584 128), .xmm 0] 6) := by dec_rfl
theorem d229 : ∀ feat, Dec feat ms2 229 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 32 128), .xmm 0] 5) := by dec_rfl
theorem d234 : ∀ feat, Dec feat ms2 234
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551568 128), .xmm 0] 6) := by dec_rfl
theorem d240 : ∀ feat, Dec feat ms2 240 (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbd 7 48 128), .xmm 0] 5) := by dec_rfl
theorem d245 : ∀ feat, Dec feat ms2 245
    (FV7z.mk (.sse (.movdqu)) 32 [.mem (mbi 7 2 18446744073709551552 128), .xmm 0] 6) := by dec_rfl
theorem d251 : ∀ feat, Dec feat ms2 251 (FV7z.mk .add 64 [gr 64 2, Src.opd 64 (.r 7)] 3) := by dec_rfl
theorem d254 : ∀ feat, Dec feat ms2 254
    (FV7z.mk .and 64 [gr 64 2, Src.opd 64 (.i 18446744073709551552)] 4) := by dec_rfl
theorem d258 : ∀ feat, Dec feat ms2 258 (FV7z.mk .cmp 64 [gr 64 1, Src.opd 64 (.r 2)] 3) := by dec_rfl
theorem d261 : ∀ feat, Dec feat ms2 261 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551552] 2) := by dec_rfl
theorem d263 : ∀ feat, Dec feat ms2 263 (FV7z.mk (.sse (.movdqa)) 16 [.mem (mbd 1 0 128), .xmm 0] 4) := by dec_rfl
theorem d267 : ∀ feat, Dec feat ms2 267 (FV7z.mk (.sse (.movdqa)) 16 [.mem (mbd 1 16 128), .xmm 0] 5) := by dec_rfl
theorem d272 : ∀ feat, Dec feat ms2 272 (FV7z.mk (.sse (.movdqa)) 16 [.mem (mbd 1 32 128), .xmm 0] 5) := by dec_rfl
theorem d277 : ∀ feat, Dec feat ms2 277 (FV7z.mk (.sse (.movdqa)) 16 [.mem (mbd 1 48 128), .xmm 0] 5) := by dec_rfl
theorem d282 : ∀ feat, Dec feat ms2 282 (FV7z.mk .add 64 [gr 64 1, Src.opd 64 (.i 64)] 4) := by dec_rfl
theorem d286 : ∀ feat, Dec feat ms2 286 (FV7z.mk .cmp 64 [gr 64 2, Src.opd 64 (.r 1)] 3) := by dec_rfl
theorem d289 : ∀ feat, Dec feat ms2 289 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551588] 2) := by dec_rfl
theorem d291 : ∀ feat, Dec feat ms2 291 (FV7z.mk .ret 64 [] 2) := by dec_rfl
theorem d293 : ∀ feat, Dec feat ms2 293 (FV7z.mk (.sse (.movq)) 64 [gr 64 1, .xmm 0] 5) := by dec_rfl
theorem d298 : ∀ feat, Dec feat ms2 298 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 8)] 3) := by dec_rfl
theorem d301 : ∀ feat, Dec feat ms2 301 (FV7z.mk (.jcc 3) 64 [.rel 15] 2) := by dec_rfl
theorem d303 : ∀ feat, Dec feat ms2 303 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 4)] 3) := by dec_rfl
theorem d306 : ∀ feat, Dec feat ms2 306 (FV7z.mk (.jcc 3) 64 [.rel 19] 2) := by dec_rfl
theorem d308 : ∀ feat, Dec feat ms2 308 (FV7z.mk .cmp 8 [gr 8 2, Src.opd 8 (.i 1)] 3) := by dec_rfl
theorem d311 : ∀ feat, Dec feat ms2 311 (FV7z.mk (.jcc 7) 64 [.rel 21] 2) := by dec_rfl
theorem d313 : ∀ feat, Dec feat ms2 313 (FV7z.mk (.jcc 2) 64 [.rel 2] 2) := by dec_rfl
theorem d315 : ∀ feat, Dec feat ms2 315 (FV7z.mk .mov 8 [.mem (mg (some 7) none 1 0 8), gr 8 1] 2) := by dec_rfl
theorem d317 : ∀ feat, Dec feat ms2 317 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d318 : ∀ feat, Dec feat ms2 318
    (FV7z.mk .mov 64 [.mem (mg (some 7) (some 2) 1 18446744073709551608 64), gr 64 1] 5) := by dec_rfl
theorem d323 : ∀ feat, Dec feat ms2 323 (FV7z.mk .mov 64 [.mem (mg (some 7) none 1 0 64), gr 64 1] 3) := by dec_rfl
theorem d326 : ∀ feat, Dec feat ms2 326 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d327 : ∀ feat, Dec feat ms2 327
    (FV7z.mk .mov 32 [.mem (mg (some 7) (some 2) 1 18446744073709551612 32), gr 32 1] 4) := by dec_rfl
theorem d331 : ∀ feat, Dec feat ms2 331 (FV7z.mk .mov 32 [.mem (mg (some 7) none 1 0 32), gr 32 1] 2) := by dec_rfl
theorem d333 : ∀ feat, Dec feat ms2 333 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d334 : ∀ feat, Dec feat ms2 334
    (FV7z.mk .mov 16 [.mem (mg (some 7) (some 2) 1 18446744073709551614 16), gr 16 1] 5) := by dec_rfl
theorem d339 : ∀ feat, Dec feat ms2 339 (FV7z.mk .mov 16 [.mem (mg (some 7) none 1 0 16), gr 16 1] 3) := by dec_rfl
theorem d342 : ∀ feat, Dec feat ms2 342 (FV7z.mk .ret 64 [] 1) := by dec_rfl

/-- The stretch from `0` to `15`. -/
def o0 : List VOp := [
  VOp.op Op.nop,
  VOp.movd 0 6,
  VOp.op (Op.mov 64 0 (.r 7)),
  VOp.punpcklbw 0 0]

theorem b0 (prof : Profile) : BlkV prof ms2 0 15 o0 :=
  .cons (d0 _) (OpI.endbr) (by rw [ms2_length]; decide) <|
  .cons (d4 _) (VOpI.movd) (by rw [ms2_length]; decide) <|
  .cons (d8 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .cons (d11 _) (VOpI.punpcklbw) (by rw [ms2_length]; decide) <|
  .nil 15

/-- The stretch from `15` to `28`. -/
def o15 : List VOp := [
  VOp.punpcklwd 0 0,
  VOp.pshufd 0 0 0,
  VOp.op (Op.cmp 64 2 (.i 16))]

theorem b15 (prof : Profile) : BlkV prof ms2 15 28 o15 :=
  .cons (d15 _) (VOpI.punpcklwd) (by rw [ms2_length]; decide) <|
  .cons (d19 _) (VOpI.pshufd) (by rw [ms2_length]; decide) <|
  .cons (d24 _) (OpI.cmp (.i 16) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 28

/-- The stretch from `34` to `38`. -/
def o34 : List VOp := [
  VOp.op (Op.cmp 64 2 (.i 32))]

theorem b34 (prof : Profile) : BlkV prof ms2 34 38 o34 :=
  .cons (d34 _) (OpI.cmp (.i 32) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 38

/-- The stretch from `112` to `127`. -/
def o112 : List VOp := [
  VOp.op Op.nop,
  VOp.movd 0 6,
  VOp.op (Op.mov 64 0 (.r 7)),
  VOp.punpcklbw 0 0]

theorem b112 (prof : Profile) : BlkV prof ms2 112 127 o112 :=
  .cons (d112 _) (OpI.endbr) (by rw [ms2_length]; decide) <|
  .cons (d116 _) (VOpI.movd) (by rw [ms2_length]; decide) <|
  .cons (d120 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .cons (d123 _) (VOpI.punpcklbw) (by rw [ms2_length]; decide) <|
  .nil 127

/-- The stretch from `127` to `140`. -/
def o127 : List VOp := [
  VOp.punpcklwd 0 0,
  VOp.pshufd 0 0 0,
  VOp.op (Op.cmp 64 2 (.i 16))]

theorem b127 (prof : Profile) : BlkV prof ms2 127 140 o127 :=
  .cons (d127 _) (VOpI.punpcklwd) (by rw [ms2_length]; decide) <|
  .cons (d131 _) (VOpI.pshufd) (by rw [ms2_length]; decide) <|
  .cons (d136 _) (OpI.cmp (.i 16) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 140

/-- The stretch from `146` to `150`. -/
def o146 : List VOp := [
  VOp.op (Op.cmp 64 2 (.i 32))]

theorem b146 (prof : Profile) : BlkV prof ms2 146 150 o146 :=
  .cons (d146 _) (OpI.cmp (.i 32) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 150

/-- The stretch from `163` to `170`. -/
def o163 : List VOp := [
  VOp.op (Op.cmp 64 2 (.i 2048))]

theorem b163 (prof : Profile) : BlkV prof ms2 163 170 o163 :=
  .cons (d163 _) (OpI.cmp (.i 2048) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 170

/-- The stretch from `172` to `176`. -/
def o172 : List VOp := [
  VOp.op (Op.cmp 64 2 (.i 64))]

theorem b172 (prof : Profile) : BlkV prof ms2 172 176 o172 :=
  .cons (d172 _) (OpI.cmp (.i 64) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 176

/-- The stretch from `200` to `204`. -/
def o200 : List VOp := [
  VOp.op (Op.lea 64 1 (some 7) none 1 64)]

theorem b200 (prof : Profile) : BlkV prof ms2 200 204 o200 :=
  .cons (d200 _) (OpI.lea (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 204

/-- The stretch from `208` to `212`. -/
def o208 : List VOp := [
  VOp.op (Op.and 64 1 (.i 18446744073709551552))]

theorem b208 (prof : Profile) : BlkV prof ms2 208 212 o208 :=
  .cons (d208 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 212

/-- The stretch from `251` to `261`. -/
def o251 : List VOp := [
  VOp.op (Op.add 64 2 (.r 7)),
  VOp.op (Op.and 64 2 (.i 18446744073709551552)),
  VOp.op (Op.cmp 64 1 (.r 2))]

theorem b251 (prof : Profile) : BlkV prof ms2 251 261 o251 :=
  .cons (d251 _) (OpI.add (.r 7) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .cons (d254 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .cons (d258 _) (OpI.cmp (.r 2) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 261

/-- The stretch from `282` to `289`. -/
def o282 : List VOp := [
  VOp.op (Op.add 64 1 (.i 64)),
  VOp.op (Op.cmp 64 2 (.r 1))]

theorem b282 (prof : Profile) : BlkV prof ms2 282 289 o282 :=
  .cons (d282 _) (OpI.add (.i 64) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .cons (d286 _) (OpI.cmp (.r 1) (.inr rfl)) (by rw [ms2_length]; decide) <|
  .nil 289

/-- The stretch from `293` to `301`. -/
def o293 : List VOp := [
  VOp.movqr 1 0,
  VOp.op (Op.cmp 8 2 (.i 8))]

theorem b293 (prof : Profile) : BlkV prof ms2 293 301 o293 :=
  .cons (d293 _) (VOpI.movqr) (by rw [ms2_length]; decide) <|
  .cons (d298 _) (OpI.cmp8 (.i 8)) (by rw [ms2_length]; decide) <|
  .nil 301

/-- The stretch from `303` to `306`. -/
def o303 : List VOp := [
  VOp.op (Op.cmp 8 2 (.i 4))]

theorem b303 (prof : Profile) : BlkV prof ms2 303 306 o303 :=
  .cons (d303 _) (OpI.cmp8 (.i 4)) (by rw [ms2_length]; decide) <|
  .nil 306

/-- The stretch from `308` to `311`. -/
def o308 : List VOp := [
  VOp.op (Op.cmp 8 2 (.i 1))]

theorem b308 (prof : Profile) : BlkV prof ms2 308 311 o308 :=
  .cons (d308 _) (OpI.cmp8 (.i 1)) (by rw [ms2_length]; decide) <|
  .nil 311

/-- The stretch from `315` to `317`. -/
def o315 : List VOp := [
  VOp.op (Op.st 8 (some 7) none 1 0 1)]

theorem b315 (prof : Profile) : BlkV prof ms2 315 317 o315 :=
  .cons (d315 _) (OpI.st (.inl rfl)) (by rw [ms2_length]; decide) <|
  .nil 317

/-- The stretch from `318` to `326`. -/
def o318 : List VOp := [
  VOp.op (Op.st 64 (some 7) (some 2) 1 18446744073709551608 1),
  VOp.op (Op.st 64 (some 7) none 1 0 1)]

theorem b318 (prof : Profile) : BlkV prof ms2 318 326 o318 :=
  .cons (d318 _) (OpI.st (.inr (.inr (.inr rfl)))) (by rw [ms2_length]; decide) <|
  .cons (d323 _) (OpI.st (.inr (.inr (.inr rfl)))) (by rw [ms2_length]; decide) <|
  .nil 326

/-- The stretch from `327` to `333`. -/
def o327 : List VOp := [
  VOp.op (Op.st 32 (some 7) (some 2) 1 18446744073709551612 1),
  VOp.op (Op.st 32 (some 7) none 1 0 1)]

theorem b327 (prof : Profile) : BlkV prof ms2 327 333 o327 :=
  .cons (d327 _) (OpI.st (.inr (.inr (.inl rfl)))) (by rw [ms2_length]; decide) <|
  .cons (d331 _) (OpI.st (.inr (.inr (.inl rfl)))) (by rw [ms2_length]; decide) <|
  .nil 333

/-- The stretch from `334` to `342`. -/
def o334 : List VOp := [
  VOp.op (Op.st 16 (some 7) (some 2) 1 18446744073709551614 1),
  VOp.op (Op.st 16 (some 7) none 1 0 1)]

theorem b334 (prof : Profile) : BlkV prof ms2 334 342 o334 :=
  .cons (d334 _) (OpI.st (.inr (.inl rfl))) (by rw [ms2_length]; decide) <|
  .cons (d339 _) (OpI.st (.inr (.inl rfl))) (by rw [ms2_length]; decide) <|
  .nil 342

end FV7z.Memset
