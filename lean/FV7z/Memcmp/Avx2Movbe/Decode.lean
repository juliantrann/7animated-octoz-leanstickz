import FV7z.Memcmp.Avx2Movbe.Code
import FV7z.Memcmp.Call
/-!
# `__memcmp_avx2_movbe` of `7zzs`: what its instructions decode to (PLAN.md G2.1)

At each instruction's offset in `avx2Movbe`, on a processor with AVX, AVX2 and MOVBE (`Feat`), the instruction Zellic's
decoder makes of the bytes, whatever bytes follow the code (`MemcmpCall.Dec`), by evaluation (`rfl`). `TZCNT`
decodes as `BSF` on a processor without BMI1 (`d272`, …): both, by the processor's `bmi1`. Generated from
`objdump -d` offsets and the decoder's own output; the padding (`nop`) after the last `ret` is never run.
-/
namespace FV7z.MemcmpAvx2
set_option maxRecDepth 20000
open ZellicX86 Decode MemcmpCall

/-- The processor features `__memcmp_avx2_movbe` needs, as glibc's IFUNC resolver checks them. -/
structure Feat (feat : Features) : Prop where
  avx : feat.avx = true
  avx2 : feat.avx2 = true
  movbe : feat.movbe = true

/-- Decoding at a fixed offset, by evaluation. -/
macro "dec_rfl" : tactic => `(tactic| (rintro feat ⟨h1, h2, h3⟩ f; cases feat; simp only at h1 h2 h3; subst h1 h2 h3; rfl))

/-- `TZCNT` or `BSF`, by the processor's `bmi1`. -/
macro "dec_bit" : tactic =>
  `(tactic| (rintro feat ⟨h1, h2, h3⟩; cases hb : feat.bmi1 <;> cases feat <;> simp only at h1 h2 h3 hb <;> subst h1 h2 h3 hb <;> (first | exact Or.inr fun _ => rfl | exact Or.inl fun _ => rfl)))


theorem d0 : ∀ feat, Feat feat → Dec feat avx2Movbe 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem d4 : ∀ feat, Feat feat → Dec feat avx2Movbe 4 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 32] 4) := by dec_rfl
theorem d8 : ∀ feat, Feat feat → Dec feat avx2Movbe 8 (FV7z.mk (.jcc 2) 64 [.rel 418] 6) := by dec_rfl
theorem d14 : ∀ feat, Feat feat → Dec feat avx2Movbe 14 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d18 : ∀ feat, Feat feat → Dec feat avx2Movbe 18 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d22 : ∀ feat, Feat feat → Dec feat avx2Movbe 22 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d26 : ∀ feat, Feat feat → Dec feat avx2Movbe 26 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d29 : ∀ feat, Feat feat → Dec feat avx2Movbe 29 (FV7z.mk (.jcc 5) 64 [.rel 237] 6) := by dec_rfl
theorem d35 : ∀ feat, Feat feat → Dec feat avx2Movbe 35 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d39 : ∀ feat, Feat feat → Dec feat avx2Movbe 39 (FV7z.mk (.jcc 6) 64 [.rel 196] 6) := by dec_rfl
theorem d45 : ∀ feat, Feat feat → Dec feat avx2Movbe 45 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 0 256, .vreg 0 256, .vreg 0 256] 4) := by dec_rfl
theorem d49 : ∀ feat, Feat feat → Dec feat avx2Movbe 49 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 256] 7) := by dec_rfl
theorem d56 : ∀ feat, Feat feat → Dec feat avx2Movbe 56 (FV7z.mk (.jcc 7) 64 [.rel 530] 6) := by dec_rfl
theorem d62 : ∀ feat, Feat feat → Dec feat avx2Movbe 62 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 128] 7) := by dec_rfl
theorem d69 : ∀ feat, Feat feat → Dec feat avx2Movbe 69 (FV7z.mk (.jcc 2) 64 [.rel 668] 6) := by dec_rfl
theorem d75 : ∀ feat, Feat feat → Dec feat avx2Movbe 75 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 1 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d79 : ∀ feat, Feat feat → Dec feat avx2Movbe 79 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 1 256, .vreg 1 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d83 : ∀ feat, Feat feat → Dec feat avx2Movbe 83 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 32 256)] 5) := by dec_rfl
theorem d88 : ∀ feat, Feat feat → Dec feat avx2Movbe 88 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 32 256)] 5) := by dec_rfl
theorem d93 : ∀ feat, Feat feat → Dec feat avx2Movbe 93 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 3 256, .mem (mbd 6 64 256)] 5) := by dec_rfl
theorem d98 : ∀ feat, Feat feat → Dec feat avx2Movbe 98 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 3 256, .vreg 3 256, .mem (mbd 7 64 256)] 5) := by dec_rfl
theorem d103 : ∀ feat, Feat feat → Dec feat avx2Movbe 103 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 4 256, .mem (mbd 6 96 256)] 5) := by dec_rfl
theorem d108 : ∀ feat, Feat feat → Dec feat avx2Movbe 108 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 4 256, .vreg 4 256, .mem (mbd 7 96 256)] 5) := by dec_rfl
theorem d113 : ∀ feat, Feat feat → Dec feat avx2Movbe 113 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 2 256, .vreg 1 256] 4) := by dec_rfl
theorem d117 : ∀ feat, Feat feat → Dec feat avx2Movbe 117 (FV7z.mk (.avx (.vpand)) 32 [.vreg 6 256, .vreg 4 256, .vreg 3 256] 4) := by dec_rfl
theorem d121 : ∀ feat, Feat feat → Dec feat avx2Movbe 121 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 6 256, .vreg 5 256] 4) := by dec_rfl
theorem d125 : ∀ feat, Feat feat → Dec feat avx2Movbe 125 (FV7z.mk (.avx (.vptest)) 32 [.vreg 5 256, .vreg 0 256] 5) := by dec_rfl
theorem d130 : ∀ feat, Feat feat → Dec feat avx2Movbe 130 (FV7z.mk (.jcc 3) 64 [.rel 728] 6) := by dec_rfl
theorem d136 : ∀ feat, Feat feat → Dec feat avx2Movbe 136 (FV7z.mk .lea 64 [gr 64 7, .mem (mbi 7 2 18446744073709551488 0)] 5) := by dec_rfl
theorem d141 : ∀ feat, Feat feat → Dec feat avx2Movbe 141 (FV7z.mk .lea 64 [gr 64 6, .mem (mbi 6 2 18446744073709551488 0)] 5) := by dec_rfl
theorem d146 : ∀ feat, Feat feat → Dec feat avx2Movbe 146 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 1 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d150 : ∀ feat, Feat feat → Dec feat avx2Movbe 150 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 1 256, .vreg 1 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d154 : ∀ feat, Feat feat → Dec feat avx2Movbe 154 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 32 256)] 5) := by dec_rfl
theorem d159 : ∀ feat, Feat feat → Dec feat avx2Movbe 159 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 32 256)] 5) := by dec_rfl
theorem d164 : ∀ feat, Feat feat → Dec feat avx2Movbe 164 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 1 256, .vreg 2 256] 4) := by dec_rfl
theorem d168 : ∀ feat, Feat feat → Dec feat avx2Movbe 168 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 3 256, .mem (mbd 6 64 256)] 5) := by dec_rfl
theorem d173 : ∀ feat, Feat feat → Dec feat avx2Movbe 173 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 3 256, .vreg 3 256, .mem (mbd 7 64 256)] 5) := by dec_rfl
theorem d178 : ∀ feat, Feat feat → Dec feat avx2Movbe 178 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 5 256, .vreg 3 256] 4) := by dec_rfl
theorem d182 : ∀ feat, Feat feat → Dec feat avx2Movbe 182 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 4 256, .mem (mbd 6 96 256)] 5) := by dec_rfl
theorem d187 : ∀ feat, Feat feat → Dec feat avx2Movbe 187 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 4 256, .vreg 4 256, .mem (mbd 7 96 256)] 5) := by dec_rfl
theorem d192 : ∀ feat, Feat feat → Dec feat avx2Movbe 192 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 5 256, .vreg 4 256] 4) := by dec_rfl
theorem d196 : ∀ feat, Feat feat → Dec feat avx2Movbe 196 (FV7z.mk (.avx (.vptest)) 32 [.vreg 5 256, .vreg 0 256] 5) := by dec_rfl
theorem d201 : ∀ feat, Feat feat → Dec feat avx2Movbe 201 (FV7z.mk (.jcc 3) 64 [.rel 657] 6) := by dec_rfl
theorem d207 : ∀ feat, Feat feat → Dec feat avx2Movbe 207 (FV7z.mk .xor 32 [gr 32 0, gr 32 0] 2) := by dec_rfl
theorem d209 : ∀ feat, Feat feat → Dec feat avx2Movbe 209 (FV7z.mk (.avx (.vzeroupper)) 32 [] 3) := by dec_rfl
theorem d212 : ∀ feat, Feat feat → Dec feat avx2Movbe 212 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d224 : ∀ feat, Feat feat → Dec feat avx2Movbe 224 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d228 : ∀ feat, Feat feat → Dec feat avx2Movbe 228 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d232 : ∀ feat, Feat feat → Dec feat avx2Movbe 232 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d236 : ∀ feat, Feat feat → Dec feat avx2Movbe 236 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d239 : ∀ feat, Feat feat → Dec feat avx2Movbe 239 (FV7z.mk (.jcc 5) 64 [.rel 31] 2) := by dec_rfl
theorem d241 : ∀ feat, Feat feat → Dec feat avx2Movbe 241 (FV7z.mk .lea 64 [gr 64 7, .mem (mbi 7 2 18446744073709551584 0)] 5) := by dec_rfl
theorem d246 : ∀ feat, Feat feat → Dec feat avx2Movbe 246 (FV7z.mk .lea 64 [gr 64 6, .mem (mbi 6 2 18446744073709551584 0)] 5) := by dec_rfl
theorem d251 : ∀ feat, Feat feat → Dec feat avx2Movbe 251 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d255 : ∀ feat, Feat feat → Dec feat avx2Movbe 255 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d259 : ∀ feat, Feat feat → Dec feat avx2Movbe 259 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d263 : ∀ feat, Feat feat → Dec feat avx2Movbe 263 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d266 : ∀ feat, Feat feat → Dec feat avx2Movbe 266 (FV7z.mk (.jcc 5) 64 [.rel 4] 2) := by dec_rfl
theorem d268 : ∀ feat, Feat feat → Dec feat avx2Movbe 268 (FV7z.mk (.avx (.vzeroupper)) 32 [] 3) := by dec_rfl
theorem d271 : ∀ feat, Feat feat → Dec feat avx2Movbe 271 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d272 : ∀ feat, Feat feat → Dec feat avx2Movbe 272 (FV7z.mk (.bit (.tzcnt)) 32 [gr 32 1, gr 32 0] 4) ∨
    Dec feat avx2Movbe 272 (FV7z.mk (.bit (.bsf)) 32 [gr 32 1, gr 32 0] 4) := by dec_bit
theorem d276 : ∀ feat, Feat feat → Dec feat avx2Movbe 276 (FV7z.mk .movzx 32 [gr 32 0, .mem (mbi 7 1 0 8)] 4) := by dec_rfl
theorem d280 : ∀ feat, Feat feat → Dec feat avx2Movbe 280 (FV7z.mk .movzx 32 [gr 32 2, .mem (mbi 6 1 0 8)] 4) := by dec_rfl
theorem d284 : ∀ feat, Feat feat → Dec feat avx2Movbe 284 (FV7z.mk .sub 32 [gr 32 0, gr 32 2] 2) := by dec_rfl
theorem d286 : ∀ feat, Feat feat → Dec feat avx2Movbe 286 (FV7z.mk (.avx (.vzeroupper)) 32 [] 3) := by dec_rfl
theorem d289 : ∀ feat, Feat feat → Dec feat avx2Movbe 289 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d304 : ∀ feat, Feat feat → Dec feat avx2Movbe 304 (FV7z.mk .movbe 32 [gr 32 0, .mem (mbd 7 0 32)] 4) := by dec_rfl
theorem d308 : ∀ feat, Feat feat → Dec feat avx2Movbe 308 (FV7z.mk .movbe 32 [gr 32 1, .mem (mbd 6 0 32)] 4) := by dec_rfl
theorem d312 : ∀ feat, Feat feat → Dec feat avx2Movbe 312 (FV7z.mk .shl 64 [gr 64 0, .imm 8 32] 4) := by dec_rfl
theorem d316 : ∀ feat, Feat feat → Dec feat avx2Movbe 316 (FV7z.mk .shl 64 [gr 64 1, .imm 8 32] 4) := by dec_rfl
theorem d320 : ∀ feat, Feat feat → Dec feat avx2Movbe 320 (FV7z.mk .movbe 32 [gr 32 7, .mem (mbi 7 2 18446744073709551612 32)] 6) := by dec_rfl
theorem d326 : ∀ feat, Feat feat → Dec feat avx2Movbe 326 (FV7z.mk .movbe 32 [gr 32 6, .mem (mbi 6 2 18446744073709551612 32)] 6) := by dec_rfl
theorem d332 : ∀ feat, Feat feat → Dec feat avx2Movbe 332 (FV7z.mk .or 64 [gr 64 0, gr 64 7] 3) := by dec_rfl
theorem d335 : ∀ feat, Feat feat → Dec feat avx2Movbe 335 (FV7z.mk .or 64 [gr 64 1, gr 64 6] 3) := by dec_rfl
theorem d338 : ∀ feat, Feat feat → Dec feat avx2Movbe 338 (FV7z.mk .sub 64 [gr 64 0, gr 64 1] 3) := by dec_rfl
theorem d341 : ∀ feat, Feat feat → Dec feat avx2Movbe 341 (FV7z.mk (.jcc 4) 64 [.rel 9] 2) := by dec_rfl
theorem d343 : ∀ feat, Feat feat → Dec feat avx2Movbe 343 (FV7z.mk .sbb 32 [gr 32 0, gr 32 0] 2) := by dec_rfl
theorem d345 : ∀ feat, Feat feat → Dec feat avx2Movbe 345 (FV7z.mk .or 32 [gr 32 0, .imm 32 1] 3) := by dec_rfl
theorem d348 : ∀ feat, Feat feat → Dec feat avx2Movbe 348 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d352 : ∀ feat, Feat feat → Dec feat avx2Movbe 352 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d368 : ∀ feat, Feat feat → Dec feat avx2Movbe 368 (FV7z.mk .movzx 32 [gr 32 0, .mem (mbd 7 0 16)] 3) := by dec_rfl
theorem d371 : ∀ feat, Feat feat → Dec feat avx2Movbe 371 (FV7z.mk .movzx 32 [gr 32 1, .mem (mbd 6 0 16)] 3) := by dec_rfl
theorem d374 : ∀ feat, Feat feat → Dec feat avx2Movbe 374 (FV7z.mk .shl 32 [gr 32 0, .imm 8 8] 3) := by dec_rfl
theorem d377 : ∀ feat, Feat feat → Dec feat avx2Movbe 377 (FV7z.mk .shl 32 [gr 32 1, .imm 8 8] 3) := by dec_rfl
theorem d380 : ∀ feat, Feat feat → Dec feat avx2Movbe 380 (FV7z.mk .bswap 32 [gr 32 0] 2) := by dec_rfl
theorem d382 : ∀ feat, Feat feat → Dec feat avx2Movbe 382 (FV7z.mk .bswap 32 [gr 32 1] 2) := by dec_rfl
theorem d384 : ∀ feat, Feat feat → Dec feat avx2Movbe 384 (FV7z.mk .mov 8 [gr 8 0, .mem (mbi 7 2 18446744073709551615 8)] 4) := by dec_rfl
theorem d388 : ∀ feat, Feat feat → Dec feat avx2Movbe 388 (FV7z.mk .mov 8 [gr 8 1, .mem (mbi 6 2 18446744073709551615 8)] 4) := by dec_rfl
theorem d392 : ∀ feat, Feat feat → Dec feat avx2Movbe 392 (FV7z.mk .sub 32 [gr 32 0, gr 32 1] 2) := by dec_rfl
theorem d394 : ∀ feat, Feat feat → Dec feat avx2Movbe 394 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d400 : ∀ feat, Feat feat → Dec feat avx2Movbe 400 (FV7z.mk .movzx 32 [gr 32 0, .mem (mbd 7 0 8)] 3) := by dec_rfl
theorem d403 : ∀ feat, Feat feat → Dec feat avx2Movbe 403 (FV7z.mk .movzx 32 [gr 32 1, .mem (mbd 6 0 8)] 3) := by dec_rfl
theorem d406 : ∀ feat, Feat feat → Dec feat avx2Movbe 406 (FV7z.mk .sub 32 [gr 32 0, gr 32 1] 2) := by dec_rfl
theorem d408 : ∀ feat, Feat feat → Dec feat avx2Movbe 408 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d416 : ∀ feat, Feat feat → Dec feat avx2Movbe 416 (FV7z.mk .xor 32 [gr 32 0, gr 32 0] 2) := by dec_rfl
theorem d418 : ∀ feat, Feat feat → Dec feat avx2Movbe 418 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d432 : ∀ feat, Feat feat → Dec feat avx2Movbe 432 (FV7z.mk .cmp 8 [gr 8 2, .imm 8 1] 3) := by dec_rfl
theorem d435 : ∀ feat, Feat feat → Dec feat avx2Movbe 435 (FV7z.mk (.jcc 4) 64 [.rel 18446744073709551579] 2) := by dec_rfl
theorem d437 : ∀ feat, Feat feat → Dec feat avx2Movbe 437 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551593] 2) := by dec_rfl
theorem d439 : ∀ feat, Feat feat → Dec feat avx2Movbe 439 (FV7z.mk .cmp 8 [gr 8 2, .imm 8 4] 3) := by dec_rfl
theorem d442 : ∀ feat, Feat feat → Dec feat avx2Movbe 442 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551540] 2) := by dec_rfl
theorem d444 : ∀ feat, Feat feat → Dec feat avx2Movbe 444 (FV7z.mk .cmp 8 [gr 8 2, .imm 8 8] 3) := by dec_rfl
theorem d447 : ∀ feat, Feat feat → Dec feat avx2Movbe 447 (FV7z.mk (.jcc 2) 64 [.rel 18446744073709551467] 6) := by dec_rfl
theorem d453 : ∀ feat, Feat feat → Dec feat avx2Movbe 453 (FV7z.mk .cmp 8 [gr 8 2, .imm 8 16] 3) := by dec_rfl
theorem d456 : ∀ feat, Feat feat → Dec feat avx2Movbe 456 (FV7z.mk (.jcc 3) 64 [.rel 70] 2) := by dec_rfl
theorem d458 : ∀ feat, Feat feat → Dec feat avx2Movbe 458 (FV7z.mk (.avx (.vmovq)) 32 [.vreg 1 128, .mem (mbd 7 0 64)] 4) := by dec_rfl
theorem d462 : ∀ feat, Feat feat → Dec feat avx2Movbe 462 (FV7z.mk (.avx (.vmovq)) 32 [.vreg 2 128, .mem (mbd 6 0 64)] 4) := by dec_rfl
theorem d466 : ∀ feat, Feat feat → Dec feat avx2Movbe 466 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 128, .vreg 2 128, .vreg 1 128] 4) := by dec_rfl
theorem d470 : ∀ feat, Feat feat → Dec feat avx2Movbe 470 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 128] 4) := by dec_rfl
theorem d474 : ∀ feat, Feat feat → Dec feat avx2Movbe 474 (FV7z.mk .sub 32 [gr 32 0, .imm 32 65535] 5) := by dec_rfl
theorem d479 : ∀ feat, Feat feat → Dec feat avx2Movbe 479 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551403] 6) := by dec_rfl
theorem d485 : ∀ feat, Feat feat → Dec feat avx2Movbe 485 (FV7z.mk .lea 64 [gr 64 7, .mem (mbi 7 2 18446744073709551608 0)] 5) := by dec_rfl
theorem d490 : ∀ feat, Feat feat → Dec feat avx2Movbe 490 (FV7z.mk .lea 64 [gr 64 6, .mem (mbi 6 2 18446744073709551608 0)] 5) := by dec_rfl
theorem d495 : ∀ feat, Feat feat → Dec feat avx2Movbe 495 (FV7z.mk (.avx (.vmovq)) 32 [.vreg 1 128, .mem (mbd 7 0 64)] 4) := by dec_rfl
theorem d499 : ∀ feat, Feat feat → Dec feat avx2Movbe 499 (FV7z.mk (.avx (.vmovq)) 32 [.vreg 2 128, .mem (mbd 6 0 64)] 4) := by dec_rfl
theorem d503 : ∀ feat, Feat feat → Dec feat avx2Movbe 503 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 128, .vreg 2 128, .vreg 1 128] 4) := by dec_rfl
theorem d507 : ∀ feat, Feat feat → Dec feat avx2Movbe 507 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 128] 4) := by dec_rfl
theorem d511 : ∀ feat, Feat feat → Dec feat avx2Movbe 511 (FV7z.mk .sub 32 [gr 32 0, .imm 32 65535] 5) := by dec_rfl
theorem d516 : ∀ feat, Feat feat → Dec feat avx2Movbe 516 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551366] 6) := by dec_rfl
theorem d522 : ∀ feat, Feat feat → Dec feat avx2Movbe 522 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d528 : ∀ feat, Feat feat → Dec feat avx2Movbe 528 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 128, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d532 : ∀ feat, Feat feat → Dec feat avx2Movbe 532 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 128, .vreg 2 128, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d536 : ∀ feat, Feat feat → Dec feat avx2Movbe 536 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 128] 4) := by dec_rfl
theorem d540 : ∀ feat, Feat feat → Dec feat avx2Movbe 540 (FV7z.mk .sub 32 [gr 32 0, .imm 32 65535] 5) := by dec_rfl
theorem d545 : ∀ feat, Feat feat → Dec feat avx2Movbe 545 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551337] 6) := by dec_rfl
theorem d551 : ∀ feat, Feat feat → Dec feat avx2Movbe 551 (FV7z.mk .lea 64 [gr 64 7, .mem (mbi 7 2 18446744073709551600 0)] 5) := by dec_rfl
theorem d556 : ∀ feat, Feat feat → Dec feat avx2Movbe 556 (FV7z.mk .lea 64 [gr 64 6, .mem (mbi 6 2 18446744073709551600 0)] 5) := by dec_rfl
theorem d561 : ∀ feat, Feat feat → Dec feat avx2Movbe 561 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 128, .mem (mbd 6 0 128)] 4) := by dec_rfl
theorem d565 : ∀ feat, Feat feat → Dec feat avx2Movbe 565 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 128, .vreg 2 128, .mem (mbd 7 0 128)] 4) := by dec_rfl
theorem d569 : ∀ feat, Feat feat → Dec feat avx2Movbe 569 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 128] 4) := by dec_rfl
theorem d573 : ∀ feat, Feat feat → Dec feat avx2Movbe 573 (FV7z.mk .sub 32 [gr 32 0, .imm 32 65535] 5) := by dec_rfl
theorem d578 : ∀ feat, Feat feat → Dec feat avx2Movbe 578 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551304] 6) := by dec_rfl
theorem d584 : ∀ feat, Feat feat → Dec feat avx2Movbe 584 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d592 : ∀ feat, Feat feat → Dec feat avx2Movbe 592 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d596 : ∀ feat, Feat feat → Dec feat avx2Movbe 596 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d600 : ∀ feat, Feat feat → Dec feat avx2Movbe 600 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d604 : ∀ feat, Feat feat → Dec feat avx2Movbe 604 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d607 : ∀ feat, Feat feat → Dec feat avx2Movbe 607 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551275] 6) := by dec_rfl
theorem d613 : ∀ feat, Feat feat → Dec feat avx2Movbe 613 (FV7z.mk .mov 64 [gr 64 1, gr 64 7] 3) := by dec_rfl
theorem d616 : ∀ feat, Feat feat → Dec feat avx2Movbe 616 (FV7z.mk .and 32 [gr 32 1, .imm 32 31] 3) := by dec_rfl
theorem d619 : ∀ feat, Feat feat → Dec feat avx2Movbe 619 (FV7z.mk .sub 64 [gr 64 1, .imm 64 32] 4) := by dec_rfl
theorem d623 : ∀ feat, Feat feat → Dec feat avx2Movbe 623 (FV7z.mk .sub 64 [gr 64 6, gr 64 1] 3) := by dec_rfl
theorem d626 : ∀ feat, Feat feat → Dec feat avx2Movbe 626 (FV7z.mk .sub 64 [gr 64 7, gr 64 1] 3) := by dec_rfl
theorem d629 : ∀ feat, Feat feat → Dec feat avx2Movbe 629 (FV7z.mk .add 64 [gr 64 2, gr 64 1] 3) := by dec_rfl
theorem d632 : ∀ feat, Feat feat → Dec feat avx2Movbe 632 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 1 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d636 : ∀ feat, Feat feat → Dec feat avx2Movbe 636 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 1 256, .vreg 1 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d640 : ∀ feat, Feat feat → Dec feat avx2Movbe 640 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 32 256)] 5) := by dec_rfl
theorem d645 : ∀ feat, Feat feat → Dec feat avx2Movbe 645 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 32 256)] 5) := by dec_rfl
theorem d650 : ∀ feat, Feat feat → Dec feat avx2Movbe 650 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 1 256, .vreg 2 256] 4) := by dec_rfl
theorem d654 : ∀ feat, Feat feat → Dec feat avx2Movbe 654 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 3 256, .mem (mbd 6 64 256)] 5) := by dec_rfl
theorem d659 : ∀ feat, Feat feat → Dec feat avx2Movbe 659 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 3 256, .vreg 3 256, .mem (mbd 7 64 256)] 5) := by dec_rfl
theorem d664 : ∀ feat, Feat feat → Dec feat avx2Movbe 664 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 5 256, .vreg 3 256] 4) := by dec_rfl
theorem d668 : ∀ feat, Feat feat → Dec feat avx2Movbe 668 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 4 256, .mem (mbd 6 96 256)] 5) := by dec_rfl
theorem d673 : ∀ feat, Feat feat → Dec feat avx2Movbe 673 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 4 256, .vreg 4 256, .mem (mbd 7 96 256)] 5) := by dec_rfl
theorem d678 : ∀ feat, Feat feat → Dec feat avx2Movbe 678 (FV7z.mk (.avx (.vpand)) 32 [.vreg 5 256, .vreg 5 256, .vreg 4 256] 4) := by dec_rfl
theorem d682 : ∀ feat, Feat feat → Dec feat avx2Movbe 682 (FV7z.mk (.avx (.vptest)) 32 [.vreg 5 256, .vreg 0 256] 5) := by dec_rfl
theorem d687 : ∀ feat, Feat feat → Dec feat avx2Movbe 687 (FV7z.mk (.jcc 3) 64 [.rel 171] 6) := by dec_rfl
theorem d693 : ∀ feat, Feat feat → Dec feat avx2Movbe 693 (FV7z.mk .add 64 [gr 64 7, .imm 64 128] 7) := by dec_rfl
theorem d700 : ∀ feat, Feat feat → Dec feat avx2Movbe 700 (FV7z.mk .add 64 [gr 64 6, .imm 64 128] 7) := by dec_rfl
theorem d707 : ∀ feat, Feat feat → Dec feat avx2Movbe 707 (FV7z.mk .sub 64 [gr 64 2, .imm 64 128] 7) := by dec_rfl
theorem d714 : ∀ feat, Feat feat → Dec feat avx2Movbe 714 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 128] 7) := by dec_rfl
theorem d721 : ∀ feat, Feat feat → Dec feat avx2Movbe 721 (FV7z.mk (.jcc 3) 64 [.rel 18446744073709551525] 2) := by dec_rfl
theorem d723 : ∀ feat, Feat feat → Dec feat avx2Movbe 723 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 32] 4) := by dec_rfl
theorem d727 : ∀ feat, Feat feat → Dec feat avx2Movbe 727 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551124] 6) := by dec_rfl
theorem d733 : ∀ feat, Feat feat → Dec feat avx2Movbe 733 (FV7z.mk .cmp 64 [gr 64 2, .imm 64 64] 4) := by dec_rfl
theorem d737 : ∀ feat, Feat feat → Dec feat avx2Movbe 737 (FV7z.mk (.jcc 6) 64 [.rel 18446744073709551097] 6) := by dec_rfl
theorem d743 : ∀ feat, Feat feat → Dec feat avx2Movbe 743 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d747 : ∀ feat, Feat feat → Dec feat avx2Movbe 747 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d751 : ∀ feat, Feat feat → Dec feat avx2Movbe 751 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d755 : ∀ feat, Feat feat → Dec feat avx2Movbe 755 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d758 : ∀ feat, Feat feat → Dec feat avx2Movbe 758 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551124] 6) := by dec_rfl
theorem d764 : ∀ feat, Feat feat → Dec feat avx2Movbe 764 (FV7z.mk .add 64 [gr 64 7, .imm 64 32] 4) := by dec_rfl
theorem d768 : ∀ feat, Feat feat → Dec feat avx2Movbe 768 (FV7z.mk .add 64 [gr 64 6, .imm 64 32] 4) := by dec_rfl
theorem d772 : ∀ feat, Feat feat → Dec feat avx2Movbe 772 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d776 : ∀ feat, Feat feat → Dec feat avx2Movbe 776 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d780 : ∀ feat, Feat feat → Dec feat avx2Movbe 780 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d784 : ∀ feat, Feat feat → Dec feat avx2Movbe 784 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d787 : ∀ feat, Feat feat → Dec feat avx2Movbe 787 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551095] 6) := by dec_rfl
theorem d793 : ∀ feat, Feat feat → Dec feat avx2Movbe 793 (FV7z.mk .lea 64 [gr 64 7, .mem (mbi 7 2 18446744073709551520 0)] 5) := by dec_rfl
theorem d798 : ∀ feat, Feat feat → Dec feat avx2Movbe 798 (FV7z.mk .lea 64 [gr 64 6, .mem (mbi 6 2 18446744073709551520 0)] 5) := by dec_rfl
theorem d803 : ∀ feat, Feat feat → Dec feat avx2Movbe 803 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d807 : ∀ feat, Feat feat → Dec feat avx2Movbe 807 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d811 : ∀ feat, Feat feat → Dec feat avx2Movbe 811 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d815 : ∀ feat, Feat feat → Dec feat avx2Movbe 815 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d818 : ∀ feat, Feat feat → Dec feat avx2Movbe 818 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551064] 6) := by dec_rfl
theorem d824 : ∀ feat, Feat feat → Dec feat avx2Movbe 824 (FV7z.mk .add 64 [gr 64 7, .imm 64 32] 4) := by dec_rfl
theorem d828 : ∀ feat, Feat feat → Dec feat avx2Movbe 828 (FV7z.mk .add 64 [gr 64 6, .imm 64 32] 4) := by dec_rfl
theorem d832 : ∀ feat, Feat feat → Dec feat avx2Movbe 832 (FV7z.mk (.avx (.vmovdqu)) 32 [.vreg 2 256, .mem (mbd 6 0 256)] 4) := by dec_rfl
theorem d836 : ∀ feat, Feat feat → Dec feat avx2Movbe 836 (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 0 256)] 4) := by dec_rfl
theorem d840 : ∀ feat, Feat feat → Dec feat avx2Movbe 840 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d844 : ∀ feat, Feat feat → Dec feat avx2Movbe 844 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d847 : ∀ feat, Feat feat → Dec feat avx2Movbe 847 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551035] 6) := by dec_rfl
theorem d853 : ∀ feat, Feat feat → Dec feat avx2Movbe 853 (FV7z.mk (.avx (.vzeroupper)) 32 [] 3) := by dec_rfl
theorem d856 : ∀ feat, Feat feat → Dec feat avx2Movbe 856 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d864 : ∀ feat, Feat feat → Dec feat avx2Movbe 864 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 1 256] 4) := by dec_rfl
theorem d868 : ∀ feat, Feat feat → Dec feat avx2Movbe 868 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d871 : ∀ feat, Feat feat → Dec feat avx2Movbe 871 (FV7z.mk (.jcc 5) 64 [.rel 18446744073709551011] 6) := by dec_rfl
theorem d877 : ∀ feat, Feat feat → Dec feat avx2Movbe 877 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 2 256] 4) := by dec_rfl
theorem d881 : ∀ feat, Feat feat → Dec feat avx2Movbe 881 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d884 : ∀ feat, Feat feat → Dec feat avx2Movbe 884 (FV7z.mk (.jcc 5) 64 [.rel 42] 2) := by dec_rfl
theorem d886 : ∀ feat, Feat feat → Dec feat avx2Movbe 886 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 3 256] 4) := by dec_rfl
theorem d890 : ∀ feat, Feat feat → Dec feat avx2Movbe 890 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d893 : ∀ feat, Feat feat → Dec feat avx2Movbe 893 (FV7z.mk (.jcc 5) 64 [.rel 65] 2) := by dec_rfl
theorem d895 : ∀ feat, Feat feat → Dec feat avx2Movbe 895 (FV7z.mk (.avx (.vpmovmskb)) 32 [gr 32 0, .vreg 4 256] 4) := by dec_rfl
theorem d899 : ∀ feat, Feat feat → Dec feat avx2Movbe 899 (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3) := by dec_rfl
theorem d902 : ∀ feat, Feat feat → Dec feat avx2Movbe 902 (FV7z.mk (.bit (.tzcnt)) 32 [gr 32 1, gr 32 0] 4) ∨
    Dec feat avx2Movbe 902 (FV7z.mk (.bit (.bsf)) 32 [gr 32 1, gr 32 0] 4) := by dec_bit
theorem d906 : ∀ feat, Feat feat → Dec feat avx2Movbe 906 (FV7z.mk .movzx 32 [gr 32 0, .mem (mbi 7 1 96 8)] 5) := by dec_rfl
theorem d911 : ∀ feat, Feat feat → Dec feat avx2Movbe 911 (FV7z.mk .movzx 32 [gr 32 2, .mem (mbi 6 1 96 8)] 5) := by dec_rfl
theorem d916 : ∀ feat, Feat feat → Dec feat avx2Movbe 916 (FV7z.mk .sub 32 [gr 32 0, gr 32 2] 2) := by dec_rfl
theorem d918 : ∀ feat, Feat feat → Dec feat avx2Movbe 918 (FV7z.mk (.avx (.vzeroupper)) 32 [] 3) := by dec_rfl
theorem d921 : ∀ feat, Feat feat → Dec feat avx2Movbe 921 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d928 : ∀ feat, Feat feat → Dec feat avx2Movbe 928 (FV7z.mk (.bit (.tzcnt)) 32 [gr 32 1, gr 32 0] 4) ∨
    Dec feat avx2Movbe 928 (FV7z.mk (.bit (.bsf)) 32 [gr 32 1, gr 32 0] 4) := by dec_bit
theorem d932 : ∀ feat, Feat feat → Dec feat avx2Movbe 932 (FV7z.mk .movzx 32 [gr 32 0, .mem (mbi 7 1 32 8)] 5) := by dec_rfl
theorem d937 : ∀ feat, Feat feat → Dec feat avx2Movbe 937 (FV7z.mk .movzx 32 [gr 32 2, .mem (mbi 6 1 32 8)] 5) := by dec_rfl
theorem d942 : ∀ feat, Feat feat → Dec feat avx2Movbe 942 (FV7z.mk .sub 32 [gr 32 0, gr 32 2] 2) := by dec_rfl
theorem d944 : ∀ feat, Feat feat → Dec feat avx2Movbe 944 (FV7z.mk (.avx (.vzeroupper)) 32 [] 3) := by dec_rfl
theorem d947 : ∀ feat, Feat feat → Dec feat avx2Movbe 947 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem d960 : ∀ feat, Feat feat → Dec feat avx2Movbe 960 (FV7z.mk (.bit (.tzcnt)) 32 [gr 32 1, gr 32 0] 4) ∨
    Dec feat avx2Movbe 960 (FV7z.mk (.bit (.bsf)) 32 [gr 32 1, gr 32 0] 4) := by dec_bit
theorem d964 : ∀ feat, Feat feat → Dec feat avx2Movbe 964 (FV7z.mk .movzx 32 [gr 32 0, .mem (mbi 7 1 64 8)] 5) := by dec_rfl
theorem d969 : ∀ feat, Feat feat → Dec feat avx2Movbe 969 (FV7z.mk .movzx 32 [gr 32 2, .mem (mbi 6 1 64 8)] 5) := by dec_rfl
theorem d974 : ∀ feat, Feat feat → Dec feat avx2Movbe 974 (FV7z.mk .sub 32 [gr 32 0, gr 32 2] 2) := by dec_rfl
theorem d976 : ∀ feat, Feat feat → Dec feat avx2Movbe 976 (FV7z.mk (.avx (.vzeroupper)) 32 [] 3) := by dec_rfl
theorem d979 : ∀ feat, Feat feat → Dec feat avx2Movbe 979 (FV7z.mk .ret 64 [] 1) := by dec_rfl

end FV7z.MemcmpAvx2
