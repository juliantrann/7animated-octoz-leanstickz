import FV7z.Strncmp.Code
import FV7z.Lemmas.Sse2b
/-!
# The shifted loops of `__strncmp_sse2` (PLAN.md G3, `strncmp`)

When the two strings' offsets in their 16 bytes differ, `__strncmp_sse2` swaps them so that `rsi`'s is the greater, by
`k = 16 - (rsi's - rdi's)` jumps by its table to one of 15 loops at `c = 400 + 384 * (k - 1)`, and compares `rsi`'s
aligned vectors with `rdi`'s shifted by `16 - k` bytes (`psrldq`, `pslldq`, `por`). The loops share one layout: the
template's straight-line pieces as `VOp` lists of `k` (`A<offset>`, the offset in the loop's code), its jumps
(`JccAt`, `JmpAt`), and its end (`TailC`: for `k < 15` a jump to the shared end at `6144`, for `k = 15` the shared end
itself); `AshrC prof k c e` gathers them, `e` 4 (0 for `k = 15`, whose `jne` at 268 is short and what follows
it up to 304 four bytes earlier).
Generated from the decoder's output (`decshow`) by `tools/strncmp_gen.py`.
-/
namespace FV7z.Strncmp
set_option maxRecDepth 20000
open ZellicX86 Decode FV7z.Leaf


/-- The template's piece from `0` to `25`. -/
def A0 (k : Nat) : List VOp := [
  VOp.pxor 0 0,
  VOp.movdqa_m 2 7 0,
  VOp.movdqa_m 1 6 0,
  VOp.pcmpeqb 0 1,
  VOp.pslldq 2 (16 - k),
  VOp.pcmpeqb 2 1]

/-- The template's piece from `25` to `42`. -/
def A25 : List VOp := [
  VOp.psubb 2 0,
  VOp.pmovmskb 9 2,
  VOp.op (Op.shr 2 (.r 1)),
  VOp.op (Op.shr 9 (.r 1)),
  VOp.op (Op.sub 32 2 (.r 9))]

/-- The template's piece from `48` to `60`. -/
def A48 : List VOp := [
  VOp.movdqa_m 3 7 0,
  VOp.op (Op.lea 64 9 (some 1) (some 11) 1 18446744073709551600),
  VOp.op (Op.cmp 64 11 (.r 9))]

/-- The template's piece from `66` to `69`. -/
def A66 : List VOp := [
  VOp.op (Op.test 64 9 (.r 9))]

/-- The template's piece from `75` to `106`. -/
def A75 (k : Nat) : List VOp := [
  VOp.op (Op.mov 64 11 (.r 9)),
  VOp.pxor 0 0,
  VOp.op (Op.mov 64 1 (.i 16)),
  VOp.op (Op.mov 32 9 (.i k)),
  VOp.op (Op.lea 64 10 (some 7) none 1 k),
  VOp.op (Op.and 64 10 (.i 4095))]

/-- The template's piece from `106` to `128`. -/
def A106 : List VOp := [
  VOp.op (Op.sub 64 10 (.i 4096)),
  VOp.op (Op.nop),
  VOp.op (Op.nop)]

/-- The template's piece from `128` to `132`. -/
def A128 : List VOp := [
  VOp.op (Op.add 64 10 (.i 16))]

/-- The template's piece from `138` to `166`. -/
def A138 (k : Nat) : List VOp := [
  VOp.movdqa_mi 1 6 1,
  VOp.movdqa_mi 2 7 1,
  VOp.movdqa 4 2,
  VOp.psrldq 3 k,
  VOp.pslldq 2 (16 - k),
  VOp.por 2 3]

/-- The template's piece from `166` to `188`. -/
def A166 : List VOp := [
  VOp.pcmpeqb 0 1,
  VOp.pcmpeqb 1 2,
  VOp.psubb 1 0,
  VOp.pmovmskb 2 1,
  VOp.op (Op.sub 32 2 (.i 65535))]

/-- The template's piece from `194` to `198`. -/
def A194 : List VOp := [
  VOp.op (Op.sub 64 11 (.i 16))]

/-- The template's piece from `204` to `216`. -/
def A204 : List VOp := [
  VOp.op (Op.add 64 1 (.i 16)),
  VOp.movdqa 3 4,
  VOp.op (Op.add 64 10 (.i 16))]

/-- The template's piece from `218` to `246`. -/
def A218 (k : Nat) : List VOp := [
  VOp.movdqa_mi 1 6 1,
  VOp.movdqa_mi 2 7 1,
  VOp.movdqa 4 2,
  VOp.psrldq 3 k,
  VOp.pslldq 2 (16 - k),
  VOp.por 2 3]

/-- The template's piece from `246` to `268`. -/
def A246 : List VOp := [
  VOp.pcmpeqb 0 1,
  VOp.pcmpeqb 1 2,
  VOp.psubb 1 0,
  VOp.pmovmskb 2 1,
  VOp.op (Op.sub 32 2 (.i 65535))]

/-- The template's piece from `274` to `278`. -/
def A274 : List VOp := [
  VOp.op (Op.sub 64 11 (.i 16))]

/-- The template's piece from `284` to `292`. -/
def A284 : List VOp := [
  VOp.op (Op.add 64 1 (.i 16)),
  VOp.movdqa 3 4]

/-- The template's piece from `304` to `318`. -/
def A304 (k : Nat) : List VOp := [
  VOp.pcmpeqb 0 3,
  VOp.pmovmskb 2 0,
  VOp.op (Op.test 32 2 (.i (65536 - 2 ^ k)))]

/-- The template's piece from `320` to `324`. -/
def A320 (k : Nat) : List VOp := [
  VOp.op (Op.cmp 64 11 (.i (16 - k)))]

/-- The template's piece from `326` to `337`. -/
def A326 : List VOp := [
  VOp.pxor 0 0,
  VOp.op (Op.sub 64 10 (.i 4096))]

/-- The end from `352` for `k < 15`: then a jump to `6144`. -/
def T352 (k : Nat) : List VOp := [
  VOp.movdqa_mi 1 6 1,
  VOp.psrldq 0 k,
  VOp.psrldq 3 k]

/-- The end from `352` for `k = 15`: on to `6144`. -/
def T352s (k : Nat) : List VOp := [
  VOp.movdqa_mi 1 6 1,
  VOp.psrldq 3 k,
  VOp.psrldq 0 k,
  VOp.op (Op.nop)]

/-- The end of the loop at `c`. -/
def TailC (prof : Profile) (k c : Nat) : Prop :=
  (BlkV prof scm (c + 352) (c + 367) (T352 k) ∧ JmpAt prof (c + 367) 5 6144) ∨
    (BlkV prof scm (c + 352) (c + 368) (T352s k) ∧ c + 368 = 6144)

/-- The loop at `c` shifting by `k`. -/
structure AshrC (prof : Profile) (k c e : Nat) : Prop where
  p0 : BlkV prof scm c (c + 25) (A0 k)
  p25 : BlkV prof scm (c + 25) (c + 42) A25
  j42 : JccAt prof 5 (c + 42) 6 (6165)
  p48 : BlkV prof scm (c + 48) (c + 60) A48
  j60 : JccAt prof 2 (c + 60) 6 (6212)
  p66 : BlkV prof scm (c + 66) (c + 69) A66
  j69 : JccAt prof 4 (c + 69) 6 (6212)
  p75 : BlkV prof scm (c + 75) (c + 106) (A75 k)
  p106 : BlkV prof scm (c + 106) (c + 128) A106
  p128 : BlkV prof scm (c + 128) (c + 132) A128
  j132 : JccAt prof 15 (c + 132) 6 (c + 304)
  p138 : BlkV prof scm (c + 138) (c + 166) (A138 k)
  p166 : BlkV prof scm (c + 166) (c + 188) A166
  j188 : JccAt prof 5 (c + 188) 6 (6160)
  p194 : BlkV prof scm (c + 194) (c + 198) A194
  j198 : JccAt prof 6 (c + 198) 6 (6212)
  p204 : BlkV prof scm (c + 204) (c + 216) A204
  j216 : JccAt prof 15 (c + 216) 2 (c + 304)
  p218 : BlkV prof scm (c + 218) (c + 246) (A218 k)
  p246 : BlkV prof scm (c + 246) (c + 268) A246
  j268 : JccAt prof 5 (c + 268) (2 + e) (6160)
  p274 : BlkV prof scm (c + 270 + e) (c + 274 + e) A274
  j278 : JccAt prof 6 (c + 274 + e) 6 (6212)
  p284 : BlkV prof scm (c + 280 + e) (c + 288 + e) A284
  j292 : JmpAt prof (c + 288 + e) 5 (c + 128)
  p304 : BlkV prof scm (c + 304) (c + 318) (A304 k)
  j318 : JccAt prof 5 (c + 318) 2 (c + 352)
  p320 : BlkV prof scm (c + 320) (c + 324) (A320 k)
  j324 : JccAt prof 6 (c + 324) 2 (c + 352)
  p326 : BlkV prof scm (c + 326) (c + 337) A326
  j337 : JmpAt prof (c + 337) 5 (c + 138)
  tail : TailC prof k c

end FV7z.Strncmp
