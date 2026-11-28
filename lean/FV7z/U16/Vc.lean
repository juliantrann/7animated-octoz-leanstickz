import FV7z.U16.Spec
/-!
# `Utf8_To_Utf16`: the pieces from the cut points (PLAN.md §M, M1)

`vc_*`: what `W_*` asks from the cut point it starts at, `Q` generic, the exits as hypotheses in the code's terms; the
values the proof does not follow (`rax`, `rbp`, the stored characters) bound by `∀`. Cut points: the entry; 109, 116,
the next character; 125, the loop's head (a byte at `rdx`); 141, one character stored; 174, a lead byte's form set up;
192, 201, 209, the inner loop (`rdi` the next byte, `r8` the bytes left, `esi` the bytes read); 272, a form that fails;
295, 299, its character; 312, the end (`*destLen`); 392, 409, 413, 492, a whole form's one or two characters.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.U16

local notation:max "w64(" x ")" => BitVec.setWidth 64 x
local notation:max "w32(" x ")" => BitVec.setWidth 32 x

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: `srcLim` = `src`, to 312; else the flag bits, `rbx` = `dest`, to 125. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (f2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (f3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (f4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (f5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (f6 : ∀ i < 8, Foot Wl (Addr.add (S6 g.rsp) i))
    (f7 : ∀ i < 8, Foot Wl (Addr.add (S6 g.rsp + 18446744073709551608#64) i))
    (f8 : decide (g.rdx = g.rcx) = false → ∀ i < 4, Foot Wl (Addr.add (S6 g.rsp + 18446744073709551604#64) i))
    (h312 : decide (g.rdx = g.rcx) = true → ∀ fl,
      Q 312 { g with rsp := S6 g.rsp, r11 := w64(w32(g.r11) ^^^ w32(g.r11)) } fl (Vs0 g V))
    (h125 : decide (g.rdx = g.rcx) = false → ∀ fl,
      Q 125 { g with
          rbx := g.rdi, rsp := S6 g.rsp, r8 := w64(w32(g.r8) &&& 4#32), r10 := g.rcx,
          r11 := w64(w32(g.r11) ^^^ w32(g.r11)), r12 := w64(w32(g.r8) &&& 2#32), r13 := w64(128#32),
          r14 := w64(65533#32), r15 := w64(w32(g.r8) &&& 1#32) } fl (Vs1 g V)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 f3 f4 f5 f6 f7 f8 h312 h125 ⊢
  wpx [W_0, W_579, W_24, o0, o43, o1]
  repeat' (first | with_reducible exact f1 | with_reducible exact f2 | with_reducible exact f3 |
    with_reducible exact f4 | with_reducible exact f5 | with_reducible exact f6 | with_reducible exact f7 |
    with_reducible (apply f8 <;> assumption) | apply And.intro | intro _)
  all_goals first
    | (apply h312 <;> assumption)
    | (apply h125 <;> assumption)

/-- 109: the next byte, one more character. -/
theorem vc_109 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 116 { g with rdx := g.r9, r11 := g.r11 + 1#64 } fl V) : W_109 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_109, o5]
  repeat' (first | apply And.intro | intro _)
  all_goals apply h

/-- 116: at `srcLim`, to 312; else to 125. -/
theorem vc_116 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h312 : decide (g.rdx = g.r10) = true → ∀ fl, Q 312 g fl V)
    (h125 : decide (g.rdx = g.r10) = false → ∀ fl, Q 125 g fl V) : W_116 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h312 h125 ⊢
  wpx [W_116, o6]
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | (apply h312 <;> assumption)
    | (apply h125 <;> assumption)

/-- 125: the byte at `rdx`; a lead byte to 174 (by its class), a byte that cannot start a form stored (with `dest`)
and to 109, a byte under `0x80` to 141 (with `dest`) or 109. -/
theorem vc_125 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fq : ∀ i < 1, Foot F.data (Addr.add g.rdx i))
    (h3 : na (rb V g.rdx) = true → lv (rb V g.rdx) = true → g223 (rb V g.rdx) = true → g239 (rb V g.rdx) = true →
      ∀ fl a bp, Q 174 { g with
        rax := a, rcx := w64(3#32), rdx := dl (rb V g.rdx) 18446744073709551376#64, rbp := bp,
        r9 := g.rdx + 1#64 } fl V)
    (h2 : na (rb V g.rdx) = true → lv (rb V g.rdx) = true → g223 (rb V g.rdx) = true → g239 (rb V g.rdx) = false →
      ∀ fl a bp, Q 174 { g with
        rax := a, rcx := w64(2#32), rdx := dl (rb V g.rdx) 18446744073709551392#64, rbp := bp,
        r9 := g.rdx + 1#64 } fl V)
    (h1 : na (rb V g.rdx) = true → lv (rb V g.rdx) = true → g223 (rb V g.rdx) = false →
      ∀ fl a bp, Q 174 { g with
        rax := a, rcx := w64(1#32), rdx := dl (rb V g.rdx) 18446744073709551424#64, rbp := bp,
        r9 := g.rdx + 1#64 } fl V)
    (hz : na (rb V g.rdx) = true → lv (rb V g.rdx) = false → zq g.rbx = true →
      ∀ fl a d, Q 109 { g with rax := a, rdx := d, r9 := g.rdx + 1#64 } fl V)
    (fw : na (rb V g.rdx) = true → lv (rb V g.rdx) = false → zq g.rbx = false →
      ∀ i < 4, Foot Wl (Addr.add (g.rbx + g.r11 * 4#64) i))
    (hs : na (rb V g.rdx) = true → lv (rb V g.rdx) = false → zq g.rbx = false →
      ∀ fl a d (w : BitVec 32), Q 109 { g with rax := a, rdx := d, r9 := g.rdx + 1#64 } fl
        (Vst V (g.rbx + g.r11 * 4#64) (toBytesLE w 4)))
    (ha : na (rb V g.rdx) = false → zq g.rbx = true → ∀ fl a, Q 109 { g with rax := a, r9 := g.rdx + 1#64 } fl V)
    (h141 : na (rb V g.rdx) = false → zq g.rbx = false →
      ∀ fl a, Q 141 { g with rax := a, r9 := g.rdx + 1#64 } fl V) :
    W_125 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fq h3 h2 h1 hz fw hs ha h141 ⊢
  wpx [W_125, W_80, W_152, W_432, W_504, W_436, W_163, W_88, W_93, W_136, o7, o2, o9, o36, o40, o37, o10, o3, o4,
    Op.zxr]
  repeat' (first | with_reducible exact fq | with_reducible (apply fw <;> assumption) | apply And.intro | intro _)
  all_goals first
    | with_reducible (apply h3 <;> assumption)
    | with_reducible (apply h2 <;> assumption)
    | with_reducible (apply h1 <;> assumption)
    | with_reducible (apply hz <;> assumption)
    | with_reducible (apply hs <;> assumption)
    | with_reducible (apply ha <;> assumption)
    | with_reducible (apply h141 <;> assumption)

/-- 141: the character `eax` stored. -/
theorem vc_141 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 4, Foot Wl (Addr.add (g.rbx + g.r11 * 4#64) i))
    (h : ∀ fl (w : BitVec 32), Q 109 g fl (Vst V (g.rbx + g.r11 * 4#64) (toBytesLE w 4))) :
    W_141 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_141, o8]
  repeat' (first | with_reducible exact fw | apply And.intro | intro _)
  all_goals apply h

/-- 174: the least value (`0x80 >> cl`), the bytes left, `rdi` at the next byte, to 209. -/
theorem vc_174 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl a, Q 209 { g with
      rax := a, rcx := w64(w32(g.r13) >>> ((BitVec.setWidth 8 g.rcx).toNat % 32)),
      rsi := w64(w32(g.rsi) ^^^ w32(g.rsi)), rdi := g.r9, r8 := w64(w32(g.rcx + 18446744073709551615#64)) } fl V) :
    W_174 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_174, o11]
  repeat' (first | apply And.intro | intro _)
  all_goals apply h

/-- 192: bytes left, to 201; else the value: with bit 2 of `flags` and the `0xEF80` class the lead byte's character
(141 or 109), else 392. -/
theorem vc_192 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (ff : zr w32(g.r8) = true → ∀ i < 4, Foot F.data (Addr.add (g.rsp + 18446744073709551604#64) i))
    (ha : zr w32(g.r8) = true → zr (rdd(V, g.rsp + 18446744073709551604#64)) = true →
      ∀ fl a, Q 392 { g with rax := a } fl V)
    (hb : zr w32(g.r8) = true → zr (rdd(V, g.rsp + 18446744073709551604#64)) = false → esc w32(g.rdx) = true →
      zq g.rbx = true → ∀ fl a, Q 109 { g with rax := a } fl V)
    (hc : zr w32(g.r8) = true → zr (rdd(V, g.rsp + 18446744073709551604#64)) = false → esc w32(g.rdx) = true →
      zq g.rbx = false → ∀ fl a, Q 141 { g with rax := a } fl V)
    (hd : zr w32(g.r8) = true → zr (rdd(V, g.rsp + 18446744073709551604#64)) = false → esc w32(g.rdx) = false →
      ∀ fl a, Q 392 { g with rax := a } fl V)
    (he : zr w32(g.r8) = false → ∀ fl, Q 201 g fl V) : W_192 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ff ha hb hc hd he ⊢
  wpx [W_192, W_368, W_376, W_552, W_561, o12, o30, o31, o3, o42]
  repeat' (first | with_reducible (apply ff <;> assumption) | apply And.intro | intro _)
  all_goals first
    | with_reducible (apply ha <;> assumption)
    | with_reducible (apply hb <;> assumption)
    | with_reducible (apply hc <;> assumption)
    | with_reducible (apply hd <;> assumption)
    | with_reducible (apply he <;> assumption)

/-- 201: the next byte, one fewer left. -/
theorem vc_201 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 209 { g with rdi := g.rdi + 1#64, r8 := w64(w32(g.r8) - 1#32) } fl V) : W_201 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_201, o13]
  repeat' (first | apply And.intro | intro _)
  all_goals apply h

/-- 209: the inner loop's byte; at `srcLim` or not `0x80`-`0xBF`, to 272; else kept in `edx`, with the first one's
checks (overlong, surrogate, past `0x10FFFF`) to 272, else to 192 or 201. -/
theorem vc_209 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (he : decide (g.rdi = g.r10) = true → ∀ fl, Q 272 g fl V)
    (fq : decide (g.rdi = g.r10) = false → ∀ i < 1, Foot F.data (Addr.add g.rdi i))
    (hb : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = true → ∀ fl a, Q 272 { g with rax := a } fl V)
    (h192 : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = true →
      ∀ fl a, Q 192 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.rsi) + 1#32) } fl V)
    (ho : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = false →
      ovl w32(g.rcx) (acc w32(g.rdx) (rb V g.rdi)) = true →
      ∀ fl a, Q 272 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.rsi) + 1#32) } fl V)
    (hu : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = false →
      ovl w32(g.rcx) (acc w32(g.rdx) (rb V g.rdi)) = false → decide (w32(g.r8) = 1#32) = true →
      zr w32(g.r15) = true →
      ∀ fl a, Q 201 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.rsi) + 1#32) } fl V)
    (hn : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = false →
      ovl w32(g.rcx) (acc w32(g.rdx) (rb V g.rdi)) = false → decide (w32(g.r8) = 1#32) = true →
      zr w32(g.r15) = false → nsg (acc w32(g.rdx) (rb V g.rdi)) = true →
      ∀ fl a, Q 201 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.rsi) + 1#32) } fl V)
    (hs : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = false →
      ovl w32(g.rcx) (acc w32(g.rdx) (rb V g.rdi)) = false → decide (w32(g.r8) = 1#32) = true →
      zr w32(g.r15) = false → nsg (acc w32(g.rdx) (rb V g.rdi)) = false →
      ∀ fl a, Q 272 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.r15)) } fl V)
    (h3 : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = false →
      ovl w32(g.rcx) (acc w32(g.rdx) (rb V g.rdi)) = false → decide (w32(g.r8) = 1#32) = false →
      (!decide (w32(g.r8 + 1#64) = 3#32)) = true →
      ∀ fl a, Q 192 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.rsi) + 1#32) } fl V)
    (hl : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = false →
      ovl w32(g.rcx) (acc w32(g.rdx) (rb V g.rdi)) = false → decide (w32(g.r8) = 1#32) = false →
      (!decide (w32(g.r8 + 1#64) = 3#32)) = false → l271 (acc w32(g.rdx) (rb V g.rdi)) = true →
      ∀ fl a, Q 192 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.rsi) + 1#32) } fl V)
    (hh : decide (g.rdi = g.r10) = false → bad (rb V g.rdi) = false → (!decide (w32(g.rsi) + 1#32 = 1#32)) = false →
      ovl w32(g.rcx) (acc w32(g.rdx) (rb V g.rdi)) = false → decide (w32(g.r8) = 1#32) = false →
      (!decide (w32(g.r8 + 1#64) = 3#32)) = false → l271 (acc w32(g.rdx) (rb V g.rdi)) = false →
      ∀ fl a, Q 272 { g with rax := a, rdx := w64(acc w32(g.rdx) (rb V g.rdi)), rsi := w64(w32(g.rsi) + 1#32) } fl V) :
    W_209 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he fq hb h192 ho hu hn hs h3 hl hh ⊢
  wpx [W_209, W_214, W_225, W_238, W_242, W_336, W_345, W_363, W_252, W_257, W_265, o14, o15, o16, o17, o18, o27,
    o28, o29, o19, o20, o21]
  repeat' (first | with_reducible (apply fq <;> assumption) | apply And.intro | intro _)
  all_goals first
    | with_reducible (apply he <;> assumption)
    | with_reducible (apply hb <;> assumption)
    | with_reducible (apply h192 <;> assumption)
    | with_reducible (apply ho <;> assumption)
    | with_reducible (apply hu <;> assumption)
    | with_reducible (apply hn <;> assumption)
    | with_reducible (apply hs <;> assumption)
    | with_reducible (apply h3 <;> assumption)
    | with_reducible (apply hl <;> assumption)
    | with_reducible (apply hh <;> assumption)

/-- 272: a form that fails; `rdx` past the lead byte (bit 1 of `flags`) or the bytes read, to 295 (with `dest`) or
299. -/
theorem vc_272 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h1 : zr w32(g.r12) = true → (!zq g.rbx) = true →
      ∀ fl bp, Q 295 { g with rdx := w64(w32(g.rsi)) + g.r9, rbp := bp } fl V)
    (h2 : zr w32(g.r12) = true → (!zq g.rbx) = false →
      ∀ fl bp, Q 299 { g with rdx := w64(w32(g.rsi)) + g.r9, rbp := bp } fl V)
    (h3 : zr w32(g.r12) = false → zq g.rbx = true → ∀ fl bp, Q 299 { g with rdx := g.r9, rbp := bp } fl V)
    (h4 : zr w32(g.r12) = false → zq g.rbx = false → ∀ fl bp, Q 295 { g with rdx := g.r9, rbp := bp } fl V) :
    W_272 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 h4 ⊢
  wpx [W_272, W_528, W_547, W_281, o22, o41, o23]
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | with_reducible (apply h1 <;> assumption)
    | with_reducible (apply h2 <;> assumption)
    | with_reducible (apply h3 <;> assumption)
    | with_reducible (apply h4 <;> assumption)

/-- 295: the character `ebp` stored. -/
theorem vc_295 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 4, Foot Wl (Addr.add (g.rbx + g.r11 * 4#64) i))
    (h : ∀ fl (w : BitVec 32), Q 299 g fl (Vst V (g.rbx + g.r11 * 4#64) (toBytesLE w 4))) :
    W_295 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_295, o24]
  repeat' (first | with_reducible exact fw | apply And.intro | intro _)
  all_goals apply h

/-- 299: one more character; to 125, or 312 at `srcLim`. -/
theorem vc_299 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h125 : (!decide (g.rdx = g.r10)) = true → ∀ fl, Q 125 { g with r11 := g.r11 + 1#64 } fl V)
    (h312 : (!decide (g.rdx = g.r10)) = false → ∀ fl, Q 312 { g with r11 := g.r11 + 1#64 } fl V) :
    W_299 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h125 h312 ⊢
  wpx [W_299, o25]
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | (apply h125 <;> assumption)
    | (apply h312 <;> assumption)

/-- 312: `*destLen` = `r11`, `eax` 1, the six `pop`s, to the `ret`. -/
theorem vc_312 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 18446744073709551608#64) i))
    (fp : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rsp + 18446744073709551608#64)) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (f6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 335 { g with
      rax := w64(1#32),
      rbx := rdq(Vst V (rdq(V, g.rsp + 18446744073709551608#64)) (toBytesLE g.r11 8), g.rsp),
      rsp := g.rsp + 8 + 8 + 8 + 8 + 8 + 8,
      rbp := rdq(Vst V (rdq(V, g.rsp + 18446744073709551608#64)) (toBytesLE g.r11 8), g.rsp + 8),
      r12 := rdq(Vst V (rdq(V, g.rsp + 18446744073709551608#64)) (toBytesLE g.r11 8), g.rsp + 8 + 8),
      r13 := rdq(Vst V (rdq(V, g.rsp + 18446744073709551608#64)) (toBytesLE g.r11 8), g.rsp + 8 + 8 + 8),
      r14 := rdq(Vst V (rdq(V, g.rsp + 18446744073709551608#64)) (toBytesLE g.r11 8), g.rsp + 8 + 8 + 8 + 8),
      r15 := rdq(Vst V (rdq(V, g.rsp + 18446744073709551608#64)) (toBytesLE g.r11 8), g.rsp + 8 + 8 + 8 + 8 + 8) } fl
      (Vst V (rdq(V, g.rsp + 18446744073709551608#64)) (toBytesLE g.r11 8))) :
    W_312 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 fp f1 f2 f3 f4 f5 f6 h ⊢
  wpx [W_312, o26]
  repeat' (first | with_reducible exact f0 | with_reducible exact fp | with_reducible exact f1 |
    with_reducible exact f2 | with_reducible exact f3 | with_reducible exact f4 | with_reducible exact f5 |
    with_reducible exact f6 | apply And.intro | intro _)
  all_goals apply h

/-- 392: a whole form's value; past `0xFFFF` a surrogate pair (with `dest`) and to 492, else one character and to
409. -/
theorem vc_392 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h1 : big w32(g.rdx) = true → zq g.rbx = true → ∀ fl, Q 492 g fl V)
    (fa : big w32(g.rdx) = true → zq g.rbx = false → ∀ i < 4, Foot Wl (Addr.add (g.rbx + g.r11 * 4#64) i))
    (fb : big w32(g.rdx) = true → zq g.rbx = false → ∀ i < 4, Foot Wl (Addr.add (g.rbx + g.r11 * 4#64 + 4#64) i))
    (h2 : big w32(g.rdx) = true → zq g.rbx = false → ∀ fl a d (w₁ w₂ : BitVec 32),
      Q 492 { g with rax := a, rdx := d } fl (Vst (Vst V (g.rbx + g.r11 * 4#64) (toBytesLE w₁ 4))
        (g.rbx + g.r11 * 4#64 + 4#64) (toBytesLE w₂ 4)))
    (h3 : big w32(g.rdx) = false → zq g.rbx = true → ∀ fl, Q 409 g fl V)
    (fc : big w32(g.rdx) = false → zq g.rbx = false → ∀ i < 4, Foot Wl (Addr.add (g.rbx + g.r11 * 4#64) i))
    (h4 : big w32(g.rdx) = false → zq g.rbx = false → ∀ fl (w : BitVec 32), Q 409 g fl
      (Vst V (g.rbx + g.r11 * 4#64) (toBytesLE w 4))) :
    W_392 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 fa fb h2 h3 fc h4 ⊢
  wpx [W_392, W_456, W_461, W_400, W_405, o32, o3, o38, o33]
  repeat' (first | with_reducible (apply fa <;> assumption) | with_reducible (apply fb <;> assumption) |
    with_reducible (apply fc <;> assumption) | apply And.intro | intro _)
  all_goals first
    | with_reducible (apply h1 <;> assumption)
    | with_reducible (apply h2 <;> assumption)
    | with_reducible (apply h3 <;> assumption)
    | with_reducible (apply h4 <;> assumption)

/-- 409: one more character. -/
theorem vc_409 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 413 { g with r11 := g.r11 + 1#64 } fl V) : W_409 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_409, o34]
  repeat' (first | apply And.intro | intro _)
  all_goals apply h

/-- 413: `rdx` past the bytes read. -/
theorem vc_413 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 116 { g with rdx := g.r9 + g.rsi } fl V) : W_413 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_413, o35]
  repeat' (first | apply And.intro | intro _)
  all_goals apply h

/-- 492: two more characters. -/
theorem vc_492 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 413 { g with r11 := g.r11 + 2#64 } fl V) : W_492 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_492, o39]
  repeat' (first | apply And.intro | intro _)
  all_goals apply h

end FV7z.U16
