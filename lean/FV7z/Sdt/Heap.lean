import FV7z.Sdt.Holds
/-!
# `CArchiveExtractCallback::SetDirsTimes` (PLAN.md §M, M1): the heap sort's pieces

The pairs `P` (`rbp`), `n` of them, sorted by `Sort2` (`CPP/Common/MyVector.h`, inlined): from 141 (`r13` = `n`),
`n` = 1 to 355 (`ecx` = the only index); else the heap built (151: `rax` = `n - 1`, `rdi` = `d` from `n / 2 - 1`
down, `r9` = the pair `d`, `r11` = `2 d + 1`), each `d` sifted down (219: `r12d`, `r13d` = the pair `d`; 238:
`[rsp]` = `d`, `r8` = the hole `p`, `rcx` = the child `c`; 248–303: the larger child, `rdx` its slot, `r10d` its
key; 309: the child moved up, the next `c` = `2 c + 1`; 182/696: `rdi` = `d` back, 191: the pair stored at
`rdx`, `d` 0 to 544). Then (544) the root swapped with the last (`rax` = `m`, `m -= 1`, 1 left to 355), the new
root (`r10d`, `ecx`) sifted down (579–672, `r8` the hole, `rsi` the child, `rdi` = `2 r8`), stored at 538.

- `Hk`, `Kc`, `Ke`: the registers the pieces keep.
- `vc_*`: the pieces' conditions (the keys compared as numbers; only the bounds matter for the run).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sdt
set_option linter.unusedVariables false

/-- `rsp`, `this`, the pairs, the last index. -/
abbrev Hk (g g' : Gprs) : Prop := g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.rax = g.rax

/-- In the heap's sift: also the hole, the build's `r9`, `r11`, the pair sifted. -/
abbrev Kc (g g' : Gprs) : Prop :=
  Hk g g' ∧ g'.r8 = g.r8 ∧ g'.r9 = g.r9 ∧ g'.r11 = g.r11 ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13

/-- In the sort's sift: also the hole, the pair sifted. -/
abbrev Ke (g g' : Gprs) : Prop := Hk g g' ∧ g'.r8 = g.r8 ∧ g'.r10 = g.r10 ∧ g'.rcx = g.rcx

variable {F : Footprint} {Wl : List Rgn}

theorem ltF {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : (a.toNat < b.toNat) = False := eq_false (by omega)
theorem eqF {w : Nat} {a b : BitVec w} (h : b.toNat < a.toNat) : (a = b) = False :=
  eq_false (fun e => by rw [e] at h; omega)
theorem eqF' {w : Nat} {a b : BitVec w} (h : a.toNat < b.toNat) : (a = b) = False :=
  eq_false (fun e => by rw [e] at h; omega)
theorem ltF' {w : Nat} {a b : BitVec w} (h : b.toNat ≤ a.toNat) : (a.toNat < b.toNat) = False :=
  eq_false (by omega)

/-! ## The build -/

/-- `cmp r13, 1`: one pair, `ecx` = its index, to 355. -/
theorem vc_141e {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 4#64) i)) (h1 : g.r13 = 1#64)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp →
      g'.rcx = BitVec.setWidth 64 rdd(V, g.rbp + 4#64) → ∀ fl, Q 355 g' fl V) :
    W_141 F Wl Q g f V := by
  have t := eq_true h1
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 t h ⊢
  sdx [W_141, W_352, W_151, o7, o22, o8, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- More pairs: `rax` = `n - 1`, `r13` = `n / 2`, `rdi` = `n / 2 - 1`, `r9`, `r11`; to 219. -/
theorem vc_141n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h1 : ¬ g.r13 = 1#64)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.rax = g.r13 + 18446744073709551615#64 →
      g'.rdi = (g.r13 >>> 1) + 18446744073709551615#64 →
      g'.r9 = g.rbp + ((g.r13 >>> 1) + 18446744073709551615#64) * 8#64 →
      g'.r11 = (g.r13 >>> 1) + 18446744073709551615#64 + ((g.r13 >>> 1) + 18446744073709551615#64) + 1#64 →
      ∀ fl, Q 219 g' fl V) :
    W_141 F Wl Q g f V := by
  have t := eq_false h1
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at t h ⊢
  sdx [W_141, W_352, W_151, o7, o22, o8, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The pair `d` loaded; `rax` below `r11` (no child): to 191. -/
theorem vc_219b {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add g.r9 i)) (f4 : ∀ i < 4, Foot F.data (Addr.add (g.r9 + 4#64) i))
    (hlt : g.rax.toNat < g.r11.toNat)
    (h : ∀ g', Hk g g' → g'.rdi = g.rdi → g'.r9 = g.r9 → g'.r11 = g.r11 →
      g'.r12 = BitVec.setWidth 64 rdd(V, g.r9) → g'.r13 = BitVec.setWidth 64 rdd(V, g.r9 + 4#64) →
      g'.rdx = g.r9 → ∀ fl, Q 191 g' fl V) :
    W_219 F Wl Q g f V := by
  have t := eq_true hlt
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at f0 f4 t h ⊢
  sdx [W_219, W_238, o13, o14, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- A child: `[rsp]` = `d`, `rcx` = `r11`, `r8` = `d`; to 248. -/
theorem vc_219n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add g.r9 i)) (f4 : ∀ i < 4, Foot F.data (Addr.add (g.r9 + 4#64) i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rsp i)) (hge : ¬ g.rax.toNat < g.r11.toNat)
    (h : ∀ g', Hk g g' → g'.r9 = g.r9 → g'.r11 = g.r11 →
      g'.r12 = BitVec.setWidth 64 rdd(V, g.r9) → g'.r13 = BitVec.setWidth 64 rdd(V, g.r9 + 4#64) →
      g'.rcx = g.r11 → g'.r8 = g.rdi → g'.rsi = g.rdi + g.rdi →
      ∀ fl, Q 248 g' fl (Vst V g.rsp (toBytesLE g.rdi 8))) :
    W_219 F Wl Q g f V := by
  have t := eq_false hge
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at f0 f4 w0 t h ⊢
  sdx [W_219, W_238, o13, o14, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The pair stored at `rdx`; `d` 0: the heap built, to 544. -/
theorem vc_191z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 4, Foot Wl (Addr.add g.rdx i)) (w4 : ∀ i < 4, Foot Wl (Addr.add (g.rdx + 4#64) i))
    (hz : g.rdi = 0)
    (h : ∀ g', Hk g g' → ∀ fl, Q 544 g' fl (Vst (Vst V g.rdx (toBytesLE (BitVec.setWidth 32 g.r12) 4))
      (g.rdx + 4#64) (toBytesLE (BitVec.setWidth 32 g.r13) 4))) :
    W_191 F Wl Q g f V := by
  have t := beq_iff_eq.2 hz
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at w0 w4 t h ⊢
  sdx [W_191, W_215, o11, o12, t]
  all_goals repeat' (first | refine h _ ?_ _ | sdc)

/-- The pair stored; `d - 1`, the previous pair: back to 219. -/
theorem vc_191n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 4, Foot Wl (Addr.add g.rdx i)) (w4 : ∀ i < 4, Foot Wl (Addr.add (g.rdx + 4#64) i))
    (hz : ¬ g.rdi = 0)
    (h : ∀ g', Hk g g' → g'.rdi = g.rdi - 1#64 → g'.r9 = g.r9 - 8#64 → g'.r11 = g.r11 - 2#64 →
      ∀ fl, Q 219 g' fl (Vst (Vst V g.rdx (toBytesLE (BitVec.setWidth 32 g.r12) 4))
      (g.rdx + 4#64) (toBytesLE (BitVec.setWidth 32 g.r13) 4))) :
    W_191 F Wl Q g f V := by
  have t := beq_eq_false_iff_ne.2 hz
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at w0 w4 t h ⊢
  sdx [W_191, W_215, o11, o12, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- `rdi` = `d` back, `rdx` = the hole: to 191. -/
theorem vc_182 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h : ∀ g', Kc g g' → g'.rdi = rdq(V, g.rsp) → g'.rdx = g.rbp + g.r8 * 8#64 → ∀ fl, Q 191 g' fl V) :
    W_182 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Kc, Hk] at f0 h ⊢
  sdx [W_182, o10]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | sdc)

/-! ## The build's sift: the larger child -/

/-- The left child `c` the last: to 298 with it. -/
theorem vc_248a {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rcx * 8#64) i)) (hle : g.rax.toNat ≤ g.rcx.toNat)
    (h : ∀ g', Kc g g' → g'.rcx = g.rcx → g'.rsi = g.rsi → g'.rdx = g.rbp + g.rcx * 8#64 →
      g'.r10 = BitVec.setWidth 64 rdd(V, g.rbp + g.rcx * 8#64) → ∀ fl, Q 298 g' fl V) :
    W_248 F Wl Q g f V := by
  rcases Nat.lt_or_eq_of_le hle with hl | he
  · have t := eq_true hl
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Kc, Hk] at f0 t h ⊢
    sdx [W_248, W_261, o15, o16, t]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)
  · have t := eq_true (BitVec.eq_of_toNat_eq he)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Kc, Hk] at f0 t h ⊢
    sdx [W_248, W_261, o15, o16, t]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- Both children, the right's key below the left's: to 289. -/
theorem vc_248r {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rcx * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rsi + 2#64) * 8#64) i)) (hgt : g.rcx.toNat < g.rax.toNat)
    (hl : rdd(V, g.rbp + (g.rsi + 2#64) * 8#64).toNat < rdd(V, g.rbp + g.rcx * 8#64).toNat)
    (h : ∀ g', Kc g g' → g'.rcx = g.rcx → g'.rsi = g.rsi + 2#64 → g'.r14 = g.rbp + (g.rsi + 2#64) * 8#64 →
      g'.r15 = BitVec.setWidth 64 rdd(V, g.rbp + (g.rsi + 2#64) * 8#64) → ∀ fl, Q 289 g' fl V) :
    W_248 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 := eq_true hl
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Kc, Hk] at f0 f1 t1 t2 t3 h ⊢
  sdx [W_248, W_261, o15, o16, t1, t2, t3]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- Both children, the right's key above the left's: to 298 with the left. -/
theorem vc_248l {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rcx * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rsi + 2#64) * 8#64) i)) (hgt : g.rcx.toNat < g.rax.toNat)
    (hg : rdd(V, g.rbp + g.rcx * 8#64).toNat < rdd(V, g.rbp + (g.rsi + 2#64) * 8#64).toNat)
    (h : ∀ g', Kc g g' → g'.rcx = g.rcx → g'.rsi = g.rsi + 2#64 → g'.rdx = g.rbp + g.rcx * 8#64 →
      g'.r10 = BitVec.setWidth 64 rdd(V, g.rbp + g.rcx * 8#64) → ∀ fl, Q 298 g' fl V) :
    W_248 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 := ltF' (Nat.le_of_lt hg)
  have t4 := eqF hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Kc, Hk] at f0 f1 t1 t2 t3 t4 h ⊢
  sdx [W_248, W_261, W_278, o15, o16, t1, t2, t3, t4]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- Equal keys, the right's index not above the left's: to 298 with the left. -/
theorem vc_248e1 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rcx * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rsi + 2#64) * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rcx * 8#64 + 4#64) i))
    (f3 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rsi + 2#64) * 8#64 + 4#64) i))
    (hgt : g.rcx.toNat < g.rax.toNat)
    (he : rdd(V, g.rbp + (g.rsi + 2#64) * 8#64) = rdd(V, g.rbp + g.rcx * 8#64))
    (hle : rdd(V, g.rbp + (g.rsi + 2#64) * 8#64 + 4#64).toNat ≤ rdd(V, g.rbp + g.rcx * 8#64 + 4#64).toNat)
    (h : ∀ g', Kc g g' → g'.rcx = g.rcx → g'.rsi = g.rsi + 2#64 → g'.rdx = g.rbp + g.rcx * 8#64 →
      g'.r10 = BitVec.setWidth 64 rdd(V, g.rbp + g.rcx * 8#64) → ∀ fl, Q 298 g' fl V) :
    W_248 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 : (rdd(V, g.rbp + (g.rsi + 2#64) * 8#64).toNat < rdd(V, g.rbp + g.rcx * 8#64).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t4 := eq_true he
  rcases Nat.lt_or_eq_of_le hle with hl | hq
  · have t5 := eq_true hl
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Kc, Hk] at f0 f1 f2 f3 t1 t2 t3 t4 t5 h ⊢
    sdx [W_248, W_261, W_278, W_280, o15, o16, o17, t1, t2, t3, t4, t5]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)
  · have t5 := eq_true (BitVec.eq_of_toNat_eq hq)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Kc, Hk] at f0 f1 f2 f3 t1 t2 t3 t4 t5 h ⊢
    sdx [W_248, W_261, W_278, W_280, o15, o16, o17, t1, t2, t3, t4, t5]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- Equal keys, the right's index above the left's: to 289. -/
theorem vc_248e2 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rcx * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rsi + 2#64) * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rcx * 8#64 + 4#64) i))
    (f3 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rsi + 2#64) * 8#64 + 4#64) i))
    (hgt : g.rcx.toNat < g.rax.toNat)
    (he : rdd(V, g.rbp + (g.rsi + 2#64) * 8#64) = rdd(V, g.rbp + g.rcx * 8#64))
    (hg : rdd(V, g.rbp + g.rcx * 8#64 + 4#64).toNat < rdd(V, g.rbp + (g.rsi + 2#64) * 8#64 + 4#64).toNat)
    (h : ∀ g', Kc g g' → g'.rcx = g.rcx → g'.rsi = g.rsi + 2#64 → g'.r14 = g.rbp + (g.rsi + 2#64) * 8#64 →
      g'.r15 = BitVec.setWidth 64 rdd(V, g.rbp + (g.rsi + 2#64) * 8#64) → ∀ fl, Q 289 g' fl V) :
    W_248 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 : (rdd(V, g.rbp + (g.rsi + 2#64) * 8#64).toNat < rdd(V, g.rbp + g.rcx * 8#64).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t4 := eq_true he
  have t5 := ltF' (Nat.le_of_lt hg)
  have t6 := eqF hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Kc, Hk] at f0 f1 f2 f3 t1 t2 t3 t4 t5 t6 h ⊢
  sdx [W_248, W_261, W_278, W_280, o15, o16, o17, t1, t2, t3, t4, t5, t6]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The right child chosen: `r10` its key, `rdx` its slot, `rcx` = `rsi`; to 298. -/
theorem vc_289 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Kc g g' → g'.rcx = g.rsi → g'.rsi = g.rsi → g'.rdx = g.r14 →
      g'.r10 = BitVec.setWidth 64 (BitVec.setWidth 32 g.r15) → ∀ fl, Q 298 g' fl V) :
    W_289 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Kc, Hk] at h ⊢
  sdx [W_289, o18]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-! ## The build's sift: the pair against the child -/

/-- The pair's key below the child's: to 182. -/
theorem vc_298s {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : (BitVec.setWidth 32 g.r12).toNat < (BitVec.setWidth 32 g.r10).toNat) (h : ∀ fl, Q 182 g fl V) :
    W_298 F Wl Q g f V := by
  have t := eq_true hl
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at t h ⊢
  sdx [W_298, W_303, o19, t]
  all_goals repeat' (first | refine h _ | sdc)

/-- The pair's key above the child's: to 309. -/
theorem vc_298g {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hg : (BitVec.setWidth 32 g.r10).toNat < (BitVec.setWidth 32 g.r12).toNat) (h : ∀ fl, Q 309 g fl V) :
    W_298 F Wl Q g f V := by
  have t1 := ltF' (Nat.le_of_lt hg)
  have t2 := eqF hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at t1 t2 h ⊢
  sdx [W_298, W_303, o19, t1, t2]
  all_goals repeat' (first | refine h _ | sdc)

/-- Equal keys, the pair's index below the child's: to 309. -/
theorem vc_298e1 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 4#64) i))
    (he : BitVec.setWidth 32 g.r12 = BitVec.setWidth 32 g.r10)
    (hl : (BitVec.setWidth 32 g.r13).toNat < rdd(V, g.rdx + 4#64).toNat) (h : ∀ fl, Q 309 g fl V) :
    W_298 F Wl Q g f V := by
  have t1 : ((BitVec.setWidth 32 g.r12).toNat < (BitVec.setWidth 32 g.r10).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t2 := eq_true he
  have t3 := eq_true hl
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 t1 t2 t3 h ⊢
  sdx [W_298, W_303, W_176, o19, o9, t1, t2, t3]
  all_goals repeat' (first | refine h _ | sdc)

/-- Equal keys, the pair's index not below the child's: to 182. -/
theorem vc_298e2 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 4#64) i))
    (he : BitVec.setWidth 32 g.r12 = BitVec.setWidth 32 g.r10)
    (hge : ¬ (BitVec.setWidth 32 g.r13).toNat < rdd(V, g.rdx + 4#64).toNat) (h : ∀ fl, Q 182 g fl V) :
    W_298 F Wl Q g f V := by
  have t1 : ((BitVec.setWidth 32 g.r12).toNat < (BitVec.setWidth 32 g.r10).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t2 := eq_true he
  have t3 := eq_false hge
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 t1 t2 t3 h ⊢
  sdx [W_298, W_303, W_176, o19, o9, t1, t2, t3]
  all_goals repeat' (first | refine h _ | sdc)

/-- The child moved up to the hole; its children past the last: `rdi` = `d` back, to 191. -/
theorem vc_309b {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (w0 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + g.r8 * 8#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hlt : g.rax.toNat < (g.rcx + g.rcx + 1#64).toNat)
    (h : ∀ g', Hk g g' → g'.r9 = g.r9 → g'.r11 = g.r11 → g'.r12 = g.r12 → g'.r13 = g.r13 → g'.rdx = g.rdx →
      g'.rdi = rdq(Vst V (g.rbp + g.r8 * 8#64) (toBytesLE rdq(V, g.rdx) 8), g.rsp) →
      ∀ fl, Q 191 g' fl (Vst V (g.rbp + g.r8 * 8#64) (toBytesLE rdq(V, g.rdx) 8))) :
    W_309 F Wl Q g f V := by
  have t := eq_true hlt
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at f0 w0 fs t h ⊢
  sdx [W_309, W_696, W_334, o20, o49, o21, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The child moved up; the next hole the child, the next child `2 c + 1`: to 248. -/
theorem vc_309n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (w0 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + g.r8 * 8#64) i))
    (hge : ¬ g.rax.toNat < (g.rcx + g.rcx + 1#64).toNat)
    (h : ∀ g', Hk g g' → g'.r9 = g.r9 → g'.r11 = g.r11 → g'.r12 = g.r12 → g'.r13 = g.r13 →
      g'.r8 = g.rcx → g'.rcx = g.rcx + g.rcx + 1#64 → g'.rsi = g.rcx + g.rcx →
      ∀ fl, Q 248 g' fl (Vst V (g.rbp + g.r8 * 8#64) (toBytesLE rdq(V, g.rdx) 8))) :
    W_309 F Wl Q g f V := by
  have t := eq_false hge
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at f0 w0 t h ⊢
  sdx [W_309, W_696, W_334, o20, o49, o21, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- `r12` = 0 (the first of the sorted pairs), to 373. -/
theorem vc_355 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.rcx = g.rcx → g'.r12 = 0#64 →
      ∀ fl, Q 373 g' fl V) :
    W_355 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  sdx [W_355, o23]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-! ## The sort -/

/-- The bytes after the root swapped with the pair `m` (`rax`). -/
abbrev Vsw (V : Addr → Byte) (P m : Addr) : Addr → Byte :=
  Vst (Vst (Vst V (P + m * 8#64) (toBytesLE rdq(V, P) 8)) P (toBytesLE rdd(V, P + m * 8#64) 4)) (P + 4#64)
    (toBytesLE rdd(V, P + m * 8#64 + 4#64) 4)

/-- The swap; `m` 1: sorted, `ecx` = the first index, to 355. -/
theorem vc_544z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rax * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rax * 8#64 + 4#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + g.rax * 8#64) i))
    (w2 : ∀ i < 4, Foot Wl (Addr.add g.rbp i)) (w3 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 4#64) i))
    (h1 : g.rax = 1#64)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp →
      g'.rcx = BitVec.setWidth 64 rdd(V, g.rbp + g.rax * 8#64 + 4#64) → ∀ fl, Q 355 g' fl (Vsw V g.rbp g.rax)) :
    W_544 F Wl Q g f V := by
  have t := eq_true h1
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vsw] at f1 f2 f3 w1 w2 w3 t h ⊢
  sdx [W_544, W_579, o39, o40, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- The swap; `m` above 1: `m - 1`, the root sifted from the hole 0 (`rsi` = 1), to 589. -/
theorem vc_544n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rax * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rax * 8#64 + 4#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + g.rax * 8#64) i))
    (w2 : ∀ i < 4, Foot Wl (Addr.add g.rbp i)) (w3 : ∀ i < 4, Foot Wl (Addr.add (g.rbp + 4#64) i))
    (h1 : ¬ g.rax = 1#64)
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.rax = g.rax - 1#64 →
      g'.r10 = BitVec.setWidth 64 rdd(V, g.rbp + g.rax * 8#64) →
      g'.rcx = BitVec.setWidth 64 rdd(V, g.rbp + g.rax * 8#64 + 4#64) → g'.rdi = 0#64 → g'.r8 = 0#64 →
      g'.rsi = 1#64 → ∀ fl, Q 589 g' fl (Vsw V g.rbp g.rax)) :
    W_544 F Wl Q g f V := by
  have t := eq_false h1
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vsw] at f1 f2 f3 w1 w2 w3 t h ⊢
  sdx [W_544, W_579, o39, o40, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The left child `rsi` the last: to 640 with it. -/
theorem vc_589a {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rsi * 8#64) i)) (hle : g.rax.toNat ≤ g.rsi.toNat)
    (h : ∀ g', Ke g g' → g'.rsi = g.rsi → g'.rdi = g.rdi → g'.rdx = g.rbp + g.rsi * 8#64 →
      g'.r9 = BitVec.setWidth 64 rdd(V, g.rbp + g.rsi * 8#64) → ∀ fl, Q 640 g' fl V) :
    W_589 F Wl Q g f V := by
  rcases Nat.lt_or_eq_of_le hle with hl | he
  · have t := eq_true hl
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Ke, Hk] at f0 t h ⊢
    sdx [W_589, W_602, o41, o42, t]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)
  · have t := eq_true (BitVec.eq_of_toNat_eq he)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Ke, Hk] at f0 t h ⊢
    sdx [W_589, W_602, o41, o42, t]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- Both children, the right's key below the left's: to 631. -/
theorem vc_589r {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rsi * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rdi + 2#64) * 8#64) i)) (hgt : g.rsi.toNat < g.rax.toNat)
    (hl : rdd(V, g.rbp + (g.rdi + 2#64) * 8#64).toNat < rdd(V, g.rbp + g.rsi * 8#64).toNat)
    (h : ∀ g', Ke g g' → g'.rdi = g.rdi + 2#64 → g'.r11 = g.rbp + (g.rdi + 2#64) * 8#64 →
      g'.r12 = BitVec.setWidth 64 rdd(V, g.rbp + (g.rdi + 2#64) * 8#64) → ∀ fl, Q 631 g' fl V) :
    W_589 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 := eq_true hl
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ke, Hk] at f0 f1 t1 t2 t3 h ⊢
  sdx [W_589, W_602, o41, o42, t1, t2, t3]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- Both children, the right's key above the left's: to 640 with the left. -/
theorem vc_589l {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rsi * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rdi + 2#64) * 8#64) i)) (hgt : g.rsi.toNat < g.rax.toNat)
    (hg : rdd(V, g.rbp + g.rsi * 8#64).toNat < rdd(V, g.rbp + (g.rdi + 2#64) * 8#64).toNat)
    (h : ∀ g', Ke g g' → g'.rsi = g.rsi → g'.rdi = g.rdi + 2#64 → g'.rdx = g.rbp + g.rsi * 8#64 →
      g'.r9 = BitVec.setWidth 64 rdd(V, g.rbp + g.rsi * 8#64) → ∀ fl, Q 640 g' fl V) :
    W_589 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 := ltF' (Nat.le_of_lt hg)
  have t4 := eqF hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ke, Hk] at f0 f1 t1 t2 t3 t4 h ⊢
  sdx [W_589, W_602, W_619, o41, o42, t1, t2, t3, t4]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- Equal keys, the right's index not above the left's: to 640 with the left. -/
theorem vc_589e1 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rsi * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rdi + 2#64) * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rsi * 8#64 + 4#64) i))
    (f3 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rdi + 2#64) * 8#64 + 4#64) i))
    (hgt : g.rsi.toNat < g.rax.toNat)
    (he : rdd(V, g.rbp + (g.rdi + 2#64) * 8#64) = rdd(V, g.rbp + g.rsi * 8#64))
    (hle : rdd(V, g.rbp + (g.rdi + 2#64) * 8#64 + 4#64).toNat ≤ rdd(V, g.rbp + g.rsi * 8#64 + 4#64).toNat)
    (h : ∀ g', Ke g g' → g'.rsi = g.rsi → g'.rdi = g.rdi + 2#64 → g'.rdx = g.rbp + g.rsi * 8#64 →
      g'.r9 = BitVec.setWidth 64 rdd(V, g.rbp + g.rsi * 8#64) → ∀ fl, Q 640 g' fl V) :
    W_589 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 : (rdd(V, g.rbp + (g.rdi + 2#64) * 8#64).toNat < rdd(V, g.rbp + g.rsi * 8#64).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t4 := eq_true he
  rcases Nat.lt_or_eq_of_le hle with hl | hq
  · have t5 := eq_true hl
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Ke, Hk] at f0 f1 f2 f3 t1 t2 t3 t4 t5 h ⊢
    sdx [W_589, W_602, W_619, W_621, o41, o42, o43, t1, t2, t3, t4, t5]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)
  · have t5 := eq_true (BitVec.eq_of_toNat_eq hq)
    obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
    dsimp only [Ke, Hk] at f0 f1 f2 f3 t1 t2 t3 t4 t5 h ⊢
    sdx [W_589, W_602, W_619, W_621, o41, o42, o43, t1, t2, t3, t4, t5]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- Equal keys, the right's index above the left's: to 631. -/
theorem vc_589e2 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rsi * 8#64) i))
    (f1 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rdi + 2#64) * 8#64) i))
    (f2 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + g.rsi * 8#64 + 4#64) i))
    (f3 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + (g.rdi + 2#64) * 8#64 + 4#64) i))
    (hgt : g.rsi.toNat < g.rax.toNat)
    (he : rdd(V, g.rbp + (g.rdi + 2#64) * 8#64) = rdd(V, g.rbp + g.rsi * 8#64))
    (hg : rdd(V, g.rbp + g.rsi * 8#64 + 4#64).toNat < rdd(V, g.rbp + (g.rdi + 2#64) * 8#64 + 4#64).toNat)
    (h : ∀ g', Ke g g' → g'.rdi = g.rdi + 2#64 → g'.r11 = g.rbp + (g.rdi + 2#64) * 8#64 →
      g'.r12 = BitVec.setWidth 64 rdd(V, g.rbp + (g.rdi + 2#64) * 8#64) → ∀ fl, Q 631 g' fl V) :
    W_589 F Wl Q g f V := by
  have t1 := ltF (Nat.le_of_lt hgt)
  have t2 := eqF hgt
  have t3 : (rdd(V, g.rbp + (g.rdi + 2#64) * 8#64).toNat < rdd(V, g.rbp + g.rsi * 8#64).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t4 := eq_true he
  have t5 := ltF' (Nat.le_of_lt hg)
  have t6 := eqF hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ke, Hk] at f0 f1 f2 f3 t1 t2 t3 t4 t5 t6 h ⊢
  sdx [W_589, W_602, W_619, W_621, o41, o42, o43, t1, t2, t3, t4, t5, t6]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- The right child chosen: `r9` its key, `rdx` its slot, `rsi` = `rdi`; to 640. -/
theorem vc_631 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Ke g g' → g'.rsi = g.rdi → g'.rdi = g.rdi → g'.rdx = g.r11 →
      g'.r9 = BitVec.setWidth 64 (BitVec.setWidth 32 g.r12) → ∀ fl, Q 640 g' fl V) :
    W_631 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ke, Hk] at h ⊢
  sdx [W_631, o44]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ _ | sdc)

/-- The root's key below the child's: to 533. -/
theorem vc_640s {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hl : (BitVec.setWidth 32 g.r10).toNat < (BitVec.setWidth 32 g.r9).toNat) (h : ∀ fl, Q 533 g fl V) :
    W_640 F Wl Q g f V := by
  have t := eq_true hl
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at t h ⊢
  sdx [W_640, W_645, o45, t]
  all_goals repeat' (first | refine h _ | sdc)

/-- The root's key above the child's: to 647. -/
theorem vc_640g {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hg : (BitVec.setWidth 32 g.r9).toNat < (BitVec.setWidth 32 g.r10).toNat) (h : ∀ fl, Q 647 g fl V) :
    W_640 F Wl Q g f V := by
  have t1 := ltF' (Nat.le_of_lt hg)
  have t2 := eqF hg
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at t1 t2 h ⊢
  sdx [W_640, W_645, o45, t1, t2]
  all_goals repeat' (first | refine h _ | sdc)

/-- Equal keys, the root's index below the child's: to 647. -/
theorem vc_640e1 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 4#64) i))
    (he : BitVec.setWidth 32 g.r10 = BitVec.setWidth 32 g.r9)
    (hl : (BitVec.setWidth 32 g.rcx).toNat < rdd(V, g.rdx + 4#64).toNat) (h : ∀ fl, Q 647 g fl V) :
    W_640 F Wl Q g f V := by
  have t1 : ((BitVec.setWidth 32 g.r10).toNat < (BitVec.setWidth 32 g.r9).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t2 := eq_true he
  have t3 := eq_true hl
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 t1 t2 t3 h ⊢
  sdx [W_640, W_645, W_528, o45, o36, t1, t2, t3]
  all_goals repeat' (first | refine h _ | sdc)

/-- Equal keys, the root's index not below the child's: to 533. -/
theorem vc_640e2 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f4 : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 4#64) i))
    (he : BitVec.setWidth 32 g.r10 = BitVec.setWidth 32 g.r9)
    (hge : ¬ (BitVec.setWidth 32 g.rcx).toNat < rdd(V, g.rdx + 4#64).toNat) (h : ∀ fl, Q 533 g fl V) :
    W_640 F Wl Q g f V := by
  have t1 : ((BitVec.setWidth 32 g.r10).toNat < (BitVec.setWidth 32 g.r9).toNat) = False :=
    eq_false (by rw [he]; omega)
  have t2 := eq_true he
  have t3 := eq_false hge
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f4 t1 t2 t3 h ⊢
  sdx [W_640, W_645, W_528, o45, o36, t1, t2, t3]
  all_goals repeat' (first | refine h _ | sdc)

/-- `rdx` = the hole, to 538. -/
theorem vc_533 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Ke g g' → g'.rdx = g.rbp + g.r8 * 8#64 → ∀ fl, Q 538 g' fl V) :
    W_533 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ke, Hk] at h ⊢
  sdx [W_533, o37]
  all_goals repeat' (first | refine h _ ?_ ?_ _ | sdc)

/-- The root stored at `rdx`, to 544. -/
theorem vc_538 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 4, Foot Wl (Addr.add g.rdx i)) (w4 : ∀ i < 4, Foot Wl (Addr.add (g.rdx + 4#64) i))
    (h : ∀ g', Hk g g' → ∀ fl, Q 544 g' fl (Vst (Vst V g.rdx (toBytesLE (BitVec.setWidth 32 g.r10) 4))
      (g.rdx + 4#64) (toBytesLE (BitVec.setWidth 32 g.rcx) 4))) :
    W_538 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at w0 w4 h ⊢
  sdx [W_538, o38]
  all_goals repeat' (first | refine h _ ?_ _ | sdc)

/-- The child moved up to the hole; its children past `m`: to 538 (the child's slot). -/
theorem vc_647b {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (w0 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + g.r8 * 8#64) i))
    (hlt : g.rax.toNat < (g.rsi + g.rsi + 1#64).toNat)
    (h : ∀ g', Hk g g' → g'.r10 = g.r10 → g'.rcx = g.rcx → g'.rdx = g.rdx →
      ∀ fl, Q 538 g' fl (Vst V (g.rbp + g.r8 * 8#64) (toBytesLE rdq(V, g.rdx) 8))) :
    W_647 F Wl Q g f V := by
  have t := eq_true hlt
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at f0 w0 t h ⊢
  sdx [W_647, W_672, o46, o47, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | sdc)

/-- The child moved up; the next hole the child, the next child `2 c + 1`: to 589. -/
theorem vc_647n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdx i)) (w0 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + g.r8 * 8#64) i))
    (hge : ¬ g.rax.toNat < (g.rsi + g.rsi + 1#64).toNat)
    (h : ∀ g', Hk g g' → g'.r10 = g.r10 → g'.rcx = g.rcx → g'.r8 = g.rsi → g'.rsi = g.rsi + g.rsi + 1#64 →
      g'.rdi = g.rsi + g.rsi → ∀ fl, Q 589 g' fl (Vst V (g.rbp + g.r8 * 8#64) (toBytesLE rdq(V, g.rdx) 8))) :
    W_647 F Wl Q g f V := by
  have t := eq_false hge
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Hk] at f0 w0 t h ⊢
  sdx [W_647, W_672, o46, o47, t]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ _ | sdc)

end FV7z.Sdt
