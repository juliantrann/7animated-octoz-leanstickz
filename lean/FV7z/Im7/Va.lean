import FV7z.Im7.S
/-!
# `_int_malloc` from the entry to 512 for a largebin request, `nb` a variable (PLAN.md G3, `malloc`)

The way `0 → 9 → 304 → 320 → 340 → 352`, then by `nb`:
- `PaA`: `nb >> 6` above 48, `nb >> 9` at most 20 (482 → 512): the index `91 + (nb >> 9)` at `rsp + 0x28`;
- `PaB`: `nb >> 9` above 20, `nb >> 12` at most 10 (492 → 507 → 512): `110 + (nb >> 12)`;
- `PaCa`: `nb >> 12` above 10, `nb >> 15` below 5 (492 → 2192 → 512): `119 + (nb >> 15)`;
- `PaCb`: `nb >> 15` at least 5, `nb` at most `0xbffff`: `124 + (nb >> 18)`; `PaCc`: `nb` above it: 126.

The flags of the comparisons with `nb` are hypotheses in the form `simp` leaves them (`decide (x.toNat < c) = b`,
`decide (x = c#64) = b`); a jump taken on `CF ∨ ZF` gets `c || z = true` for the two.
-/
set_option Elab.async false
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im7

/-- From the entry to 512, `nb >> 6` above 48 and `nb >> 9` at most 20. -/
def PaA (F : Footprint) (Wl : List Rgn) : Prop :=
  ∀ {fb S n nb : Addr} {c1 z1 : Bool} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = nb →
    decide (nb.toNat < 128) = false → decide (nb = 128#64) = false →
    decide (nb.toNat < 1023) = false → decide (nb = 1023#64) = false →
    decide (nb.toNat < 786431) = true →
    decide ((nb >>> 6).toNat < 48) = false → decide (nb >>> 6 = 48#64) = false →
    decide ((nb >>> 9).toNat < 20) = c1 → decide (nb >>> 9 = 20#64) = z1 → (c1 || z1) = true →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 8013224#64) = 128#64 →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ _ V₁ => j = 512 ∧ g₁.rbx = 7940672#64 ∧ g₁.r13 = nb ∧ g₁.rsp = S ∧
      rdd(V₁, S + 40#64) = (nb >>> 9).setWidth 32 + 91#32 ∧ Im2.Fr S g V V₁) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vcA {F : Footprint} {Wl : List Rgn} : PaA F Wl := by
  intro fb S n nb c1 z1 g f V hrsp hsi hdi m d1 d2 e c320 z320 c340 z340 c398 c476 z476 c486 z486 h486 hS hlo hgm hgf
    hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  lwp [W_0, W_9, W_304, W_320, W_340, W_352, W_482, o0, o1, o2, o3, o4, o5, o6, p1, p2, p3, p4, p5, p6, p7, q1, hS, hS',
    m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486, z486, h486, BitVec.xor_self]
  lc7 [p1, p2, p3, p4, p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486, z486,
    h486, BitVec.xor_self]

/-- From the entry to 512 (507), `nb >> 9` above 20 and `nb >> 12` at most 10. -/
def PaB (F : Footprint) (Wl : List Rgn) : Prop :=
  ∀ {fb S n nb : Addr} {c2 z2 : Bool} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = nb →
    decide (nb.toNat < 128) = false → decide (nb = 128#64) = false →
    decide (nb.toNat < 1023) = false → decide (nb = 1023#64) = false →
    decide (nb.toNat < 786431) = true →
    decide ((nb >>> 6).toNat < 48) = false → decide (nb >>> 6 = 48#64) = false →
    decide ((nb >>> 9).toNat < 20) = false → decide (nb >>> 9 = 20#64) = false →
    decide ((nb >>> 12).toNat < 10) = c2 → decide (nb >>> 12 = 10#64) = z2 → (c2 || z2) = true →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 8013224#64) = 128#64 →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ _ V₁ => j = 512 ∧ g₁.rbx = 7940672#64 ∧ g₁.r13 = nb ∧ g₁.rsp = S ∧
      rdd(V₁, S + 40#64) = BitVec.setWidth 32 (nb >>> 12 + 110#64) ∧ Im2.Fr S g V V₁) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vcB {F : Footprint} {Wl : List Rgn} : PaB F Wl := by
  intro fb S n nb c2 z2 g f V hrsp hsi hdi m d1 d2 e c320 z320 c340 z340 c398 c476 z476 c486 z486 c497 z497 h497 hS hlo
    hgm hgf hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  lwp [W_0, W_9, W_304, W_320, W_340, W_352, W_482, W_492, W_507, o0, o1, o2, o3, o4, o5, o6, o7, o8, p1, p2, p3, p4,
    p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486, z486, c497, z497, h497,
    BitVec.xor_self]
  lc7 [p1, p2, p3, p4, p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486, z486,
    c497, z497, h497, BitVec.xor_self]

/-- From the entry to 512 (2192), `nb >> 12` above 10 and `nb >> 15` below 5. -/
def PaCa (F : Footprint) (Wl : List Rgn) : Prop :=
  ∀ {fb S n nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = nb →
    decide (nb.toNat < 128) = false → decide (nb = 128#64) = false →
    decide (nb.toNat < 1023) = false → decide (nb = 1023#64) = false →
    decide (nb.toNat < 786431) = true →
    decide ((nb >>> 6).toNat < 48) = false → decide (nb >>> 6 = 48#64) = false →
    decide ((nb >>> 9).toNat < 20) = false → decide (nb >>> 9 = 20#64) = false →
    decide ((nb >>> 12).toNat < 10) = false → decide (nb >>> 12 = 10#64) = false →
    decide ((nb >>> 15).toNat < 5) = true →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 8013224#64) = 128#64 →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ _ V₁ => j = 512 ∧ g₁.rbx = 7940672#64 ∧ g₁.r13 = nb ∧ g₁.rsp = S ∧
      rdd(V₁, S + 40#64) = BitVec.setWidth 32 (nb >>> 15 + 119#64) ∧ Im2.Fr S g V V₁) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vcCa {F : Footprint} {Wl : List Rgn} : PaCa F Wl := by
  intro fb S n nb g f V hrsp hsi hdi m d1 d2 e c320 z320 c340 z340 c398 c476 z476 c486 z486 c497 z497 c2192 hS hlo hgm
    hgf hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  lwp [W_0, W_9, W_304, W_320, W_340, W_352, W_482, W_492, W_2192, o0, o1, o2, o3, o4, o5, o6, o7, o18, p1, p2, p3, p4,
    p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486, z486, c497, z497, c2192,
    BitVec.xor_self]
  lc7 [p1, p2, p3, p4, p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, c476, z476, c486, z486,
    c497, z497, c2192, BitVec.xor_self]

/-- From the entry to 512 (2192), `nb >> 15` at least 5 and `nb` at most `0xbffff`. -/
def PaCb (F : Footprint) (Wl : List Rgn) : Prop :=
  ∀ {fb S n nb : Addr} {c3 z3 : Bool} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = nb →
    decide (nb.toNat < 128) = false → decide (nb = 128#64) = false →
    decide (nb.toNat < 1023) = false → decide (nb = 1023#64) = false →
    decide (nb.toNat < 786431) = c3 → decide (nb = 786431#64) = z3 → (c3 || z3) = true →
    decide ((nb >>> 6).toNat < 48) = false → decide (nb >>> 6 = 48#64) = false →
    decide ((nb >>> 9).toNat < 20) = false → decide (nb >>> 9 = 20#64) = false →
    decide ((nb >>> 12).toNat < 10) = false → decide (nb >>> 12 = 10#64) = false →
    decide ((nb >>> 15).toNat < 5) = false →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 8013224#64) = 128#64 →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ _ V₁ => j = 512 ∧ g₁.rbx = 7940672#64 ∧ g₁.r13 = nb ∧ g₁.rsp = S ∧
      rdd(V₁, S + 40#64) = BitVec.setWidth 32 (nb >>> 18 + 124#64) ∧ Im2.Fr S g V V₁) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vcCb {F : Footprint} {Wl : List Rgn} : PaCb F Wl := by
  intro fb S n nb c3 z3 g f V hrsp hsi hdi m d1 d2 e c320 z320 c340 z340 c398 z398 h398 c476 z476 c486 z486 c497 z497
    c2192 hS hlo hgm hgf hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  lwp [W_0, W_9, W_304, W_320, W_340, W_352, W_482, W_492, W_2192, o0, o1, o2, o3, o4, o5, o6, o7, o18, p1, p2, p3, p4,
    p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, z398, h398, c476, z476, c486, z486, c497,
    z497, c2192, BitVec.xor_self]
  lc7 [p1, p2, p3, p4, p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, z398, h398, c476, z476,
    c486, z486, c497, z497, c2192, BitVec.xor_self]

/-- From the entry to 512 (2192), `nb` above `0xbffff`: the index 126. -/
def PaCc (F : Footprint) (Wl : List Rgn) : Prop :=
  ∀ {fb S n nb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte},
    g.rsp = S + 184#64 → g.rsi = n → g.rdi = 7940672#64 →
    n.msb = false → decide ((n + 23#64).toNat < 31) = false → decide (n + 23#64 = 31#64) = false →
    n + 23#64 &&& 18446744073709551600#64 = nb →
    decide (nb.toNat < 128) = false → decide (nb = 128#64) = false →
    decide (nb.toNat < 1023) = false → decide (nb = 1023#64) = false →
    decide (nb.toNat < 786431) = false → decide (nb = 786431#64) = false →
    decide ((nb >>> 6).toNat < 48) = false → decide (nb >>> 6 = 48#64) = false →
    decide ((nb >>> 9).toNat < 20) = false → decide (nb >>> 9 = 20#64) = false →
    decide ((nb >>> 12).toNat < 10) = false → decide (nb >>> 12 = 10#64) = false →
    decide ((nb >>> 15).toNat < 5) = false →
    S.toNat + 256 < 2 ^ 64 → 8029888 ≤ S.toNat → rdq(V, 8013224#64) = 128#64 →
    (∀ i < 8, Foot F.data (Addr.add (8013224#64) i)) →
    (∀ i < 184, Foot Wl (Addr.add S i)) → (∀ i < 184, Foot F.data (Addr.add S i)) →
    W_0 fb F Wl (fun j g₁ _ V₁ => j = 512 ∧ g₁.rbx = 7940672#64 ∧ g₁.r13 = nb ∧ g₁.rsp = S ∧
      rdd(V₁, S + 40#64) = 126#32 ∧ Im2.Fr S g V V₁) g f V

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 100000 in
theorem vcCc {F : Footprint} {Wl : List Rgn} : PaCc F Wl := by
  intro fb S n nb g f V hrsp hsi hdi m d1 d2 e c320 z320 c340 z340 c398 z398 c476 z476 c486 z486 c497 z497 c2192 hS hlo
    hgm hgf hsw hsd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hrsp hsi hdi ⊢
  subst hrsp hsi hdi
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := pu S
  have q1 := rd_below (S := S) (x := 8013224#64) (n := 8) (hx := by rw [BitVec.toNat_ofNat]; omega) (hS := hS)
  have hS' : S.toNat + 256 < 18446744073709551616 := hS
  lwp [W_0, W_9, W_304, W_320, W_340, W_352, W_482, W_492, W_2192, o0, o1, o2, o3, o4, o5, o6, o7, o18, p1, p2, p3, p4,
    p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, z398, c476, z476, c486, z486, c497, z497,
    c2192, BitVec.xor_self]
  lc7 [p1, p2, p3, p4, p5, p6, p7, q1, hS, hS', m, d1, d2, e, hgm, c320, z320, c340, z340, c398, z398, c476, z476, c486,
    z486, c497, z497, c2192, BitVec.xor_self]

end FV7z.Im7
