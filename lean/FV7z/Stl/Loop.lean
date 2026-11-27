import FV7z.Stl.Tail
import FV7z.Stl.Vz
/-!
# `____strtoul_l_internal`: the digit loop (PLAN.md §M, M1)

The loop at 296 keeps the registers `Dr` (the frame, `rbp = 0`, `CU` in `r10`, `CB` in `r11`, `p` in `r13`,
`rdi = p + k`) with `cl` the byte at `p + k`, the bytes kept (`Ag (Kr Kk S) (Vf V0 g0)`) and `E` in its slot. At the
NUL (`k = n`) it leaves to 368 (`vc_296x`: `CB[0]` is not a letter); past a byte that is not 0 (`k < n`) it reads
`p + k + 1` (265, 345) and comes back to 296 with `k + 1` (291), or leaves to 368. By induction on `n - k`.

- `Sl`: the tables the loop reads. `Dr`, `LpG`: the registers, the goal at 296 with `k`.
- `ap1`, `rbS`: the next address; a byte of the string reads the entry's.
- `t291`, `t265`, `t345`, `t332`, `s296` (one round), `lpAll`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Nlc (Ag)
namespace FV7z.Stl

/-! ## Names -/

/-- The tables the loop reads: the pointer to `CB` (at 7935176) readable, kept and outside the frame; `CB`'s entries
and `CU`'s (by a zero-extended byte) readable; `CB[0]` readable, kept, outside the frame and not a letter. -/
structure Sl (F : Footprint) (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) : Prop where
  fB : ∀ i < 8, Foot F.data (Addr.add 7935176#64 i)
  kB : ∀ i < 8, Kk (Addr.add 7935176#64 i) ∧
    ((Addr.add 7935176#64 i).toNat < g0.rsp.toNat - 88 ∨ g0.rsp.toNat ≤ (Addr.add 7935176#64 i).toNat)
  fCz : ∀ w : BitVec 8, ∀ i < 1,
    Foot F.data (Addr.add (Cb V0 + BitVec.setWidth 64 (BitVec.setWidth 32 w) * 2#64 + 1#64) i)
  fUz : ∀ w : BitVec 8, ∀ i < 4,
    Foot F.data (Addr.add (Cu V0 + BitVec.setWidth 64 (BitVec.setWidth 32 w) * 4#64) i)
  fC0 : ∀ i < 1, Foot F.data (Addr.add (Cb V0 + 1#64) i)
  kC0 : ∀ i < 1, Kk (Addr.add (Cb V0 + 1#64) i) ∧
    ((Addr.add (Cb V0 + 1#64) i).toNat < g0.rsp.toNat - 88 ∨
      g0.rsp.toNat ≤ (Addr.add (Cb V0 + 1#64) i).toNat)
  c0 : (rb V0 (Cb V0 + 1#64) &&& 4#8 == 0) = true

/-- The loop's registers with `rdi = p + k`. -/
abbrev Dr (g0 g : Gprs) (V0 : Addr → Byte) (k : Nat) : Prop :=
  g.rsp = S88 g0.rsp ∧ g.rbp = 0#64 ∧ g.r10 = Cu V0 ∧ g.r11 = Cb V0 ∧ g.r13 = g0.rdi ∧
    g.rdi = Addr.add g0.rdi k

theorem Dr.lg {g0 g g' : Gprs} {V0 : Addr → Byte} {k : Nat} (h : Dr g0 g V0 k) (hl : Lg g g')
    (hd : g'.rdi = g.rdi) : Dr g0 g' V0 k := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨l1, -, l3, l4, l5, l6, -⟩ := hl
  exact ⟨l1.trans h1, l3.trans h2, l4.trans h3, l5.trans h4, l6.trans h5, hd.trans h6⟩

theorem ap1 (p : Addr) (k : Nat) : Addr.add p k + 1#64 = Addr.add p (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A byte of the string reads the entry's. -/
theorem rbS {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 : Gprs} {F : Footprint} {n k : Nat}
    (hS : 80 ≤ g0.rsp.toNat) (Sw : Sv F Kk V0 g0 n) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hk : k ≤ n) :
    rb V (Addr.add g0.rdi k) = rb V0 (Addr.add g0.rdi k) :=
  congrArg (ofBytesLE 8) (rdK hS hag fun i hi => by rw [show i = 0 by omega, a0]; exact Sw.kp k hk)

/-- The loop's goal at 296 with `rdi = p + k`. -/
def LpG (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) (k : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = stl_at.add 296 → Dr g0 Y.cpu.gpr V0 k →
    Y.cpu.gpr.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (rb V (Addr.add g0.rdi k))) →
    Ag (Kr Kk g0.rsp) (Vf V0 g0) V → rdq(V, S88 g0.rsp + 8#64) = g0.rsi → GoG prof L o gev gP gE Y t

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ n : Nat}

/-! ## One round -/

set_option maxHeartbeats 4000000 in
/-- From 291 with `rdi = p + k`: to 368, or back to 296. -/
theorem t291 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (Sw : Sv F Kk V0 g0 n) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 291) (hD : Dr g0 Y.cpu.gpr V0 k)
    (hrc : Y.cpu.gpr.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (rb V (Addr.add g0.rdi k))))
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (ih : LpG prof F Wl L s₀ o gev gP gE Kk V0 g0 k)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  refine (c_291 prof fb).run c hfs E.hin _ hK hA hr vc_291 ?_
  rintro j' g fl V' ⟨hj, hV, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  have hZ : Z.cpu.gpr = Y.cpu.gpr := hgZ.trans hg
  rcases hj with rfl | rfl
  · exact t368 c hfs E Sw hk hKZ hAZ hrZ (by rw [hZ]; exact hD.1) hag hEs (by rw [hZ]; exact hD.2.2.2.2.1)
      (by rw [hZ]; exact hD.2.2.2.2.2) kr
  · exact ih Z t₁ _ hKZ hAZ hrZ (by rw [hZ]; exact hD) (by rw [hZ]; exact hrc) hag hEs

set_option maxHeartbeats 4000000 in
/-- From 265 with `rdi = p + k`, `k < n`: the next byte; to 368, or to 291 with `k + 1`. -/
theorem t265 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (Sw : Sv F Kk V0 g0 n) {k : Nat} (hk : k < n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 265) (hD : Dr g0 Y.cpu.gpr V0 k)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (ih : LpG prof F Wl L s₀ o gev gP gE Kk V0 g0 (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hdi := hD.2.2.2.2.2
  have f1 : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rdi + 1#64) i) := fun i hi => by
    rw [show i = 0 by omega, a0, hdi, ap1]
    exact Sw.fp _ (by omega)
  refine (c_265 prof fb).run c hfs E.hin _ hK hA hr (vc_265 f1) ?_
  rintro j' g fl V' ⟨hV, hl, hd1, hrc, hj⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  have hD' : Dr g0 Z.cpu.gpr V0 (k + 1) := by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := hD
    obtain ⟨l1, -, l3, l4, l5, l6, -⟩ := hl
    rw [hgZ]
    exact ⟨l1.trans h1, l3.trans h2, l4.trans h3, l5.trans h4, l6.trans h5, by rw [hd1, hdi, ap1]⟩
  rcases hj with rfl | ⟨rfl, -⟩
  · exact t368 c hfs E Sw (by omega) hKZ hAZ hrZ hD'.1 hag hEs hD'.2.2.2.2.1 hD'.2.2.2.2.2 kr
  · exact t291 c hfs E Sw (by omega) hKZ hAZ hrZ hD' (by rw [hgZ, hrc, hdi, ap1]) hag hEs ih kr

set_option maxHeartbeats 4000000 in
/-- From 345 (an overflow seen) with `rdi = p + k`, `k < n`: as 265. -/
theorem t345 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (Sw : Sv F Kk V0 g0 n) {k : Nat} (hk : k < n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 345) (hD : Dr g0 Y.cpu.gpr V0 k)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (ih : LpG prof F Wl L s₀ o gev gP gE Kk V0 g0 (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hdi := hD.2.2.2.2.2
  have f1 : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rdi + 1#64) i) := fun i hi => by
    rw [show i = 0 by omega, a0, hdi, ap1]
    exact Sw.fp _ (by omega)
  refine (c_345 prof fb).run c hfs E.hin _ hK hA hr (vc_345 f1) ?_
  rintro j' g fl V' ⟨hV, hl, hd1, hrc, hj⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  have hD' : Dr g0 Z.cpu.gpr V0 (k + 1) := by
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := hD
    obtain ⟨l1, -, l3, l4, l5, l6, -⟩ := hl
    rw [hgZ]
    exact ⟨l1.trans h1, l3.trans h2, l4.trans h3, l5.trans h4, l6.trans h5, by rw [hd1, hdi, ap1]⟩
  rcases hj with rfl | ⟨rfl, -⟩
  · exact t368 c hfs E Sw (by omega) hKZ hAZ hrZ hD'.1 hag hEs hD'.2.2.2.2.1 hD'.2.2.2.2.2 kr
  · exact t291 c hfs E Sw (by omega) hKZ hAZ hrZ hD' (by rw [hgZ, hrc, hdi, ap1]) hag hEs ih kr

set_option maxHeartbeats 4000000 in
/-- From 332 (a digit value) with `rdi = p + k`, `k < n`: to 368, 265 or 345. -/
theorem t332 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (Sw : Sv F Kk V0 g0 n) {k : Nat} (hk : k < n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 332) (hD : Dr g0 Y.cpu.gpr V0 k)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (ih : LpG prof F Wl L s₀ o gev gP gE Kk V0 g0 (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hlt := g0.rsp.isLt
  obtain ⟨-, e18, -, -⟩ := slots hS96
  have f18 : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 18#64) i) := by
    rw [hD.1]
    exact fun i hi => c.hws _ (stk E.wf (by omega) (by omega) (by omega) i hi)
  refine (c_332 prof fb).run c hfs E.hin _ hK hA hr (vc_332 f18) ?_
  rintro j' g fl V' ⟨hj, hV, hl, hd⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  have hD' : Dr g0 Z.cpu.gpr V0 k := by rw [hgZ]; exact hD.lg hl hd
  rcases hj with rfl | rfl | rfl
  · exact t368 c hfs E Sw (by omega) hKZ hAZ hrZ hD'.1 hag hEs hD'.2.2.2.2.1 hD'.2.2.2.2.2 kr
  · exact t265 c hfs E Sw hk hKZ hAZ hrZ hD' hag hEs ih kr
  · exact t345 c hfs E Sw hk hKZ hAZ hrZ hD' hag hEs ih kr

set_option maxHeartbeats 4000000 in
/-- One round from 296 with `rdi = p + k`: the NUL to 368; else a digit or a letter to 332, or to 368. -/
theorem s296 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) {k : Nat} (hk : k ≤ n)
    (ih : k < n → LpG prof F Wl L s₀ o gev gP gE Kk V0 g0 (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    LpG prof F Wl L s₀ o gev gP gE Kk V0 g0 k := by
  intro Y t V hK hA hr hD hrc hag hEs
  have hS96 := E.s96
  have hS : 80 ≤ g0.rsp.toNat := by omega
  have hb := rbS hS Sw hag hk
  by_cases hb0 : rb V0 (Addr.add g0.rdi k) = 0
  · have hz : Y.cpu.gpr.rcx = 0#64 := by rw [hrc, hb, hb0] <;> decide
    have hC : rb V (Cb V0 + 1#64) = rb V0 (Cb V0 + 1#64) := congrArg (ofBytesLE 8) (rdK hS hag St.kC0)
    have fC : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.r11 +
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 Y.cpu.gpr.rcx)) * 2#64 + 1#64) i) := by
      rw [hD.2.2.2.1]
      exact St.fCz _
    have hd : (decide ((BitVec.setWidth 8 (BitVec.setWidth 32 (Y.cpu.gpr.rcx + 18446744073709551568#64))).toNat < 9) ||
        decide (BitVec.setWidth 8 (BitVec.setWidth 32 (Y.cpu.gpr.rcx + 18446744073709551568#64)) = 9#8)) = false := by
      rw [hz]
      decide
    have h0 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (0#64))) * 2#64 = 0#64 := by decide
    have ha : (rb V (Y.cpu.gpr.r11 + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 Y.cpu.gpr.rcx)) * 2#64
        + 1#64) &&& 4#8 == 0) = true := by
      rw [hD.2.2.2.1, hz, h0, BitVec.add_zero, hC]
      exact St.c0
    refine (c_296 prof fb).run c hfs E.hin _ hK hA hr (vc_296x hD.2.1 hd fC ha) ?_
    rintro j' g fl V' ⟨rfl, hV, hl, hd⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst hV
    have hD' : Dr g0 Z.cpu.gpr V0 k := by rw [hgZ]; exact hD.lg hl hd
    exact t368 c hfs E Sw hk hKZ hAZ hrZ hD'.1 hag hEs hD'.2.2.2.2.1 hD'.2.2.2.2.2 kr
  · have hkn : k < n := Nat.lt_of_le_of_ne hk fun e => hb0 (by rw [e]; exact Sw.z)
    have fC : ∀ i < 1, Foot F.data (Addr.add (Y.cpu.gpr.r11 +
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 Y.cpu.gpr.rcx)) * 2#64 + 1#64) i) := by
      rw [hD.2.2.2.1]
      exact St.fCz _
    have fU : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.r10 +
        BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 Y.cpu.gpr.rcx)) * 4#64) i) := by
      rw [hD.2.2.1]
      exact St.fUz _
    refine (c_296 prof fb).run c hfs E.hin _ hK hA hr (vc_296 hD.2.1 fC fU) ?_
    rintro j' g fl V' ⟨hj, hV, hl, hd⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst hV
    have hD' : Dr g0 Z.cpu.gpr V0 k := by rw [hgZ]; exact hD.lg hl hd
    rcases hj with rfl | rfl
    · exact t332 c hfs E Sw hkn hKZ hAZ hrZ hD' hag hEs (ih hkn) kr
    · exact t368 c hfs E Sw hk hKZ hAZ hrZ hD'.1 hag hEs hD'.2.2.2.2.1 hD'.2.2.2.2.2 kr

/-- The loop from every `k ≤ n`, by induction on `n - k`. -/
theorem lpAll (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (Sw : Sv F Kk V0 g0 n) (St : Sl F Kk V0 g0) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    ∀ m k, n - k = m → k ≤ n → LpG prof F Wl L s₀ o gev gP gE Kk V0 g0 k := by
  intro m
  induction m with
  | zero => exact fun k hm hk => s296 c hfs E Sw St hk (fun h => absurd hm (by omega)) kr
  | succ m ih => exact fun k hm hk => s296 c hfs E Sw St hk (fun h => ih (k + 1) (by omega) (by omega)) kr

end

end FV7z.Stl
