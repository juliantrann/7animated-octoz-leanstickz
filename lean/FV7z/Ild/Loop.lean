import FV7z.Ild.Holds
/-!
# `_nl_intern_locale_data`: the loop over the values (PLAN.md §M, M1)

The loop at 196 keeps the registers `Lr` (the frame, the new block `p` in `rax`, `cnt = k` in `rcx`, the jump table
in `rdx`, the data in `rbx`, `c` in `ebp`/`r9`/`r14`, the type tables in `r10`, `datasize` in `r12`, `N` in `r13`)
and the bytes kept (`Ag (Kr Kk S) (Vf V0 g0)`); the block is `Bk` (`8N + 64` bytes, writable, apart from `Kk`).

- `cZ`, `Lr`, `Bk`, `LpAt`: the loop's registers, the block, the loop's goal at 196 with `cnt = k`.
- `sa`, `aI`, `ne64`: the store address `p + 8k + 64`, `data + idx`, `N ≠ k + 1`.
- `fr6_out`, `rdK`: reads in `Kk` outside the frame read the entry's bytes.
- `t307` (the next value or the end), `t299` (a string: its address stored), `t336` (a word: its value stored, or
  misaligned and out by `free`), `t288` (the value's type from `_nl_value_types[c]`): one value from 288 on.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Tun (Vst_out)
open FV7z.Mcn (fr6 fr_e6)
open FV7z.Nlc (Ag Res)
namespace FV7z.Ild

/-! ## Names -/

/-- `c` zero-extended (`ebp`, `r9`). -/
abbrev cZ (g0 : Gprs) : Addr := BitVec.setWidth 64 (BitVec.setWidth 32 g0.rdi)

/-- The loop's registers with `cnt = k`. -/
abbrev Lr (g0 g : Gprs) (p : Addr) (N k : Nat) : Prop :=
  g.rsp = S56 g0.rsp ∧ g.rax = p ∧ g.rcx = BitVec.ofNat 64 k ∧ g.rdx = 7268832#64 ∧ g.rbx = g0.rsi ∧
    g.rbp = cZ g0 ∧ g.r9 = cZ g0 ∧ g.r10 = 7865536#64 ∧ g.r12 = g0.rdx ∧ g.r13 = BitVec.ofNat 64 N ∧
    g.r14 = BitVec.signExtend 64 (BitVec.setWidth 32 g0.rdi)

/-- The new block: `8N + 64` bytes, writable, apart from `Kk`. -/
abbrev Bk (Wl : List Rgn) (Kk : Addr → Prop) (p : Addr) (N : Nat) : Prop :=
  p.toNat + (8 * N + 64) ≤ 2 ^ 64 ∧ (∀ i < 8 * N + 64, Foot Wl (Addr.add p i)) ∧
    ∀ y : Addr, p.toNat ≤ y.toNat → y.toNat < p.toNat + (8 * N + 64) → ¬ Kk y

/-- The loop's goal at 196 with `cnt = k`. -/
def LpAt (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) (p : Addr) (N k : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = ild_at.add 196 → Lr g0 Y.cpu.gpr p N k → Ag (Kr Kk g0.rsp) (Vf V0 g0) V →
    GoG prof L o gev gP gE Y t

/-! ## Numbers and bytes -/

/-- The store address of the `k`-th value. -/
theorem sa (p : Addr) (k : Nat) : p + BitVec.ofNat 64 k * 8#64 + 64#64 = Addr.add p (8 * k + 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem aI (a x : Addr) : a + x = Addr.add a x.toNat := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ne64 {N m : Nat} (hN : N < 2 ^ 64) (hm : m < 2 ^ 64) (h : m ≠ N) :
    ¬ BitVec.ofNat 64 N = BitVec.ofNat 64 m := by
  intro e
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hm] at e'
  exact h e'.symm

/-- Outside the pushes, the entry's bytes. -/
theorem fr6_out (V : Addr → Byte) (S : Addr) (a b c d e f : BitVec 64) (hS : 80 ≤ S.toNat) (x : Addr)
    (hx : ¬ (S.toNat - 48 ≤ x.toNat ∧ x.toNat < S.toNat)) : fr6 V S a b c d e f x = V x := by
  have hl := S.isLt
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := fr_e6 hS
  unfold fr6
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e5]; omega) (by rw [toBytesLE_length, e5]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- A read in `Kk` outside the frame `[S - 64, S)`: the entry's bytes. -/
theorem rdK {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 : Gprs} {x : Addr} {m : Nat} (hS : 80 ≤ g0.rsp.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (hx : ∀ i < m, Kk (Addr.add x i) ∧
      ((Addr.add x i).toNat < g0.rsp.toNat - 64 ∨ g0.rsp.toNat ≤ (Addr.add x i).toNat)) :
    List.map V (byteAddrs x m) = List.map V0 (byteAddrs x m) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  obtain ⟨hk, ho⟩ := hx i hi
  rw [hag _ (Or.inr ⟨hk, ho⟩)]
  exact fr6_out V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx hS _ (by omega)

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ : Nat}

/-! ## One value -/

set_option maxHeartbeats 4000000 in
/-- From 307 after the `k`-th value: to the next (196) or to the end (264, `rax = p`). -/
theorem t307 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 307) (hL : Lr g0 Y.cpu.gpr p N k) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hL0 := hL
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11⟩ := hL0
  by_cases hl : k + 1 < N
  · refine (c_307 prof fb).run c hfs E.hin _ hK hA hr
      (vc_307l (by rw [l10, l3, Nlc.on1]; exact ne64 (by omega) (by omega) (by omega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    refine kn hl Z t₁ _ hKZ hAZ hrZ ?_ hag
    rw [hgZ]
    exact ⟨l1, l2, by show Y.cpu.gpr.rcx + 1#64 = _; rw [l3, Nlc.on1], l4, l5, l6, l7, l8, l9, l10, l11⟩
  · have he : Y.cpu.gpr.r13 = Y.cpu.gpr.rcx + 1#64 := by
      rw [l10, l3, Nlc.on1, show N = k + 1 by omega]
    refine (c_307 prof fb).run c hfs E.hin _ hK hA hr (vc_307e he) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    refine t264 c hfs E hKZ hAZ hrZ (by rw [hgZ]; exact l1) hag ⟨8 * N + 64, ?_⟩ kr
    rw [hgZ]
    show Res Wl Kk (8 * N + 64) Y.cpu.gpr.rax
    rw [l2]
    exact Or.inr hB

set_option maxHeartbeats 4000000 in
/-- From 299 (a string, `rdi = idx`): `data + idx` stored at `p + 8k + 64`, then 307. -/
theorem t299 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 299) (hL : Lr g0 Y.cpu.gpr p N k) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hB0 := hB
  obtain ⟨hw0, hw, hnk⟩ := hB0
  have ea : Y.cpu.gpr.rax + Y.cpu.gpr.rcx * 8#64 + 64#64 = Addr.add p (8 * k + 64) := by
    rw [hL.2.1, hL.2.2.1, sa]
  have en : (Addr.add p (8 * k + 64)).toNat = p.toNat + (8 * k + 64) :=
    toNat_add_of_fits (n := 8 * N + 64) (by omega) hw0
  refine (c_299 prof fb).run c hfs E.hin _ hK hA hr (vc_299 (by rw [ea]; exact Nlc.wsub hw (by omega))) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
  rw [ea] at hAZ
  exact t307 c hfs E hB hN hk hKZ hAZ hrZ (by rw [hgZ]; exact hL)
    (hag.st (by rw [toBytesLE_length, en]; omega)
      fun y hy => by rw [toBytesLE_length]; exact noK E.kf hnk (by rw [en]; omega) (by rw [en]; omega) y hy) kn kr

set_option maxHeartbeats 4000000 in
/-- From 336 (a word, `rsi = rdi = idx ≤ datasize`): misaligned, out by `free`; aligned, the u32 at `data + idx`
stored at `p + 8k + 64`, then 307. -/
theorem t336 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 336) (hL : Lr g0 Y.cpu.gpr p N k) (hdi : Y.cpu.gpr.rdi.toNat ≤ g0.rdx.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hB0 := hB
  obtain ⟨hw0, hw, hnk⟩ := hB0
  cases hm : (BitVec.setWidth 32 Y.cpu.gpr.rsi &&& 3#32 == 0)
  · refine (c_336 prof fb).run c hfs E.hin _ hK hA hr (vc_336a hm) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t240 c hfs E hfre hKZ hAZ hrZ (by rw [hgZ]; exact hL.1) hag kr
  · have ea : Y.cpu.gpr.rax + Y.cpu.gpr.rcx * 8#64 + 64#64 = Addr.add p (8 * k + 64) := by
      rw [hL.2.1, hL.2.2.1, sa]
    have en : (Addr.add p (8 * k + 64)).toNat = p.toNat + (8 * k + 64) :=
      toNat_add_of_fits (n := 8 * N + 64) (by omega) hw0
    have ed : Y.cpu.gpr.rbx + Y.cpu.gpr.rdi = Addr.add g0.rsi Y.cpu.gpr.rdi.toNat := by
      rw [hL.2.2.2.2.1, aI]
    have f1 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rbx + Y.cpu.gpr.rdi) i) := by
      intro i hi
      rw [ed, addr_add_add]
      exact E.fd _ (by omega)
    refine (c_336 prof fb).run c hfs E.hin _ hK hA hr
      (vc_336b hm f1 (by rw [ea]; exact Nlc.wsub hw (by omega))) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    rw [ea] at hAZ
    exact t307 c hfs E hB hN hk hKZ hAZ hrZ (by rw [hgZ]; exact hL)
      (hag.st (by rw [toBytesLE_length, en]; omega)
        fun y hy => by rw [toBytesLE_length]; exact noK E.kf hnk (by rw [en]; omega) (by rw [en]; omega) y hy) kn kr

set_option maxHeartbeats 4000000 in
/-- From 288 (`cnt ≤ lim c`, `rdi = idx ≤ datasize`): the type of the `k`-th value, then 336 (a word) or 299. -/
theorem t288 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N)
    (hkl : k ≤ lim.getD (BitVec.setWidth 32 g0.rdi).toNat 0)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 288) (hL : Lr g0 Y.cpu.gpr p N k) (hdi : Y.cpu.gpr.rdi.toNat ≤ g0.rdx.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s80
  have hL0 := hL
  obtain ⟨-, -, l3, -, -, -, -, l8, -, -, l11⟩ := hL0
  have et : Y.cpu.gpr.r10 + Y.cpu.gpr.r14 * 8#64 = tA g0 := by rw [l8, l11]
  have eT : tT V Y.cpu.gpr = rdq(V0, tA g0) := by
    show ofBytesLE 64 (List.map V (byteAddrs (Y.cpu.gpr.r10 + Y.cpu.gpr.r14 * 8#64) 8)) = _
    rw [et, rdK hS hag E.kT]
  have f1 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.r10 + Y.cpu.gpr.r14 * 8#64) i) := by
    rw [et]
    exact E.fT
  have f2 : ∀ i < 4, Foot F.data (Addr.add (tT V Y.cpu.gpr + Y.cpu.gpr.rcx * 4#64) i) := by
    rw [eT, l3]
    exact E.fY k hkl
  by_cases ht : ty V Y.cpu.gpr = 5#32
  · refine (c_288 prof fb).run c hfs E.hin _ hK hA hr (vc_288a f1 f2 ht) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t336 c hfs E hfre hB hN hk hKZ hAZ hrZ (by rw [hgZ]; exact hL) (by rw [hgZ]; exact hdi) hag kn kr
  · refine (c_288 prof fb).run c hfs E.hin _ hK hA hr (vc_288b f1 f2 ht) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t299 c hfs E hB hN hk hKZ hAZ hrZ (by rw [hgZ]; exact hL) hag kn kr

end

end FV7z.Ild
