import FV7z.Ild.Loop
import FV7z.Hca.Holds
/-!
# `_nl_intern_locale_data`: the loop's head and the cases (PLAN.md §M, M1)

From 196 with `cnt = k`: `idx` (the u32 at `data + 8 + 4k`) past `datasize` goes out by `free`; else the jump
through `ild_jt` (read as at the entry: it is in `Kk`, outside the frame) to the category's case `ild_cases[c]`,
which checks `cnt ≤ lim c` (to 288, else out by `free`); `c = 0` (435) stores strings past 85 without a type, and
`c = 9` (318) reads the type itself.

- `ia4`, `jt4`, `sw3`, `jtV`: the offset's address, the table entry's address, `c` through `ebp`, the case reached.
- `tcs`: a case `cnt ≤ K` (to 288) or not (to 240), for the generated pair `vc_ℓt`/`vc_ℓf`.
- `t435`, `t318`: the cases of `c = 0` and `c = 9`.
- `t196`: the loop's head.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Nlc (Ag Res)
namespace FV7z.Ild

/-! ## Numbers and bytes -/

/-- The address of the `k`-th offset. -/
theorem ia4 (a : Addr) (k : Nat) : a + BitVec.ofNat 64 k * 4#64 + 8#64 = Addr.add a (4 * k + 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- The address of the jump table's entry `x`. -/
theorem jt4 (x : BitVec 32) : 7268832#64 + BitVec.setWidth 64 x * 4#64 = Addr.add 7268832#64 (4 * x.toNat) := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw3 (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = x := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ : Nat}

/-- The jump table's entry for `c`, read where the bytes kept are the pushes': the case `ild_cases[c]`. -/
theorem jtV (E : Env F Wl L Kk V0 g0 fb e₂ j₂) {V : Addr → Byte} (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) :
    BitVec.signExtend 64 (ofBytesLE 32 (List.map V (byteAddrs (7268832#64 + cZ g0 * 4#64) 4))) + 7268832#64 =
      Addr.add ild_at (ild_cases.getD (BitVec.setWidth 32 g0.rdi).toNat 0) := by
  have hc := E.c12
  have h1 : ∀ i < 4, Kk (Addr.add (Addr.add 7268832#64 (4 * (BitVec.setWidth 32 g0.rdi).toNat)) i) ∧
      ((Addr.add (Addr.add 7268832#64 (4 * (BitVec.setWidth 32 g0.rdi).toNat)) i).toNat < g0.rsp.toNat - 64 ∨
        g0.rsp.toNat ≤ (Addr.add (Addr.add 7268832#64 (4 * (BitVec.setWidth 32 g0.rdi).toNat)) i).toNat) := by
    intro i hi
    rw [addr_add_add]
    exact E.kJ _ (by omega)
  have h2 := Hca.sub_rd V0 7268832#64 ild_jt 52 E.jt (4 * (BitVec.setWidth 32 g0.rdi).toNat) 4 (by omega)
  rw [jt4, rdK E.s80 hag h1, h2]
  exact jt_case _ (by omega)

/-! ## The cases -/

set_option maxHeartbeats 4000000 in
/-- A case `ℓ` checking `cnt ≤ K` (`K = lim c`): to 288, else to 240. -/
theorem tcs (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N)
    {ℓ K cv : Nat} {W : Wpt} (C : SpF prof ild ild_at fb ℓ W) (hK64 : K < 2 ^ 64)
    (hcv : (BitVec.setWidth 32 g0.rdi).toNat = cv) (hKl : K = lim.getD cv 0)
    (vt : ∀ {g : Gprs} {f : Rflags} {V : Addr → Byte},
      (decide (g.rcx.toNat < K) || decide (g.rcx = BitVec.ofNat 64 K)) = true →
      W F Wl (fun j' g' _ V' => j' = 288 ∧ V' = V ∧ g' = g) g f V)
    (vf : ∀ {g : Gprs} {f : Rflags} {V : Addr → Byte},
      (decide (g.rcx.toNat < K) || decide (g.rcx = BitVec.ofNat 64 K)) = false →
      W F Wl (fun j' g' _ V' => j' = 240 ∧ V' = V ∧ g' = g) g f V)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add ℓ) (hL : Lr g0 Y.cpu.gpr p N k) (hdi : Y.cpu.gpr.rdi.toNat ≤ g0.rdx.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hk64 : k < 2 ^ 64 := by omega
  have eb : (decide (Y.cpu.gpr.rcx.toNat < K) || decide (Y.cpu.gpr.rcx = BitVec.ofNat 64 K)) =
      decide (k ≤ K) := by
    rw [be _ K hK64, hL.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  by_cases h : k ≤ K
  · refine C.run c hfs E.hin _ hK hA hr (vt (by rw [eb]; exact decide_eq_true h)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    have hkl : k ≤ lim.getD (BitVec.setWidth 32 g0.rdi).toNat 0 := by
      rw [hcv, ← hKl]
      exact h
    exact t288 c hfs E hfre hB hN hk hkl hKZ hAZ hrZ (by rw [hgZ]; exact hL) (by rw [hgZ]; exact hdi) hag kn kr
  · refine C.run c hfs E.hin _ hK hA hr (vf (by rw [eb]; exact decide_eq_false h)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t240 c hfs E hfre hKZ hAZ hrZ (by rw [hgZ]; exact hL.1) hag kr

set_option maxHeartbeats 4000000 in
/-- `c = 0` (435): `cnt ≤ 85` to 288; past it, a string without a type (299). -/
theorem t435 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N)
    (hcv : (BitVec.setWidth 32 g0.rdi).toNat = 0)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 435) (hL : Lr g0 Y.cpu.gpr p N k) (hdi : Y.cpu.gpr.rdi.toNat ≤ g0.rdx.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hk64 : k < 2 ^ 64 := by omega
  have e0 : BitVec.setWidth 32 g0.rdi = 0#32 := BitVec.eq_of_toNat_eq hcv
  have hz : (BitVec.setWidth 32 Y.cpu.gpr.rbp == 0) = true := by
    rw [hL.2.2.2.2.2.1, sw3, e0]
    all_goals decide
  have eb : (decide (Y.cpu.gpr.rcx.toNat < 85) || decide (Y.cpu.gpr.rcx = 85#64)) = decide (k ≤ 85) := by
    rw [be _ 85 (by decide), hL.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  by_cases h : k ≤ 85
  · refine (c_435 prof fb).run c hfs E.hin _ hK hA hr (vc_435b hz (by rw [eb]; exact decide_eq_true h)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    have hkl : k ≤ lim.getD (BitVec.setWidth 32 g0.rdi).toNat 0 := by
      rw [hcv]
      exact h
    exact t288 c hfs E hfre hB hN hk hkl hKZ hAZ hrZ (by rw [hgZ]; exact hL) (by rw [hgZ]; exact hdi) hag kn kr
  · refine (c_435 prof fb).run c hfs E.hin _ hK hA hr (vc_435a hz (by rw [eb]; exact decide_eq_false h)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t299 c hfs E hB hN hk hKZ hAZ hrZ (by rw [hgZ]; exact hL) hag kn kr

set_option maxHeartbeats 4000000 in
/-- `c = 9` (318): `cnt ≤ 12`, then the type (336 a word, 299 not); else to 240. -/
theorem t318 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N)
    (hcv : (BitVec.setWidth 32 g0.rdi).toNat = 9)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 318) (hL : Lr g0 Y.cpu.gpr p N k) (hdi : Y.cpu.gpr.rdi.toNat ≤ g0.rdx.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s80
  have hk64 : k < 2 ^ 64 := by omega
  have hL0 := hL
  obtain ⟨-, -, l3, -, -, -, -, l8, -, -, l11⟩ := hL0
  have eb : (decide (Y.cpu.gpr.rcx.toNat < 12) || decide (Y.cpu.gpr.rcx = 12#64)) = decide (k ≤ 12) := by
    rw [be _ 12 (by decide), l3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk64]
  by_cases h : k ≤ 12
  · have hkl : k ≤ lim.getD (BitVec.setWidth 32 g0.rdi).toNat 0 := by
      rw [hcv]
      exact h
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
    have ht' : (decide (Y.cpu.gpr.rcx.toNat < 12) || decide (Y.cpu.gpr.rcx = 12#64)) = true := by
      rw [eb]
      exact decide_eq_true h
    by_cases ht : ty V Y.cpu.gpr = 5#32
    · refine (c_318 prof fb).run c hfs E.hin _ hK hA hr (vc_318a ht' f1 f2 ht) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
      exact t336 c hfs E hfre hB hN hk hKZ hAZ hrZ (by rw [hgZ]; exact hL) (by rw [hgZ]; exact hdi) hag kn kr
    · refine (c_318 prof fb).run c hfs E.hin _ hK hA hr (vc_318b ht' f1 f2 ht) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
      exact t299 c hfs E hB hN hk hKZ hAZ hrZ (by rw [hgZ]; exact hL) hag kn kr
  · refine (c_318 prof fb).run c hfs E.hin _ hK hA hr (vc_318f (by rw [eb]; exact decide_eq_false h)) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t240 c hfs E hfre hKZ hAZ hrZ (by rw [hgZ]; exact hL.1) hag kr

/-! ## The loop's head -/

set_option maxHeartbeats 4000000 in
/-- From 196 with `cnt = k` (`4N + 8 < datasize`): `idx` past `datasize` out by `free`, else the category's case. -/
theorem t196 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {p : Addr} {N k : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hk : k < N) (hNd : 4 * N + 8 < g0.rdx.toNat)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 196) (hL : Lr g0 Y.cpu.gpr p N k) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kn : k + 1 < N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N (k + 1))
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hL0 := hL
  obtain ⟨l1, -, l3, l4, l5, l6, l7, -, l9, -⟩ := hL0
  have hc := E.c12
  have hc6 := E.c6
  have ex : Y.cpu.gpr.rbx + Y.cpu.gpr.rcx * 4#64 + 8#64 = Addr.add g0.rsi (4 * k + 8) := by rw [l5, l3, ia4]
  have f1 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rbx + Y.cpu.gpr.rcx * 4#64 + 8#64) i) := by
    intro i hi
    rw [ex, addr_add_add]
    exact E.fd _ (by omega)
  by_cases hb : Y.cpu.gpr.r12.toNat < (ix V Y.cpu.gpr).toNat
  · refine (c_196 prof fb).run c hfs E.hin _ hK hA hr (vc_196b hb f1) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t240 c hfs E hfre hKZ hAZ hrZ (by rw [hgZ]; exact l1) hag kr
  · have hcb : (BitVec.setWidth 32 Y.cpu.gpr.rbp).toNat ≤ 12 := by
      rw [l6, sw3]
      exact hc
    have hf : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rdx + Y.cpu.gpr.r9 * 4#64) i) := by
      intro i hi
      rw [l4, l7, jt4, addr_add_add]
      exact E.fJ _ (by omega)
    have ht : BitVec.signExtend 64 (ofBytesLE 32 (List.map V (byteAddrs (Y.cpu.gpr.rdx + Y.cpu.gpr.r9 * 4#64) 4))) +
        Y.cpu.gpr.rdx = Addr.add ild_at (ild_cases.getD (BitVec.setWidth 32 g0.rdi).toNat 0) := by
      rw [l4, l7]
      exact jtV E hag
    have hd0 : (ix V Y.cpu.gpr).toNat ≤ g0.rdx.toNat := by
      rw [← l9]
      omega
    have hℓ : ild_cases.getD (BitVec.setWidth 32 g0.rdi).toNat 0 < ild.length := lt_len (cs_ok _ (by omega))
    refine (c_196 prof fb).run c hfs E.hin _ hK hA hr
      (vc_196c (Q := fun j' g' _ V' => j' = ild_cases.getD (BitVec.setWidth 32 g0.rdi).toNat 0 ∧ V' = V ∧
        g' = { Y.cpu.gpr with
          rsi := ix V Y.cpu.gpr, rdi := ix V Y.cpu.gpr,
          r8 := Addr.add ild_at (ild_cases.getD (BitVec.setWidth 32 g0.rdi).toNat 0) })
        hb hcb f1 fun _ => vc_217 hf ht hℓ fun _ => ⟨rfl, rfl, rfl⟩) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    have hLZ : Lr g0 Z.cpu.gpr p N k := by
      rw [hgZ]
      exact hL
    have hdZ : Z.cpu.gpr.rdi.toNat ≤ g0.rdx.toNat := by
      rw [hgZ]
      exact hd0
    have hc13 : (BitVec.setWidth 32 g0.rdi).toNat < 13 := by omega
    generalize hcv : (BitVec.setWidth 32 g0.rdi).toNat = cv at hc13 hrZ
    match cv, hcv, hrZ, hc13 with
    | 0, h, hr', _ => exact t435 c hfs E hfre hB hN hk h hKZ hAZ hr' hLZ hdZ hag kn kr
    | 1, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 5) (c_420 prof fb) (by decide) h rfl vc_420t vc_420f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 2, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 158) (c_402 prof fb) (by decide) h rfl vc_402t vc_402f hKZ hAZ hr' hLZ
        hdZ hag kn kr
    | 3, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 18) (c_391 prof fb) (by decide) h rfl vc_391t vc_391f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 4, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 45) (c_380 prof fb) (by decide) h rfl vc_380t vc_380f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 5, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 4) (c_279 prof fb) (by decide) h rfl vc_279t vc_279f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 6, h, _, _ => exact absurd h hc6
    | 7, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 2) (c_358 prof fb) (by decide) h rfl vc_358t vc_358f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 8, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 6) (c_350 prof fb) (by decide) h rfl vc_350t vc_350f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 9, h, hr', _ => exact t318 c hfs E hfre hB hN hk h hKZ hAZ hr' hLZ hdZ hag kn kr
    | 10, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 4) (c_279 prof fb) (by decide) h rfl vc_279t vc_279f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 11, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 1) (c_228 prof fb) (by decide) h rfl vc_228t vc_228f hKZ hAZ hr' hLZ hdZ
        hag kn kr
    | 12, h, hr', _ =>
      exact tcs c hfs E hfre hB hN hk (K := 15) (c_369 prof fb) (by decide) h rfl vc_369t vc_369f hKZ hAZ hr' hLZ
        hdZ hag kn kr
    | n + 13, _, _, h13 => exact absurd h13 (by omega)

/-- The loop from `cnt = k`, `m + 1` values left. -/
theorem lpAll (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {p : Addr} {N : Nat} (hB : Bk Wl Kk p N) (hN : N < 2 ^ 32) (hNd : 4 * N + 8 < g0.rdx.toNat)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    ∀ m k, k + m + 1 = N → LpAt prof F Wl L s₀ o gev gP gE Kk V0 g0 p N k := by
  intro m
  induction m with
  | zero =>
    intro k hk Y t V hK hA hr hL hag
    exact t196 c hfs E hfre hB hN (by omega) hNd hK hA hr hL hag (fun h => absurd h (by omega)) kr
  | succ m ih =>
    intro k hk Y t V hK hA hr hL hag
    exact t196 c hfs E hfre hB hN (by omega) hNd hK hA hr hL hag (fun _ => ih (k + 1) (by omega)) kr

end

end FV7z.Ild
