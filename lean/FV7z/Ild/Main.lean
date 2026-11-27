import FV7z.Ild.Disp
/-!
# `_nl_intern_locale_data`: from the entry to the loop, and `ild_ok` (PLAN.md §M, M1)

- `oT`, `nN_lt`, `m8`, `m4`: `N` (a u32) as a number, `8N + 64` (`malloc`'s size), `4N + 8`.
- `agH`: the header's stores (in the new block) keep the bytes kept.
- `t127` (after `malloc`: `rax = 0` out; the header; `N = 0` out, else the loop by `lpAll`), `t122` (the `call` of
  `malloc`), `t65` (the magic, `N` against `_nl_category_num_items[c]`, `4N + 8 < datasize`), `t0` (the pushes,
  `datasize > 7`).
- `ild_ok`: from the entry with the registers `g0` and the bytes `V0`, given `Env`, `malloc` (`Mal`), `free`
  (`Fre`) and the caller's continuation (`Kret`), the run goes on to the goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Mcn (fr6 rds fr_e6)
open FV7z.Nlc (Ag Res)
namespace FV7z.Ild

/-! ## Numbers and bytes -/

theorem oT (x : Addr) : BitVec.ofNat 64 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem nN_lt (V : Addr → Byte) (g : Gprs) : (nN V g).toNat < 2 ^ 32 := by
  have := (ofBytesLE 32 (List.map V (byteAddrs (g.rbx + 4#64) 4))).isLt
  simp only [nN, BitVec.toNat_setWidth]
  omega

theorem m8 {x : Addr} (hx : x.toNat < 2 ^ 32) : x * 8#64 + 64#64 = BitVec.ofNat 64 (8 * x.toNat + 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem m4 {x : Addr} (hx : x.toNat < 2 ^ 32) : (x * 4#64 + 8#64).toNat = 4 * x.toNat + 8 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

/-- The header's stores at `p + 8 … p + 56` (in the block) keep the bytes kept. -/
theorem agH {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 g : Gprs} {Wl : List Rgn} {p : Addr} {N : Nat}
    (hkf : ∀ y : Addr, g0.rsp.toNat - 48 ≤ y.toNat → y.toNat < g0.rsp.toNat + 8 → Kk y)
    (hB : Bk Wl Kk p N) (hp : g.rax = p) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) :
    Ag (Kr Kk g0.rsp) (Vf V0 g0) (Vh V g) := by
  obtain ⟨hw0, -, hnk⟩ := hB
  have e : ∀ m, m + 8 ≤ 64 → (g.rax + BitVec.ofNat 64 m).toNat = p.toNat + m := by
    intro m hm
    rw [hp, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have st : ∀ (W : Addr → Byte) (m : Nat) (bs : List Byte), m + 8 ≤ 64 → bs.length ≤ 8 →
      Ag (Kr Kk g0.rsp) (Vf V0 g0) W →
      Ag (Kr Kk g0.rsp) (Vf V0 g0) (Vst W (g.rax + BitVec.ofNat 64 m) bs) := by
    intro W m bs hm hb h
    have ea := e m hm
    exact h.st (by rw [ea]; omega) fun y hy =>
      noK (a := g.rax + BitVec.ofNat 64 m) (m := bs.length) hkf hnk (by rw [ea]; omega) (by rw [ea]; omega) y hy
  exact st _ 56 _ (by omega) (by rw [toBytesLE_length]; omega)
    (st _ 48 _ (by omega) (by rw [toBytesLE_length]; omega)
      (st _ 40 _ (by omega) (by rw [toBytesLE_length]; omega)
        (st _ 32 _ (by omega) (by rw [toBytesLE_length]; omega)
          (st _ 16 _ (by omega) (by rw [toBytesLE_length]; omega)
            (st _ 8 _ (by omega) (by rw [toBytesLE_length]; omega) hag)))))

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ : Nat}

/-! ## From the entry to the loop -/

set_option maxHeartbeats 4000000 in
/-- From 127 (after `malloc`, `rax = p`, `r13 = N`): `p = 0` out; the header; `N = 0` out, else the loop. -/
theorem t127 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 127) (hsp : Y.cpu.gpr.rsp = S56 g0.rsp) (hbx : Y.cpu.gpr.rbx = g0.rsi)
    (hbp : Y.cpu.gpr.rbp = cZ g0) (h12 : Y.cpu.gpr.r12 = g0.rdx)
    (h14 : Y.cpu.gpr.r14 = BitVec.signExtend 64 (BitVec.setWidth 32 g0.rdi))
    (hN : Y.cpu.gpr.r13.toNat < 2 ^ 32) (hNd : 4 * Y.cpu.gpr.r13.toNat + 8 < g0.rdx.toNat)
    (hres : Res Wl Kk (8 * Y.cpu.gpr.r13.toNat + 64) Y.cpu.gpr.rax) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  cases hz : (Y.cpu.gpr.rax == 0)
  · have hB : Bk Wl Kk Y.cpu.gpr.rax Y.cpu.gpr.r13.toNat := by
      rcases hres with h0 | hB
      · rw [h0] at hz
        exact absurd hz (by decide)
      · exact hB
    have hw := hB.2.1
    have w1 := Nlc.wsub (e := 8) (m := 8) hw (by omega)
    have w2 := Nlc.wsub (e := 16) (m := 8) hw (by omega)
    have w3 := Nlc.wsub (e := 32) (m := 8) hw (by omega)
    have w4 := Nlc.wsub (e := 40) (m := 8) hw (by omega)
    have w5 := Nlc.wsub (e := 48) (m := 8) hw (by omega)
    have w6 := Nlc.wsub (e := 56) (m := 4) hw (by omega)
    have hag' := agH E.kf hB rfl hag
    cases hn : (Y.cpu.gpr.r13 == 0)
    · have hN0 : Y.cpu.gpr.r13.toNat ≠ 0 := fun h => by
        have e0 : Y.cpu.gpr.r13 = 0 := BitVec.eq_of_toNat_eq h
        rw [e0] at hn
        exact absurd hn (by decide)
      have hLr : Lr g0 { Y.cpu.gpr with
          rcx := 0#64, rdx := 7268832#64, r9 := BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbp),
          r10 := 7865536#64 } Y.cpu.gpr.rax Y.cpu.gpr.r13.toNat 0 :=
        ⟨hsp, rfl, rfl, rfl, hbx, hbp, by show BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbp) = _; rw [hbp, sw3],
          rfl, h12, (oT _).symm, h14⟩
      refine (c_127 prof fb).run c hfs E.hin _ hK hA hr (vc_127n hz hn w1 w2 w3 w4 w5 w6) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
      exact lpAll c hfs E hfre hB hN hNd kr (Y.cpu.gpr.r13.toNat - 1) 0 (by omega) Z t₁ _ hKZ hAZ hrZ
        (by rw [hgZ]; exact hLr) hag'
    · refine (c_127 prof fb).run c hfs E.hin _ hK hA hr (vc_127e hz hn w1 w2 w3 w4 w5 w6) ?_
      rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
      exact t264 c hfs E hKZ hAZ hrZ (by rw [hgZ]; exact hsp) hag' ⟨8 * Y.cpu.gpr.r13.toNat + 64, by rw [hgZ]; exact hres⟩ kr
  · refine (c_127 prof fb).run c hfs E.hin _ hK hA hr (vc_127z hz) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t264 c hfs E hKZ hAZ hrZ (by rw [hgZ]; exact hsp) hag ⟨8 * Y.cpu.gpr.r13.toNat + 64, by rw [hgZ]; exact hres⟩ kr

set_option maxHeartbeats 4000000 in
/-- From 122: the `call` of `malloc` with `rdi = 8N + 64`, then 127. -/
theorem t122 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 122) (hsp : Y.cpu.gpr.rsp = S56 g0.rsp) (hbx : Y.cpu.gpr.rbx = g0.rsi)
    (hbp : Y.cpu.gpr.rbp = cZ g0) (h12 : Y.cpu.gpr.r12 = g0.rdx)
    (h14 : Y.cpu.gpr.r14 = BitVec.signExtend 64 (BitVec.setWidth 32 g0.rdi))
    (hN : Y.cpu.gpr.r13.toNat < 2 ^ 32) (hNd : 4 * Y.cpu.gpr.r13.toNat + 8 < g0.rdx.toNat)
    (hdi : Y.cpu.gpr.rdi = BitVec.ofNat 64 (8 * Y.cpu.gpr.r13.toNat + 64)) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s80
  have hl := g0.rsp.isLt
  have e64 := s64_e hS
  obtain ⟨cM, hcM, hM0⟩ := E.mc
  refine c.s_call hK hA E.hin (lt_len (by decide)) hr (call_122 _) hcM hM0 ml_122
    (by rw [hsp]; exact stk E.wf (by omega) (by omega) (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp] at hA₂
  have esp₂ : Y₂.cpu.gpr.rsp = S56 g0.rsp - 8 := by
    rw [hg₂]
    show Y.cpu.gpr.rsp - 8 = _
    rw [hsp]
  refine hmal (8 * Y.cpu.gpr.r13.toNat + 64) Y₂ t₂ _ _ hK₂ hA₂ hr₂ esp₂ (rds (by rw [e64]; omega))
    (by rw [hg₂]; exact hdi) ?_
  intro Z t' V' hKZ hAZ hkp hrZ hspZ hkm hres
  rw [hg₂] at hkm
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := hkm
  exact t127 c hfs E hfre hKZ hAZ hrZ hspZ (k1.trans hbx) (k2.trans hbp) (k3.trans h12) (k5.trans h14)
    (by rw [k4]; exact hN) (by rw [k4]; exact hNd) (by rw [k4]; exact hres) (agC hS E.kf hag hkp) kr

set_option maxHeartbeats 4000000 in
/-- From 65 (`datasize > 7`): a wrong magic, `N < _nl_category_num_items[c]` or `4N + 8 ≥ datasize` out (248);
else `r13 = N`, `r14 = sext c`, `rdi = 8N + 64`, then the `call` (122). -/
theorem t65 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = ild_at.add 65) (hsp : Y.cpu.gpr.rsp = S56 g0.rsp) (hbx : Y.cpu.gpr.rbx = g0.rsi)
    (h12 : Y.cpu.gpr.r12 = g0.rdx) (hbp : Y.cpu.gpr.rbp = cZ g0) (hd7 : 7 < g0.rdx.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have f1 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 4#64) i) := by
    intro i hi
    rw [hbx, show g0.rsi + 4#64 = Addr.add g0.rsi 4 from rfl, addr_add_add]
    exact E.fd _ (by omega)
  have f2 : ∀ i < 8, Foot F.data (Addr.add (ia Y.cpu.gpr) i) := by
    show ∀ i < 8,
      Foot F.data (Addr.add (7270432#64 + BitVec.signExtend 64 (BitVec.setWidth 32 Y.cpu.gpr.rbp) * 8#64) i)
    rw [hbp, sw3]
    exact E.fI
  by_cases hm : BitVec.setWidth 32 Y.cpu.gpr.rdx = BitVec.setWidth 32 Y.cpu.gpr.rax
  · by_cases hi : (nN V Y.cpu.gpr).toNat < (nI V Y.cpu.gpr).toNat
    · refine (c_65 prof fb).run c hfs E.hin _ hK hA hr (vc_65b hm f1 f2 hi) ?_
      rintro j' g fl V' ⟨rfl, rfl, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
      exact t248 c hfs E hKZ hAZ hrZ (by rw [hgZ, hg, hsp]) hag kr
    · by_cases h4 : (nN V Y.cpu.gpr * 4#64 + 8#64).toNat < Y.cpu.gpr.r12.toNat
      · have hN := nN_lt V Y.cpu.gpr
        have q14 : BitVec.signExtend 64 (BitVec.setWidth 32 Y.cpu.gpr.rbp) =
            BitVec.signExtend 64 (BitVec.setWidth 32 g0.rdi) := by
          rw [hbp, sw3]
        have qd : 4 * (nN V Y.cpu.gpr).toNat + 8 < g0.rdx.toNat := by
          rw [← m4 hN, ← h12]
          exact h4
        have qi : nN V Y.cpu.gpr * 8#64 + 64#64 = BitVec.ofNat 64 (8 * (nN V Y.cpu.gpr).toNat + 64) := m8 hN
        refine (c_65 prof fb).run c hfs E.hin _ hK hA hr (vc_65d hm f1 f2 hi h4) ?_
        rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
        exact t122 c hfs E hmal hfre hKZ hAZ hrZ (by rw [hgZ]; exact hsp) (by rw [hgZ]; exact hbx)
          (by rw [hgZ]; exact hbp) (by rw [hgZ]; exact h12) (by rw [hgZ]; exact q14) (by rw [hgZ]; exact hN)
          (by rw [hgZ]; exact qd) (by rw [hgZ]; exact qi) hag kr
      · refine (c_65 prof fb).run c hfs E.hin _ hK hA hr (vc_65c hm f1 f2 hi h4) ?_
        rintro j' g fl V' ⟨rfl, rfl, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
        exact t248 c hfs E hKZ hAZ hrZ (by rw [hgZ, hg, hsp]) hag kr
  · refine (c_65 prof fb).run c hfs E.hin _ hK hA hr (vc_65a hm) ?_
    rintro j' g fl V' ⟨rfl, rfl, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact t248 c hfs E hKZ hAZ hrZ (by rw [hgZ, hg, hsp]) hag kr

set_option maxHeartbeats 4000000 in
/-- From the entry (`rsp = S`, the registers `g0`, the bytes `V0`): the pushes; `datasize ≤ 7` out (248), else 65. -/
theorem t0 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V0) (hr : Y.cpu.rip = ild_at.add 0)
    (hg : Y.cpu.gpr = g0) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS := E.s80
  have hl := g0.rsp.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  have w : ∀ b : Addr, g0.rsp.toNat - 56 ≤ b.toNat → b.toNat + 8 ≤ g0.rsp.toNat →
      ∀ i < 8, Foot Wl (Addr.add b i) := fun b h1 h2 => stk E.wf (by omega) h2 (by omega)
  have w1 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w2 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w3 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w4 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w5 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have w6 : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 - 8) i) := by
    rw [hg]
    exact w _ (by omega) (by omega)
  have hag : Ag (Kr Kk g0.rsp) (Vf V0 g0)
      (fr6 V0 Y.cpu.gpr.rsp Y.cpu.gpr.r15 Y.cpu.gpr.r14 Y.cpu.gpr.r13 Y.cpu.gpr.r12 Y.cpu.gpr.rbp Y.cpu.gpr.rbx) := by
    rw [hg]
    exact fun _ _ => rfl
  cases hd : (decide (Y.cpu.gpr.rdx.toNat < 7) || decide (Y.cpu.gpr.rdx = 7#64))
  · have hd7 : 7 < g0.rdx.toNat := by
      rw [be _ 7 (by decide)] at hd
      have h := of_decide_eq_false hd
      rw [hg] at h
      omega
    have f1 : ∀ i < 4, Foot F.data (Addr.add Y.cpu.gpr.rsi i) := by
      rw [hg]
      intro i hi
      exact E.fd i (by omega)
    refine (c_0 prof fb).run c hfs E.hin _ hK hA hr (vc_0n hd w1 w2 w3 w4 w5 w6 f1) ?_
    rintro j' g fl V' ⟨rfl, rfl, h1, h2, h3, h4⟩ Z t₁ hKZ hAZ hrZ hgZ -
    rw [← hgZ] at h1 h2 h3 h4
    exact t65 c hfs E hmal hfre hKZ hAZ hrZ (by rw [h1, hg]) (by rw [h2, hg]) (by rw [h3, hg]) (by rw [h4, hg])
      hd7 hag kr
  · refine (c_0 prof fb).run c hfs E.hin _ hK hA hr (vc_0e hd w1 w2 w3 w4 w5 w6) ?_
    rintro j' g fl V' ⟨rfl, rfl, h1⟩ Z t₁ hKZ hAZ hrZ hgZ -
    rw [← hgZ] at h1
    exact t248 c hfs E hKZ hAZ hrZ (by rw [h1, hg]) hag kr

/-- `_nl_intern_locale_data` (`0x615210`): from the entry with the registers `g0` and the bytes `V0`, given `Env`,
`malloc` (`Mal`), `free` (`Fre`) and the caller's continuation at the return address (`Kret`: `rsp = S + 8`, the
registers a call keeps, the bytes kept as the pushes' where kept, `rax` 0 or a block `malloc` gave), the run goes
on to the goal. -/
theorem ild_ok (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    (hmal : Mal prof F Wl L s₀ o gev gP gE g0.rsp Kk) (hfre : Fre prof F Wl L s₀ o gev gP gE g0.rsp Kk)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V0) (hr : X.cpu.rip = ild_at)
    (hg : X.cpu.gpr = g0) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE X t :=
  t0 c hfs E hmal hfre hK hA (hr.trans (by decide : ild_at = ild_at.add 0)) hg kr

end

end FV7z.Ild
