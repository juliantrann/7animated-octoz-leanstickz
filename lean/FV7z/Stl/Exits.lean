import FV7z.Stl.Holds
/-!
# `____strtoul_l_internal`: the ways out (PLAN.md §M, M1)

As `Ild/Holds.lean` (`t264`, `t248`): every way out passes 448 (the pops) and the `ret` at 462, with `rsp` the frame
`S88 S` and the bytes kept as the pushes' (`Ag (Kr Kk S) (Vf V0 g0) V`).

- `t448`: the pops and the `ret`; the caller's `Kret`.
- `t432`: `errno = EINVAL`, then 448. `t927`: to 448. `t790`: `*E = p` (`E ≠ 0` in the frame slot), then 448.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Mcn (fr6 rds rdo fr_e6 fr6_rd)
open FV7z.Nlc (Ag)
namespace FV7z.Stl

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ : Nat}

set_option maxHeartbeats 4000000 in
/-- From 448: the pops and the `ret` at 462. -/
theorem t448 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 448) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (k : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS : 80 ≤ g0.rsp.toNat := by omega
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  obtain ⟨u0, u1, u2, u3, u4, u5⟩ := u40 hS96 hS8
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := q40 g0.rsp
  have ffr : ∀ b : Addr, g0.rsp.toNat - 48 ≤ b.toNat → b.toNat + 8 ≤ g0.rsp.toNat →
      ∀ i < 8, Foot F.data (Addr.add b i) := fun b h1 h2 i hi => c.hws _ (stk E.wf (by omega) h2 (by omega) i hi)
  obtain ⟨r6, r5, r4, r3, r2, r1⟩ := fr6_rd V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx hS
  have g6 : rdq(V, g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) = g0.rbx :=
    (rdF (x := g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r6
  have g5 : rdq(V, g0.rsp - 8 - 8 - 8 - 8 - 8) = g0.rbp :=
    (rdF (x := g0.rsp - 8 - 8 - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r5
  have g4 : rdq(V, g0.rsp - 8 - 8 - 8 - 8) = g0.r12 :=
    (rdF (x := g0.rsp - 8 - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r4
  have g3 : rdq(V, g0.rsp - 8 - 8 - 8) = g0.r13 :=
    (rdF (x := g0.rsp - 8 - 8 - 8) hag (by omega) (by omega) hS8).trans r3
  have g2 : rdq(V, g0.rsp - 8 - 8) = g0.r14 := (rdF (x := g0.rsp - 8 - 8) hag (by omega) (by omega) hS8).trans r2
  have g1 : rdq(V, g0.rsp - 8) = g0.r15 := (rdF (x := g0.rsp - 8) hag (by omega) (by omega) hS8).trans r1
  have gra : rdq(V, g0.rsp) = e₂.add j₂ := (rdF (x := g0.rsp) hag (by omega) (Nat.le_refl _) hS8).trans
    ((fr6_ra V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx hS hS8).trans E.hra)
  obtain ⟨cR, hcR, hjR⟩ := E.rc
  refine (c_448 prof fb).run c hfs E.hin _ hK hA hr
    (vc_448 (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))
      (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))
      (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))) ?_
  rintro j' g fl V' ⟨rfl, hV, hsp', hbx, hbp, h12, h13, h14, h15⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  subst hgZ
  rw [hsp, q6] at hsp'
  rw [hsp, q0, g6] at hbx
  rw [hsp, q1, g5] at hbp
  rw [hsp, q2, g4] at h12
  rw [hsp, q3, g3] at h13
  rw [hsp, q4, g2] at h14
  rw [hsp, q5, g1] at h15
  refine c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_462 _) (by rw [hsp']; exact E.fra) hcR hjR
    (by rw [hsp']; exact gra) ?_
  rintro W t₂ hKW hAW ⟨hrW, hgW⟩
  exact k W t₂ _ hKW hAW hag hrW (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hsp'])
    ⟨(congrArg Gprs.rbx hgW).trans hbx, (congrArg Gprs.rbp hgW).trans hbp, (congrArg Gprs.r12 hgW).trans h12,
      (congrArg Gprs.r13 hgW).trans h13, (congrArg Gprs.r14 hgW).trans h14, (congrArg Gprs.r15 hgW).trans h15⟩

set_option maxHeartbeats 4000000 in
/-- From 432: `errno = EINVAL`, then 448. -/
theorem t432 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 432) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (k : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  refine (c_432 prof fb).run c hfs E.hin _ hK hA hr (vc_432 E.ef) ?_
  rintro j' g fl V' ⟨rfl, hV, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  exact t448 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp)
    (hag.st (by rw [toBytesLE_length]; exact E.eo) fun y hy => by rw [toBytesLE_length]; exact E.ek y hy) k

set_option maxHeartbeats 4000000 in
/-- From 927: to 448. -/
theorem t927 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 927) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (k : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  refine (c_927 prof fb).run c hfs E.hin _ hK hA hr vc_927 ?_
  rintro j' g fl V' ⟨rfl, hV, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  exact t448 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp) hag k

set_option maxHeartbeats 4000000 in
/-- From 790: `*E = p` (`E` in the frame slot, not 0), then 448. -/
theorem t790 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 790) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (hE0 : g0.rsi ≠ 0#64) (hEv : rdq(V, S88 g0.rsp + 8#64) = g0.rsi)
    (k : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  obtain ⟨e8, -, -, -⟩ := slots hS96
  have fE : ∀ i < 8, Foot F.data (Addr.add (S88 g0.rsp + 8#64) i) :=
    fun i hi => c.hws _ (stk E.wf (by omega) (by omega) (by omega) i hi)
  refine (c_790 prof fb).run c hfs E.hin _ hK hA hr
    (vc_790 (by rw [hsp]; exact fE) (by rw [hsp, hEv]; exact E.eW hE0)) ?_
  rintro j' g fl V' ⟨rfl, hV, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
  subst hV
  rw [hsp, hEv] at hAZ
  exact t448 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp)
    (hag.st (by rw [toBytesLE_length]; exact E.eL hE0) fun y hy => by rw [toBytesLE_length]; exact E.eK hE0 y hy) k

end

end FV7z.Stl
