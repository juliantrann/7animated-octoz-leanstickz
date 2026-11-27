import FV7z.Stl.Exits
import FV7z.Lemmas.Signed
/-!
# `____strtoul_l_internal`: after the digits (PLAN.md §M, M1)

From 368 (the end of the digit loop, `rdi = p + k`, `k ≤ n`) to the caller: 368 stores the end at `E` (if `E ≠ 0`)
and goes to 390 (digits read) or to 748 (no digit: `*E = p`, or after a lone `0x` `*E = rdi - 1`); 390 sets
`errno = ERANGE` (to 448) or pops and returns at 429.

- `c14_1`: `jle` after `cmp x, 1` for a small `x` is `x ≤ 1`. `am`, `ak`: addresses in the string.
- `fr6_out`, `rdK`: reads in `Kk` outside the frame read the entry's bytes.
- `Sv`: the string `p` (`n` bytes, then the NUL) and the `toupper` table (`CU`), what the tail reads.
- `t390`, `t748`, `t368`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Stm (Km stk)
open FV7z.Tun (Vst_out)
open FV7z.Mcn (fr6 rds rdo fr_e6 fr6_rd)
open FV7z.Nlc (Ag)
namespace FV7z.Stl

/-! ## Numbers -/

/-- `jle` after `cmp x, 1` (64 bits) for `x < 2^62`: `x ≤ 1`. -/
theorem c14_1 (f : Rflags) (x : BitVec 64) (hx : x.toNat < 2 ^ 62) :
    (subF f x 1#64).cond 14 = decide (x.toNat ≤ 1) := by
  rw [Sbrk.cond_14, subF_zf', subF_sf, subF_of, overflowSub]
  have ex := BitVec.msb_eq_decide x
  have er := BitVec.msb_eq_decide (x - 1#64)
  rw [BitVec.toNat_sub] at er
  have h1 : (1#64).msb = false := by decide
  have hz : (x - 1#64 == 0) = decide (x.toNat = 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    exact ⟨fun h => by bv_omega, fun h => by bv_omega⟩
  rw [hz, h1]
  have hxl := x.isLt
  cases hmx : x.msb <;> cases hmr : (x - 1#64).msb <;> rw [hmx] at ex <;> rw [hmr] at er <;>
    simp only [Bool.false_eq, Bool.true_eq, decide_eq_false_iff_not, decide_eq_true_eq, BitVec.toNat_ofNat] at ex er <;>
    rw [Bool.eq_iff_iff] <;> simp <;> omega

/-- `d` bytes back in the string. -/
theorem am (p : Addr) {k d : Nat} (h : d ≤ k) (hk : p.toNat + k < 2 ^ 64) (c : BitVec 64)
    (hc : c.toNat = 2 ^ 64 - d) : Addr.add p k + c = Addr.add p (k - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, hc]
  omega

theorem ak (p : Addr) (k : Nat) : Addr.add p k - p = BitVec.ofNat 64 k := by
  have := p.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem a0 (a : Addr) : Addr.add a 0 = a := by
  simp only [Addr.add]
  exact BitVec.add_zero a

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

/-- A read in `Kk` outside the frame `[S - 88, S)`: the entry's bytes. -/
theorem rdK {Kk : Addr → Prop} {V0 V : Addr → Byte} {g0 : Gprs} {x : Addr} {m : Nat} (hS : 80 ≤ g0.rsp.toNat)
    (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (hx : ∀ i < m, Kk (Addr.add x i) ∧
      ((Addr.add x i).toNat < g0.rsp.toNat - 88 ∨ g0.rsp.toNat ≤ (Addr.add x i).toNat)) :
    List.map V (byteAddrs x m) = List.map V0 (byteAddrs x m) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hy
  obtain ⟨hk, ho⟩ := hx i hi
  rw [hag _ (Or.inr ⟨hk, ho⟩)]
  exact fr6_out V0 g0.rsp g0.r15 g0.r14 g0.r13 g0.r12 g0.rbp g0.rbx hS _ (by omega)

/-! ## The string and the tables -/

/-- The string `p = rdi` (`n < 2^62` bytes, not 0, then the NUL), readable, kept (`Kk`) and outside the frame;
the pointer to the `toupper` table (`CU`, at 7935192) readable, kept and outside the frame, its entries readable. -/
structure Sv (F : Footprint) (Kk : Addr → Prop) (V0 : Addr → Byte) (g0 : Gprs) (n : Nat) : Prop where
  nl : n < 2 ^ 62
  pl : g0.rdi.toNat + n + 1 ≤ 2 ^ 64
  fp : ∀ k ≤ n, Foot F.data (Addr.add g0.rdi k)
  kp : ∀ k ≤ n, Kk (Addr.add g0.rdi k) ∧
    ((Addr.add g0.rdi k).toNat < g0.rsp.toNat - 88 ∨ g0.rsp.toNat ≤ (Addr.add g0.rdi k).toNat)
  nz : ∀ k < n, V0 (Addr.add g0.rdi k) ≠ 0
  z : V0 (Addr.add g0.rdi n) = 0
  fU : ∀ i < 8, Foot F.data (Addr.add 7935192#64 i)
  kU : ∀ i < 8, Kk (Addr.add 7935192#64 i) ∧
    ((Addr.add 7935192#64 i).toNat < g0.rsp.toNat - 88 ∨ g0.rsp.toNat ≤ (Addr.add 7935192#64 i).toNat)
  fUe : ∀ w : BitVec 8, ∀ i < 4, Foot F.data (Addr.add (Cu V0 + BitVec.signExtend 64 w * 4#64) i)

section
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {Kk : Addr → Prop} {V0 : Addr → Byte} {g0 : Gprs} {fb e₂ : Addr} {j₂ : Nat}

/-! ## The ways out after the digits -/

set_option maxHeartbeats 4000000 in
/-- From 390: `errno = ERANGE` (to 448), or the pops and the `ret` at 429. -/
theorem t390 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 390) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS : 80 ≤ g0.rsp.toNat := by omega
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := fr_e6 hS
  obtain ⟨u0, u1, u2, u3, u4, u5⟩ := u40 hS96 hS8
  obtain ⟨q0, q1, q2, q3, q4, q5, q6⟩ := q40 g0.rsp
  obtain ⟨-, -, e20, -⟩ := slots hS96
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
  have fS : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 20#64) i) := by
    rw [hsp]
    exact fun i hi => c.hws _ (stk E.wf (by omega) (by omega) (by omega) i hi)
  refine (c_390 prof fb).run c hfs E.hin _ hK hA hr
    (vc_390 E.ef fS (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))
      (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))
      (by rw [hsp]; exact ffr _ (by omega) (by omega)) (by rw [hsp]; exact ffr _ (by omega) (by omega))) ?_
  rintro j' g fl V' (⟨rfl, hV, hg⟩ | ⟨rfl, hV, hsp', hbx, hbp, h12, h13, h14, h15⟩) Z t₁ hKZ hAZ hrZ hgZ -
  · subst hV
    exact t448 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp)
      (hag.st (by rw [toBytesLE_length]; exact E.eo) fun y hy => by rw [toBytesLE_length]; exact E.ek y hy) kr
  · subst hV
    subst hgZ
    rw [hsp, q6] at hsp'
    rw [hsp, q0, g6] at hbx
    rw [hsp, q1, g5] at hbp
    rw [hsp, q2, g4] at h12
    rw [hsp, q3, g3] at h13
    rw [hsp, q4, g2] at h14
    rw [hsp, q5, g1] at h15
    refine c.s_ret hKZ hAZ E.hin (lt_len (by decide)) hrZ (ret_429 _) (by rw [hsp']; exact E.fra) hcR hjR
      (by rw [hsp']; exact gra) ?_
    rintro W t₂ hKW hAW ⟨hrW, hgW⟩
    exact kr W t₂ _ hKW hAW hag hrW (by rw [hgW]; show Z.cpu.gpr.rsp + 8 = _; rw [hsp'])
      ⟨(congrArg Gprs.rbx hgW).trans hbx, (congrArg Gprs.rbp hgW).trans hbp, (congrArg Gprs.r12 hgW).trans h12,
        (congrArg Gprs.r13 hgW).trans h13, (congrArg Gprs.r14 hgW).trans h14, (congrArg Gprs.r15 hgW).trans h15⟩

set_option maxHeartbeats 4000000 in
/-- From 748 (no digit, `rdi = p + k`): `E = 0` to 927; `k ≤ 1` to 790 (`*E = p`); else after `0x` to 927 with
`*E = rdi - 1`, or to 790. -/
theorem t748 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 748) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi) (h13 : Y.cpu.gpr.r13 = g0.rdi)
    (hdi : Y.cpu.gpr.rdi = Addr.add g0.rdi k) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  have hnl := Sw.nl
  have hpl := Sw.pl
  obtain ⟨e8, -, -, -⟩ := slots hS96
  have fE : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8#64) i) := by
    rw [hsp]
    exact fun i hi => c.hws _ (stk E.wf (by omega) (by omega) (by omega) i hi)
  by_cases hz : g0.rsi = 0#64
  · refine (c_748 prof fb).run c hfs E.hin _ hK hA hr (vc_748z (by rw [hsp, hEs, hz]) fE) ?_
    rintro j' g fl V' ⟨rfl, hV, hg⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst hV
    exact t927 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp) hag kr
  have hEv : rdq(V, Y.cpu.gpr.rsp + 8#64) = g0.rsi := by rw [hsp, hEs]
  have hn : ¬ rdq(V, Y.cpu.gpr.rsp + 8#64) = 0#64 := by rw [hEv]; exact hz
  have hd : Y.cpu.gpr.rdi - Y.cpu.gpr.r13 = BitVec.ofNat 64 k := by rw [hdi, h13, ak]
  have hkn : (BitVec.ofNat 64 k).toNat = k := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases h1 : k ≤ 1
  · refine (c_748 prof fb).run c hfs E.hin _ hK hA hr
      (vc_748s hn fE fun fl => by
        rw [hd, c14_1 fl (BitVec.ofNat 64 k) (by rw [hkn]; omega), hkn]; exact decide_eq_true h1) ?_
    rintro j' g fl V' ⟨rfl, hV, hg, -⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst hV
    exact t790 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp) hag hz hEs kr
  have hm1 : Y.cpu.gpr.rdi + 18446744073709551615#64 = Addr.add g0.rdi (k - 1) := by
    rw [hdi]
    exact am g0.rdi (by omega) (by omega) _ (by decide)
  have hm2 : Y.cpu.gpr.rdi + 18446744073709551614#64 = Addr.add g0.rdi (k - 2) := by
    rw [hdi]
    exact am g0.rdi (by omega) (by omega) _ (by decide)
  have hU : Cu V = Cu V0 := congrArg (ofBytesLE 64) (rdK (by omega) hag Sw.kU)
  refine (c_748 prof fb).run c hfs E.hin _ hK hA hr
    (vc_748l hn fE (by rw [hEv]; exact E.eW hz)
      (fun fl => by rw [hd, c14_1 fl (BitVec.ofNat 64 k) (by rw [hkn]; omega), hkn]; exact decide_eq_false h1)
      (fun i hi => by rw [show i = 0 by omega, hm1, a0]; exact Sw.fp _ (by omega))
      (fun i hi => by rw [show i = 0 by omega, hm2, a0]; exact Sw.fp _ (by omega))
      Sw.fU (by rw [hU, hm1]; exact Sw.fUe _)) ?_
  rintro j' g fl V' (⟨rfl, hV, hg, -⟩ | ⟨rfl, hV, hg⟩) Z t₁ hKZ hAZ hrZ hgZ -
  · subst hV
    exact t790 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp) hag hz hEs kr
  · subst hV
    rw [hEv] at hAZ
    exact t927 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp)
      (hag.st (by rw [toBytesLE_length]; exact E.eL hz) fun y hy => by rw [toBytesLE_length]; exact E.eK hz y hy) kr

set_option maxHeartbeats 4000000 in
/-- From 368 (the end of the digits, `rdi = p + k`): no digit to 748; else `*E = rdi` (if `E ≠ 0`) and 390. -/
theorem t368 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (E : Env F Wl L Kk V0 g0 fb e₂ j₂)
    {n : Nat} (Sw : Sv F Kk V0 g0 n) {k : Nat} (hk : k ≤ n)
    {Y : State} {t : Nat} {V : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V)
    (hr : Y.cpu.rip = stl_at.add 368) (hsp : Y.cpu.gpr.rsp = S88 g0.rsp) (hag : Ag (Kr Kk g0.rsp) (Vf V0 g0) V)
    (hEs : rdq(V, S88 g0.rsp + 8#64) = g0.rsi) (h13 : Y.cpu.gpr.r13 = g0.rdi)
    (hdi : Y.cpu.gpr.rdi = Addr.add g0.rdi k) (kr : Kret prof F Wl L s₀ o gev gP gE Kk V0 g0 (e₂.add j₂)) :
    GoG prof L o gev gP gE Y t := by
  have hS96 := E.s96
  have hS8 := E.s8
  have hl := g0.rsp.isLt
  obtain ⟨e8, -, -, -⟩ := slots hS96
  have fE : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 8#64) i) := by
    rw [hsp]
    exact fun i hi => c.hws _ (stk E.wf (by omega) (by omega) (by omega) i hi)
  have hEv : rdq(V, Y.cpu.gpr.rsp + 8#64) = g0.rsi := by rw [hsp, hEs]
  by_cases hz : g0.rsi = 0#64
  · refine (c_368 prof fb).run c hfs E.hin _ hK hA hr (vc_368z (by rw [hEv, hz]) fE) ?_
    rintro j' g fl V' (⟨rfl, hV, hg⟩ | ⟨rfl, hV, hg, -⟩) Z t₁ hKZ hAZ hrZ hgZ -
    · subst hV
      exact t748 c hfs E Sw hk hKZ hAZ hrZ (by rw [hgZ, hg]; exact hsp) hag hEs (by rw [hgZ, hg]; exact h13)
        (by rw [hgZ, hg]; exact hdi) kr
    · subst hV
      exact t390 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp) hag kr
  · have hn : (rdq(V, Y.cpu.gpr.rsp + 8#64) == 0) = false := by
      rw [hEv]
      exact beq_eq_false_iff_ne.2 hz
    refine (c_368 prof fb).run c hfs E.hin _ hK hA hr (vc_368n hn fE (by rw [hEv]; exact E.eW hz)) ?_
    rintro j' g fl V' (⟨rfl, hV, hg⟩ | ⟨rfl, hV, hg, -⟩) Z t₁ hKZ hAZ hrZ hgZ -
    · subst hV
      exact t748 c hfs E Sw hk hKZ hAZ hrZ (by rw [hgZ, hg]; exact hsp) hag hEs (by rw [hgZ, hg]; exact h13)
        (by rw [hgZ, hg]; exact hdi) kr
    · subst hV
      rw [hEv] at hAZ
      exact t390 c hfs E hKZ hAZ hrZ (by rw [hgZ]; show g.rsp = _; rw [hg]; exact hsp)
        (hag.st (by rw [toBytesLE_length]; exact E.eL hz) fun y hy => by rw [toBytesLE_length]; exact E.eK hz y hy) kr

end

end FV7z.Stl
