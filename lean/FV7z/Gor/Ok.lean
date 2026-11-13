import FV7z.Gor.Run
/-!
# `_dl_get_origin` from its entry to the caller (PLAN.md G3, startup)

`gor_ok`: `gor_head` (the prologue, `readlink ("/proc/self/exe")` inline, the loop back to the last `/`), then the
`malloc` of the directory (`g124`, `g278`, `mal_firstn`) and the copy: to the caller with `rax = p` (the copy, NUL
ended, in the first chunk of the heap) and the five registers a call keeps as at the entry; or, `readlink` failing, to
the `ret` with `rax = -1` (`ke`, as in `gor_head`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Smm (corr size smEv smEv2)
open FV7z.Mhi (Tp C2)
open FV7z.Mal (MPre After)
namespace FV7z.Gor

variable {prof : Profile} {F : Footprint} {Wl N : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64}

/-- The bytes at the `malloc` of `_dl_get_origin`: the entry's (`V`), the four saved registers below `rsp` (`frV`), the
answer `x` of `readlink` at `B = rsp - 4136`. -/
abbrev Vg (V : Addr → Byte) (g : Gprs) (x : ExePath) : Addr → Byte := Vst (frV V g) (g.rsp - 4136#64) x.bytes

theorem Vg_lo {V : Addr → Byte} {g : Gprs} {x : ExePath} (h32 : 8192 ≤ g.rsp.toNat) (hl : x.bytes.length < 4096)
    {a : Addr} (ha : a.toNat < g.rsp.toNat - 4136) : Vg V g x a = V a := by
  have hB : (g.rsp - 4136#64).toNat = g.rsp.toNat - 4136 := by bv_omega
  unfold Vg
  rw [Tun.Vst_out _ _ _ _ (by rw [hB]; have := g.rsp.isLt; omega) (.inl (by rw [hB]; omega)),
    frV_out V g a (by omega) (.inl (by omega))]

theorem Vg_hi {V : Addr → Byte} {g : Gprs} {x : ExePath} (h32 : 8192 ≤ g.rsp.toNat) (hl : x.bytes.length < 4096)
    {a : Addr} (ha : g.rsp.toNat ≤ a.toNat) : Vg V g x a = V a := by
  have hB : (g.rsp - 4136#64).toNat = g.rsp.toNat - 4136 := by bv_omega
  unfold Vg
  rw [Tun.Vst_out _ _ _ _ (by rw [hB]; have := g.rsp.isLt; omega) (.inr (by rw [hB]; omega)),
    frV_out V g a (by omega) (.inr ha)]

/-- `_dl_get_origin` from its entry (`rsp`, bytes `V`): on `readlink`'s answer `x` (`/proc/self/exe`), `malloc (n)`
and the copy of the `s` bytes of the directory to `p = Tp b + 16`, to the return address with `rax = p` (`k`); or
`rax = -1` at the `ret` (`ke`). -/
theorem gor_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor)
    (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx) {X : State} {t : Nat} {V : Addr → Byte}
    {e' : Addr} {code cpy : List Byte} {j : Nat} {Pm : (Addr → Byte) → Prop}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gor_at)
    (h32 : 8192 ≤ X.cpu.gpr.rsp.toNat) (htop : X.cpu.gpr.rsp.toNat ≤ userPtrMax prof.feat)
    (hrt : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hst : ∀ i < 4136, Foot Wl (Addr.add (X.cpu.gpr.rsp - 4136#64) i))
    (hsm : ∀ i < 408, Foot Wl (Addr.add (X.cpu.gpr.rsp - 4136#64 - 240#64 - 168) i))
    (hlo : 8029888 + 408 ≤ X.cpu.gpr.rsp.toNat - 4136)
    (hbs : (b + size pad 656#64).toNat + 4096 + 408 + 4136 ≤ X.cpu.gpr.rsp.toNat)
    (hbuf : ∀ i < 4096, Foot F.data (Addr.add (X.cpu.gpr.rsp - 4136#64) i))
    (hfr : ∀ i < 40, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32#64) i))
    (hpf : ∀ i < 16, Foot F.data (Addr.add 7366691#64 i)) (hpn : ∀ i < 14, V (Addr.add 7366691#64 i) ≠ 0)
    (hpz : V (Addr.add 7366691#64 14) = 0) (hpp : (byteAddrs 7366691#64 14).map V = pse)
    (hof : ∀ i < 8, Foot F.data (Addr.add (8029440#64) i)) (hoz : rdq(V, 8029440#64) = 0#64)
    (hps : ProcSelfExe o) (hpre : MPre F V b fsb pad sm mx)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : PcpyAt prof L o 4198592#64 Pm)
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pm W)
    (hinr : CodeIn L e' code) (hj : j < code.length) (hra : rdq(V, X.cpu.gpr.rsp) = e'.add j)
    (ke : ∀ r Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (frV V X.cpu.gpr) → Z.cpu.rip = gor_at.add 271 →
      Z.cpu.gpr.rax = 18446744073709551615#64 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp → Z.cpu.gpr.rbx = X.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv X.cpu.gpr r]) gP gE Z t')
    (k : ∀ (x : ExePath) (n s : Nat) (s₁ : State) (Vc M W : Addr → Byte) (evs : List Event) (Z : State) (t' : Nat)
      (g : Gprs), x.bytes.length < 4096 →
      Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + size pad 656#64 + C2 b pad) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem W →
      2 ≤ n → n ≤ 4097 → 1 ≤ s → s + 1 ≤ n → g.rsp = X.cpu.gpr.rsp - 4136#64 - 8 →
      (∀ a : Addr, a.toNat < X.cpu.gpr.rsp.toNat - 4144 ∨ X.cpu.gpr.rsp.toNat - 4136 ≤ a.toNat →
        Vc a = Vg V X.cpu.gpr x a) →
      After fsb (X.cpu.gpr.rsp - 4136#64 - 240#64) b pad sm (nbOf n) g Vc M →
      (∀ a : Addr, X.cpu.gpr.rsp.toNat - 4136 ≤ a.toNat → M a = Vg V X.cpu.gpr x a) →
      W (Addr.add (Tp b + 16#64) s) = 0 →
      (∀ a : Addr, (a.toNat < (Tp b + 16#64).toNat ∨ (Tp b + 16#64).toNat + s + 1 ≤ a.toNat) →
        (a.toNat < X.cpu.gpr.rsp.toNat - 4144 ∨ X.cpu.gpr.rsp.toNat - 4136 ≤ a.toNat) → W a = M a) →
      Z.cpu.rip = e'.add j → Z.cpu.gpr.rax = Tp b + 16#64 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = b ∧ g₂.r14 = size pad 656#64 ∧
        (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂])) →
      GoG prof L o (gev ++ [gEv X.cpu.gpr (.procExe x)] ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hR := X.cpu.gpr.rsp.isLt
  have hB : (X.cpu.gpr.rsp - 4136#64).toNat = X.cpu.gpr.rsp.toNat - 4136 := by bv_omega
  have hB8 : (X.cpu.gpr.rsp - 4136#64 - 8).toNat = X.cpu.gpr.rsp.toNat - 4144 := by bv_omega
  have eB : X.cpu.gpr.rsp - 4136#64 + 4104#64 = X.cpu.gpr.rsp - 32#64 := by bv_omega
  have eR : X.cpu.gpr.rsp - 4136#64 + 4136#64 = X.cpu.gpr.rsp := by bv_omega
  have eS : X.cpu.gpr.rsp - 4136#64 + 4144#64 = X.cpu.gpr.rsp + 8#64 := by bv_omega
  have e2 : X.cpu.gpr.rsp - 4136#64 + 4112#64 = X.cpu.gpr.rsp - 4136#64 + 4104#64 + 8 := by bv_omega
  have e3 : X.cpu.gpr.rsp - 4136#64 + 4120#64 = X.cpu.gpr.rsp - 4136#64 + 4104#64 + 8 + 8 := by bv_omega
  have e4 : X.cpu.gpr.rsp - 4136#64 + 4128#64 = X.cpu.gpr.rsp - 4136#64 + 4104#64 + 8 + 8 + 8 := by bv_omega
  have hfs := mc.hfs
  have hbl := mc.hbl
  have hbt := mc.hB.brk_lt
  have hb47 : b.toNat < 2 ^ 47 := by omega
  obtain ⟨-, hnb⟩ := nbOf_bnd (n := 2) (by omega)
  obtain ⟨hbc, -, hT0, -, -⟩ := lay hb47 mc.hnb mc.hpd hnb
  -- what the four `rdq` of the frame and the return address read
  have fr : ∀ x : ExePath, x.bytes.length < 4096 →
      rdq(Vg V X.cpu.gpr x, X.cpu.gpr.rsp - 4136#64 + 4104#64) = X.cpu.gpr.rbx ∧
      rdq(Vg V X.cpu.gpr x, X.cpu.gpr.rsp - 4136#64 + 4112#64) = X.cpu.gpr.rbp ∧
      rdq(Vg V X.cpu.gpr x, X.cpu.gpr.rsp - 4136#64 + 4120#64) = X.cpu.gpr.r12 ∧
      rdq(Vg V X.cpu.gpr x, X.cpu.gpr.rsp - 4136#64 + 4128#64) = X.cpu.gpr.r13 ∧
      rdq(Vg V X.cpu.gpr x, X.cpu.gpr.rsp - 4136#64 + 4136#64) = e'.add j := fun x hl => by
    obtain ⟨r1, r2, r3, r4⟩ := frV_rd V X.cpu.gpr _ x.bytes (by omega) rfl (by omega)
    refine ⟨r1, by rw [e2]; exact r2, by rw [e3]; exact r3, by rw [e4]; exact r4, ?_⟩
    rw [eR, Sbrk.rd_eq (V' := Vg V X.cpu.gpr x) (V := V) (x := X.cpu.gpr.rsp) (n := 8) hrt
      fun a h _ => Vg_hi h32 hl h]
    exact hra
  refine gor_head c hin hK hA hrip h32 htop hst (by omega) hpf hpn hpz hpp hof hoz hps ke ?_ ?_
  · -- `malloc (2)`
    intro x Z t' hl hKZ hAZ hrZ hdi hsp hbp h14 h15 hsl
    obtain ⟨r1, r2, r3, r4, r5⟩ := fr x hl
    refine g124 c hin mc hKZ hAZ hrZ hdi hsp (hpre.lo mc.hfs mc.hfb fun a ha => Vg_lo h32 hl (by omega)) hsm
      (by rw [hB]; omega) (by rw [hB]; omega) (by rw [hB]; omega) (fun i hi => by rw [eB]; exact hfr i hi) hinr hj
      r5 ?_
    intro n s s₁ Vc M W evs Z₁ t₁ g hc hB' hK₁ hA₁ hn2 hn hs1 hsn hg hVc hAf MV hnul hout hr hax
      hsp₁ hbx hbp₁ h12 h13 h14₁ h15₁ hev
    exact k x n s s₁ Vc M W evs Z₁ t₁ g hl hc hB' hK₁ hA₁ hn2 hn hs1 hsn hg
      (fun a ha => hVc a (by rw [hB]; omega)) hAf (fun a ha => MV a (by rw [hB]; exact ha)) hnul
      (fun a h1 h2 => hout a h1 (by rw [hB]; omega)) hr hax (by rw [hsp₁, eS])
      (hbx.trans r1) (hbp₁.trans r2) (h12.trans r3) (h13.trans r4) (h14₁.trans h14) (h15₁.trans h15) hev
  · -- `malloc (s + 2)`
    intro x Z t' hl hKZ hAZ hrZ hdi hbx hsp hbp h14 h15 hs1
    obtain ⟨r1, r2, r3, r4, r5⟩ := fr x hl
    have hs : sl (Vg V X.cpu.gpr x) (X.cpu.gpr.rsp - 4136#64) x.bytes.length < 4096 := by
      rcases sl_lt (Vg V X.cpu.gpr x) (X.cpu.gpr.rsp - 4136#64) x.bytes.length with h | h
      · omega
      · rw [h]; show 0 < 4096; omega
    refine g278 c hin mc hKZ hAZ hrZ hdi hbx hs1 hs hsp hbp
      (hpre.lo mc.hfs mc.hfb fun a ha => Vg_lo h32 hl (by omega)) hsm (by rw [hB]; omega) (by rw [hB]; omega)
      (by rw [hB]; omega) hbuf (fun i hi => by rw [eB]; exact hfr i hi) hinc hc0 hcpy
      (fun W hW => hPm W fun a ha => (hW a ha).trans (Vg_lo h32 hl (by omega))) hinr hj r5 ?_
    intro n s s₁ Vc M W evs Z₁ t₁ g hc hB' hK₁ hA₁ hn2 hn hs1' hsn hg hVc hAf MV hnul hout hr hax
      hsp₁ hbx₁ hbp₁ h12 h13 h14₁ h15₁ hev
    exact k x n s s₁ Vc M W evs Z₁ t₁ g hl hc hB' hK₁ hA₁ hn2 hn hs1' hsn hg
      (fun a ha => hVc a (by rw [hB]; omega)) hAf (fun a ha => MV a (by rw [hB]; exact ha)) hnul
      (fun a h1 h2 => hout a h1 (by rw [hB]; omega)) hr hax (by rw [hsp₁, eS])
      (hbx₁.trans r1) (hbp₁.trans r2) (h12.trans r3) (h13.trans r4) (h14₁.trans h14) (h15₁.trans h15) hev

end FV7z.Gor
