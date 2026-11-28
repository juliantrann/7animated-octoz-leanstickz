import FV7z.Cps.Sel
/-!
# `NCommandLineParser::CParser::ParseString`: the switch loop and the start (PLAN.md §M, M1)

- `from170`, `from156`, `from126`: the end of a round of the switch loop (the prefix test `k151`, the longest match).
- `str112`: the key's `strlen` loop, by induction on the bytes left before the NUL.
- `from96`, `loop`: a round of the switch loop, and all of them by induction on the forms left.
- `from78`, `from55`, `from28`: the start: the stack guard stored, `len` 0 to 328, `s[0]` not '-' to 328, no
  switches to 735, else the loop.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {ch : Addr} {ln : BitVec 32} {sp : Addr} {kp : Nat → Addr}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- From 170 (the form `k` done): the next form to `kn`, after the last one to 183. -/
theorem from170 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 170) {k : Nat} (hl : Lp S g0 k Y.cpu.gpr)
    (hbt : Bt (k + 1) Y.cpu.gpr) (hk : k < nS g0) (hIW : I W)
    (kn : Nx prof F Wl L s₀ o gev gP gE S g0 I k) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ls, l14, lcx, l13, l12⟩ := hl
  refine (c_170 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧
      ((j' = 96 ∧ g'.rsp = Y.cpu.gpr.rsp ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.rcx = Y.cpu.gpr.rcx ∧
        g'.r15 = Y.cpu.gpr.r15 ∧ g'.rbp = Y.cpu.gpr.rbp ∧ g'.r13 = Y.cpu.gpr.r13 + 24#64 ∧
        g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12 + 1#32) ∧
        ¬BitVec.setWidth 32 Y.cpu.gpr.rcx = BitVec.setWidth 32 Y.cpu.gpr.r12 + 1#32) ∨
      (j' = 183 ∧ g'.rsp = Y.cpu.gpr.rsp ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15 ∧
        g'.rbp = Y.cpu.gpr.rbp ∧ BitVec.setWidth 32 Y.cpu.gpr.rcx = BitVec.setWidth 32 Y.cpu.gpr.r12 + 1#32)))
    hK hA hr
    (vc_170 (fun _ a1 a2 a3 a4 a5 a6 a7 a8 _ => ⟨rfl, Or.inl ⟨rfl, a1, a2, a3, a4, a5, a6, a7, a8⟩⟩)
      fun _ a1 a2 a3 a4 a5 _ => ⟨rfl, Or.inr ⟨rfl, a1, a2, a3, a4, a5⟩⟩) ?_
  have hn := nS_lt g0
  rintro j' g fl V₁ ⟨hV₁, ⟨rfl, gs, g14, gcx, g15, gbp, g13, g12, gne⟩ | ⟨rfl, gs, g14, g15, gbp, geq⟩⟩
    U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    have hc : ¬BitVec.setWidth 32 g0.rcx = BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32 := by
      rw [← lcx, ← l12]
      exact gne
    have hk1 : k + 1 < nS g0 := knext hk hc
    have e13 : U.cpu.gpr.r13 = e24 g0.rdx (k + 1) := by
      rw [g13, l13]
      exact e24s _ _
    have e12 : U.cpu.gpr.r12 = BitVec.ofNat 64 (k + 1) := by
      rw [g12, l12]
      exact i32 (by omega)
    have ecx : BitVec.setWidth 32 U.cpu.gpr.rcx = BitVec.setWidth 32 g0.rcx := by
      rw [gcx]
      exact lcx
    exact kn U W t₁ hKU hAU hrU ⟨gs.trans ls, g14.trans l14, ecx, e13, e12⟩ (Bt.eq hbt g15 gbp) hIW hk1
  · subst V₁ hgU
    have hc : BitVec.setWidth 32 g0.rcx = BitVec.setWidth 32 (BitVec.ofNat 64 k) + 1#32 := by
      rw [← lcx, ← l12]
      exact geq
    exact from183 E hKU hAU hrU (gs.trans ls) (g14.trans l14) (kexit hk hc) (Bt.eq hbt g15 gbp) hIW

/-- From 156 (back from the prefix test): `numSwitches` back into `ecx`; the match the longest so far or not, to
170. -/
theorem from156 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 156) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) {k : Nat} (h13 : Y.cpu.gpr.r13 = e24 g0.rdx k)
    (h12 : Y.cpu.gpr.r12 = BitVec.ofNat 64 k) (hbt : Bt k Y.cpu.gpr) (hk : k < nS g0) (hIW : I W)
    (hM : rdd(W, aR S + 12#64) = BitVec.setWidth 32 g0.rcx) (kn : Nx prof F Wl L s₀ o gev gP gE S g0 I k) :
    GoG prof L o gev gP gE Y t := by
  refine (c_156 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 170 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.r13 = Y.cpu.gpr.r13 ∧ g'.r12 = Y.cpu.gpr.r12 ∧
      g'.rcx = BitVec.setWidth 64 rdd(W, Y.cpu.gpr.rsp + 12#64) ∧
      (g'.r15 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r15) ∧
          g'.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbp) ∨
        g'.r15 = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) ∧
          g'.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.r12))) hK hA hr
    (vc_156 (by rw [hs]; exact E.f12) fun _ a1 a2 a3 a4 a5 a6 _ => ⟨rfl, rfl, a1, a2, a3, a4, a5, a6⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g14, g13, g12, gcx, gd⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hn := nS_lt g0
  have hcx : BitVec.setWidth 32 U.cpu.gpr.rcx = BitVec.setWidth 32 g0.rcx := by
    rw [gcx, hs, hM, s64]
  have hbt' : Bt (k + 1) U.cpu.gpr := by
    rcases gd with ⟨e15, ebp⟩ | ⟨e15, ebp⟩
    · rcases hbt with h | ⟨b, hb, e⟩
      · left
        rw [e15, s64]
        exact h
      · refine Or.inr ⟨b, by omega, ?_⟩
        rw [ebp, e]
        exact w32 (by omega)
    · refine Or.inr ⟨k, by omega, ?_⟩
      rw [ebp, h12]
      exact w32 (by omega)
  exact from170 E hKU hAU hrU ⟨gs.trans hs, g14.trans h14, hcx, g13.trans h13, g12.trans h12⟩ hbt' hk hIW kn

/-- From 126 (the key's length in `ebx`): too long for the rest of `s` to 170, else `numSwitches` saved and the
prefix test (`k151`), from its return 156. -/
theorem from126 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 126) {k : Nat} (hl : Lp S g0 k Y.cpu.gpr)
    (hbt : Bt k Y.cpu.gpr) (hk : k < nS g0) (hIW : I W) (kn : Nx prof F Wl L s₀ o gev gP gE S g0 I k) :
    GoG prof L o gev gP gE Y t := by
  refine (c_126 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => Lk Y.cpu.gpr g' ∧ ((j' = 170 ∧ V' = W) ∨
      (j' = 151 ∧ V' = Vst W (Y.cpu.gpr.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rcx) 4)))) hK hA hr
    (vc_126 (by rw [hl.2.1]; exact E.fs8) (by rw [hl.2.1]; exact E.fs0) (by rw [hl.1]; exact E.w12)
      (fun _ a1 _ _ => ⟨a1, Or.inl ⟨rfl, rfl⟩⟩) fun _ a1 _ _ _ => ⟨a1, Or.inr ⟨rfl, rfl⟩⟩) ?_
  rintro j' g fl V₁ ⟨gl, ⟨rfl, hV₁⟩ | ⟨rfl, hV₁⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    exact from170 E hKU hAU hrU (hl.lk gl) (Bt.mono (hbt.lk gl) (Nat.le_succ k)) hk hIW kn
  · subst V₁ hgU
    have hl' := hl.lk gl
    have hb' := hbt.lk gl
    rw [hl.1] at hAU
    have hI1 := E.hc12 W (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rcx) 4) (toBytesLE_length _ _) hIW
    have hM1 : rdd(Vst W (aR S + 12#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rcx) 4), aR S + 12#64) =
        BitVec.setWidth 32 g0.rcx := (E.hr12 W _).trans hl.2.2.1
    refine callK E hKU hAU hrU hl'.1 (lt_len (by decide)) (call_151 _) tgt_151 E.cK (E.k151 _ _ hI1 hM1) trivial ?_
    rintro Z W' t₃ hKZ hAZ hrZ hsZ hkZ - ⟨hIZ, hMZ⟩
    exact from156 E hKZ hAZ hrZ hsZ (hkZ.2.2.2.2.1.trans hl'.2.1) (hkZ.2.2.2.1.trans hl'.2.2.2.1)
      (hkZ.2.2.1.trans hl'.2.2.2.2) (Bt.eq hb' hkZ.2.2.2.2.2 hkZ.2.1) hk hIZ hMZ kn

/-- The key's `strlen` loop at 112 (`rsi` = the key `kp k`, `rax` = `j`, before the NUL at `l`), by induction on
`l - j`. -/
theorem str112 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) {k : Nat} (hk : k < nS g0)
    (kn : Nx prof F Wl L s₀ o gev gP gE S g0 I k) {l : Nat} (hky : Ky F I (kp k) l) :
    ∀ (n j : Nat), l - j = n → j < l → ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem W → Y.cpu.rip = cps_at.add 112 → Lp S g0 k Y.cpu.gpr → Bt k Y.cpu.gpr →
      Y.cpu.gpr.rsi = kp k → Y.cpu.gpr.rax = BitVec.ofNat 64 j → I W → GoG prof L o gev gP gE Y t := by
  intro n
  induction n with
  | zero =>
    intro j hn hj
    exfalso
    omega
  | succ n ih =>
    intro j hn hj Y W t hK hA hr hl hbt hsi hax hIW
    have hj1 : j + 1 < 4294967296 := by
      have := hky.1
      omega
    have ea : Y.cpu.gpr.rsi + nx Y.cpu.gpr.rax = kp k + BitVec.ofNat 64 (j + 1) := by
      rw [hsi, hax, nxe hj1]
    refine (c_112 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Lk Y.cpu.gpr g' ∧
        ((j' = 112 ∧ g'.rsi = Y.cpu.gpr.rsi ∧ g'.rax = nx Y.cpu.gpr.rax ∧ W (Y.cpu.gpr.rsi + nx Y.cpu.gpr.rax) ≠ 0#8) ∨
          j' = 126)) hK hA hr
      (vc_112 (by rw [ea]; exact hky.2.1 (j + 1) (Nat.succ_le_of_lt hj))
        (fun _ a1 a2 a3 a4 _ => ⟨rfl, a1, Or.inl ⟨rfl, a2, a3, a4⟩⟩) fun _ a1 _ _ => ⟨rfl, a1, Or.inr rfl⟩) ?_
    rintro j' g fl V₁ ⟨hV₁, gl, ⟨rfl, gsi, gax, gnz⟩ | rfl⟩ U t₁ hKU hAU hrU hgU -
    · subst V₁ hgU
      have hj2 : j + 1 < l := by
        rcases Nat.lt_or_ge (j + 1) l with h | h
        · exact h
        · exfalso
          apply gnz
          have e : j + 1 = l := by omega
          rw [ea, e]
          exact hky.2.2 W hIW
      have eax : U.cpu.gpr.rax = BitVec.ofNat 64 (j + 1) := by
        rw [gax, hax]
        exact nxe hj1
      exact ih (j + 1) (by omega) hj2 U W t₁ hKU hAU hrU (hl.lk gl) (hbt.lk gl) (gsi.trans hsi) eax hIW
    · subst V₁ hgU
      exact from126 E hKU hAU hrU (hl.lk gl) (hbt.lk gl) hk hIW kn

/-- From 96 (the form `k`): its key empty to 126, else the `strlen` loop (112). -/
theorem from96 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 96) {k : Nat} (hl : Lp S g0 k Y.cpu.gpr)
    (hbt : Bt k Y.cpu.gpr) (hk : k < nS g0) (hIW : I W) (kn : Nx prof F Wl L s₀ o gev gP gE S g0 I k) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨l, hky⟩ := E.hky k hk
  have e13 : rdq(W, Y.cpu.gpr.r13) = kp k := by
    rw [hl.2.2.2.1]
    exact E.hkp W hIW k hk
  have ek : kp k + BitVec.ofNat 64 0 = kp k := BitVec.add_zero _
  have f0 : ∀ i < 1, Foot F.data (Addr.add (kp k) i) := by
    have h := hky.2.1 0 (Nat.zero_le _)
    rw [ek] at h
    exact h
  refine (c_96 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Lk Y.cpu.gpr g' ∧ (j' = 126 ∨
      (j' = 112 ∧ g'.rsi = rdq(W, Y.cpu.gpr.r13) ∧ g'.rax = 0#64 ∧ W rdq(W, Y.cpu.gpr.r13) ≠ 0#8))) hK hA hr
    (vc_96 (by rw [hl.2.2.2.1]; exact (E.ffo k hk).1) (by rw [e13]; exact f0)
      (fun _ a1 _ _ _ => ⟨rfl, a1, Or.inl rfl⟩) fun _ a1 a2 a3 a4 _ => ⟨rfl, a1, Or.inr ⟨rfl, a2, a3, a4⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gl, rfl | ⟨rfl, gsi, gax, gnz⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    exact from126 E hKU hAU hrU (hl.lk gl) (hbt.lk gl) hk hIW kn
  · subst V₁ hgU
    have hl0 : 0 < l := by
      rcases Nat.eq_zero_or_pos l with h | h
      · exfalso
        apply gnz
        have hz := hky.2.2 W hIW
        rw [h, ek] at hz
        rw [e13]
        exact hz
      · exact h
    exact str112 E hk kn hky (l - 0) 0 rfl hl0 U W t₁ hKU hAU hrU (hl.lk gl) (hbt.lk gl) (gsi.trans e13) gax hIW

/-- The switch loop from the form `k`, by induction on the forms left. -/
theorem loop (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) :
    ∀ (n k : Nat), nS g0 - k = n → k < nS g0 → ∀ (Y : State) (W : Addr → Byte) (t : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem W → Y.cpu.rip = cps_at.add 96 → Lp S g0 k Y.cpu.gpr → Bt k Y.cpu.gpr → I W →
      GoG prof L o gev gP gE Y t := by
  intro n
  induction n with
  | zero =>
    intro k hn hk
    exfalso
    omega
  | succ n ih =>
    intro k hn hk Y W t hK hA hr hl hbt hIW
    exact from96 E hK hA hr hl hbt hk hIW fun U W' t' hKU hAU hrU hlU hbU hIU hk1 =>
      ih (k + 1) (by omega) hk1 U W' t' hKU hAU hrU hlU hbU hIU

/-- From 78 (`numSwitches` not 0): the loop's registers, the loop from the form 0. -/
theorem from78 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 78) (hs : Y.cpu.gpr.rsp = aR S)
    (h14 : Y.cpu.gpr.r14 = g0.rsi) (hcx : BitVec.setWidth 32 Y.cpu.gpr.rcx = BitVec.setWidth 32 g0.rcx)
    (h0 : BitVec.setWidth 32 Y.cpu.gpr.rcx ≠ 0) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_78 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 96 ∧ V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      g'.r14 = Y.cpu.gpr.r14 ∧ g'.rcx = Y.cpu.gpr.rcx ∧ g'.r13 = rdq(W, Y.cpu.gpr.rsp + 16#64) ∧ g'.r12 = 0#64 ∧
      BitVec.setWidth 32 g'.r15 = 4294967295#32 ∧ g'.rbp = 0#64) hK hA hr
    (vc_78 (by rw [hs]; exact E.f16) fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1, a2, a3, a4, a5, a6, a7⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, g14, gcx, g13, g12, g15, gbp⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hpos : 0 < nS g0 := by
    have h1 : (BitVec.setWidth 32 g0.rcx).toNat ≠ 0 := fun e =>
      h0 (by rw [hcx]; exact BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    exact Nat.pos_of_ne_zero h1
  have e13 : U.cpu.gpr.r13 = e24 g0.rdx 0 := by
    rw [g13, hs, (E.hF W hIW).1]
    exact (e24z _).symm
  have ecx : BitVec.setWidth 32 U.cpu.gpr.rcx = BitVec.setWidth 32 g0.rcx := by
    rw [gcx]
    exact hcx
  exact loop E (nS g0 - 0) 0 rfl hpos U W t₁ hKU hAU hrU ⟨gs.trans hs, g14.trans h14, ecx, e13, g12⟩ (Or.inl g15) hIW

/-- From 55 (`len` not 0): `s[0]` not '-' to 328, no switches to "Unknown switch" (735), else 78. -/
theorem from55 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 55) (hs : Y.cpu.gpr.rsp = aR S)
    (hsi : Y.cpu.gpr.rsi = g0.rsi) (hcx : Y.cpu.gpr.rcx = g0.rcx) (hln : ln ≠ 0) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_55 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ g'.rsp = Y.cpu.gpr.rsp ∧
      (j' = 328 ∨ j' = 735 ∨ (j' = 78 ∧ g'.r14 = Y.cpu.gpr.rsi ∧ g'.rcx = Y.cpu.gpr.rcx ∧
        BitVec.setWidth 32 Y.cpu.gpr.rcx ≠ 0))) hK hA hr
    (vc_55 (by rw [hsi]; exact E.fs0) (by rw [hsi, (E.hs W hIW).1]; exact E.fch0 hln)
      (fun _ a1 _ => ⟨rfl, a1, Or.inl rfl⟩) (fun _ a1 _ => ⟨rfl, a1, Or.inr (Or.inl rfl)⟩)
      fun _ a1 a2 a3 a4 _ => ⟨rfl, a1, Or.inr (Or.inr ⟨rfl, a2, a3, a4⟩)⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, rfl | rfl | ⟨rfl, g14, gcx, gnz⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    exact from328 E hKU hAU hrU (gs.trans hs) hIW
  · subst V₁ hgU
    exact from735 E hKU hAU hrU (gs.trans hs) hIW
  · subst V₁ hgU
    have ecx : BitVec.setWidth 32 U.cpu.gpr.rcx = BitVec.setWidth 32 g0.rcx := by
      rw [gcx, hcx]
    have enz : BitVec.setWidth 32 U.cpu.gpr.rcx ≠ 0 := by
      rw [gcx]
      exact gnz
    exact from78 E hKU hAU hrU (gs.trans hs) (g14.trans hsi) ecx enz hIW

/-- From 28 (the bytes `W` before the stack guard's store, `I` after it): `len` 0 to 328, else 55. -/
theorem from28 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I Ok ch ln sp kp) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = cps_at.add 28) (hs : Y.cpu.gpr.rsp = aR S)
    (hsi : Y.cpu.gpr.rsi = g0.rsi) (hcx : Y.cpu.gpr.rcx = g0.rcx)
    (hI0 : I (Vst W (aR S + 56#64) (toBytesLE rdq(W, fb + 40#64) 8))) :
    GoG prof L o gev gP gE Y t := by
  refine (c_28 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => g'.rsp = Y.cpu.gpr.rsp ∧
      V' = Vst W (Y.cpu.gpr.rsp + 56#64) (toBytesLE rdq(W, fb + 40#64) 8) ∧
      (j' = 328 ∨ (j' = 55 ∧ g'.rsi = Y.cpu.gpr.rsi ∧ g'.rcx = Y.cpu.gpr.rcx ∧ rdd(V', Y.cpu.gpr.rsi + 8#64) ≠ 0)))
    hK hA hr
    (vc_28 (cn := rdq(W, fb + 40#64)) rfl E.fcl (by rw [hs]; exact E.w56) (by rw [hsi]; exact E.fs8)
      (fun _ a1 _ => ⟨a1, rfl, Or.inl rfl⟩) fun _ a1 a2 a3 a4 _ => ⟨a1, rfl, Or.inr ⟨rfl, a2, a3, a4⟩⟩) ?_
  rintro j' g fl V₁ ⟨gs, hV₁, rfl | ⟨rfl, gsi, gcx, gnz⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    rw [hs] at hAU
    exact from328 E hKU hAU hrU (gs.trans hs) hI0
  · subst V₁ hgU
    rw [hs] at hAU gnz
    rw [hsi, (E.hs _ hI0).2.1] at gnz
    exact from55 E hKU hAU hrU (gs.trans hs) (gsi.trans hsi) (gcx.trans hcx) gnz hI0

end Runs

end FV7z.Cps
