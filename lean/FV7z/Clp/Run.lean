import FV7z.Clp.Holds
/-!
# `CLocalProgress::Init`: the run (PLAN.md §M, M1)

The run of `CLocalProgress::Init` at `0x461ff0` from its entry to its return address, from the pieces of
`Clp/Holds.lean`, under the contracts `Hyp` of what it calls and of the objects it destroys. `I ps W`: what holds of
the bytes `W` with the objects `ps` (innermost first) being destroyed; `K ps W c`: `c` is the `_ratioProgress` yet to
be released, of the innermost of `ps` (of `this` for `ps = []`); `T k W`: the bytes after the `k`-th step of the
tail (`_ratioProgress` = NULL, `AddRef`, the old `_progress` released, `QueryInterface`).
`AtJ j P`: the run goes on to the goal from the `j`-th byte of the code with the registers and the bytes as `P`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Clp
set_option linter.unusedVariables false

/-- `d` is `K`'s pending `_ratioProgress`, or the `_progress` of the innermost object being destroyed. -/
def Ch (K : List Addr → (Addr → Byte) → Addr → Prop) (ps : List Addr) (W : Addr → Byte) (d : Addr) : Prop :=
  K ps W d ∨ ∃ q ps', ps = q :: ps' ∧ rdq(W, q + 16#64) = d

/-- From the `j`-th byte of the code with the registers and the bytes as `P`, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (V : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = clp_at.add j → P Y.cpu.gpr V → GoG prof L o gev gP gE Y t

/-- What the run needs: the code, the frame, the objects' fields, and the contracts of the calls. -/
structure Hyp (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (g₀ : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : List Addr → (Addr → Byte) → Prop)
    (K : List Addr → (Addr → Byte) → Addr → Prop) (T : Nat → (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L clp_at clp
  hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  w1 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8) i)
  w2 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) i)
  w3 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) i)
  w4 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8) i)
  w5 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8) i)
  w6 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)
  wc : ∀ i < 8, Foot Wl (Addr.add (sp72 g₀.rsp - 8) i)
  ws : ∀ i < 8, Foot Wl (Addr.add (sp72 g₀.rsp + 8#64) i)
  ns : (sp72 g₀.rsp + 8#64).toNat + 8 ≤ 2 ^ 64
  hl : ∀ i < 8, Foot F.data (Addr.add g₀.rsp i)
  w24 : ∀ i < 8, Foot Wl (Addr.add (g₀.rdi + 24#64) i)
  w16 : ∀ i < 8, Foot Wl (Addr.add (g₀.rdi + 16#64) i)
  w14 : ∀ i < 1, Foot Wl (Addr.add (g₀.rdi + 14#64) i)
  pz : g₀.rsi ≠ 0
  vf : ∀ ps W d, I ps W → Ch K ps W d → d ≠ 0 → Vf F W d
  ko : ∀ ps W c, I ps W → K ps W c → c ≠ 0 → rdq(W, rdq(W, c) + 16#64) = rlK → Ofp F Wl c
  ob : ∀ q ps W, I (q :: ps) W → Ofp F Wl q
  dn : ∀ ps W c, I ps W → K ps W c → c ≠ 0 → rdq(W, rdq(W, c) + 16#64) = rlK → rdd(W, c + 8#64) ≠ 1#32 →
    I ps (Wdec W c)
  dz : ∀ ps W c, I ps W → K ps W c → c ≠ 0 → rdq(W, rdq(W, c) + 16#64) = rlK → rdd(W, c + 8#64) = 1#32 →
    I (c :: ps) (Vv (Wdec W c) c) ∧ K (c :: ps) (Vv (Wdec W c) c) (rdq(Wdec W c, c + 24#64))
  kR : ∀ ps W d, I ps W → Ch K ps W d → d ≠ 0 → CodeOK L (rdq(W, rdq(W, d) + 16#64)) ∧
    Callc prof F Wl L s₀ o gev gP gE g₀.rsp (rdq(W, rdq(W, d) + 16#64)) (fun g => g.rdi = d) W (I ps)
  kS : ∀ q ps W d, I (q :: ps) W → Ch K (q :: ps) W d → d ≠ 0 →
    CodeOK L (rdq(Wsp g₀.rsp W q, rdq(W, d) + 16#64)) ∧
    Callc prof F Wl L s₀ o gev gP gE g₀.rsp (rdq(Wsp g₀.rsp W q, rdq(W, d) + 16#64)) (fun g => g.rdi = d)
      (Wsp g₀.rsp W q) (I (q :: ps))
  kD : ∀ q ps W, I (q :: ps) W →
    Callc prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014e0#64 (fun g => g.rdi = q ∧ g.rsi = 56#64) W (I ps)
  z0 : ∀ W, I [] W → rdq(W, g₀.rdi + 24#64) = 0 → T 0 W
  z24 : ∀ W, I [] W → T 0 (Vst W (g₀.rdi + 24#64) (toBytesLE (0#64 : BitVec 64) 8))
  fP : ∀ W, T 0 W → (∀ i < 8, Foot F.data (Addr.add g₀.rsi i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (rdq(W, g₀.rsi) + 8#64) i))
  kA : ∀ W, T 0 W → CodeOK L (rdq(W, rdq(W, g₀.rsi) + 8#64)) ∧
    Callc prof F Wl L s₀ o gev gP gE g₀.rsp (rdq(W, rdq(W, g₀.rsi) + 8#64)) (fun g => g.rdi = g₀.rsi) W (T 1)
  q0 : ∀ W, T 1 W → rdq(W, g₀.rdi + 16#64) = 0 → T 2 W
  fq : ∀ W, T 1 W → rdq(W, g₀.rdi + 16#64) ≠ 0 → Vf F W (rdq(W, g₀.rdi + 16#64))
  kQ1 : ∀ W, T 1 W → rdq(W, g₀.rdi + 16#64) ≠ 0 →
    CodeOK L (rdq(W, rdq(W, rdq(W, g₀.rdi + 16#64)) + 16#64)) ∧
    Callc prof F Wl L s₀ o gev gP gE g₀.rsp (rdq(W, rdq(W, rdq(W, g₀.rdi + 16#64)) + 16#64))
      (fun g => g.rdi = rdq(W, g₀.rdi + 16#64)) W (T 2)
  fp2 : ∀ W, T 2 W → (∀ i < 8, Foot F.data (Addr.add g₀.rsi i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (rdq(W, g₀.rsi)) i))
  kQ : ∀ W, T 2 W → CodeOK L (rdq(Vst W (g₀.rdi + 16#64) (toBytesLE g₀.rsi 8), rdq(W, g₀.rsi))) ∧
    Callc prof F Wl L s₀ o gev gP gE g₀.rsp (rdq(Vst W (g₀.rdi + 16#64) (toBytesLE g₀.rsi 8), rdq(W, g₀.rsi)))
      (fun g => g.rdi = g₀.rsi ∧ g.rsi = 7255904#64 ∧ g.rdx = g₀.rdi + 24#64)
      (Vst W (g₀.rdi + 16#64) (toBytesLE g₀.rsi 8)) (T 3)
  fr : ∀ W, T 3 W → Fr g₀ (e₂.add j₂) (Vb g₀ W)
  kr : ∀ (Z : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vb g₀ W) → T 3 W →
    Z.cpu.rip = e₂.add j₂ → Ocv.Bk g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t'

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {g₀ : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : List Addr → (Addr → Byte) → Prop}
  {K : List Addr → (Addr → Byte) → Addr → Prop} {T : Nat → (Addr → Byte) → Prop}

/-! ## The calls, from a register condition `Rg` the calls keep -/

/-- A `call rax` at `j` releasing `d` (`kR`). -/
theorem callR {j len : Nat} (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) {Rg : Gprs → Prop}
    (hsk : ∀ g g', Rg g → Sk g g' → Rg g') (hrs : ∀ g, Rg g → g.rsp = sp72 g₀.rsp) (hj : j < 497)
    (hd : Dec prof.feat clp j (FV7z.mk .call 64 [gr 64 0] len)) {ps : List Addr}
    (k : AtJ prof F Wl L s₀ o gev gP gE (j + len) fun g W => Rg g ∧ I ps W) :
    AtJ prof F Wl L s₀ o gev gP gE j fun g W => Rg g ∧ I ps W ∧ ∃ d, Ch K ps W d ∧ d ≠ 0 ∧ g.rdi = d ∧
      g.rax = rdq(W, rdq(W, d) + 16#64) := by
  rintro U W t hKU hAU hrU ⟨hR, hI, d, hch, hd0, hdi, hax⟩
  obtain ⟨hcO, kc⟩ := H.kR ps W d hI hch hd0
  refine cl_r H.c H.hin hKU hAU hrU (lt_len hj) hd hcO hax (hrs _ hR) H.wc kc hdi ?_
  intro Z W' t' hKZ hAZ hP hrZ hsk' _
  exact k Z W' t' hKZ hAZ hrZ ⟨hsk _ _ hR hsk', hP⟩

/-- A `call [rax + 16]` at `j` releasing `d` (`kR`). -/
theorem callM {j : Nat} (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) {Rg : Gprs → Prop}
    (hsk : ∀ g g', Rg g → Sk g g' → Rg g') (hrs : ∀ g, Rg g → g.rsp = sp72 g₀.rsp) (hj : j < 497)
    (hd : Dec prof.feat clp j (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3)) {ps : List Addr}
    (k : AtJ prof F Wl L s₀ o gev gP gE (j + 3) fun g W => Rg g ∧ I ps W) :
    AtJ prof F Wl L s₀ o gev gP gE j fun g W => Rg g ∧ I ps W ∧ ∃ d, Ch K ps W d ∧ d ≠ 0 ∧ g.rdi = d ∧
      g.rax = rdq(W, d) := by
  rintro U W t hKU hAU hrU ⟨hR, hI, d, hch, hd0, hdi, hax⟩
  obtain ⟨hcO, kc⟩ := H.kR ps W d hI hch hd0
  have hb : eaD U 0 16 = rdq(W, d) + 16#64 := by
    show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
    rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, hax]
  refine cl_m H.c H.hin hKU hAU hrU (lt_len hj) hd hb (H.vf ps W d hI hch hd0).2 hcO rfl (hrs _ hR) H.wc kc hdi
    ?_
  intro Z W' t' hKZ hAZ hP hrZ hsk' _
  exact k Z W' t' hKZ hAZ hrZ ⟨hsk _ _ hR hsk', hP⟩

/-- A `call [rax + 16]` at `j` releasing `d` (`kS`), `q` spilled to `[rsp + 8]`: reloaded after. -/
theorem callS {j : Nat} (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) {Rg : Gprs → Prop}
    (hsk : ∀ g g', Rg g → Sk g g' → Rg g') (hrs : ∀ g, Rg g → g.rsp = sp72 g₀.rsp) (hj : j < 497)
    (hd : Dec prof.feat clp j (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3)) {q : Addr} {ps : List Addr}
    (k : AtJ prof F Wl L s₀ o gev gP gE (j + 3) fun g W =>
      Rg g ∧ I (q :: ps) W ∧ rdq(W, sp72 g₀.rsp + 8#64) = q) :
    AtJ prof F Wl L s₀ o gev gP gE j fun g W' => Rg g ∧ ∃ W d, W' = Wsp g₀.rsp W q ∧ I (q :: ps) W ∧
      Ch K (q :: ps) W d ∧ d ≠ 0 ∧ g.rdi = d ∧ g.rax = rdq(W, d) := by
  rintro U W' t hKU hAU hrU ⟨hR, W, d, rfl, hI, hch, hd0, hdi, hax⟩
  obtain ⟨hcO, kc⟩ := H.kS q ps W d hI hch hd0
  have hb : eaD U 0 16 = rdq(W, d) + 16#64 := by
    show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
    rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, hax]
  refine cl_m H.c H.hin hKU hAU hrU (lt_len hj) hd hb (H.vf (q :: ps) W d hI hch hd0).2 hcO rfl (hrs _ hR) H.wc
    kc hdi ?_
  intro Z W'' t' hKZ hAZ hP hrZ hsk' hsp
  exact k Z W'' t' hKZ hAZ hrZ ⟨hsk _ _ hR hsk', hP, hsp.trans (rdself H.ns)⟩

/-- A `call 0x6014e0` at `j`: `operator delete (q, 56)` (`kD`). -/
theorem callD {j rel : Nat} (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) {Rg : Gprs → Prop}
    (hsk : ∀ g g', Rg g → Sk g g' → Rg g') (hrs : ∀ g, Rg g → g.rsp = sp72 g₀.rsp) (hj : j < 497)
    (hd : Dec prof.feat clp j (FV7z.mk .call 64 [.rel rel] 5))
    (htg : clp_at.add (j + 5) + BitVec.ofNat 64 rel = 0x6014e0#64) {q : Addr} {ps : List Addr}
    (k : AtJ prof F Wl L s₀ o gev gP gE (j + 5) fun g W => Rg g ∧ I ps W) :
    AtJ prof F Wl L s₀ o gev gP gE j fun g W => Rg g ∧ I (q :: ps) W ∧ g.rdi = q ∧ g.rsi = 56#64 := by
  rintro U W t hKU hAU hrU ⟨hR, hI, hdi, hsi⟩
  refine cl_d H.c H.hin H.hin2 hKU hAU hrU (lt_len hj) hd htg (hrs _ hR) H.wc (H.kD q ps W hI) ⟨hdi, hsi⟩ ?_
  intro Z W' t' hKZ hAZ hP hrZ hsk' _
  exact k Z W' t' hKZ hAZ hrZ ⟨hsk _ _ hR hsk', hP⟩

/-- A `jmp` from `j` to `j'`. -/
theorem jmpP {j j' : Nat} {Wj : Wpt} (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T)
    (cj : Sp prof clp clp_at j Wj)
    (vj : ∀ (F : Footprint) (Wl : List Rgn) (g : Gprs) (f : Rflags) (V : Addr → Byte),
      Wj F Wl (fun j'' g' _ V' => j'' = j' ∧ g' = g ∧ V' = V) g f V)
    {P : Gprs → (Addr → Byte) → Prop} (k : AtJ prof F Wl L s₀ o gev gP gE j' P) :
    AtJ prof F Wl L s₀ o gev gP gE j P := by
  rintro Y W t hKY hAY hrY hP
  refine cj.run H.c H.hin _ hKY hAY hrY (vj _ _ _ _ _) ?_
  rintro j'' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  exact k U W t₁ hKU hAU hrU (by rw [hgU]; exact hP)

/-- The registers after the six pops: `rsp` back at the entry's, the saved ones restored. -/
theorem pops6_bk {g : Gprs} {W : Addr → Byte} {ra : Addr} (hs : g.rsp = sp72 g₀.rsp) (hfr : Fr g₀ ra W) :
    (pops6 W g).rsp = g₀.rsp ∧ Ocv.Kp g₀ (pops6 W g) := by
  obtain ⟨f1, f2, f3, f4, f5, f6, -⟩ := hfr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [pops6] <;> rw [hs] <;> simp only [sp72, a24, Ocv.a1s] <;>
    assumption

/-! ## The tail -/

/-- 130: `_inSizeIsMain`, the pops, the `ret`. -/
theorem a130 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 130 fun g W => Rr g₀ g ∧ T 3 W := by
  rintro Y W t hKY hAY hrY ⟨⟨hs, hbx, hbp, h13⟩, hT⟩
  have l1 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64) i) := by
    rw [hs]; simp only [sp72, a24, Ocv.a1s]; exact fun i hi => H.c.hws _ (H.w6 i hi)
  have l2 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64 + 8) i) := by
    rw [hs]; simp only [sp72, a24, Ocv.a1s]; exact fun i hi => H.c.hws _ (H.w5 i hi)
  have l3 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64 + 8 + 8) i) := by
    rw [hs]; simp only [sp72, a24, Ocv.a1s]; exact fun i hi => H.c.hws _ (H.w4 i hi)
  have l4 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8) i) := by
    rw [hs]; simp only [sp72, a24, Ocv.a1s]; exact fun i hi => H.c.hws _ (H.w3 i hi)
  have l5 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8) i) := by
    rw [hs]; simp only [sp72, a24, Ocv.a1s]; exact fun i hi => H.c.hws _ (H.w2 i hi)
  have l6 : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i) := by
    rw [hs]; simp only [sp72, a24, Ocv.a1s]; exact fun i hi => H.c.hws _ (H.w1 i hi)
  refine (c_130 prof).run H.c H.hin
    (fun j' g' _ V₁ => j' = 148 ∧ g' = pops6 (Vb g₀ W) Y.cpu.gpr ∧ V₁ = Vb g₀ W) hKY hAY hrY
    (vc_130 (by rw [hbx]; exact H.w14) l1 l2 l3 l4 l5 l6
      fun _ => ⟨rfl, by rw [hbx, h13], by rw [hbx, h13]⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  have hfr := H.fr W hT
  obtain ⟨hsP, hkP⟩ := pops6_bk (W := Vb g₀ W) hs hfr
  have hsU : U.cpu.gpr.rsp = g₀.rsp := (congrArg Gprs.rsp hgU).trans hsP
  refine H.c.s_ret hKU hAU H.hin (lt_len (by decide)) hrU (ret_148 _) (by rw [hsU]; exact H.hl) H.hin₂ H.h₂
    (by rw [hsU]; exact hfr.2.2.2.2.2.2) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  refine H.kr Z W t₂ hKZ hAZ hT hrZ ⟨?_, ?_⟩
  · rw [hgZ]
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ, hgU]
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hkP
    exact ⟨k1, k2, k3, k4, k5, k6⟩

/-- 106: `_progress` = `progress`, `QueryInterface` at 128. -/
theorem a106 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 106 fun g W => Rr g₀ g ∧ T 2 W := by
  rintro Y W t hKY hAY hrY ⟨⟨hs, hbx, hbp, h13⟩, hT⟩
  obtain ⟨fp, fv⟩ := H.fp2 W hT
  obtain ⟨hcO, kc⟩ := H.kQ W hT
  refine (c_106 prof).run H.c H.hin _ hKY hAY hrY
    (vc_106 (v := rdq(W, g₀.rsi)) (by rw [hbp]) (by rw [hbp]; exact fp) (by rw [hbx]; exact H.w16)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  rw [hbx, hbp] at hAU
  have hRU : Rr g₀ U.cpu.gpr := by rw [hgU]; exact ⟨hs, hbx, hbp, h13⟩
  have hax : U.cpu.gpr.rax = rdq(W, g₀.rsi) := by rw [hgU]; try rfl
  have hdi : U.cpu.gpr.rdi = g₀.rsi := by rw [hgU]; exact hbp
  have hdx : U.cpu.gpr.rdx = g₀.rdi + 24#64 := by rw [hgU]; show Y.cpu.gpr.rbx + 24#64 = _; rw [hbx]
  have hsi : U.cpu.gpr.rsi = 7255904#64 := by rw [hgU]; try rfl
  have hb : eaD U 0 0 = rdq(W, g₀.rsi) := by
    show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 0 = _
    rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, hax]
    try exact BitVec.add_zero _
  refine cl_m H.c H.hin hKU hAU hrU (lt_len (by decide)) (callm_128 _) hb fv hcO rfl hRU.1 H.wc kc
    ⟨hdi, hsi, hdx⟩ ?_
  intro Z W' t' hKZ hAZ hP hrZ hsk _
  exact a130 H Z W' t' hKZ hAZ hrZ ⟨hRU.sk hsk, hP⟩

/-- 91: the old `_progress` released (103) when not NULL. -/
theorem a91 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 91 fun g W => Rr g₀ g ∧ T 1 W := by
  rintro Y W t hKY hAY hrY ⟨⟨hs, hbx, hbp, h13⟩, hT⟩
  have fd : ∀ i < 8, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 16#64) i) := by
    rw [hbx]; exact fun i hi => H.c.hws _ (H.w16 i hi)
  by_cases hd0 : rdq(W, g₀.rdi + 16#64) = 0
  · refine (c_91 prof).run H.c H.hin _ hKY hAY hrY
      (vc_91z (d := rdq(W, g₀.rdi + 16#64)) (by rw [hbx]) hd0 fd) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    exact a106 H U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact ⟨hs, hbx, hbp, h13⟩, H.q0 W hT hd0⟩
  · obtain ⟨fv, fx⟩ := H.fq W hT hd0
    obtain ⟨hcO, kc⟩ := H.kQ1 W hT hd0
    refine (c_91 prof).run H.c H.hin _ hKY hAY hrY
      (vc_91n (d := rdq(W, g₀.rdi + 16#64)) (v := rdq(W, rdq(W, g₀.rdi + 16#64))) (by rw [hbx]) hd0 fd rfl fv) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    have hRU : Rr g₀ U.cpu.gpr := by rw [hgU]; exact ⟨hs, hbx, hbp, h13⟩
    have hax : U.cpu.gpr.rax = rdq(W, rdq(W, g₀.rdi + 16#64)) := by rw [hgU]; try rfl
    have hdi : U.cpu.gpr.rdi = rdq(W, g₀.rdi + 16#64) := by rw [hgU]; try rfl
    have hb : eaD U 0 16 = rdq(W, rdq(W, g₀.rdi + 16#64)) + 16#64 := by
      show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 16 = _
      rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, hax]
    refine cl_m H.c H.hin hKU hAU hrU (lt_len (by decide)) (callm_103 _) hb fx hcO rfl hRU.1 H.wc kc hdi ?_
    intro Z W' t' hKZ hAZ hP hrZ hsk _
    exact a106 H Z W' t' hKZ hAZ hrZ ⟨hRU.sk hsk, hP⟩

/-- 76: `progress->AddRef ()` at 88. -/
theorem a76 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 76 fun g W => Rr g₀ g ∧ T 0 W := by
  rintro Y W t hKY hAY hrY ⟨⟨hs, hbx, hbp, h13⟩, hT⟩
  obtain ⟨fp, fv⟩ := H.fP W hT
  obtain ⟨hcO, kc⟩ := H.kA W hT
  refine (c_76 prof).run H.c H.hin _ hKY hAY hrY
    (vc_76 (v := rdq(W, g₀.rsi)) (by rw [hbp]; exact H.pz) (by rw [hbp]) (by rw [hbp]; exact fp)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  have hRU : Rr g₀ U.cpu.gpr := by rw [hgU]; exact ⟨hs, hbx, hbp, h13⟩
  have hax : U.cpu.gpr.rax = rdq(W, g₀.rsi) := by rw [hgU]; try rfl
  have hdi : U.cpu.gpr.rdi = g₀.rsi := by rw [hgU]; exact hbp
  have hb : eaD U 0 8 = rdq(W, g₀.rsi) + 8#64 := by
    show U.cpu.gpr.get (regOf 0) + BitVec.ofNat 64 8 = _
    rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, hax]
  refine cl_m H.c H.hin hKU hAU hrU (lt_len (by decide)) (callm_88 _) hb fv hcO rfl hRU.1 H.wc kc hdi ?_
  intro Z W' t' hKZ hAZ hP hrZ hsk _
  exact a91 H Z W' t' hKZ hAZ hrZ ⟨hRU.sk hsk, hP⟩

/-- 68: `_ratioProgress` = NULL. -/
theorem a68 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 68 fun g W => Rr g₀ g ∧ I [] W := by
  rintro Y W t hKY hAY hrY ⟨⟨hs, hbx, hbp, h13⟩, hI⟩
  refine (c_68 prof).run H.c H.hin _ hKY hAY hrY (vc_68 (by rw [hbx]; exact H.w24)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  rw [hbx] at hAU
  exact a76 H U _ t₁ hKU hAU hrU ⟨by rw [hgU]; exact ⟨hs, hbx, hbp, h13⟩, H.z24 W hI⟩

/-! ## The deletes and the `_progress` releases of the objects destroyed -/

theorem a437 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 437 fun g W => Rr g₀ g ∧ I [] W :=
  jmpP H (c_437 prof) (fun _ _ _ _ _ => vc_437) (a68 H)

/-- 424: `operator delete (q1, 56)` at 432. -/
theorem a424 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 424 fun g W => ∃ q1, L1 g₀ q1 g ∧ I [q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, hL, hI⟩
  refine (c_424 prof).run H.c H.hin _ hKY hAY hrY vc_424 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  refine callD H (Rg := Rr g₀) (fun _ _ h k => h.sk k) (fun _ h => h.1) (by decide) (calld_432 _) tgt_432
    (q := q1) (ps := []) (a437 H) U W t₁ hKU hAU hrU ⟨?_, hI, ?_, ?_⟩
  · rw [hgU]; exact hL.1
  · rw [hgU]; exact hL.2
  · rw [hgU]; try rfl

/-- 408: `q1->_progress` released (421) when not NULL. -/
theorem a408 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 408 fun g W => ∃ q1, L1 g₀ q1 g ∧ I [q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, hL, hI⟩
  obtain ⟨-, f16, -, -⟩ := H.ob q1 [] W hI
  have h12 : Y.cpu.gpr.r12 = q1 := hL.2
  by_cases hd0 : rdq(W, q1 + 16#64) = 0
  · refine (c_408 prof).run H.c H.hin _ hKY hAY hrY
      (vc_408z (d := rdq(W, q1 + 16#64)) (by rw [h12]) hd0 (by rw [h12]; exact f16)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    exact a424 H U W t₁ hKU hAU hrU ⟨q1, by rw [hgU]; exact hL, hI⟩
  · have hch : Ch K [q1] W (rdq(W, q1 + 16#64)) := Or.inr ⟨q1, [], rfl, rfl⟩
    obtain ⟨fd, -⟩ := H.vf [q1] W _ hI hch hd0
    refine (c_408 prof).run H.c H.hin _ hKY hAY hrY
      (vc_408n (d := rdq(W, q1 + 16#64)) (v := rdq(W, rdq(W, q1 + 16#64))) (by rw [h12]) hd0
        (by rw [h12]; exact f16) rfl fd) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    refine callM H (Rg := L1 g₀ q1) (ps := [q1]) (fun _ _ h k => h.sk k) (fun _ h => h.1.1) (by decide)
      (callm_421 _) ?_ U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hL, hI, _, hch, hd0, by rw [hgU]; try rfl,
        by rw [hgU]; try rfl⟩
    intro Z W' t' hKZ hAZ hrZ hP
    exact a424 H Z W' t' hKZ hAZ hrZ ⟨q1, hP.1, hP.2⟩

/-- 395: `operator delete (q2, 56)` at 403. -/
theorem a395 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 395 fun g W => ∃ q1 q2, L2 g₀ q1 q2 g ∧ I [q2, q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, hL, hI⟩
  refine (c_395 prof).run H.c H.hin _ hKY hAY hrY vc_395 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  refine callD H (Rg := L1 g₀ q1) (fun _ _ h k => h.sk k) (fun _ h => h.1.1) (by decide) (calld_403 _) tgt_403
    (q := q2) (ps := [q1]) ?_ U W t₁ hKU hAU hrU ⟨?_, hI, ?_, ?_⟩
  · intro Z W' t' hKZ hAZ hrZ hP
    exact a408 H Z W' t' hKZ hAZ hrZ ⟨q1, hP.1, hP.2⟩
  · rw [hgU]; exact hL.1
  · rw [hgU]; exact hL.2
  · rw [hgU]; try rfl

/-- 380: `q2->_progress` released (392) when not NULL. -/
theorem a380 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 380 fun g W => ∃ q1 q2, L2 g₀ q1 q2 g ∧ I [q2, q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, hL, hI⟩
  obtain ⟨-, f16, -, -⟩ := H.ob q2 [q1] W hI
  have h14 : Y.cpu.gpr.r14 = q2 := hL.2
  by_cases hd0 : rdq(W, q2 + 16#64) = 0
  · refine (c_380 prof).run H.c H.hin _ hKY hAY hrY
      (vc_380z (d := rdq(W, q2 + 16#64)) (by rw [h14]) hd0 (by rw [h14]; exact f16)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    exact a395 H U W t₁ hKU hAU hrU ⟨q1, q2, by rw [hgU]; exact hL, hI⟩
  · have hch : Ch K [q2, q1] W (rdq(W, q2 + 16#64)) := Or.inr ⟨q2, [q1], rfl, rfl⟩
    obtain ⟨fd, -⟩ := H.vf [q2, q1] W _ hI hch hd0
    refine (c_380 prof).run H.c H.hin _ hKY hAY hrY
      (vc_380n (d := rdq(W, q2 + 16#64)) (v := rdq(W, rdq(W, q2 + 16#64))) (by rw [h14]) hd0
        (by rw [h14]; exact f16) rfl fd) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    refine callM H (Rg := L2 g₀ q1 q2) (ps := [q2, q1]) (fun _ _ h k => h.sk k) (fun _ h => h.1.1.1)
      (by decide) (callm_392 _) ?_ U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hL, hI, _, hch, hd0,
        by rw [hgU]; try rfl, by rw [hgU]; try rfl⟩
    intro Z W' t' hKZ hAZ hrZ hP
    exact a395 H Z W' t' hKZ hAZ hrZ ⟨q1, q2, hP.1, hP.2⟩

/-- 367: `operator delete (q3, 56)` at 375. -/
theorem a367 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 367 fun g W => ∃ q1 q2 q3, L3 g₀ q1 q2 q3 g ∧ I [q3, q2, q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, q3, hL, hI⟩
  refine (c_367 prof).run H.c H.hin _ hKY hAY hrY vc_367 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  refine callD H (Rg := L2 g₀ q1 q2) (fun _ _ h k => h.sk k) (fun _ h => h.1.1.1) (by decide) (calld_375 _)
    tgt_375 (q := q3) (ps := [q2, q1]) ?_ U W t₁ hKU hAU hrU ⟨?_, hI, ?_, ?_⟩
  · intro Z W' t' hKZ hAZ hrZ hP
    exact a380 H Z W' t' hKZ hAZ hrZ ⟨q1, q2, hP.1, hP.2⟩
  · rw [hgU]; exact hL.1
  · rw [hgU]; exact hL.2
  · rw [hgU]; try rfl

/-- 352: `q3->_progress` released (364) when not NULL. -/
theorem a352 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 352 fun g W => ∃ q1 q2 q3, L3 g₀ q1 q2 q3 g ∧ I [q3, q2, q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, q3, hL, hI⟩
  obtain ⟨-, f16, -, -⟩ := H.ob q3 [q2, q1] W hI
  have h15 : Y.cpu.gpr.r15 = q3 := hL.2
  by_cases hd0 : rdq(W, q3 + 16#64) = 0
  · refine (c_352 prof).run H.c H.hin _ hKY hAY hrY
      (vc_352z (d := rdq(W, q3 + 16#64)) (by rw [h15]) hd0 (by rw [h15]; exact f16)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    exact a367 H U W t₁ hKU hAU hrU ⟨q1, q2, q3, by rw [hgU]; exact hL, hI⟩
  · have hch : Ch K [q3, q2, q1] W (rdq(W, q3 + 16#64)) := Or.inr ⟨q3, [q2, q1], rfl, rfl⟩
    obtain ⟨fd, -⟩ := H.vf [q3, q2, q1] W _ hI hch hd0
    refine (c_352 prof).run H.c H.hin _ hKY hAY hrY
      (vc_352n (d := rdq(W, q3 + 16#64)) (v := rdq(W, rdq(W, q3 + 16#64))) (by rw [h15]) hd0
        (by rw [h15]; exact f16) rfl fd) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    refine callM H (Rg := L3 g₀ q1 q2 q3) (ps := [q3, q2, q1]) (fun _ _ h k => h.sk k) (fun _ h => h.1.1.1.1)
      (by decide) (callm_364 _) ?_ U W t₁ hKU hAU hrU ⟨by rw [hgU]; exact hL, hI, _, hch, hd0,
        by rw [hgU]; try rfl, by rw [hgU]; try rfl⟩
    intro Z W' t' hKZ hAZ hrZ hP
    exact a367 H Z W' t' hKZ hAZ hrZ ⟨q1, q2, q3, hP.1, hP.2⟩

/-- 339: `operator delete (q4, 56)` at 347. -/
theorem a339 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 339 fun g W => ∃ q1 q2 q3 q4, L3 g₀ q1 q2 q3 g ∧ g.r8 = q4 ∧
      I [q4, q3, q2, q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, q3, q4, hL, h8, hI⟩
  refine (c_339 prof).run H.c H.hin _ hKY hAY hrY vc_339 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  refine callD H (Rg := L3 g₀ q1 q2 q3) (fun _ _ h k => h.sk k) (fun _ h => h.1.1.1.1) (by decide)
    (calld_347 _) tgt_347 (q := q4) (ps := [q3, q2, q1]) ?_ U W t₁ hKU hAU hrU ⟨?_, hI, ?_, ?_⟩
  · intro Z W' t' hKZ hAZ hrZ hP
    exact a352 H Z W' t' hKZ hAZ hrZ ⟨q1, q2, q3, hP.1, hP.2⟩
  · rw [hgU]; exact hL
  · rw [hgU]; exact h8
  · rw [hgU]; try rfl

/-- 334: `q4` reloaded from `[rsp + 8]`. -/
theorem a334 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 334 fun g W => ∃ q1 q2 q3 q4, L3 g₀ q1 q2 q3 g ∧ I [q4, q3, q2, q1] W ∧
      rdq(W, sp72 g₀.rsp + 8#64) = q4 := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, q3, q4, hL, hI, hq⟩
  have hs : Y.cpu.gpr.rsp = sp72 g₀.rsp := hL.1.1.1.1
  refine (c_334 prof).run H.c H.hin _ hKY hAY hrY
    (vc_334 (x := q4) (by rw [hs]; exact hq) (by rw [hs]; exact fun i hi => H.c.hws _ (H.ws i hi))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  exact a339 H U W t₁ hKU hAU hrU ⟨q1, q2, q3, q4, by rw [hgU]; exact hL, by rw [hgU]; try rfl, hI⟩

/-- 314: `q4->_progress` released (331, `q4` spilled) when not NULL. -/
theorem a314 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 314 fun g W => ∃ q1 q2 q3 q4, L3 g₀ q1 q2 q3 g ∧ g.r8 = q4 ∧
      I [q4, q3, q2, q1] W := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, q3, q4, hL, h8, hI⟩
  obtain ⟨-, f16, -, -⟩ := H.ob q4 [q3, q2, q1] W hI
  have hs : Y.cpu.gpr.rsp = sp72 g₀.rsp := hL.1.1.1.1
  by_cases hd0 : rdq(W, q4 + 16#64) = 0
  · refine (c_314 prof).run H.c H.hin _ hKY hAY hrY
      (vc_314z (d := rdq(W, q4 + 16#64)) (by rw [h8]) hd0 (by rw [h8]; exact f16)) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    exact a339 H U W t₁ hKU hAU hrU ⟨q1, q2, q3, q4, by rw [hgU]; exact hL, by rw [hgU]; exact h8, hI⟩
  · have hch : Ch K [q4, q3, q2, q1] W (rdq(W, q4 + 16#64)) := Or.inr ⟨q4, [q3, q2, q1], rfl, rfl⟩
    obtain ⟨fd, -⟩ := H.vf [q4, q3, q2, q1] W _ hI hch hd0
    refine (c_314 prof).run H.c H.hin _ hKY hAY hrY
      (vc_314n (d := rdq(W, q4 + 16#64)) (v := rdq(W, rdq(W, q4 + 16#64))) (S := g₀.rsp) hs (by rw [h8]) hd0
        (by rw [h8]; exact f16) rfl fd H.ws) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
    rw [h8] at hAU
    refine callS H (Rg := L3 g₀ q1 q2 q3) (q := q4) (ps := [q3, q2, q1]) (fun _ _ h k => h.sk k)
      (fun _ h => h.1.1.1.1) (by decide) (callm_331 _) ?_ U _ t₁ hKU hAU hrU
      ⟨by rw [hgU]; exact hL, W, _, rfl, hI, hch, hd0, by rw [hgU]; try rfl, by rw [hgU]; try rfl⟩
    intro Z W' t' hKZ hAZ hrZ hP
    exact a334 H Z W' t' hKZ hAZ hrZ ⟨q1, q2, q3, q4, hP.1, hP.2.1, hP.2.2⟩

/-- 309: `q4` reloaded from `[rsp + 8]`. -/
theorem a309 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 309 fun g W => ∃ q1 q2 q3 q4, L3 g₀ q1 q2 q3 g ∧ I [q4, q3, q2, q1] W ∧
      rdq(W, sp72 g₀.rsp + 8#64) = q4 := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, q3, q4, hL, hI, hq⟩
  have hs : Y.cpu.gpr.rsp = sp72 g₀.rsp := hL.1.1.1.1
  refine (c_309 prof).run H.c H.hin _ hKY hAY hrY
    (vc_309 (x := q4) (by rw [hs]; exact hq) (by rw [hs]; exact fun i hi => H.c.hws _ (H.ws i hi))) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ U t₁ hKU hAU hrU hgU -
  exact a314 H U W t₁ hKU hAU hrU ⟨q1, q2, q3, q4, by rw [hgU]; exact hL, by rw [hgU]; try rfl, hI⟩

/-! ## The levels: the count dropped, the object destroyed when it reaches 0 -/

/-- 279: the fourth level, `c` in `r8`. -/
theorem d279 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 279 fun g W => ∃ q1 q2 q3 c, L3 g₀ q1 q2 q3 g ∧ g.r8 = c ∧ g.rcx = vtv ∧
      I [q3, q2, q1] W ∧ K [q3, q2, q1] W c ∧ c ≠ 0 ∧ rdq(W, rdq(W, c) + 16#64) = rlK := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, q3, c, hL, h8, hcx, hI, hK, hc0, hrl⟩
  obtain ⟨o8, -, o24, o0⟩ := H.ko _ W c hI hK hc0 hrl
  have e : eaD Y 8 8 = c + 8#64 := by
    show Y.cpu.gpr.get (regOf 8) + BitVec.ofNat 64 8 = _
    rw [show Y.cpu.gpr.get (regOf 8) = Y.cpu.gpr.r8 from rfl, h8]
  refine H.c.s_sub_mi32f hKY hAY H.hin (lt_len (by decide)) hrY (sub_279 _) (by rw [e]; exact o8) ?_
  rintro U t₁ hKU hAU ⟨hrU, hgU, hfU⟩
  rw [e] at hAU hfU
  have hz : U.cpu.rflags.zf = decide (rdd(W, c + 8#64) = 1#32) := by rw [hfU, subF_zf]
  have hLU : L3 g₀ q1 q2 q3 U.cpu.gpr := by rw [hgU]; exact hL
  have h8U : U.cpu.gpr.r8 = c := by rw [hgU]; exact h8
  have hcxU : U.cpu.gpr.rcx = 7879648#64 := by rw [hgU]; exact hcx
  by_cases h1 : rdd(W, c + 8#64) = 1#32
  · obtain ⟨hI', hK'⟩ := H.dz _ W c hI hK hc0 hrl h1
    have hz' : U.cpu.rflags.zf = true := hz.trans (decide_eq_true h1)
    by_cases h0 : rdq(Wdec W c, c + 24#64) = 0
    · refine (c_284 prof).run H.c H.hin _ hKU hAU hrU
        (vc_284z0 (c := rdq(Wdec W c, c + 24#64)) hz' hcxU (by rw [h8U]; try rfl) (by rw [h8U]; exact o24)
          (by rw [h8U]; exact o0) h0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      rw [h8U] at hAZ
      exact a314 H Z _ t₂ hKZ hAZ hrZ ⟨q1, q2, q3, c, by rw [hgZ]; exact hLU, by rw [hgZ]; exact h8U, hI'⟩
    · obtain ⟨fv, -⟩ := H.vf _ _ _ hI' (Or.inl hK') h0
      refine (c_284 prof).run H.c H.hin _ hKU hAU hrU
        (vc_284zn (c := rdq(Wdec W c, c + 24#64)) (v := rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)))
          (S := g₀.rsp) hz' hcxU hLU.1.1.1.1 (by rw [h8U]; try rfl) (by rw [h8U]; exact o24)
          (by rw [h8U]; exact o0) h0 (by rw [h8U]; try rfl) fv H.ws) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      rw [h8U] at hAZ
      refine callS H (Rg := L3 g₀ q1 q2 q3) (q := c) (ps := [q3, q2, q1]) (fun _ _ h k => h.sk k)
        (fun _ h => h.1.1.1.1) (by decide) (callm_306 _) ?_ Z _ t₂ hKZ hAZ hrZ
        ⟨by rw [hgZ]; exact hLU, _, _, rfl, hI', Or.inl hK', h0, by rw [hgZ]; try rfl, by rw [hgZ]; try rfl⟩
      intro Z' W' t' hKZ' hAZ' hrZ' hP
      exact a309 H Z' W' t' hKZ' hAZ' hrZ' ⟨q1, q2, q3, c, hP.1, hP.2.1, hP.2.2⟩
  · have hz' : U.cpu.rflags.zf = false := hz.trans (decide_eq_false h1)
    refine (c_284 prof).run H.c H.hin _ hKU hAU hrU (vc_284n hz') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    exact a352 H Z _ t₂ hKZ hAZ hrZ ⟨q1, q2, q3, by rw [hgZ]; exact hLU, H.dn _ W c hI hK hc0 hrl h1⟩

theorem a492 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 492 fun g W => ∃ q1 q2 q3, L3 g₀ q1 q2 q3 g ∧ I [q3, q2, q1] W :=
  jmpP H (c_492 prof) (fun _ _ _ _ _ => vc_492) (a352 H)

/-- 240: the third level, `c` in `r15`. -/
theorem d240 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 240 fun g W => ∃ q1 q2 c, L2 g₀ q1 q2 g ∧ g.r15 = c ∧ g.rcx = vtv ∧
      g.rdx = rlK ∧ I [q2, q1] W ∧ K [q2, q1] W c ∧ c ≠ 0 ∧ rdq(W, rdq(W, c) + 16#64) = rlK := by
  rintro Y W t hKY hAY hrY ⟨q1, q2, c, hL, h15, hcx, hdx, hI, hK, hc0, hrl⟩
  obtain ⟨o8, -, o24, o0⟩ := H.ko _ W c hI hK hc0 hrl
  have e : eaD Y 15 8 = c + 8#64 := by
    show Y.cpu.gpr.get (regOf 15) + BitVec.ofNat 64 8 = _
    rw [show Y.cpu.gpr.get (regOf 15) = Y.cpu.gpr.r15 from rfl, h15]
  refine H.c.s_sub_mi32f hKY hAY H.hin (lt_len (by decide)) hrY (sub_240 _) (by rw [e]; exact o8) ?_
  rintro U t₁ hKU hAU ⟨hrU, hgU, hfU⟩
  rw [e] at hAU hfU
  have hz : U.cpu.rflags.zf = decide (rdd(W, c + 8#64) = 1#32) := by rw [hfU, subF_zf]
  have hLU : L2 g₀ q1 q2 U.cpu.gpr := by rw [hgU]; exact hL
  have h15U : U.cpu.gpr.r15 = c := by rw [hgU]; exact h15
  have hcxU : U.cpu.gpr.rcx = 7879648#64 := by rw [hgU]; exact hcx
  have hdxU : U.cpu.gpr.rdx = 4596368#64 := by rw [hgU]; exact hdx
  by_cases h1 : rdd(W, c + 8#64) = 1#32
  · obtain ⟨hI', hK'⟩ := H.dz _ W c hI hK hc0 hrl h1
    have hz' : U.cpu.rflags.zf = true := hz.trans (decide_eq_true h1)
    by_cases h0 : rdq(Wdec W c, c + 24#64) = 0
    · refine (c_245 prof).run H.c H.hin _ hKU hAU hrU
        (vc_245z0 (c := rdq(Wdec W c, c + 24#64)) hz' hcxU (by rw [h15U]; try rfl) (by rw [h15U]; exact o24)
          (by rw [h15U]; exact o0) h0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      rw [h15U] at hAZ
      exact a352 H Z _ t₂ hKZ hAZ hrZ ⟨q1, q2, c, by rw [hgZ]; exact ⟨hLU, h15U⟩, hI'⟩
    · obtain ⟨fv, fx⟩ := H.vf _ _ _ hI' (Or.inl hK') h0
      by_cases hx : rdq(Vv (Wdec W c) c, rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)) + 16#64) = rlK
      · refine (c_245 prof).run H.c H.hin _ hKU hAU hrU
          (vc_245zk (c := rdq(Wdec W c, c + 24#64)) (vt := rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)))
            (x := rlK) hz' hcxU (by rw [h15U]; try rfl) (by rw [h15U]; exact o24) (by rw [h15U]; exact o0) h0
            hdxU (by rw [h15U]; try rfl) (by rw [h15U]; exact hx) rfl fv fx) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
        rw [h15U] at hAZ
        exact d279 H Z _ t₂ hKZ hAZ hrZ ⟨q1, q2, c, _, by rw [hgZ]; exact ⟨hLU, h15U⟩, by rw [hgZ]; try rfl,
          by rw [hgZ]; exact hcxU, hI', hK', h0, hx⟩
      · refine (c_245 prof).run H.c H.hin _ hKU hAU hrU
          (vc_245zm (c := rdq(Wdec W c, c + 24#64)) (vt := rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)))
            (x := rdq(Vv (Wdec W c) c, rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)) + 16#64))
            hz' hcxU (by rw [h15U]; try rfl) (by rw [h15U]; exact o24) (by rw [h15U]; exact o0) h0
            hdxU (by rw [h15U]; try rfl) (by rw [h15U]; try rfl) hx fv fx) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
        rw [h15U] at hAZ
        refine callR H (Rg := L3 g₀ q1 q2 c) (ps := [c, q2, q1]) (fun _ _ h k => h.sk k) (fun _ h => h.1.1.1.1)
          (by decide) (callr_490 _) ?_ Z _ t₂ hKZ hAZ hrZ
          ⟨by rw [hgZ]; exact ⟨hLU, h15U⟩, hI', _, Or.inl hK', h0, by rw [hgZ]; try rfl, by rw [hgZ]; try rfl⟩
        intro Z' W' t' hKZ' hAZ' hrZ' hP
        exact a492 H Z' W' t' hKZ' hAZ' hrZ' ⟨q1, q2, c, hP.1, hP.2⟩
  · have hz' : U.cpu.rflags.zf = false := hz.trans (decide_eq_false h1)
    refine (c_245 prof).run H.c H.hin _ hKU hAU hrU (vc_245n hz') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    exact a380 H Z _ t₂ hKZ hAZ hrZ ⟨q1, q2, by rw [hgZ]; exact hLU, H.dn _ W c hI hK hc0 hrl h1⟩

theorem a469 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 469 fun g W => ∃ q1 q2, L2 g₀ q1 q2 g ∧ I [q2, q1] W :=
  jmpP H (c_469 prof) (fun _ _ _ _ _ => vc_469) (a380 H)

/-- 197: the second level, `c` in `r14`. -/
theorem d197 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 197 fun g W => ∃ q1 c, L1 g₀ q1 g ∧ g.r14 = c ∧ g.rcx = vtv ∧
      g.rdx = rlK ∧ I [q1] W ∧ K [q1] W c ∧ c ≠ 0 ∧ rdq(W, rdq(W, c) + 16#64) = rlK := by
  rintro Y W t hKY hAY hrY ⟨q1, c, hL, h14, hcx, hdx, hI, hK, hc0, hrl⟩
  obtain ⟨o8, -, o24, o0⟩ := H.ko _ W c hI hK hc0 hrl
  have e : eaD Y 14 8 = c + 8#64 := by
    show Y.cpu.gpr.get (regOf 14) + BitVec.ofNat 64 8 = _
    rw [show Y.cpu.gpr.get (regOf 14) = Y.cpu.gpr.r14 from rfl, h14]
  refine H.c.s_sub_mi32f hKY hAY H.hin (lt_len (by decide)) hrY (sub_197 _) (by rw [e]; exact o8) ?_
  rintro U t₁ hKU hAU ⟨hrU, hgU, hfU⟩
  rw [e] at hAU hfU
  have hz : U.cpu.rflags.zf = decide (rdd(W, c + 8#64) = 1#32) := by rw [hfU, subF_zf]
  have hLU : L1 g₀ q1 U.cpu.gpr := by rw [hgU]; exact hL
  have h14U : U.cpu.gpr.r14 = c := by rw [hgU]; exact h14
  have hcxU : U.cpu.gpr.rcx = 7879648#64 := by rw [hgU]; exact hcx
  have hdxU : U.cpu.gpr.rdx = 4596368#64 := by rw [hgU]; exact hdx
  by_cases h1 : rdd(W, c + 8#64) = 1#32
  · obtain ⟨hI', hK'⟩ := H.dz _ W c hI hK hc0 hrl h1
    have hz' : U.cpu.rflags.zf = true := hz.trans (decide_eq_true h1)
    by_cases h0 : rdq(Wdec W c, c + 24#64) = 0
    · refine (c_202 prof).run H.c H.hin _ hKU hAU hrU
        (vc_202z0 (c := rdq(Wdec W c, c + 24#64)) hz' hcxU (by rw [h14U]; try rfl) (by rw [h14U]; exact o24)
          (by rw [h14U]; exact o0) h0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      rw [h14U] at hAZ
      exact a380 H Z _ t₂ hKZ hAZ hrZ ⟨q1, c, by rw [hgZ]; exact ⟨hLU, h14U⟩, hI'⟩
    · obtain ⟨fv, fx⟩ := H.vf _ _ _ hI' (Or.inl hK') h0
      by_cases hx : rdq(Vv (Wdec W c) c, rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)) + 16#64) = rlK
      · refine (c_202 prof).run H.c H.hin _ hKU hAU hrU
          (vc_202zk (c := rdq(Wdec W c, c + 24#64)) (vt := rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)))
            (x := rlK) hz' hcxU (by rw [h14U]; try rfl) (by rw [h14U]; exact o24) (by rw [h14U]; exact o0) h0
            hdxU (by rw [h14U]; try rfl) (by rw [h14U]; exact hx) rfl fv fx) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
        rw [h14U] at hAZ
        exact d240 H Z _ t₂ hKZ hAZ hrZ ⟨q1, c, _, by rw [hgZ]; exact ⟨hLU, h14U⟩, by rw [hgZ]; try rfl,
          by rw [hgZ]; exact hcxU, by rw [hgZ]; exact hdxU, hI', hK', h0, hx⟩
      · refine (c_202 prof).run H.c H.hin _ hKU hAU hrU
          (vc_202zm (c := rdq(Wdec W c, c + 24#64)) (vt := rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)))
            (x := rdq(Vv (Wdec W c) c, rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)) + 16#64))
            hz' hcxU (by rw [h14U]; try rfl) (by rw [h14U]; exact o24) (by rw [h14U]; exact o0) h0
            hdxU (by rw [h14U]; try rfl) (by rw [h14U]; try rfl) hx fv fx) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
        rw [h14U] at hAZ
        refine callR H (Rg := L2 g₀ q1 c) (ps := [c, q1]) (fun _ _ h k => h.sk k) (fun _ h => h.1.1.1)
          (by decide) (callr_467 _) ?_ Z _ t₂ hKZ hAZ hrZ
          ⟨by rw [hgZ]; exact ⟨hLU, h14U⟩, hI', _, Or.inl hK', h0, by rw [hgZ]; try rfl, by rw [hgZ]; try rfl⟩
        intro Z' W' t' hKZ' hAZ' hrZ' hP
        exact a469 H Z' W' t' hKZ' hAZ' hrZ' ⟨q1, c, hP.1, hP.2⟩
  · have hz' : U.cpu.rflags.zf = false := hz.trans (decide_eq_false h1)
    refine (c_202 prof).run H.c H.hin _ hKU hAU hrU (vc_202n hz') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    exact a408 H Z _ t₂ hKZ hAZ hrZ ⟨q1, by rw [hgZ]; exact hLU, H.dn _ W c hI hK hc0 hrl h1⟩

theorem a485 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 485 fun g W => ∃ q1, L1 g₀ q1 g ∧ I [q1] W :=
  jmpP H (c_485 prof) (fun _ _ _ _ _ => vc_485) (a408 H)

/-- 60: the first level, `this->_ratioProgress` = `c` in `r12`. -/
theorem d60 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 60 fun g W => ∃ c, Rr g₀ g ∧ g.r12 = c ∧ g.rdx = rlK ∧ I [] W ∧ K [] W c ∧
      c ≠ 0 ∧ rdq(W, rdq(W, c) + 16#64) = rlK := by
  rintro Y W t hKY hAY hrY ⟨c, hR, h12, hdx, hI, hK, hc0, hrl⟩
  obtain ⟨o8, -, o24, o0⟩ := H.ko _ W c hI hK hc0 hrl
  have e : eaD Y 12 8 = c + 8#64 := by
    show Y.cpu.gpr.get (regOf 12) + BitVec.ofNat 64 8 = _
    rw [show Y.cpu.gpr.get (regOf 12) = Y.cpu.gpr.r12 from rfl, h12]
  refine H.c.s_sub_mi32f hKY hAY H.hin (lt_len (by decide)) hrY (sub_60 _) (by rw [e]; exact o8) ?_
  rintro U t₁ hKU hAU ⟨hrU, hgU, hfU⟩
  rw [e] at hAU hfU
  have hz : U.cpu.rflags.zf = decide (rdd(W, c + 8#64) = 1#32) := by rw [hfU, subF_zf]
  have hRU : Rr g₀ U.cpu.gpr := by rw [hgU]; exact hR
  have h12U : U.cpu.gpr.r12 = c := by rw [hgU]; exact h12
  have hdxU : U.cpu.gpr.rdx = 4596368#64 := by rw [hgU]; exact hdx
  by_cases h1 : rdd(W, c + 8#64) = 1#32
  · obtain ⟨hI', hK'⟩ := H.dz _ W c hI hK hc0 hrl h1
    have hz' : U.cpu.rflags.zf = true := hz.trans (decide_eq_true h1)
    by_cases h0 : rdq(Wdec W c, c + 24#64) = 0
    · refine (c_66 prof).run H.c H.hin _ hKU hAU hrU
        (vc_66z0 (c := rdq(Wdec W c, c + 24#64)) hz' (by rw [h12U]; try rfl) (by rw [h12U]; exact o24)
          (by rw [h12U]; exact o0) h0) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      rw [h12U] at hAZ
      exact a408 H Z _ t₂ hKZ hAZ hrZ ⟨c, by rw [hgZ]; exact ⟨hRU, h12U⟩, hI'⟩
    · obtain ⟨fv, fx⟩ := H.vf _ _ _ hI' (Or.inl hK') h0
      by_cases hx : rdq(Vv (Wdec W c) c, rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)) + 16#64) = rlK
      · refine (c_66 prof).run H.c H.hin _ hKU hAU hrU
          (vc_66zk (c := rdq(Wdec W c, c + 24#64)) (vt := rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)))
            (x := rlK) hz' (by rw [h12U]; try rfl) (by rw [h12U]; exact o24) (by rw [h12U]; exact o0) h0
            hdxU (by rw [h12U]; try rfl) (by rw [h12U]; exact hx) rfl fv fx) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
        rw [h12U] at hAZ
        exact d197 H Z _ t₂ hKZ hAZ hrZ ⟨c, _, by rw [hgZ]; exact ⟨hRU, h12U⟩, by rw [hgZ]; try rfl,
          by rw [hgZ]; try rfl, by rw [hgZ]; exact hdxU, hI', hK', h0, hx⟩
      · refine (c_66 prof).run H.c H.hin _ hKU hAU hrU
          (vc_66zm (c := rdq(Wdec W c, c + 24#64)) (vt := rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)))
            (x := rdq(Vv (Wdec W c) c, rdq(Vv (Wdec W c) c, rdq(Wdec W c, c + 24#64)) + 16#64))
            hz' (by rw [h12U]; try rfl) (by rw [h12U]; exact o24) (by rw [h12U]; exact o0) h0
            hdxU (by rw [h12U]; try rfl) (by rw [h12U]; try rfl) hx fv fx) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
        rw [h12U] at hAZ
        refine callR H (Rg := L1 g₀ c) (ps := [c]) (fun _ _ h k => h.sk k) (fun _ h => h.1.1)
          (by decide) (callr_483 _) ?_ Z _ t₂ hKZ hAZ hrZ
          ⟨by rw [hgZ]; exact ⟨hRU, h12U⟩, hI', _, Or.inl hK', h0, by rw [hgZ]; try rfl, by rw [hgZ]; try rfl⟩
        intro Z' W' t' hKZ' hAZ' hrZ' hP
        exact a485 H Z' W' t' hKZ' hAZ' hrZ' ⟨c, hP.1, hP.2⟩
  · have hz' : U.cpu.rflags.zf = false := hz.trans (decide_eq_false h1)
    refine (c_66 prof).run H.c H.hin _ hKU hAU hrU (vc_66n hz') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
    exact a68 H Z _ t₂ hKZ hAZ hrZ ⟨by rw [hgZ]; exact hRU, H.dn _ W c hI hK hc0 hrl h1⟩

theorem a453 (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) :
    AtJ prof F Wl L s₀ o gev gP gE 453 fun g W => Rr g₀ g ∧ I [] W :=
  jmpP H (c_453 prof) (fun _ _ _ _ _ => vc_453) (a68 H)

/-! ## The run -/

/-- `CLocalProgress::Init` from its entry, the registers `g₀`, the bytes `V`: the run goes on to the goal. -/
theorem lpi_ok (H : Hyp prof F Wl L s₀ o gev gP gE g₀ e₂ code₂ j₂ I K T) {X : State} {V : Addr → Byte} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = clp_at) (hg : X.cpu.gpr = g₀)
    (hI : I [] (Vp6 V g₀)) (hK0 : K [] (Vp6 V g₀) (rdq(Vp6 V g₀, g₀.rdi + 24#64))) :
    GoG prof L o gev gP gE X t := by
  subst hg
  have hr0 : X.cpu.rip = clp_at.add 0 := by rw [hrip, addr_add_zero]
  have fc : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rdi + 24#64) i) := fun i hi => H.c.hws _ (H.w24 i hi)
  by_cases h0 : rdq(Vp6 V X.cpu.gpr, X.cpu.gpr.rdi + 24#64) = 0
  · refine (c_0 prof).run H.c H.hin _ hK hA hr0 (vc_0z rfl h0 fc H.w1 H.w2 H.w3 H.w4 H.w5 H.w6) ?_
    rintro j' g' fl V₁ ⟨rfl, rfl, hR⟩ Z t₁ hKZ hAZ hrZ rfl -
    exact a76 H Z _ t₁ hKZ hAZ hrZ ⟨hR, H.z0 _ hI h0⟩
  · obtain ⟨fv, fx⟩ := H.vf [] _ _ hI (Or.inl hK0) h0
    by_cases hx : rdq(Vp6 V X.cpu.gpr, rdq(Vp6 V X.cpu.gpr, rdq(Vp6 V X.cpu.gpr, X.cpu.gpr.rdi + 24#64)) + 16#64)
        = rlK
    · refine (c_0 prof).run H.c H.hin _ hK hA hr0
        (vc_0k rfl h0 rfl rfl hx fc fv fx H.w1 H.w2 H.w3 H.w4 H.w5 H.w6) ?_
      rintro j' g' fl V₁ ⟨rfl, rfl, hR, h12, hdx⟩ Z t₁ hKZ hAZ hrZ rfl -
      exact d60 H Z _ t₁ hKZ hAZ hrZ ⟨_, hR, h12, hdx, hI, hK0, h0, hx⟩
    · refine (c_0 prof).run H.c H.hin _ hK hA hr0
        (vc_0m rfl h0 rfl rfl hx fc fv fx H.w1 H.w2 H.w3 H.w4 H.w5 H.w6) ?_
      rintro j' g' fl V₁ ⟨rfl, rfl, hR, h12, hdi, hax⟩ Z t₁ hKZ hAZ hrZ rfl -
      exact callR H (Rg := Rr X.cpu.gpr) (ps := []) (fun _ _ h k => h.sk k) (fun _ h => h.1) (by decide)
        (callr_451 _) (a453 H) Z _ t₁ hKZ hAZ hrZ ⟨hR, hI, _, Or.inl hK0, h0, hdi, hax⟩

end FV7z.Clp
