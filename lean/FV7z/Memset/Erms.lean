import FV7z.Memset.Code
import FV7z.Strlen.Loop
import FV7z.Ipa.Set
/-!
# `__memset_erms` (PLAN.md M, the PLT contracts of `launch_to_main`)

At `+80` of `ms2` (`0x65c6a0` in `7zzs`): `test rdx, rdx`; 0: `rax = rdi`, `ret`; else `rcx = rdx`, `eax = sil`,
`rdx = rdi`, `rep stosb`, `rax = rdx`, `ret`.

`Ipa.SetAt` asks neither the direction flag clear at the call nor the 8 bytes at `rsp` short of the top of the address
space (a return address that wraps to `0` might be among the bytes stored into), and without the first `rep stosb`
stores downwards. `SetAtD` is `Ipa.SetAt` with both (`X.cpu.rflags.df = false`, `rsp + 8 ≤ 2 ^ 64`); the contracts
reached through the PLT are to take it (PLAN.md M). `setAtD_erms`: a call at `+80` does what `SetAtD` says.
-/
namespace FV7z.Memset
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

/-- The registers a call keeps, as at the call. -/
def KpS (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧
    g.r15 = g₀.r15

/-- What the call returns to, from registers `g₀` and bytes `V` at the call: `SetAtD`'s continuation, its return
address in code. -/
def RetS (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (g₀ : Gprs) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add g₀.rsp i)) ∧ ∃ (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat), CodeIn L e₂ code₂ ∧
    j₂ < code₂.length ∧ ofBytesLE 64 ((byteAddrs g₀.rsp 8).map V) = e₂.add j₂ ∧
    ∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = g₀.rsp + 8 →
      Z.cpu.gpr.rax = g₀.rdi → Z.cpu.gpr.rbx = g₀.rbx → Z.cpu.gpr.rbp = g₀.rbp → Z.cpu.gpr.r12 = g₀.r12 →
      Z.cpu.gpr.r13 = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 → Z.cpu.gpr.r15 = g₀.r15 →
      (∀ i < g₀.rdx.toNat, V₂ (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8) →
      (∀ a : Addr, ¬ (g₀.rdi.toNat ≤ a.toNat ∧ a.toNat < g₀.rdi.toNat + g₀.rdx.toNat) → V₂ a = V a) →
      GoG prof L o gev gP gE Z t'

/-- `Ipa.SetAt` with the direction flag clear and the return address's bytes not wrapping. -/
def SetAtD (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (e : Addr) (Pm : (Addr → Byte) → Prop) :
    Prop :=
  ∀ {F : Footprint} {Wl : List Rgn} {s₀ : State} {gev : List Event} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {X : State} {t : Nat} {V : Addr → Byte} {e' : Addr} {code : List Byte}
    {j : Nat}, Seg prof F Wl L s₀ o → KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e → Pm V →
    CodeIn L e' code → j < code.length → rdq(V, X.cpu.gpr.rsp) = e'.add j →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) →
    (∀ i < X.cpu.gpr.rdx.toNat, Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
    X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ 2 ^ 64 →
    (X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat ≤ X.cpu.gpr.rsp.toNat ∨
      X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
    X.cpu.rflags.df = false → X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 →
    (∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → Z.cpu.gpr.rax = X.cpu.gpr.rdi →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ i < X.cpu.gpr.rdx.toNat, V₂ (Addr.add X.cpu.gpr.rdi i) = X.cpu.gpr.rsi.setWidth 8) →
      (∀ a : Addr, ¬ (X.cpu.gpr.rdi.toNat ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rdi.toNat + X.cpu.gpr.rdx.toNat) →
        V₂ a = V a) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- A `ret` with `rax = rdi`, the bytes `V₂` as `RetS` asks and the return address's as in `V`. -/
theorem ret_atS (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {j : Nat} (hj : j < ms2.length)
    (hd : Dec prof.feat ms2 j (FV7z.mk .ret 64 [] 1)) {Y : State} {t : Nat} {g₀ : Gprs} {V₂ : Addr → Byte}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₂) (hrip : Y.cpu.rip = e.add j) (hkp : KpS g₀ Y.cpu.gpr)
    (hax : Y.cpu.gpr.rax = g₀.rdi) (hra : ∀ i < 8, V₂ (Addr.add g₀.rsp i) = V (Addr.add g₀.rsp i))
    (hfill : ∀ i < g₀.rdx.toNat, V₂ (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8)
    (hout : ∀ a : Addr, ¬ (g₀.rdi.toNat ≤ a.toNat ∧ a.toNat < g₀.rdi.toNat + g₀.rdx.toNat) → V₂ a = V a)
    (hR : RetS prof F Wl L s₀ o gev gP gE V g₀) : GoG prof L o gev gP gE Y t := by
  obtain ⟨hl, e₂, code₂, j₂, hin₂, h₂, hra₂, K⟩ := hR
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := hkp
  have hrd : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V₂) = e₂.add j₂ := by
    rw [hsp, ← hra₂]
    congr 1
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    exact hra i hi
  refine c.s_ret hK hA hin hj hrip hd (by rw [hsp]; exact hl) hin₂ h₂ hrd ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine K Z t' V₂ hKZ hAZ hrZ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hfill hout <;> rw [hgZ]
  · exact congrArg (· + (8 : BitVec 64)) hsp
  · exact hax
  · exact hbx
  · exact hbp
  · exact h12
  · exact h13
  · exact h14
  · exact h15

theorem setWidth8_zx (x : BitVec 64) : (((x.setWidth 8).setWidth 32).setWidth 64).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

/-- `__memset_erms` from `+80`, called with registers `g₀`. -/
theorem erms (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e ms2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 80) (hg : X.cpu.gpr = g₀)
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i)) (hov : g₀.rdi.toNat + g₀.rdx.toNat ≤ 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf : X.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetS prof F Wl L s₀ o gev gP gE V g₀) : GoG prof L o gev gP gE X t := by
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  have hkp : KpS g₀ X.cpu.gpr := by rw [hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `endbr64`, `test rdx, rdx`
  refine c.s_blkV hin (b80 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  have hg₁' : Y₁.cpu.gpr = X.cpu.gpr := by rw [hg₁]
  have hc := cond5_mask hP
  simp only [gv, Src.val, get2, BitVec.setWidth_eq, BitVec.and_self] at hc
  refine c.s_jccV hK₁ hA₁ hin (by rw [ms2_length]; omega) hr₁ (d87 prof.feat) (tgt := 93) rfl
    (by rw [ms2_length]; omega) ?_ ?_
  · -- `rdx ≠ 0`: `mov rcx, rdx`, `movzx eax, sil`, `mov rdx, rdi`, `rep stosb`
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc] at htk
    have hdx : X.cpu.gpr.rdx.toNat ≠ 0 := fun h => by
      rw [BitVec.eq_of_toNat_eq (y := 0#64) h] at htk
      exact absurd htk (by decide)
    obtain ⟨n, hn⟩ : ∃ n, X.cpu.gpr.rdx.toNat = n + 1 := ⟨X.cpu.gpr.rdx.toNat - 1, by omega⟩
    refine c.s_blkV hin (b93 prof) hK₂ hA₂ hr₂ ?_
    refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
    intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ _
    rw [hg₂, hg₁'] at hg₃
    simp only [wr, gv, Src.val, set_rax, set_rcx, set_rdx, get2, get6, get7, BitVec.setWidth_eq] at hg₃
    have hcx₃ : Y₃.cpu.gpr.rcx.toNat = n + 1 := by simp only [hg₃]; exact hn
    have hdi₃ : Y₃.cpu.gpr.rdi = g₀.rdi := by simp only [hg₃, hg]
    have hdx₃ : Y₃.cpu.gpr.rdx = g₀.rdi := by simp only [hg₃, hg]
    have hax₃ : Y₃.cpu.gpr.rax.setWidth 8 = g₀.rsi.setWidth 8 := by simp only [hg₃, hg]; exact setWidth8_zx _
    have hkp₃ : KpS g₀ Y₃.cpu.gpr := by simp only [KpS, hg₃]; exact hkp
    rw [hg] at hn
    refine c.s_rep_stosb hdf₀ hin (j := 103) (by rw [ms2_length]; omega) (by rw [ms2_length]; omega)
      (d103 prof.feat) n hK₃ hA₃ hr₃ hcx₃ (fun i hi => by rw [hdi₃]; exact hst i (by omega)) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    rw [hdi₃, hax₃] at hA₄
    -- `mov rax, rdx`, `ret`
    refine c.s_blkV hin (b105 prof) hK₄ hA₄ hr₄ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ _ _
    rw [hg₄] at hg₅
    simp only [wr, gv, Src.val, set_rax, get2, BitVec.setWidth_eq] at hg₅
    have hkp₅ : KpS g₀ Y₅.cpu.gpr := by simp only [KpS, hg₅]; exact hkp₃
    have hax₅ : Y₅.cpu.gpr.rax = g₀.rdi := by simp only [hg₅]; exact hdx₃
    refine ret_atS c hin (by rw [ms2_length]; omega) (d108 prof.feat) hK₅ hA₅ hr₅ hkp₅ hax₅ (fun i hi => ?_)
      (fun i hi => ?_) (fun a ha => ?_) hR
    · refine VfillB_out _ _ _ _ _ fun k hk e' => ?_
      have h1 := congrArg BitVec.toNat e'
      rw [toNat_add_of_fits (n := 8) hi hsp8, toNat_add_of_fits (n := n + 1) hk (by omega)] at h1
      omega
    · exact VfillB_in _ _ _ _ (by omega) i (by omega)
    · refine VfillB_out _ _ _ _ _ fun k hk e' => ha ?_
      rw [e', toNat_add_of_fits (n := n + 1) hk (by omega)]
      omega
  · -- `rdx = 0`: `mov rax, rdi`, `ret`
    intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc] at hfa
    have hdx : X.cpu.gpr.rdx = 0 := by
      cases h : X.cpu.gpr.rdx == 0
      · rw [h] at hfa; exact absurd hfa (by decide)
      · exact beq_iff_eq.1 h
    refine c.s_blkV hin (b89 prof) hK₂ hA₂ hr₂ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ _
    rw [hg₂, hg₁'] at hg₃
    simp only [wr, gv, Src.val, set_rax, get7, BitVec.setWidth_eq] at hg₃
    have hkp₃ : KpS g₀ Y₃.cpu.gpr := by simp only [KpS, hg₃]; exact hkp
    have hax₃ : Y₃.cpu.gpr.rax = g₀.rdi := by simp only [hg₃, hg]
    rw [hg] at hdx
    refine ret_atS c hin (by rw [ms2_length]; omega) (d92 prof.feat) hK₃ hA₃ hr₃ hkp₃ hax₃ (fun _ _ => rfl)
      (fun i hi => ?_) (fun _ _ => rfl) hR
    rw [hdx] at hi
    exact absurd hi (Nat.not_lt_zero _)

/-- A call of `__memset_erms` does what `SetAtD` says. -/
theorem setAtD_erms {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr}
    {Pm : (Addr → Byte) → Prop} (hin : CodeIn L e ms2) : SetAtD prof L o (e.add 80) Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j c hK hA hrip _ hin₂ hj hra hl hst hov hsp hdf hsp8 K
  exact erms (g₀ := X.cpu.gpr) c hin hK hA hrip rfl hst hov hsp hdf hsp8 ⟨hl, e', code, j, hin₂, hj, hra, K⟩

end FV7z.Memset
