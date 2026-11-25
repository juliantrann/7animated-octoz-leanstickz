import FV7z.Memcpy.Code
import FV7z.Memset.Sse2
import FV7z.Tls.Holds
import FV7z.Gor.Mem
/-!
# `__memmove_erms` and `__mempcpy_erms` (PLAN.md M, the PLT contracts of `launch_to_main`)

`__memmove_erms` at `+128` of `mc2` (`0x65b950` in `7zzs`): `rax = rdi`; `rdx = 0`: `ret`; else `rcx = rdx`, and with
`rdi < rsi` a forward `rep movsb`, with `rdi = rsi` `ret`, with `rsi + rcx ≤ rdi` a forward `rep movsb`, else (`rdi`
inside the source) a backward one between `std` and `cld`. `__mempcpy_erms` at `+80`: `rax = rdi`; `rdx = 0`: `ret`;
else `rax = rdi + rdx` and on at `+140`. The ranges of `Tls.CpyAt` and `Gor.PcpyAt` are apart, so with `rdx ≠ 0`
neither the `rdi = rsi` exit nor the backward copy is reached (`from140`): `cpyAt_erms`, `pcpyAt_erms`.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-! ## Stretches -/

/-- `endbr64`, `mov rax, rdi`, `test rdx, rdx` (at `80` and at `128`). -/
def o80 : List VOp := [
  VOp.op Op.nop,
  VOp.op (Op.mov 64 0 (.r 7)),
  VOp.op (Op.test 64 2 (.r 2))]

theorem b80 (prof : Profile) : BlkV prof mc2 80 90 o80 :=
  .cons (d80 _) (OpI.endbr) (by rw [mc2_length]; decide) <|
  .cons (d84 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d87 _) (OpI.test (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .nil 90

theorem b128 (prof : Profile) : BlkV prof mc2 128 138 o80 :=
  .cons (d128 _) (OpI.endbr) (by rw [mc2_length]; decide) <|
  .cons (d132 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d135 _) (OpI.test (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .nil 138

/-- `add rax, rdx`. -/
def o92 : List VOp := [
  VOp.op (Op.add 64 0 (.r 2))]

theorem b92 (prof : Profile) : BlkV prof mc2 92 95 o92 :=
  .cons (d92 _) (OpI.add (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .nil 95

/-- `mov rcx, rdx`, `cmp rdi, rsi`. -/
def o140 : List VOp := [
  VOp.op (Op.mov 64 1 (.r 2)),
  VOp.op (Op.cmp 64 7 (.r 6))]

theorem b140 (prof : Profile) : BlkV prof mc2 140 146 o140 :=
  .cons (d140 _) (OpI.mov (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d143 _) (OpI.cmp (.r 6) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .nil 146

/-- `lea rdx, [rsi + rcx]`, `cmp rdi, rdx`. -/
def o150 : List VOp := [
  VOp.op (Op.lea 64 2 (some 6) (some 1) 1 0),
  VOp.op (Op.cmp 64 7 (.r 2))]

theorem b150 (prof : Profile) : BlkV prof mc2 150 157 o150 :=
  .cons (d150 _) (OpI.lea (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d154 _) (OpI.cmp (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .nil 157

/-! ## The runs -/

/-- What the call returns to, from registers `g₀` and bytes `V` at the call, with `rax = r`: the continuation of
`Tls.CpyAt` (`r = rdi`) or `Gor.PcpyAt` (`r = rdi + rdx`), its return address in code. -/
def RetC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (V : Addr → Byte)
    (g₀ : Gprs) (r : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add g₀.rsp i)) ∧ ∃ (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat), CodeIn L e₂ code₂ ∧
    j₂ < code₂.length ∧ ofBytesLE 64 ((byteAddrs g₀.rsp 8).map V) = e₂.add j₂ ∧
    ∀ Z t' V₂, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = g₀.rsp + 8 →
      Z.cpu.gpr.rax = r → Z.cpu.gpr.rbx = g₀.rbx → Z.cpu.gpr.rbp = g₀.rbp → Z.cpu.gpr.r12 = g₀.r12 →
      Z.cpu.gpr.r13 = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 → Z.cpu.gpr.r15 = g₀.r15 →
      (∀ i < g₀.rdx.toNat, V₂ (Addr.add g₀.rdi i) = V (Addr.add g₀.rsi i)) →
      (∀ a : Addr, ¬ (g₀.rdi.toNat ≤ a.toNat ∧ a.toNat < g₀.rdi.toNat + g₀.rdx.toNat) → V₂ a = V a) →
      GoG prof L o gev gP gE Z t'

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- A `ret` with `rax = r`, the bytes `V₂` as `RetC` asks and the return address's as in `V`. -/
theorem ret_atC (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {j len : Nat} (hj : j < mc2.length)
    (hd : Dec prof.feat mc2 j (FV7z.mk .ret 64 [] len)) {Y : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    {V₂ : Addr → Byte} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₂) (hrip : Y.cpu.rip = e.add j)
    (hkp : KpS g₀ Y.cpu.gpr) (hax : Y.cpu.gpr.rax = r)
    (hra : ∀ i < 8, V₂ (Addr.add g₀.rsp i) = V (Addr.add g₀.rsp i))
    (hcp : ∀ i < g₀.rdx.toNat, V₂ (Addr.add g₀.rdi i) = V (Addr.add g₀.rsi i))
    (hout : ∀ a : Addr, ¬ (g₀.rdi.toNat ≤ a.toNat ∧ a.toNat < g₀.rdi.toNat + g₀.rdx.toNat) → V₂ a = V a)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE Y t := by
  obtain ⟨hl, e₂, code₂, j₂, hin₂, h₂, hra₂, K⟩ := hR
  obtain ⟨hsp, hbx, hbp, h12, h13, h14, h15⟩ := hkp
  have hrd : ofBytesLE 64 ((byteAddrs Y.cpu.gpr.rsp 8).map V₂) = e₂.add j₂ := by
    rw [hsp, ← hra₂]
    congr 1
    refine List.map_congr_left fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    exact hra i hi
  refine c.s_retL hK hA hin hj hrip hd (by rw [hsp]; exact hl) hin₂ h₂ hrd ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine K Z t' V₂ hKZ hAZ hrZ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hcp hout <;> rw [hgZ]
  · exact congrArg (· + (8 : BitVec 64)) hsp
  · exact hax
  · exact hbx
  · exact hbp
  · exact h12
  · exact h13
  · exact h14
  · exact h15

/-- From `159`, `rcx = rdx = n + 1`: the forward `rep movsb` and the `ret`. -/
theorem from159 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {Y : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    {r : Addr} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 159)
    (hkp : KpS g₀ Y.cpu.gpr) (hax : Y.cpu.gpr.rax = r) (hdi : Y.cpu.gpr.rdi = g₀.rdi) (hsi : Y.cpu.gpr.rsi = g₀.rsi)
    (hcx : Y.cpu.gpr.rcx.toNat = n + 1) (hn : g₀.rdx.toNat = n + 1)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64) (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf₀ : s₀.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE Y t := by
  refine c.s_rep_movsb hdf₀ hin (j := 159) (by rw [mc2_length]; omega) (by rw [mc2_length]; omega)
    (d159 prof.feat) n hK hA hrip hcx (fun i hi => by rw [hsi]; exact hsrc i (by omega))
    (fun i hi => by rw [hdi]; exact hst i (by omega)) ?_
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hdi, hsi] at hA₁
  have hkp₁ : KpS g₀ Y₁.cpu.gpr := by rw [hg₁]; exact hkp
  have hax₁ : Y₁.cpu.gpr.rax = r := by rw [hg₁]; exact hax
  refine ret_atC c hin (by rw [mc2_length]; omega) (d161 prof.feat) hK₁ hA₁ hr₁ hkp₁ hax₁ (fun i hi => ?_)
    (fun i hi => ?_) (fun a ha => ?_) hR
  · refine VcopyB_out _ _ _ _ _ fun k hk e' => ?_
    have h1 := congrArg BitVec.toNat e'
    rw [toNat_add_of_fits (n := 8) hi hsp8, toNat_add_of_fits (n := n + 1) hk (by omega)] at h1
    omega
  · exact VcopyB_in (n + 1) V g₀.rdi g₀.rsi (by omega) (by omega) (by omega) i (by omega)
  · refine VcopyB_out _ _ _ _ _ fun k hk e' => ha ?_
    rw [e', toNat_add_of_fits (n := n + 1) hk (by omega)]
    omega

/-- From `140`, `rdx = n + 1`, `rax = r`, the ranges apart: `mov rcx, rdx`, `cmp rdi, rsi`, and either `rdi < rsi` or
(`rdi ≠ rsi`, `lea rdx, [rsi + rcx]`, `cmp rdi, rdx`) `rsi + rcx ≤ rdi`; on at `159` both ways. -/
theorem from140 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {Y : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    {r : Addr} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 140)
    (hkp : KpS g₀ Y.cpu.gpr) (hax : Y.cpu.gpr.rax = r) (hdi : Y.cpu.gpr.rdi = g₀.rdi) (hsi : Y.cpu.gpr.rsi = g₀.rsi)
    (hdx : Y.cpu.gpr.rdx = g₀.rdx) (hn : g₀.rdx.toNat = n + 1)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64) (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf₀ : s₀.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE Y t := by
  -- `mov rcx, rdx`, `cmp rdi, rsi`
  refine c.s_blkV hin (b140 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [wr, gv, Src.val, set_rcx, get2, get6, get7, BitVec.setWidth_eq] at hg₁ hP
  have hkp₁ : KpS g₀ Y₁.cpu.gpr := by rw [hg₁]; exact hkp
  have hax₁ : Y₁.cpu.gpr.rax = r := by rw [hg₁]; exact hax
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := by rw [hg₁]; exact hdi
  have hsi₁ : Y₁.cpu.gpr.rsi = g₀.rsi := by rw [hg₁]; exact hsi
  have hcx₁ : Y₁.cpu.gpr.rcx = g₀.rdx := by rw [hg₁]; exact hdx
  have hcn₁ : Y₁.cpu.gpr.rcx.toNat = n + 1 := by rw [hcx₁]; exact hn
  have hcf : fl.cf = decide (g₀.rdi.toNat < g₀.rsi.toNat) := by rw [hP, subF_cf, hdi, hsi]
  have hzf : fl.zf = decide (g₀.rdi = g₀.rsi) := by rw [hP, subF_zf, hdi, hsi]
  refine c.s_jccF hK₁ hA₁ hin (by rw [mc2_length]; omega) hr₁ (d146 prof.feat) (tgt := 159) rfl
    (by rw [mc2_length]; omega) ?_ ?_
  · -- `rdi < rsi`
    intro _ Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    exact from159 c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hkp₁) (by rw [hg₂]; exact hax₁) (by rw [hg₂]; exact hdi₁)
      (by rw [hg₂]; exact hsi₁) (by rw [hg₂]; exact hcn₁) hn hsrc hst hs64 hd64 hap hsp hdf₀ hsp8 hR
  intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _, hf₂⟩
  rw [hf₁, cond_2, hcf] at hfa
  have hge : g₀.rsi.toNat ≤ g₀.rdi.toNat := by
    have := of_decide_eq_false hfa
    omega
  refine c.s_jccV hK₂ hA₂ hin (by rw [mc2_length]; omega) hr₂ (d148 prof.feat) (tgt := 161) rfl
    (by rw [mc2_length]; omega) ?_ ?_
  · -- `rdi = rsi`: not with the ranges apart and `rdx ≠ 0`
    intro htk
    rw [hf₂, rfz_cond, hf₁, cond_4, hzf] at htk
    have h := congrArg BitVec.toNat (of_decide_eq_true htk)
    omega
  intro hne Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
  rw [hf₂, rfz_cond, hf₁, cond_4, hzf] at hne
  have hne' : g₀.rdi.toNat ≠ g₀.rsi.toNat := fun h => by
    rw [BitVec.eq_of_toNat_eq h] at hne
    simp at hne
  have hgt : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat := by omega
  -- `lea rdx, [rsi + rcx]`, `cmp rdi, rdx`
  refine c.s_blkV hin (b150 prof) hK₃ hA₃ hr₃ ?_
  refine wpV_reg fun _ _ => wpV_reg fun fl₄ hP₄ => wpV_nil ?_
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ hf₄ _
  simp only [wr, gv, Src.val, eaG, optV, set_rdx, get1, get2, get6, get7, BitVec.setWidth_eq, BitVec.mul_one,
    BitVec.add_zero] at hg₄ hP₄
  have hg₃' : Y₃.cpu.gpr = Y₁.cpu.gpr := hg₃.trans hg₂
  have hcf₄ : fl₄.cf = false := by
    rw [hP₄, subF_cf, hg₃', hdi₁, hsi₁, hcx₁, BitVec.toNat_add, Nat.mod_eq_of_lt hs64]
    exact decide_eq_false (by omega)
  refine c.s_jccV hK₄ hA₄ hin (by rw [mc2_length]; omega) hr₄ (d157 prof.feat) (tgt := 162) rfl
    (by rw [mc2_length]; omega) ?_ ?_
  · intro htk
    rw [hf₄, cond_2, hcf₄] at htk
    exact absurd htk (by decide)
  intro _ Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, _⟩
  have hg₅' : Y₅.cpu.gpr = { Y₁.cpu.gpr with rdx := Y₁.cpu.gpr.rsi + Y₁.cpu.gpr.rcx } := by
    rw [hg₅, hg₄, hg₃']
  exact from159 c hin hK₅ hA₅ hr₅ (by rw [hg₅']; exact hkp₁) (by rw [hg₅']; exact hax₁) (by rw [hg₅']; exact hdi₁)
    (by rw [hg₅']; exact hsi₁) (by rw [hg₅']; exact hcn₁) hn hsrc hst hs64 hd64 hap hsp hdf₀ hsp8 hR

/-- `__memmove_erms` from `+128`, called with registers `g₀`. -/
theorem erms (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 128) (hg : X.cpu.gpr = g₀)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64) (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf : X.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ g₀.rdi) : GoG prof L o gev gP gE X t := by
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  have hkp : KpS g₀ X.cpu.gpr := by rw [hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `endbr64`, `mov rax, rdi`, `test rdx, rdx`
  refine c.s_blkV hin (b128 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  have hc := cond4_mask hP
  simp only [wr, gv, Src.val, set_rax, get2, get7, BitVec.setWidth_eq, BitVec.and_self] at hg₁ hc
  have hkp₁ : KpS g₀ Y₁.cpu.gpr := by rw [hg₁]; exact hkp
  have hax₁ : Y₁.cpu.gpr.rax = g₀.rdi := by simp only [hg₁, hg]
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; omega) hr₁ (d138 prof.feat) (tgt := 161) rfl
    (by rw [mc2_length]; omega) ?_ ?_
  · -- `rdx = 0`: `ret`
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc, hg] at htk
    have hdx : g₀.rdx = 0 := beq_iff_eq.1 htk
    refine ret_atC c hin (by rw [mc2_length]; omega) (d161 prof.feat) hK₂ hA₂ hr₂ (by rw [hg₂]; exact hkp₁)
      (by rw [hg₂]; exact hax₁) (fun _ _ => rfl) (fun i hi => ?_) (fun _ _ => rfl) hR
    rw [hdx] at hi
    exact absurd hi (Nat.not_lt_zero _)
  · -- `rdx ≠ 0`
    intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc, hg] at hfa
    have hdx : g₀.rdx.toNat ≠ 0 := fun h => by
      rw [BitVec.eq_of_toNat_eq (y := 0#64) h] at hfa
      exact absurd hfa (by decide)
    obtain ⟨n, hn⟩ : ∃ n, g₀.rdx.toNat = n + 1 := ⟨g₀.rdx.toNat - 1, by omega⟩
    exact from140 c hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hkp₁) (by rw [hg₂]; exact hax₁)
      (by simp only [hg₂, hg₁, hg]) (by simp only [hg₂, hg₁, hg])
      (by simp only [hg₂, hg₁, hg]) hn hsrc hst hs64 hd64 hap hsp hdf₀ hsp8 hR

/-- `__mempcpy_erms` from `+80`, called with registers `g₀`. -/
theorem perms (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 80) (hg : X.cpu.gpr = g₀)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64) (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf : X.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ (g₀.rdi + g₀.rdx)) : GoG prof L o gev gP gE X t := by
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  have hkp : KpS g₀ X.cpu.gpr := by rw [hg]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `endbr64`, `mov rax, rdi`, `test rdx, rdx`
  refine c.s_blkV hin (b80 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  have hc := cond4_mask hP
  simp only [wr, gv, Src.val, set_rax, get2, get7, BitVec.setWidth_eq, BitVec.and_self] at hg₁ hc
  have hkp₁ : KpS g₀ Y₁.cpu.gpr := by rw [hg₁]; exact hkp
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; omega) hr₁ (d90 prof.feat) (tgt := 161) rfl
    (by rw [mc2_length]; omega) ?_ ?_
  · -- `rdx = 0`: `ret`
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hc, hg] at htk
    have hdx : g₀.rdx = 0 := beq_iff_eq.1 htk
    refine ret_atC c hin (by rw [mc2_length]; omega) (d161 prof.feat) hK₂ hA₂ hr₂ (by rw [hg₂]; exact hkp₁)
      (by simp only [hg₂, hg₁, hg, hdx]; exact (BitVec.add_zero _).symm)
      (fun _ _ => rfl) (fun i hi => ?_) (fun _ _ => rfl) hR
    rw [hdx] at hi
    exact absurd hi (Nat.not_lt_zero _)
  -- `rdx ≠ 0`: `add rax, rdx`, `jmp 140`
  intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
  rw [hf₁, hc, hg] at hfa
  have hdx : g₀.rdx.toNat ≠ 0 := fun h => by
    rw [BitVec.eq_of_toNat_eq (y := 0#64) h] at hfa
    exact absurd hfa (by decide)
  obtain ⟨n, hn⟩ : ∃ n, g₀.rdx.toNat = n + 1 := ⟨g₀.rdx.toNat - 1, by omega⟩
  refine c.s_blkV hin (b92 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ _
  simp only [wr, gv, Src.val, set_rax, get0, get2, addR_eq, BitVec.setWidth_eq] at hg₃
  have hg₃' : Y₃.cpu.gpr = { g₀ with rax := g₀.rdi + g₀.rdx } := by simp only [hg₃, hg₂, hg₁, hg]
  refine c.s_jmpV hK₃ hA₃ hin (by rw [mc2_length]; omega) hr₃ (d95 prof.feat) (tgt := 140) rfl
    (by rw [mc2_length]; omega) ?_
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
  rw [hg₃'] at hg₄
  exact from140 c hin hK₄ hA₄ hr₄ (by rw [hg₄]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
    (by simp only [hg₄]) (by simp only [hg₄]) (by simp only [hg₄]) (by simp only [hg₄]) hn hsrc hst hs64 hd64
    hap hsp hdf₀ hsp8 hR

/-! ## The contracts -/

/-- A call of `__memmove_erms` (`memcpy`'s too) does what `Tls.CpyAt` says. -/
theorem cpyAt_erms {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr}
    {Pm : (Addr → Byte) → Prop} (hin : CodeIn L e mc2) : Tls.CpyAt prof L o (e.add 128) Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j c _ hK hA hrip _ hin₂ hj hra hl hsrc hst hs64 hd64 hap hsp hdf hsp8 K
  exact erms (g₀ := X.cpu.gpr) c hin hK hA hrip rfl hsrc hst hs64 hd64 hap hsp hdf hsp8
    ⟨hl, e', code, j, hin₂, hj, hra, K⟩

/-- A call of `__mempcpy_erms` does what `Gor.PcpyAt` says. -/
theorem pcpyAt_erms {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {e : Addr}
    {Pm : (Addr → Byte) → Prop} (hin : CodeIn L e mc2) : Gor.PcpyAt prof L o (e.add 80) Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j c _ hK hA hrip _ hin₂ hj hra hl hsrc hst hs64 hd64 hap hsp hdf hsp8 K
  exact perms (g₀ := X.cpu.gpr) c hin hK hA hrip rfl hsrc hst hs64 hd64 hap hsp hdf hsp8
    ⟨hl, e', code, j, hin₂, hj, hra, K⟩

end FV7z.Memcpy
