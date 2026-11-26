import FV7z.Memcpy.BwdN
import FV7z.Memcpy.Sse2b
import FV7z.Memcpy.Sse2c
/-!
# `__memmove_sse2_unaligned` and `__mempcpy_sse2_unaligned`: the dispatch (PLAN.md M, the PLT contracts)

From `16` (`__memmove_sse2_unaligned`): `rax = rdi`; from `0` (`__mempcpy_sse2_unaligned`): `rax = rdi + rdx`,
`jmp 23`. From `23`: below 16 bytes `p283`, up to 32 `p16` at `43`, else from `362`: above 128 bytes on at `483`,
below 64 `p448`, else `p377`. From `483`: with `rsi < rdi` the backward copy (`bwd632`), with `rdi = rsi` `ret`,
else the forward one (`fwd498`). Above 128 bytes the copy reads the threshold of its non-temporal loops (`hthr`).

- `b483`, `p483`; `b362`, `b371`, `p362`; `b23`, `b33`, `p23`; `b16`, `b0`, `b7`: the stretches and the runs.
- `sse2At`, `psse2At`: the calls at `16` and at `0`, with registers `g₀`.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- `cmp rdi, rsi`. -/
theorem b483 (prof : Profile) : BlkV prof mc2 483 486 [VOp.op (Op.cmp 64 7 (.r 6))] :=
  .cons (d483 _) (OpI.cmp (.r 6) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 128`. -/
theorem b362 (prof : Profile) : BlkV prof mc2 362 369 [VOp.op (Op.cmp 64 2 (.i 128))] :=
  .cons (d362 _) (OpI.cmp (.i 128) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 64`. -/
theorem b371 (prof : Profile) : BlkV prof mc2 371 375 [VOp.op (Op.cmp 64 2 (.i 64))] :=
  .cons (d371 _) (OpI.cmp (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 16`. -/
theorem b23 (prof : Profile) : BlkV prof mc2 23 27 [VOp.op (Op.cmp 64 2 (.i 16))] :=
  .cons (d23 _) (OpI.cmp (.i 16) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 32`. -/
theorem b33 (prof : Profile) : BlkV prof mc2 33 37 [VOp.op (Op.cmp 64 2 (.i 32))] :=
  .cons (d33 _) (OpI.cmp (.i 32) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `endbr64`, `mov rax, rdi`. -/
theorem b16 (prof : Profile) : BlkV prof mc2 16 23 [VOp.op Op.nop, VOp.op (Op.mov 64 0 (.r 7))] :=
  .cons (d16 _) (OpI.endbr) (by rw [mc2_length]; decide) <|
  .cons (d20 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `endbr64`, `mov rax, rdi`. -/
theorem b0 (prof : Profile) : BlkV prof mc2 0 7 [VOp.op Op.nop, VOp.op (Op.mov 64 0 (.r 7))] :=
  .cons (d0 _) (OpI.endbr) (by rw [mc2_length]; decide) <|
  .cons (d4 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `add rax, rdx`. -/
theorem b7 (prof : Profile) : BlkV prof mc2 7 10 [VOp.op (Op.add 64 0 (.r 2))] :=
  .cons (d7 _) (OpI.add (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `483`, more than 128 bytes: by `rdi` and `rsi`, the backward copy, `ret`, or the forward copy. -/
theorem p483 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 483)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx) (h128 : 128 < g₀.rdx.toNat)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  -- `cmp rdi, rsi`, `ja 632`
  refine c.s_blkV hin (b483 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [gv, Src.val, get6, get7, BitVec.setWidth_eq] at hP
  have e₁ : Y₁.cpu.gpr = X.cpu.gpr := hg₁
  have hcf : fl.cf = decide (g₀.rdi.toNat < g₀.rsi.toNat) := by rw [hP, subF_cf, hdi, hsi]
  have hzf : fl.zf = decide (g₀.rdi = g₀.rsi) := by rw [hP, subF_zf, hdi, hsi]
  refine c.s_jccF hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d486 prof.feat) (tgt := 632) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, cond_7, hcf, hzf] at htk
    have hsd := ja_t htk
    have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
    exact bwd632 c hin hK₂ hA₂ hr₂ (by rw [e₂]; exact hkp) (by rw [e₂]; exact hax) (by rw [e₂]; exact hdi)
      (by rw [e₂]; exact hsi) (by rw [e₂]; exact hdx) h128 (Nat.le_of_lt hsd) hsrc hst hd64 hs64 hsp hsp8 hthr hR
  intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _, hf₂⟩
  rw [hf₁, cond_7, hcf, hzf] at hfa
  have hds := ja_f hfa
  have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
  -- `je 282`
  refine c.s_jccV hK₂ hA₂ hin (by rw [mc2_length]; decide) hr₂ (d492 prof.feat) (tgt := 282) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
    rw [hf₂, rfz_cond, hf₁, cond_4, hzf] at htk
    have heq := of_decide_eq_true htk
    have e₃ : Y₃.cpu.gpr = X.cpu.gpr := by rw [hg₃, e₂]
    exact ret_atC c hin (by rw [mc2_length]; decide) (d282 prof.feat) hK₃ hA₃ hr₃ (by rw [e₃]; exact hkp)
      (by rw [e₃]; exact hax) (fun _ _ => rfl) (fun i _ => by rw [heq]) (fun _ _ => rfl) hR
  intro _ Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
  have e₃ : Y₃.cpu.gpr = X.cpu.gpr := by rw [hg₃, e₂]
  exact fwd498 c hin hK₃ hA₃ hr₃ (by rw [e₃]; exact hkp) (by rw [e₃]; exact hax) (by rw [e₃]; exact hdi)
    (by rw [e₃]; exact hsi) (by rw [e₃]; exact hdx) h128 hds hsrc hst hd64 hs64 hsp hsp8 hthr hR

/-- From `362`, more than 32 bytes: by `rdx`, on at `483`, `p448` or `p377`. -/
theorem p362 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 362)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx) (h32 : 32 < g₀.rdx.toNat)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  -- `cmp rdx, 128`, `ja 483`
  refine c.s_blkV hin (b362 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  have e₁ : Y₁.cpu.gpr = X.cpu.gpr := hg₁
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d369 prof.feat) (tgt := 483) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hP, cond_7, subF_cf, subF_zf] at htk
    have h := ja_t htk
    simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
    exact p483 c hin hK₂ hA₂ hr₂ (by rw [e₂]; exact hkp) (by rw [e₂]; exact hax) (by rw [e₂]; exact hdi)
      (by rw [e₂]; exact hsi) (by rw [e₂]; exact hdx) h hsrc hst hd64 hs64 hsp hsp8 hthr hR
  intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
  rw [hf₁, hP, cond_7, subF_cf, subF_zf] at hfa
  have h128 := ja_f hfa
  simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h128
  have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
  -- `cmp rdx, 64`, `jb 448`
  refine c.s_blkV hin (b371 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ _
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  rw [e₂] at hP
  have e₃ : Y₃.cpu.gpr = X.cpu.gpr := by rw [hg₃, e₂]
  refine c.s_jccV hK₃ hA₃ hin (by rw [mc2_length]; decide) hr₃ (d375 prof.feat) (tgt := 448) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
    rw [hf₃, hP, cond_2, subF_cf] at htk
    have h := of_decide_eq_true htk
    simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
    exact p448 c hin hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax) (by rw [e₄]; exact hdi)
      (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) (by omega) (by omega) hsrc hst hd64 hsp hsp8 hR
  intro hfa Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
  rw [hf₃, hP, cond_2, subF_cf] at hfa
  have h := of_decide_eq_false hfa
  simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
  exact p377 c hin hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax) (by rw [e₄]; exact hdi)
    (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) (by omega) h128 hsrc hst hd64 hsp hsp8 hR

/-- From `23`: by `rdx`, `p283`, on at `362`, or `p16` at `43`. -/
theorem p23 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 23)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  -- `cmp rdx, 16`, `jb 283`
  refine c.s_blkV hin (b23 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  have e₁ : Y₁.cpu.gpr = X.cpu.gpr := hg₁
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d27 prof.feat) (tgt := 283) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hP, cond_2, subF_cf] at htk
    have h := of_decide_eq_true htk
    simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
    exact p283 c hin hK₂ hA₂ hr₂ (by rw [e₂]; exact hkp) (by rw [e₂]; exact hax) (by rw [e₂]; exact hdi)
      (by rw [e₂]; exact hsi) (by rw [e₂]; exact hdx) h hsrc hst hd64 hsp hsp8 hR
  intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
  rw [hf₁, hP, cond_2, subF_cf] at hfa
  have h16 := of_decide_eq_false hfa
  simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h16
  have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
  -- `cmp rdx, 32`, `ja 362`
  refine c.s_blkV hin (b33 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ _
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  rw [e₂] at hP
  have e₃ : Y₃.cpu.gpr = X.cpu.gpr := by rw [hg₃, e₂]
  refine c.s_jccV hK₃ hA₃ hin (by rw [mc2_length]; decide) hr₃ (d37 prof.feat) (tgt := 362) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
    rw [hf₃, hP, cond_7, subF_cf, subF_zf] at htk
    have h := ja_t htk
    simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
    exact p362 c hin hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax) (by rw [e₄]; exact hdi)
      (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) h hsrc hst hd64 hs64 hsp hsp8 hthr hR
  intro hfa Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
  rw [hf₃, hP, cond_7, subF_cf, subF_zf] at hfa
  have h := ja_f hfa
  simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
  exact p16 c hin (c16_43 prof.feat) hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax)
    (by rw [e₄]; exact hdi) (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) (by omega) h hsrc hst hd64 hsp hsp8 hR

/-- `__memmove_sse2_unaligned` from `+16`, called with registers `g₀`. -/
theorem sse2At (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 16) (hg : X.cpu.gpr = g₀)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ g₀.rdi) : GoG prof L o gev gP gE X t := by
  -- `endbr64`, `mov rax, rdi`
  refine c.s_blkV hin (b16 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, gv, Src.val, set_rax, get7, BitVec.setWidth_eq] at hg₁
  have hg₁' : Y₁.cpu.gpr = { g₀ with rax := g₀.rdi } := by simp only [hg₁, hg]
  exact p23 c hin hK₁ hA₁ hr₁ (by rw [hg₁']; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp only [hg₁'])
    (by simp only [hg₁']) (by simp only [hg₁']) (by simp only [hg₁']) hsrc hst hd64 hs64 hsp hsp8 hthr hR

/-- `__mempcpy_sse2_unaligned` from `+0`, called with registers `g₀`. -/
theorem psse2At (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 0) (hg : X.cpu.gpr = g₀)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ (g₀.rdi + g₀.rdx)) : GoG prof L o gev gP gE X t := by
  -- `endbr64`, `mov rax, rdi`
  refine c.s_blkV hin (b0 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, gv, Src.val, set_rax, get7, BitVec.setWidth_eq] at hg₁
  -- `add rax, rdx`
  refine c.s_blkV hin (b7 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ _
  simp only [wr, gv, Src.val, set_rax, get0, get2, addR_eq, BitVec.setWidth_eq] at hg₂
  have hg₂' : Y₂.cpu.gpr = { g₀ with rax := g₀.rdi + g₀.rdx } := by simp only [hg₂, hg₁, hg]
  -- `jmp 23`
  refine c.s_jmpV hK₂ hA₂ hin (by rw [mc2_length]; decide) hr₂ (d10 prof.feat) (tgt := 23) rfl
    (by rw [mc2_length]; decide) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
  rw [hg₂'] at hg₃
  exact p23 c hin hK₃ hA₃ hr₃ (by rw [hg₃]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp only [hg₃])
    (by simp only [hg₃]) (by simp only [hg₃]) (by simp only [hg₃]) hsrc hst hd64 hs64 hsp hsp8 hthr hR

end FV7z.Memcpy
