import FV7z.Memcpy.Entry
/-!
# `__memmove_sse2_unaligned_erms` and `__mempcpy_sse2_unaligned_erms`: the dispatch (PLAN.md M, the PLT contracts)

From `208`: `rax = rdi`; from `192`: `rax = rdi + rdx`, `jmp 215`. From `215`: below 16 bytes `p283`, up to 32 `p16`
at `227`, else from `353`: up to 2048 bytes on at `362` (`p362`), else from `244`. There, from the non-temporal
threshold on, on at `483` (`p483`); below it, with `rdi < rsi` a forward `rep movsb`, with `rdi = rsi` `ret`, with
`rdi` past `rsi` and inside the source the backward copy at `632` (`bwd632`), else the forward `rep movsb`. The forward
`rep movsb` copies as `memmove` does with the ranges apart (`hap`), as `Tls.CpyAt` and `Gor.PcpyAt` give.

- `b215`, `b221`, `b353`, `bE244`, `b257`, `b264`, `b277`, `b208`, `b192`, `b199`: the stretches; `thr251`.
- `rep280`: `rep movsb`, `ret`; `p277`, `p244`, `p353`, `p215`; `sse2eAt`, `psse2eAt`: the calls at `208` and `192`.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- `cmp rdx, 16`. -/
theorem b215 (prof : Profile) : BlkV prof mc2 215 219 [VOp.op (Op.cmp 64 2 (.i 16))] :=
  .cons (d215 _) (OpI.cmp (.i 16) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 32`. -/
theorem b221 (prof : Profile) : BlkV prof mc2 221 225 [VOp.op (Op.cmp 64 2 (.i 32))] :=
  .cons (d221 _) (OpI.cmp (.i 32) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 2048`. -/
theorem b353 (prof : Profile) : BlkV prof mc2 353 360 [VOp.op (Op.cmp 64 2 (.i 2048))] :=
  .cons (d353 _) (OpI.cmp (.i 2048) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `[rip + 1362525]` at `244` is the threshold read at `550`. -/
theorem thr251 (e : Addr) : Addr.add e 251 + BitVec.ofNat 64 1362525 = BitVec.ofNat 64 (thrA e) := by
  rw [thrA, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  show Addr.add (Addr.add e 251) 1362525 = Addr.add (Addr.add e 557) 1362219
  rw [addr_add_add, addr_add_add] <;> rfl

/-- `cmp rdx, [rip + 1362525]`, at `e + 244`. -/
theorem bE244 (prof : Profile) (e : Addr) : BlkA prof mc2 e 244 251 [Op.cmpma 64 2 (thrA e)] :=
  .cons (d244 prof.feat) (OpIA.cmpm_rip (.inr (.inr rfl)) (by rw [addr_add_add]; exact thr251 e))
    (by rw [mc2_length]; decide) (.nil _)

/-- `cmp rdi, rsi`. -/
theorem b257 (prof : Profile) : BlkV prof mc2 257 260 [VOp.op (Op.cmp 64 7 (.r 6))] :=
  .cons (d257 _) (OpI.cmp (.r 6) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `lea r9, [rsi + rdx]`, `cmp rdi, r9`. -/
theorem b264 (prof : Profile) :
    BlkV prof mc2 264 271 [VOp.op (Op.lea 64 9 (some 6) (some 2) 1 0), VOp.op (Op.cmp 64 7 (.r 9))] :=
  .cons (d264 _) (OpI.lea (b := some 6) (i := some 2) (sc := 1) (d := 0) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d268 _) (OpI.cmp (.r 9) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `mov rcx, rdx`. -/
theorem b277 (prof : Profile) : BlkV prof mc2 277 280 [VOp.op (Op.mov 64 1 (.r 2))] :=
  .cons (d277 _) (OpI.mov (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `endbr64`, `mov rax, rdi`. -/
theorem b208 (prof : Profile) : BlkV prof mc2 208 215 [VOp.op Op.nop, VOp.op (Op.mov 64 0 (.r 7))] :=
  .cons (d208 _) (OpI.endbr) (by rw [mc2_length]; decide) <|
  .cons (d212 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `endbr64`, `mov rax, rdi`. -/
theorem b192 (prof : Profile) : BlkV prof mc2 192 199 [VOp.op Op.nop, VOp.op (Op.mov 64 0 (.r 7))] :=
  .cons (d192 _) (OpI.endbr) (by rw [mc2_length]; decide) <|
  .cons (d196 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `add rax, rdx`. -/
theorem b199 (prof : Profile) : BlkV prof mc2 199 202 [VOp.op (Op.add 64 0 (.r 2))] :=
  .cons (d199 _) (OpI.add (.r 2) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `280`, `rcx = rdx = n + 1`, the ranges apart: the forward `rep movsb` and the `ret`. -/
theorem rep280 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {Y : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    {r : Addr} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 280)
    (hkp : KpS g₀ Y.cpu.gpr) (hax : Y.cpu.gpr.rax = r) (hdi : Y.cpu.gpr.rdi = g₀.rdi) (hsi : Y.cpu.gpr.rsi = g₀.rsi)
    (hcx : Y.cpu.gpr.rcx.toNat = n + 1) (hn : g₀.rdx.toNat = n + 1)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64) (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf₀ : s₀.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE Y t := by
  refine c.s_rep_movsb hdf₀ hin (j := 280) (by rw [mc2_length]; omega) (by rw [mc2_length]; omega)
    (d280 prof.feat) n hK hA hrip hcx (fun i hi => by rw [hsi]; exact hsrc i (by omega))
    (fun i hi => by rw [hdi]; exact hst i (by omega)) ?_
  rintro Y₁ t₁ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hdi, hsi] at hA₁
  have hkp₁ : KpS g₀ Y₁.cpu.gpr := by rw [hg₁]; exact hkp
  have hax₁ : Y₁.cpu.gpr.rax = r := by rw [hg₁]; exact hax
  refine ret_atC c hin (by rw [mc2_length]; omega) (d282 prof.feat) hK₁ hA₁ hr₁ hkp₁ hax₁ (fun i hi => ?_)
    (fun i hi => ?_) (fun a ha => ?_) hR
  · refine VcopyB_out _ _ _ _ _ fun k hk e' => ?_
    have h1 := congrArg BitVec.toNat e'
    rw [toNat_add_of_fits (n := 8) hi hsp8, toNat_add_of_fits (n := n + 1) hk (by omega)] at h1
    omega
  · exact VcopyB_in (n + 1) V g₀.rdi g₀.rsi (by omega) (by omega) (by omega) i (by omega)
  · refine VcopyB_out _ _ _ _ _ fun k hk e' => ha ?_
    rw [e', toNat_add_of_fits (n := n + 1) hk (by omega)]
    omega

/-- From `277`, `rdx ≠ 0`, the ranges apart: `mov rcx, rdx`, the forward `rep movsb`, `ret`. -/
theorem p277 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 277)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx) (h0 : 0 < g₀.rdx.toNat)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64) (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf₀ : s₀.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  refine c.s_blkV hin (b277 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, gv, Src.val, set_rcx, get2, BitVec.setWidth_eq] at hg₁
  obtain ⟨n, hn⟩ : ∃ n, g₀.rdx.toNat = n + 1 := ⟨g₀.rdx.toNat - 1, by omega⟩
  have hkp₁ : KpS g₀ Y₁.cpu.gpr := by
    have h := hkp
    unfold KpS at h ⊢
    rw [hg₁]
    exact h
  exact rep280 c hin hK₁ hA₁ hr₁ hkp₁ (by rw [hg₁]; exact hax) (by rw [hg₁]; exact hdi) (by rw [hg₁]; exact hsi)
    (by rw [hg₁, hdx]; exact hn) hn hsrc hst hs64 hd64 hap hsp hdf₀ hsp8 hR

/-- From `244`, more than 2048 bytes, the ranges apart: from the threshold on, on at `483`; else by `rdi` and
`rsi`, the forward `rep movsb` (`p277`), `ret`, or the backward copy (`bwd632`). -/
theorem p244 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 244)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx) (h2048 : 2048 < g₀.rdx.toNat)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf₀ : s₀.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  -- `cmp rdx, [rip + 1362525]`, `jae 483`
  refine c.s_blkA_v hin (bE244 prof e) X.cpu.vec hK hA hrip rfl rfl ?_
  dsimp only [wp, Op.cmpma]
  refine ⟨fun i hi => hthr i (by omega), fun fl _ => ?_⟩
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d251 prof.feat) (tgt := 483) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro _ Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, hg₁]
    exact p483 c hin hK₂ hA₂ hr₂ (by rw [e₂]; exact hkp) (by rw [e₂]; exact hax) (by rw [e₂]; exact hdi)
      (by rw [e₂]; exact hsi) (by rw [e₂]; exact hdx) (by omega) hsrc hst hd64 hs64 hsp hsp8 hthr hR
  intro _ Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
  have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, hg₁]
  -- `cmp rdi, rsi`, `jb 277`
  refine c.s_blkV hin (b257 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ _
  simp only [gv, Src.val, get6, get7, BitVec.setWidth_eq] at hP
  rw [e₂] at hP
  have e₃ : Y₃.cpu.gpr = X.cpu.gpr := by rw [hg₃, e₂]
  have hcf : fl.cf = decide (g₀.rdi.toNat < g₀.rsi.toNat) := by rw [hP, subF_cf, hdi, hsi]
  have hzf : fl.zf = decide (g₀.rdi = g₀.rsi) := by rw [hP, subF_zf, hdi, hsi]
  refine c.s_jccF hK₃ hA₃ hin (by rw [mc2_length]; decide) hr₃ (d260 prof.feat) (tgt := 277) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro _ Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
    have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
    exact p277 c hin hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax) (by rw [e₄]; exact hdi)
      (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) (by omega) hsrc hst hs64 hd64 hap hsp hdf₀ hsp8 hR
  intro hfa Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _, hf₄⟩
  rw [hf₃, cond_2, hcf] at hfa
  have hsd : g₀.rsi.toNat ≤ g₀.rdi.toNat := by
    have := of_decide_eq_false hfa
    omega
  have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
  -- `je 282`
  refine c.s_jccV hK₄ hA₄ hin (by rw [mc2_length]; decide) hr₄ (d262 prof.feat) (tgt := 282) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, _⟩
    rw [hf₄, rfz_cond, hf₃, cond_4, hzf] at htk
    have heq := of_decide_eq_true htk
    have e₅ : Y₅.cpu.gpr = X.cpu.gpr := by rw [hg₅, e₄]
    exact ret_atC c hin (by rw [mc2_length]; decide) (d282 prof.feat) hK₅ hA₅ hr₅ (by rw [e₅]; exact hkp)
      (by rw [e₅]; exact hax) (fun _ _ => rfl) (fun i _ => by rw [heq]) (fun _ _ => rfl) hR
  intro _ Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, _⟩
  have e₅ : Y₅.cpu.gpr = X.cpu.gpr := by rw [hg₅, e₄]
  -- `lea r9, [rsi + rdx]`, `cmp rdi, r9`, `jb 632`
  refine c.s_blkV hin (b264 prof) hK₅ hA₅ hr₅ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ _ _
  simp only [wr, set_r9b] at hg₆
  rw [e₅] at hg₆
  have hkp₆ : KpS g₀ Y₆.cpu.gpr := by
    have h := hkp
    unfold KpS at h ⊢
    rw [hg₆]
    exact h
  have hax₆ : Y₆.cpu.gpr.rax = r := by rw [hg₆]; exact hax
  have hdi₆ : Y₆.cpu.gpr.rdi = g₀.rdi := by rw [hg₆]; exact hdi
  have hsi₆ : Y₆.cpu.gpr.rsi = g₀.rsi := by rw [hg₆]; exact hsi
  have hdx₆ : Y₆.cpu.gpr.rdx = g₀.rdx := by rw [hg₆]; exact hdx
  refine c.s_jccV hK₆ hA₆ hin (by rw [mc2_length]; decide) hr₆ (d271 prof.feat) (tgt := 632) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro _ Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, _⟩
    exact bwd632 c hin hK₇ hA₇ hr₇ (by rw [hg₇]; exact hkp₆) (by rw [hg₇]; exact hax₆) (by rw [hg₇]; exact hdi₆)
      (by rw [hg₇]; exact hsi₆) (by rw [hg₇]; exact hdx₆) (by omega) hsd hsrc hst hd64 hs64 hsp hsp8 hthr hR
  intro _ Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇, _⟩
  exact p277 c hin hK₇ hA₇ hr₇ (by rw [hg₇]; exact hkp₆) (by rw [hg₇]; exact hax₆) (by rw [hg₇]; exact hdi₆)
    (by rw [hg₇]; exact hsi₆) (by rw [hg₇]; exact hdx₆) (by omega) hsrc hst hs64 hd64 hap hsp hdf₀ hsp8 hR

/-- From `353`, more than 32 bytes, the ranges apart: up to 2048 on at `362`, else at `244`. -/
theorem p353 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 353)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx) (h32 : 32 < g₀.rdx.toNat)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf₀ : s₀.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  -- `cmp rdx, 2048`, `ja 244`
  refine c.s_blkV hin (b353 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  have e₁ : Y₁.cpu.gpr = X.cpu.gpr := hg₁
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d360 prof.feat) (tgt := 244) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
    rw [hf₁, hP, cond_7, subF_cf, subF_zf] at htk
    have h := ja_t htk
    simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
    exact p244 c hin hK₂ hA₂ hr₂ (by rw [e₂]; exact hkp) (by rw [e₂]; exact hax) (by rw [e₂]; exact hdi)
      (by rw [e₂]; exact hsi) (by rw [e₂]; exact hdx) h hsrc hst hd64 hs64 hap hsp hdf₀ hsp8 hthr hR
  intro _ Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, _⟩
  have e₂ : Y₂.cpu.gpr = X.cpu.gpr := by rw [hg₂, e₁]
  exact p362 c hin hK₂ hA₂ hr₂ (by rw [e₂]; exact hkp) (by rw [e₂]; exact hax) (by rw [e₂]; exact hdi)
    (by rw [e₂]; exact hsi) (by rw [e₂]; exact hdx) h32 hsrc hst hd64 hs64 hsp hsp8 hthr hR

/-- From `215`, the ranges apart: by `rdx`, `p283`, on at `353`, or `p16` at `227`. -/
theorem p215 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 215)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf₀ : s₀.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  -- `cmp rdx, 16`, `jb 283`
  refine c.s_blkV hin (b215 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ _
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  have e₁ : Y₁.cpu.gpr = X.cpu.gpr := hg₁
  refine c.s_jccV hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d219 prof.feat) (tgt := 283) rfl
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
  -- `cmp rdx, 32`, `ja 353`
  refine c.s_blkV hin (b221 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ _
  simp only [gv, Src.val, get2, BitVec.setWidth_eq] at hP
  rw [e₂] at hP
  have e₃ : Y₃.cpu.gpr = X.cpu.gpr := by rw [hg₃, e₂]
  refine c.s_jccV hK₃ hA₃ hin (by rw [mc2_length]; decide) hr₃ (d225 prof.feat) (tgt := 353) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
    rw [hf₃, hP, cond_7, subF_cf, subF_zf] at htk
    have h := ja_t htk
    simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
    have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
    exact p353 c hin hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax) (by rw [e₄]; exact hdi)
      (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) h hsrc hst hd64 hs64 hap hsp hdf₀ hsp8 hthr hR
  intro hfa Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, _⟩
  rw [hf₃, hP, cond_7, subF_cf, subF_zf] at hfa
  have h := ja_f hfa
  simp only [hdx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  have e₄ : Y₄.cpu.gpr = X.cpu.gpr := by rw [hg₄, e₃]
  exact p16 c hin (c16_227 prof.feat) hK₄ hA₄ hr₄ (by rw [e₄]; exact hkp) (by rw [e₄]; exact hax)
    (by rw [e₄]; exact hdi) (by rw [e₄]; exact hsi) (by rw [e₄]; exact hdx) (by omega) h hsrc hst hd64 hsp hsp8 hR

/-- `__memmove_sse2_unaligned_erms` from `+208`, called with registers `g₀`. -/
theorem sse2eAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 208) (hg : X.cpu.gpr = g₀)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf : X.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ g₀.rdi) : GoG prof L o gev gP gE X t := by
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  -- `endbr64`, `mov rax, rdi`
  refine c.s_blkV hin (b208 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, gv, Src.val, set_rax, get7, BitVec.setWidth_eq] at hg₁
  have hg₁' : Y₁.cpu.gpr = { g₀ with rax := g₀.rdi } := by simp only [hg₁, hg]
  exact p215 c hin hK₁ hA₁ hr₁ (by rw [hg₁']; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp only [hg₁'])
    (by simp only [hg₁']) (by simp only [hg₁']) (by simp only [hg₁']) hsrc hst hd64 hs64 hap hsp hdf₀ hsp8 hthr hR

/-- `__mempcpy_sse2_unaligned_erms` from `+192`, called with registers `g₀`. -/
theorem psse2eAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 192) (hg : X.cpu.gpr = g₀)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hap : g₀.rsi.toNat + g₀.rdx.toNat ≤ g₀.rdi.toNat ∨ g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hdf : X.cpu.rflags.df = false) (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ (g₀.rdi + g₀.rdx)) : GoG prof L o gev gP gE X t := by
  have hdf₀ : s₀.cpu.rflags.df = false := hK.df.symm.trans hdf
  -- `endbr64`, `mov rax, rdi`
  refine c.s_blkV hin (b192 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ _
  simp only [wr, gv, Src.val, set_rax, get7, BitVec.setWidth_eq] at hg₁
  -- `add rax, rdx`
  refine c.s_blkV hin (b199 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ _
  simp only [wr, gv, Src.val, set_rax, get0, get2, addR_eq, BitVec.setWidth_eq] at hg₂
  have hg₂' : Y₂.cpu.gpr = { g₀ with rax := g₀.rdi + g₀.rdx } := by simp only [hg₂, hg₁, hg]
  -- `jmp 215`
  refine c.s_jmpV hK₂ hA₂ hin (by rw [mc2_length]; decide) hr₂ (d202 prof.feat) (tgt := 215) rfl
    (by rw [mc2_length]; decide) ?_
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
  rw [hg₂'] at hg₃
  exact p215 c hin hK₃ hA₃ hr₃ (by rw [hg₃]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) (by simp only [hg₃])
    (by simp only [hg₃]) (by simp only [hg₃]) (by simp only [hg₃]) hsrc hst hd64 hs64 hap hsp hdf₀ hsp8 hthr hR

end FV7z.Memcpy
