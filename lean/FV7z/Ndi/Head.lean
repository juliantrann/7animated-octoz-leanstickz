import FV7z.Ndi.Env
import FV7z.Ndi.Vc1
import FV7z.Ndi.Vc2
/-!
# `_dl_non_dynamic_init`: from its entry to `_dl_init_paths` (PLAN.md G3, startup)

- `ndi_a`: the prologue and the `call` of `_dl_get_origin` (`0x6aefa0`). `sp` is the stack pointer of the body, 120
  under the one at entry; the five registers pushed are at `sp + 80` to `sp + 120` (`fV`).
- `ndi_b`: from the return of `_dl_get_origin` (21) to the first instruction of `_dl_init_paths` (`0x6a88f0`), when
  the kernel gave no vDSO, the exec is not secure and the environment has neither `LD_WARN` nor `LD_LIBRARY_PATH`:
  the main map's `l_origin`, `l_phdr`, `l_phnum`, the vDSO pointers and `_dl_verbose` are set (`hV`), the argument of
  `_dl_init_paths` is null.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

/-- The bytes after the five `push`es, by the stack pointer `sp` of the body. -/
def fV (V : Addr → Byte) (sp : Addr) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (sp + 112#64) (toBytesLE g.r14 8)) (sp + 104#64) (toBytesLE g.r13 8))
    (sp + 96#64) (toBytesLE g.r12 8)) (sp + 88#64) (toBytesLE g.rbp 8)) (sp + 80#64) (toBytesLE g.rbx 8)

theorem q8 (sp : BitVec 64) : sp + 120#64 - 8 = sp + 112#64 := by bv_omega
theorem q16 (sp : BitVec 64) : sp + 120#64 - 16#64 = sp + 104#64 := by bv_omega
theorem q24 (sp : BitVec 64) : sp + 120#64 - 24#64 = sp + 96#64 := by bv_omega
theorem q32 (sp : BitVec 64) : sp + 120#64 - 32#64 = sp + 88#64 := by bv_omega
theorem q40 (sp : BitVec 64) : sp + 120#64 - 40#64 = sp + 80#64 := by bv_omega
theorem q120 (sp : BitVec 64) : sp + 120#64 - 120#64 = sp := by bv_omega
theorem qn (sp : BitVec 64) (k : Nat) (h : sp.toNat + k < 2 ^ 64) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
  bv_omega

theorem frV_eq {V : Addr → Byte} {sp : Addr} {g : Gprs} (h : g.rsp = sp + 120#64) : frV V g = fV V sp g := by
  unfold frV fV
  rw [h, q8, q16, q24, q32, q40]

/-- The five registers the prologue pushed, read back. -/
theorem fV_rd (V : Addr → Byte) (sp : Addr) (g : Gprs) (hsn : sp.toNat + 128 ≤ 2 ^ 64) :
    rdq(fV V sp g, sp + 80#64) = g.rbx ∧ rdq(fV V sp g, sp + 88#64) = g.rbp ∧
    rdq(fV V sp g, sp + 96#64) = g.r12 ∧ rdq(fV V sp g, sp + 104#64) = g.r13 ∧
    rdq(fV V sp g, sp + 112#64) = g.r14 := by
  have e0 := qn sp 80 (by omega)
  have e1 := qn sp 88 (by omega)
  have e2 := qn sp 96 (by omega)
  have e3 := qn sp 104 (by omega)
  have e4 := qn sp 112 (by omega)
  have l := fun (w : BitVec 64) => toBytesLE_length w 8
  have b := fun (w : BitVec 64) => ofBytesLE_toBytesLE (w := 64) (n := 8) rfl w
  unfold fV
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [vs (l _) (by omega)]
    exact b _
  · rw [vr (l _) (by omega) (by omega) (by omega), vs (l _) (by omega)]
    exact b _
  · rw [vr (l _) (by omega) (by omega) (by omega), vr (l _) (by omega) (by omega) (by omega), vs (l _) (by omega)]
    exact b _
  · rw [vr (l _) (by omega) (by omega) (by omega), vr (l _) (by omega) (by omega) (by omega),
      vr (l _) (by omega) (by omega) (by omega), vs (l _) (by omega)]
    exact b _
  · rw [vr (l _) (by omega) (by omega) (by omega), vr (l _) (by omega) (by omega) (by omega),
      vr (l _) (by omega) (by omega) (by omega), vr (l _) (by omega) (by omega) (by omega), vs (l _) (by omega)]
    exact b _

/-- The bytes at the `call` of `_dl_init_paths`: `aV`, and `_dl_verbose` (`0x7a855c`) 0. -/
def hV (V : Addr → Byte) (org ph pn : BitVec 64) : Addr → Byte :=
  Vst (aV V org ph pn) 8029532#64 (toBytesLE 0#32 4)

theorem aV_gk (V : Addr → Byte) (org ph pn : BitVec 64) : Gk V (aV V org ph pn) :=
  ((((((((Gk.refl V).st (toBytesLE_length _ 8) (by decide)).st (toBytesLE_length _ 8) (by decide)).st
    (toBytesLE_length _ 2) (by decide)).st (toBytesLE_length _ 8) (by decide)).st (toBytesLE_length _ 8)
    (by decide)).st (toBytesLE_length _ 8) (by decide)).st (toBytesLE_length _ 8) (by decide)).st
    (toBytesLE_length _ 8) (by decide)

theorem hV_gk (V : Addr → Byte) (org ph pn : BitVec 64) : Gk V (hV V org ph pn) :=
  (aV_gk V org ph pn).st (toBytesLE_length _ 4) (by decide)

theorem aV_eqo {sp : Addr} {W V : Addr → Byte} (h : Eqo sp W V) (org ph pn : BitVec 64) :
    Eqo sp (aV W org ph pn) (aV V org ph pn) :=
  (((((((h.st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _).st _ _

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

theorem ndi_a {go : List Byte} {W : Addr → Byte} {sp : Addr} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L ndi_at ndi) (hio : CodeIn L 7008160#64 go) (ho0 : 0 < go.length) (hsn : sp.toNat + 128 ≤ 2 ^ 64)
    (hw8 : ∀ i < 8, Foot Wl (Addr.add (sp - 8#64) i)) (hpw : ∀ i < 40, Foot Wl (Addr.add (sp + 80#64) i))
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hrip : X.cpu.rip = ndi_at.add 0)
    (hsp : X.cpu.gpr.rsp = sp + 120#64)
    (k : ∀ Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst (fV W sp X.cpu.gpr) (sp - 8#64) (toBytesLE (ndi_at.add 21) 8)) →
      Z.cpu.rip = 7008160#64 → Z.cpu.gpr = { X.cpu.gpr with rsp := sp - 8#64 } → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have e := qn sp 120 (by omega)
  refine (c_0 prof).run c hin _ hK hA hrip (vc_0 (by rw [hsp, q40]; exact hpw) (by rw [hsp, e]; omega)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hsp, q120] at hg₁
  rw [frV_eq hsp] at hA₁
  have hsp₁ : Y₁.cpu.gpr.rsp = sp := by rw [hg₁]
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_16 _) hio ho0 (by decide)
    (fun i hi => by rw [hsp₁]; exact hw8 i hi) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hsp₁] at hAZ hgZ
  refine k Z t' hKZ hAZ hrZ ?_
  rw [hgZ, hg₁]
  rfl

theorem ndi_b {pl pc ip : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V W : Addr → Byte} {sp : Addr}
    {ph pn : BitVec 64} (c : Seg prof F Wl L s₀ o) (cx : Cx prof F Wl L o pl pc Pm E V sp)
    (hip : CodeIn L 6981872#64 ip) (hp0 : 0 < ip.length)
    (h1 : rdq(V, 8029448#64) = 0#64) (h2 : rdq(V, 8029568#64) = ph) (h3 : rdq(V, 8029592#64) = pn)
    (h4 : rdq(V, 8029424#64) = 0#64) (h5 : rdd(V, 7937248#64) = 0#32)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hM : Eqo sp W V)
    (hrip : X.cpu.rip = ndi_at.add 21) (hsp : X.cpu.gpr.rsp = sp)
    (k : ∀ Z t' W', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Vst W' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8)) →
      Eqo sp W' (hV V X.cpu.gpr.rax ph pn) → Z.cpu.rip = 6981872#64 → Z.cpu.gpr.rsp = sp - 8#64 →
      Z.cpu.gpr.rdi = 0#64 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have h72 := cx.h72
  -- the main map's fields, the vDSO pointers, `getenv ("LD_WARN")`
  refine (c_21 prof).run c cx.hin _ hK hA hrip (vc_21 (ph := ph) (pn := pn) cx.hr cx.hw
    (by rw [hM.rdi h72 _ 8 (by decide)]; exact h1) (by rw [hM.rdi h72 _ 8 (by decide)]; exact h2)
    (by rw [hM.rdi h72 _ 8 (by decide)]; exact h3) (by rw [hM.rdi h72 _ 8 (by decide)]; exact h4)
    (by rw [hM.rdi h72 _ 4 (by decide)]; exact h5)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have M₁ := aV_eqo hM X.cpu.gpr.rax ph pn
  have G₁ := aV_gk V X.cpu.gpr.rax ph pn
  refine gs c cx (by decide) (call_2018 _) (by decide) hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]) cx.n1
    M₁ G₁ ?_
  intro Z₁ u₁ W₁ hKZ₁ hAZ₁ hMZ₁ hrZ₁ hax₁ hspZ₁ h15Z₁
  have e15₁ : Z₁.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15Z₁, hg₁]
  clear hg₁ h15Z₁ hA₁ hK₁ hr₁ M₁
  -- `_dl_verbose`, `getenv ("LD_LIBRARY_PATH")`
  refine (c_2023 prof).run c cx.hin _ hKZ₁ hAZ₁ hrZ₁ (vc_2023 cx.hw hax₁) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have M₂ : Eqo sp (Vst W₁ 8029532#64 (toBytesLE 0#32 4)) (hV V X.cpu.gpr.rax ph pn) :=
    hMZ₁.st 8029532#64 (toBytesLE 0#32 4)
  refine gs c cx (by decide) (call_2050 _) (by decide) hK₂ hA₂ hr₂ (by rw [hg₂]; exact hspZ₁) (by rw [hg₂]) cx.n2
    M₂ (hV_gk V X.cpu.gpr.rax ph pn) ?_
  intro Z₂ u₂ W₂ hKZ₂ hAZ₂ hMZ₂ hrZ₂ hax₂ hspZ₂ h15Z₂
  have e15₂ : Z₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15Z₂, hg₂]; exact e15₁
  clear hg₂ h15Z₂ hA₂ hK₂ hr₂ M₂ hMZ₁ hAZ₁ hKZ₁ hrZ₁ hax₁ hspZ₁ e15₁ G₁
  -- the argument, the `call` of `_dl_init_paths`
  refine (c_2055 prof).run c cx.hin _ hKZ₂ hAZ₂ hrZ₂ vc_2055 ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have hsp₃ : Y₃.cpu.gpr.rsp = sp := by rw [hg₃]; exact hspZ₂
  refine c.s_call hK₃ hA₃ cx.hin (lt_len (by decide)) hr₃ (call_2058 _) hip hp0 (by decide)
    (fun i hi => by rw [hsp₃]; exact w8 cx.hstk i hi) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hsp₃] at hAZ hgZ
  refine k Z t' _ hKZ hAZ hMZ₂ hrZ (by rw [hgZ]; rfl) ?_ ?_
  · rw [hgZ]
    show Y₃.cpu.gpr.rdi = _
    rw [hg₃]
    exact hax₂
  · rw [hgZ]
    show Y₃.cpu.gpr.r15 = _
    rw [hg₃]
    exact e15₂
end FV7z.Ndi
