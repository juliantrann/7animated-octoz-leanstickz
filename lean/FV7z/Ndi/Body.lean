import FV7z.Ndi.Env
import FV7z.Ndi.Vc2
import FV7z.Ndi.Vc3
/-!
# `_dl_non_dynamic_init`: from `_dl_init_paths` to the program headers (PLAN.md G3, startup)

`body_a`: from the return of `_dl_init_paths` (2063) to the loop over the program headers (2575), with no `LD_*`
in the environment and not a secure exec — `_dl_init_all_dirs`, then five `getenv`s (`LD_BIND_NOW`, `LD_BIND_NOT`,
`LD_DYNAMIC_WEAK`, `LD_PROFILE_OUTPUT`, `LD_ASSUME_KERNEL`) that return null and the variables set from them, then
`strlen (_dl_platform)`. The bytes there are `bV` outside the 72 below `sp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

/-- The platform string (`AT_PLATFORM`): `_dl_platform` (`0x7a8548`) is `p`, above `sp`, `n ≥ 1` characters and a 0,
its pages read. -/
structure Pl (V : Addr → Byte) (F : Footprint) (sp p : Addr) (n : Nat) : Prop where
  hp : rdq(V, 8029512#64) = p
  hi : sp.toNat ≤ p.toNat
  fit : p.toNat + n < 2 ^ 64
  n1 : 1 ≤ n
  nnz : ∀ k < n, V (Addr.add p k) ≠ 0
  nz : V (Addr.add p n) = 0
  pg : ∀ x : Addr, p.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (p.toNat + n) / 4096 → Foot F.data x

/-- The bytes at the loop over the program headers: `_dl_init_all_dirs` (`0x7a85b0`) is `_dl_all_dirs`, `_dl_lazy`
(`0x7a8590`) 1, `_dl_bind_not` (`0x7a85a8`) 0, `_dl_dynamic_weak` (`0x7a8560`) 1, `_dl_profile_output` (`0x7a85a0`)
`"/var/tmp"` (`0x6f36dc`), `_dl_platformlen` (`0x7a8550`) `n`. -/
def bV (V : Addr → Byte) (n : Nat) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst (Vst V 8029616#64 (toBytesLE rdq(V, 8029552#64) 8)) 8029584#64 (toBytesLE 1#32 4))
    8029608#64 (toBytesLE 0#32 4)) 8029536#64 (toBytesLE 1#32 4)) 8029600#64 (toBytesLE 0#64 8))
    8029600#64 (toBytesLE 7288540#64 8)) 8029520#64 (toBytesLE (BitVec.ofNat 64 n) 8)

theorem bV_gk (V : Addr → Byte) (n : Nat) : Gk V (bV V n) :=
  (((((((Gk.refl V).st (toBytesLE_length _ 8) (by decide)).st (toBytesLE_length _ 4) (by decide)).st
    (toBytesLE_length _ 4) (by decide)).st (toBytesLE_length _ 4) (by decide)).st (toBytesLE_length _ 8)
    (by decide)).st (toBytesLE_length _ 8) (by decide)).st (toBytesLE_length _ 8) (by decide)

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

theorem body_a {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V W : Addr → Byte} {sp p : Addr}
    {n : Nat} (c : Seg prof F Wl L s₀ o) (cx : Cx prof F Wl L o pl pc Pm E V sp) (hpl : Pl V F sp p n)
    (hsec : rdd(V, 7937248#64) = 0#32) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hM : Eqo sp W V)
    (hrip : X.cpu.rip = ndi_at.add 2063) (hsp : X.cpu.gpr.rsp = sp)
    (k : ∀ Z t' W', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' → Eqo sp W' (bV V n) →
      Z.cpu.rip = ndi_at.add 2575 → Z.cpu.gpr.rsp = sp → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have h72 := cx.h72
  have hlt := sp.isLt
  -- `_dl_init_all_dirs`, `getenv ("LD_BIND_NOW")`
  refine (c_2063 prof).run c cx.hin _ hK hA hrip (vc_2063 cx.hr cx.hw) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  rw [hM.rdi h72 _ 8 (by decide)] at hA₁ hg₁
  have M₁ := hM.st 8029616#64 (toBytesLE rdq(V, 8029552#64) 8)
  have G₁ := (Gk.refl V).st (x := 8029616#64) (toBytesLE_length rdq(V, 8029552#64) 8) (by decide)
  refine gs c cx (by decide) (call_2084 _) (by decide) hK₁ hA₁ hr₁ (by rw [hg₁]; exact hsp) (by rw [hg₁]) cx.n3
    M₁ G₁ ?_
  intro Z₁ u₁ W₁ hKZ₁ hAZ₁ hMZ₁ hrZ₁ hax₁ hspZ₁ h15Z₁
  have e15₁ : Z₁.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15Z₁, hg₁]
  clear hg₁ h15Z₁ hA₁ hK₁ hr₁ M₁
  -- `_dl_lazy`, `getenv ("LD_BIND_NOT")`
  refine (c_2089 prof).run c cx.hin _ hKZ₁ hAZ₁ hrZ₁ (vc_2089 cx.hw hax₁) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  have M₂ := hMZ₁.st 8029584#64 (toBytesLE 1#32 4)
  have G₂ := G₁.st (x := 8029584#64) (toBytesLE_length 1#32 4) (by decide)
  refine gs c cx (by decide) (call_2120 _) (by decide) hK₂ hA₂ hr₂ (by rw [hg₂]; exact hspZ₁) (by rw [hg₂]) cx.n4
    M₂ G₂ ?_
  intro Z₂ u₂ W₂ hKZ₂ hAZ₂ hMZ₂ hrZ₂ hax₂ hspZ₂ h15Z₂
  have e15₂ : Z₂.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15Z₂, hg₂]; exact e15₁
  clear hg₂ h15Z₂ hA₂ hK₂ hr₂ M₂ hMZ₁ hAZ₁ hKZ₁ hrZ₁ hax₁ hspZ₁ e15₁ G₁
  -- `_dl_bind_not`, `getenv ("LD_DYNAMIC_WEAK")`
  refine (c_2125 prof).run c cx.hin _ hKZ₂ hAZ₂ hrZ₂ (vc_2125 cx.hw hax₂) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  have M₃ := hMZ₂.st 8029608#64 (toBytesLE 0#32 4)
  have G₃ := G₂.st (x := 8029608#64) (toBytesLE_length 0#32 4) (by decide)
  refine gs c cx (by decide) (call_2153 _) (by decide) hK₃ hA₃ hr₃ (by rw [hg₃]; exact hspZ₂) (by rw [hg₃]) cx.n5
    M₃ G₃ ?_
  intro Z₃ u₃ W₃ hKZ₃ hAZ₃ hMZ₃ hrZ₃ hax₃ hspZ₃ h15Z₃
  have e15₃ : Z₃.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15Z₃, hg₃]; exact e15₂
  clear hg₃ h15Z₃ hA₃ hK₃ hr₃ M₃ hMZ₂ hAZ₂ hKZ₂ hrZ₂ hax₂ hspZ₂ e15₂ G₂
  -- `_dl_dynamic_weak`, `getenv ("LD_PROFILE_OUTPUT")`
  refine (c_2158 prof).run c cx.hin _ hKZ₃ hAZ₃ hrZ₃ (vc_2158 cx.hw hax₃) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  have M₄ := hMZ₃.st 8029536#64 (toBytesLE 1#32 4)
  have G₄ := G₃.st (x := 8029536#64) (toBytesLE_length 1#32 4) (by decide)
  refine gs c cx (by decide) (call_2189 _) (by decide) hK₄ hA₄ hr₄ (by rw [hg₄]; exact hspZ₃) (by rw [hg₄]) cx.n6
    M₄ G₄ ?_
  intro Z₄ u₄ W₄ hKZ₄ hAZ₄ hMZ₄ hrZ₄ hax₄ hspZ₄ h15Z₄
  have e15₄ : Z₄.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15Z₄, hg₄]; exact e15₃
  clear hg₄ h15Z₄ hA₄ hK₄ hr₄ M₄ hMZ₃ hAZ₃ hKZ₃ hrZ₃ hax₃ hspZ₃ e15₃ G₃
  -- `_dl_profile_output`, the platform string not empty
  have up : ∀ x : Addr, sp.toNat ≤ x.toNat → W₄ x = V x := fun x hx =>
    (hMZ₄ x (by unfold Scr; omega)).trans (G₄ x (Bool.eq_false_iff.2 fun h => by have := nv_data h; omega))
  have hp₄ : rdq(W₄, 8029512#64) = p := by
    rw [hMZ₄.rdi h72 _ 8 (by decide), G₄.rd _ 8 (by decide) (by decide)]
    exact hpl.hp
  have hfp : Foot F.data p := hpl.pg p (Nat.le_refl _) (Nat.div_le_div_right (by omega))
  have hp0 : W₄ p ≠ 0 := by
    rw [up p hpl.hi]
    have := hpl.nnz 0 hpl.n1
    rwa [addr_add_zero] at this
  refine (c_2194 prof).run c cx.hin _ hKZ₄ hAZ₄ hrZ₄ (vc_2194 cx.hr cx.hw hax₄ ?_ hp₄
    (.inr ⟨hfp, .inr (by have := hpl.hi; omega), ?_⟩)) ?_
  · rw [hMZ₄.rdi h72 _ 4 (by decide), G₄.rd _ 4 (by decide) (by decide)]
    exact hsec
  · rw [rdb1]
    exact hp0
  rintro j' g fl V₅ ⟨rfl, rfl, rfl⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have M₅ := (hMZ₄.st 8029600#64 (toBytesLE 0#64 8)).st 8029600#64 (toBytesLE 7288540#64 8)
  have G₅ := (G₄.st (x := 8029600#64) (toBytesLE_length 0#64 8) (by decide)).st (x := 8029600#64)
    (toBytesLE_length 7288540#64 8) (by decide)
  clear up hp₄ hp0
  -- `getenv ("LD_ASSUME_KERNEL")`
  refine (c_2269 prof).run c cx.hin _ hK₅ hA₅ hr₅ vc_2269 ?_
  rintro j' g fl V₆ ⟨rfl, rfl, rfl⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  refine gs c cx (by decide) (call_2276 _) (by decide) hK₆ hA₆ hr₆ (by rw [hg₆, hg₅]; exact hspZ₄) (by rw [hg₆])
    cx.n7 M₅ G₅ ?_
  intro Z₆ u₆ W₆ hKZ₆ hAZ₆ hMZ₆ hrZ₆ hax₆ hspZ₆ h15Z₆
  have e15₆ : Z₆.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15Z₆, hg₆, hg₅]; exact e15₄
  clear hg₆ hg₅ h15Z₆ hA₆ hK₆ hr₆ hA₅ hK₅ hr₅ M₅ hMZ₄ hAZ₄ hKZ₄ hrZ₄ hax₄ hspZ₄ e15₄ G₄
  -- the platform string: `strlen`
  have hp₆ : rdq(W₆, 8029512#64) = p := by
    rw [hMZ₆.rdi h72 _ 8 (by decide), G₅.rd _ 8 (by decide) (by decide)]
    exact hpl.hp
  have hpn : p ≠ 0#64 := fun h => by
    have h1 := hpl.hi
    rw [h] at h1
    have : (0#64).toNat = 0 := rfl
    omega
  refine (c_2281 prof).run c cx.hin _ hKZ₆ hAZ₆ hrZ₆ (vc_2281 cx.hr hax₆ hp₆) ?_
  rintro j' g fl V₇ ⟨-, hj, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  obtain rfl := hj hpn
  have hsp₇ : Y₇.cpu.gpr.rsp = sp := by rw [hg₇]; exact hspZ₆
  refine c.s_call hK₇ hA₇ cx.hin (lt_len (by decide)) hr₇ (call_2563 _) cx.hil cx.hl0 (by decide)
    (fun i hi => by rw [hsp₇]; exact w8 cx.hstk i hi) ?_
  rintro Y₈ t₈ hK₈ hA₈ ⟨hr₈, hg₈⟩
  rw [hsp₇] at hA₈ hg₈
  have e8 := t8 sp (by omega)
  replace hA₈ : Agree F Y₈.proc.mm.mem (Vst V₇ (sp - 8#64) (toBytesLE (ndi_at.add (2563 + 5)) 8)) := hA₈
  have M₈ : Eqo sp (Vst V₇ (sp - 8#64) (toBytesLE (ndi_at.add (2563 + 5)) 8)) _ :=
    hMZ₆.push (by rw [e8]; omega) (by rw [e8, toBytesLE_length]; omega)
  have up : ∀ x : Addr, sp.toNat ≤ x.toNat →
      Vst V₇ (sp - 8#64) (toBytesLE (ndi_at.add (2563 + 5)) 8) x = V x := fun x hx =>
    (M₈ x (by unfold Scr; omega)).trans (G₅ x (Bool.eq_false_iff.2 fun h => by have := nv_data h; omega))
  have hdi₈ : Y₈.cpu.gpr.rdi = p := by rw [hg₈, hg₇]; rfl
  have hsp₈ : Y₈.cpu.gpr.rsp = sp - 8#64 := by rw [hg₈]; rfl
  have ap : ∀ k ≤ n, (Addr.add p k).toNat = p.toNat + k := fun k hk =>
    toNat_add_of_fits (n := n + 1) (by omega) (by have := hpl.fit; omega)
  refine cx.hlen n c hK₈ hA₈ hr₈ (cx.hPm _ (got_kept h72 M₈ G₅)) cx.hin (lt_len (show 2563 + 5 < 2897 by decide))
    ?_ (fun i hi => ?_) (by rw [hdi₈]; exact hpl.fit) (fun k hk => ?_) ?_ (fun x h1 h2 => ?_) ?_
  · rw [hsp₈, vs (toBytesLE_length _ 8) (by rw [e8]; omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  · rw [hsp₈]
    exact c.hws _ (w8 cx.hstk i hi)
  · rw [hdi₈, up _ (by rw [ap k (by omega)]; have := hpl.hi; omega)]
    exact hpl.nnz k hk
  · rw [hdi₈, up _ (by rw [ap n (Nat.le_refl _)]; have := hpl.hi; omega)]
    exact hpl.nz
  · rw [hdi₈] at h1 h2
    exact hpl.pg x h1 h2
  intro Z₈ u₈ hKZ₈ hAZ₈ hrZ₈ hspZ₈ hax₈ _ _ _ _ _ h15
  have hspZ : Z₈.cpu.gpr.rsp = sp := by rw [hspZ₈, hsp₈]; exact u8 sp
  have e15₈ : Z₈.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [h15, hg₈, hg₇]; exact e15₆
  -- `_dl_platformlen`
  refine (c_2568 prof).run c cx.hin _ hKZ₈ hAZ₈ hrZ₈ (vc_2568 cx.hw) ?_
  rintro j' g fl V₉ ⟨rfl, rfl, rfl⟩ Y₉ t₉ hK₉ hA₉ hr₉ hg₉ -
  rw [hax₈] at hA₉
  exact k Y₉ t₉ _ hK₉ hA₉ (M₈.st _ _) hr₉ (by rw [hg₉]; exact hspZ) (by rw [hg₉]; exact e15₈)
end FV7z.Ndi
