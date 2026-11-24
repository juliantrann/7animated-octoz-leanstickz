import FV7z.Im6.V
import FV7z.Im2.RunN
import FV7z.Im5.RunA
/-!
# `_int_malloc`: the second call for the request 72704 (PLAN.md G3, `malloc`; ctor 102)

- `im_second72704`: from the entry through the cut points 512, 1115, 2012 to 2549 (`vc6`), then `Im2.im_from2549`:
  the top split for `nb` = 72720, `T + 16` returned, the six registers back; the bytes at 2549 known only through the
  frame `Im2.Fr` (handed to the continuation). As `Im5.im_secondl` with the largebin 121 for the bins 64 … 99.
- `secN`: `Im5.SecA` for every request of `Im5.ClsN` (`Im5.secA`, or `im_second72704`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at)
open FV7z.Im2 (VspN)
namespace FV7z.Im6
variable {F : Footprint} {Wl : List Rgn}

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `_int_malloc` on the second call (`av` the main arena) for the request 72704 (`nb` = 72720, the largebin 121):
the fastbins flag 0, the largebin 121, the unsorted bin and the binmap's blocks 2 and 3 empty, the tcache there, the
top `T` big enough; the top is split, `T + 16` is returned, the six registers come back. -/
theorem im_second72704 {fb S T szw sm : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at)
    (hrsp : X.cpu.gpr.rsp = S + 184#64) (hsi : X.cpu.gpr.rsi = 72704#64) (hdi : X.cpu.gpr.rdi = 7940672#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64) (hfc : rdd(V, 7940680#64) = 0)
    (hl121 : rdq(V, 7942704#64) = 7942688#64)
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64) (hm2 : rdd(V, 7942824#64) = 0) (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 192, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + 72720 + 16 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i))
    (hrw : ∀ i < 8, Foot Wl (Addr.add (T + 72720#64 + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : 72720 + 32 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 184#64) = e₂.add j₂)
    (k : ∀ M Z t', Im2.Fr S X.cpu.gpr V M → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VspN T szw 72720#64 M) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs184 : ∀ i < 184, Foot Wl (Addr.add S i) := fun i hi => hsw i (by omega)
  have hsd : ∀ i < 184, Foot F.data (Addr.add S i) := fun i hi => c.hws _ (hs184 i hi)
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [hrip]; rfl)
    (vc6 hrsp hsi hdi hS hlo hfb hgm hfc hl121 htc htb hun hm2 hm3 hWd hgf htf hs184 hsd) ?_
  rintro j₁ g₁ f₁ V₁ ⟨rfl, h₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁
  refine (c_512 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ (by rw [hg₁, hf₁]; exact h₁) ?_
  rintro j₂' g₂ f₂ V₂ ⟨rfl, h₂'⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂
  refine (c_1115 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (by rw [hg₂, hf₂]; exact h₂') ?_
  rintro j₃ g₃ f₃ V₃ ⟨rfl, h₃⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃
  refine (c_2012 prof fb).run c hfs hin _ hK₃ hA₃ hr₃ (by rw [hg₃, hf₃]; exact h₃) ?_
  rintro j₄ g₄ f₄ V₄ ⟨rfl, hbx, h13, hsp, hfr⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  exact Im2.im_from2549 (nb := 72720#64) c hfs hin hK₄ hA₄ hr₄ (by rw [hg₄]; exact hbx) (by rw [hg₄, h13])
    (by rw [hg₄]; exact hsp) hfr (by decide) hS hW hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge hin₂ h₂ hra
    (fun Z t' => k V₄ Z t' hfr)

/-- `Im5.SecA` for every request `n ≤ 4104` or 72704 (`Im5.ClsN`): `Im5.secA` or `im_second72704`. -/
theorem secN {n nb : Addr} (h : Im5.ClsN n nb) : Im5.SecA n nb := by
  rcases h with h | ⟨rfl, rfl⟩
  · exact Im5.secA h
  intro prof F Wl L s₀ X o t gev gP gE V fb S T szw sm c hfs hin hK hA hrip hrsp hsi hdi hS hlo hfb hgm hfc hfz hbk
    hlb htc htb hun hm0 hm1 hm2 hm3 hW hgf htf hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge e₂ code₂ hin₂ j₂ h₂
    hra k
  exact im_second72704 c hfs hin hK hA hrip hrsp hsi hdi hS hlo hfb hgm hfc (hlb 121 (by decide) (by decide)) htc htb
    hun hm2 hm3 hW hgf htf hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge hin₂ h₂ hra k

end FV7z.Im6
