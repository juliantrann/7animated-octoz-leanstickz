import FV7z.Brk.Holds
import FV7z.Start.BrkSame
/-!
# `__brk` within the break's page (PLAN.md G3, `malloc`)

- `brk_same`: `__brk (a)` called from a run whose start has `Base`, with `a` not below the break and ending in the
  break's page, the kernel not refusing memory: the run reaches the `ret` from a new start with the same footprint,
  `Base` with the break `a`, which is in `__curbrk`; `eax` is 0, the other bytes are as they were.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
namespace FV7z.Brk

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `__brk (a)` that moves the break within its page, from its entry to its `ret`: the run goes on from a new start
with `Base` of the break `a`, which is in `__curbrk`; `eax` is 0. -/
theorem brk_same {lim : Nat} {b fsb : Addr} {ks : Kst} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (hin : CodeIn L brk_at brk) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = brk_at)
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hmg : ∀ t p, o t (.memFail p) = none)
    (hge : b.toNat ≤ X.cpu.gpr.rdi.toNat)
    (heq : pageUp X.cpu.gpr.rdi.toNat / 4096 = pageUp b.toNat / 4096)
    (k : ∀ rc r11 s₁ Z t', Seg prof F Wl L s₁ o → Base s₁ lim X.cpu.gpr.rdi fsb ks → KeptW Wl s₁ Z →
      Agree F Z.proc.mm.mem (Vst V curbrk (toBytesLE X.cpu.gpr.rdi 8)) →
      Z.cpu.rip = brk_at.add 33 → Z.cpu.gpr = ((X.cpu.gpr.set 0 0).set 1 rc).set 11 r11 →
      GoG prof L o (gev ++ [brkEv X X.cpu.gpr.rdi]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 9 ∧ g' = X.cpu.gpr.set 0 12 ∧ V' = V) hK hA
    (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hdiY : Y.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hgY]; rfl
  have hev : sysEv Y Y.cpu.gpr.rdi = brkEv X X.cpu.gpr.rdi := by
    simp only [sysEv, hgY]
    rfl
  refine c.b_brk_same hB hKY hAY hin (lt_len (by decide)) hrY (sys_9 _) (by rw [hgY]; rfl) hmg
    (by rw [hdiY]; exact hge) (by rw [hdiY]; exact heq) ?_
  rw [hev, hdiY]
  intro s₁ t₂ c' hB' hA' hr' hg'
  have hax : s₁.cpu.gpr.rax = X.cpu.gpr.rdi := by rw [hg']; rfl
  have hdi : s₁.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg', sys_rdi, hgY]; rfl
  have htop := hB.top
  have hle : X.cpu.gpr.rdi.toNat ≤ 2 ^ 47 := by
    have h := hB.le
    rw [← heq] at h
    unfold pageUp at h
    omega
  refine (c_11 prof).run c' hin _ (KeptW.refl _ _) hA' hr'
    (vc_11 hcur (by rw [hax]; exact hle) (by rw [hax, hdi]; omega)) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ U t₃ hKU hAU hrU hgU -
  rw [hax] at hAU
  refine k (Y.cpu.rip.add 2) (rf0 Y).toBits s₁ U t₃ c' hB' hKU hAU hrU ?_
  rw [hgU, hg']
  unfold sysGpr
  rw [hgY]
  exact gpr_ret _ _ _ _

end FV7z.Brk
