import FV7z.Mun.Holds
import FV7z.Start.Unmap
import FV7z.Start.Cpu
/-!
# `__munmap` from its entry to its return, the kernel's `munmap` included (PLAN.md §M, M1)

`Mun/Holds.lean`'s pieces around `Seg.s_munmap` (`Start/Unmap.lean`). `mun_pre` reaches the `syscall`; the kernel
answers an error or 0 with nothing changed (the run goes on in the same `Fn.Seg`, seen from the state after the
`syscall` by `Seg.rebase`), or unmaps the pages, 0 (the run goes on from the state after as a new start, with a
footprint `G` outside the pages and what it may store into `Wl'`); `mun_post` returns from either.

- `munG`: the registers after the `syscall`.
- `mun_ok`: from the entry to the return address, every outcome of the kernel's `munmap` the model has, but a stop
  (a page of the range special or the initial stack's first page).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Write
namespace FV7z.Mun

/-- The registers after `__munmap`'s `syscall`, from `g` at the entry: `rax` the answer `r`, `rcx` the address after
the `syscall`, `r11` the flags `f`. -/
abbrev munG (g : Gprs) (f r : BitVec 64) : Gprs := (((g.set 0 11).set 1 (mun_at.add 11)).set 11 f).set 0 r

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t : Nat} {V : Addr → Byte}

/-- `__munmap (addr, len)` from its entry to the return address at `rsp`, no page of the range special or the initial
stack's first page. The kernel's answer `r` an error or 0 with nothing changed: the run goes on in the same `Fn.Seg`
(`k`), as `mun_post` says. The pages unmapped: from the state `S` after the `syscall`, a new start of a footprint `G`
whose bytes are bytes of `F` outside the pages, `rax` 0 (`k₁`). The event is `munmap`'s, from the registers at the
entry with `rax` 11. -/
theorem mun_ok {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L mun_at mun)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mun_at)
    (hfx : X.proc.mm.mem.touchesFixed (munFirst X) (munN X) = false) (hrs : s₀.thread.rseq = none)
    {G : Footprint} {Wl' : List Rgn} (hGo : G.own = []) (hGc : G.code = F.code)
    (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages (munFirst X) (munN X) (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → (Foot F.writes a ∨ Foot F.reads a) ∧
      inPages (munFirst X) (munN X) (pageOf a) = false)
    (hcode : ∀ a, Foot F.codeRgns a → inPages (munFirst X) (munN X) (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64) (hl : ∀ i < 8, Foot G.data (Addr.add X.cpu.gpr.rsp i))
    (fe : ∀ i < 4, Foot Wl ((errnoAt fb).add i)) (fe' : ∀ i < 4, Foot Wl' ((errnoAt fb).add i))
    (hfe : (errnoAt fb).toNat + 4 ≤ 2 ^ 64)
    (hed : (errnoAt fb).toNat + 4 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ (errnoAt fb).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (r : BitVec 64) (Z : State) (t' : Nat), WrErr r ∨ r = 0 → KeptW Wl s₀ Z → Z.cpu.rip = e₂.add j₂ →
      (¬ WrErr r → Agree F Z.proc.mm.mem V ∧ ∃ f, Z.cpu.gpr = (munG X.cpu.gpr f r).set 4 (X.cpu.gpr.rsp + 8)) →
      (WrErr r → Agree F Z.proc.mm.mem (Vst V (errnoAt fb) (errnoB r)) ∧
        ∃ f, Z.cpu.gpr = (mErr (munG X.cpu.gpr f r)).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [tcEv (X.cpu.gpr.set 0 11) r []]) gP gE Z t')
    (k₁ : ∀ (S Z : State) (t' : Nat), Seg prof G Wl' L S o → KeptW Wl' S Z → Z.cpu.rip = e₂.add j₂ →
      Agree G Z.proc.mm.mem V → (∃ f, Z.cpu.gpr = (munG X.cpu.gpr f 0).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o (gev ++ [tcEv (X.cpu.gpr.set 0 11) 0 []]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlF : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i) := fun i hi =>
    (Start.unmap_sub c.own hGo hGw hGr _ (hl i hi)).1
  refine mun_pre c hfs hin hK hA hrip fun Y0 t₀ hK0 hA0 hr0 hg0 => ?_
  have hdi : Y0.cpu.gpr.rdi = X.cpu.gpr.rdi := by rw [hg0]; try rfl
  have hsi : Y0.cpu.gpr.rsi = X.cpu.gpr.rsi := by rw [hg0]; try rfl
  have e1 : munFirst Y0 = munFirst X := by simp only [munFirst, hdi]
  have e2 : munN Y0 = munN X := by simp only [munN, hsi]
  have hfx0 : Y0.proc.mm.mem.touchesFixed (munFirst Y0) (munN Y0) = false := by
    rw [e1, e2, Start.touchesFixed_congr (hK0.mem_map.trans hK.mem_map.symm)
      (hK0.calm.growsDown.trans hK.calm.growsDown.symm)]
    exact hfx
  have hnr : Y0.cpu.gpr.rax.toNat % 2 ^ 32 = 11 := by rw [hg0]; first | rfl | decide
  -- the registers after the `syscall`
  have hYg : ∀ (Y : State) (r : BitVec 64), Y.cpu.gpr = (sysGpr Y0 2).set 0 r →
      Y.cpu.gpr = munG X.cpu.gpr (rf0 Y0).toBits r := by
    intro Y r hgY
    rw [hgY]
    show ((Y0.cpu.gpr.set 1 (Y0.cpu.rip.add 2)).set 11 (rf0 Y0).toBits).set 0 r = _
    rw [hg0, hr0, addr_add_add]
    try rfl
  refine c.s_munmap hK0 hA0 hin (lt_len (by decide)) hr0 (sys_9 _) hnr hfx0 hrs hGo hGc hfit
    (by rw [e1, e2]; exact hGw) (by rw [e1, e2]; exact hGr) (by rw [e1, e2]; exact hcode) hww ?_ ?_
  · intro r hr Y t₁ hKY hAY ⟨hrY, hgY⟩
    rw [hg0]
    have hY := hYg Y r hgY
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hY]; try rfl
    have hax : Y.cpu.gpr.rax = r := by rw [hY]; try rfl
    refine mun_post (c.rebase hKY fun _ h => h) (by rw [hKY.seg]; exact hfs) hin hAY (hrY.trans rfl)
      (by rw [hsY]; exact hsp) (fun i hi => by rw [hsY]; exact hlF i hi) fe hfe (by rw [hsY]; exact hed) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    intro Z t₂ hKZ hrZ hok herr
    refine k r Z t₂ hr (hKY.trans hKZ fun _ h => h) hrZ (fun h => ?_) (fun h => ?_)
    · obtain ⟨hAZ, hgZ⟩ := hok (by rw [hax]; exact h)
      exact ⟨hAZ, (rf0 Y0).toBits, by rw [hgZ, hsY, hY]⟩
    · obtain ⟨hAZ, hgZ⟩ := herr (by rw [hax]; exact h)
      rw [hax] at hAZ
      exact ⟨hAZ, (rf0 Y0).toBits, by rw [hgZ, hsY, hY]⟩
  · intro Y t₁ c₁ hAY hrY hgY hsgY
    rw [hg0]
    have hY := hYg Y 0 hgY
    have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hY]; try rfl
    have hax : Y.cpu.gpr.rax = 0 := by rw [hY]; try rfl
    refine mun_post c₁ (by rw [hsgY, hK0.seg]; exact hfs) hin hAY (hrY.trans rfl) (by rw [hsY]; exact hsp)
      (fun i hi => by rw [hsY]; exact hl i hi) fe' hfe (by rw [hsY]; exact hed) hin₂ h₂ (by rw [hsY]; exact hra) ?_
    intro Z t₂ hKZ hrZ hok _
    have hn : ¬ WrErr Y.cpu.gpr.rax := by rw [hax]; unfold WrErr; decide
    obtain ⟨hAZ, hgZ⟩ := hok hn
    exact k₁ Y Z t₂ c₁ hKZ hrZ hAZ ⟨(rf0 Y0).toBits, by rw [hgZ, hsY, hY]⟩

end FV7z.Mun
