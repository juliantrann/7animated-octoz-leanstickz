import FV7z.Start.Base
/-!
# `brk` that moves the break within its page (PLAN.md G3, `malloc`)

The kernel's `brk (b)` when `b` ends in the page the break ends in: no page is mapped or unmapped, the break is `b`.
This is `__sbrk`'s call when the bytes asked for fit below the next page's start (`sysmalloc`'s second `MORECORE`,
the `correction` that aligns the end of the heap to a page).

- `syscall_brk_same`: the instruction, on Zellic's model; one answer of the stream is used (`Request.memFail`).
- `ready_brk`: `Ready` of a state with the same memory and thread and a break not below the lowest.
- `Seg.s_brk_same`: the step of a run; the run goes on from the state after as a new start, with the same footprint.
- `Seg.b_brk_same`: from a start with `Base`, to a `Base` with the new break.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `s` with the break at `b`, the pages as they were. -/
abbrev brkSt0 (s : State) (b : Addr) : State := s.withLayout s.proc.mm.mem b

/-- `brk (b)` with `b` in the break's page, when the kernel does not refuse memory: the break is `b`. -/
theorem syscall_brk_same {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 12) (hlow : s.proc.mm.brkMin.toNat ≤ s.cpu.gpr.rdi.toNat)
    (hmf : o t (.memFail 0) = none)
    (heq : pageUp s.cpu.gpr.rdi.toNat / 4096 = pageUp s.proc.mm.brk.toNat / 4096) :
    (instruction prof s).runStream o t =
      (.running (sysSt (brkSt0 s s.cpu.gpr.rdi) len s.cpu.gpr.rdi) (some (sysEv s s.cpu.gpr.rdi)), t + 1) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hbm : (nx s len (sysGpr s len) (rf0 s)).proc.mm.brkMin = s.proc.mm.brkMin := rfl
  have hbk : (nx s len (sysGpr s len) (rf0 s)).proc.mm.brk = s.proc.mm.brk := rfl
  have hme : (nx s len (sysGpr s len) (rf0 s)).proc.mm.mem = s.proc.mm.mem := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (12 ≥ 2 ^ 31) by decide, show ¬ (12 ≥ x32Bit) by decide, show ¬ (12 ≥ nrSyscalls) by decide,
    show niSyscall 12 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysBrk
  simp only [hrdi, hbm, hbk, hme, Nat.not_lt.2 hlow, ↓reduceIte]
  show (Req.bind (Req.request (.memFail 0)) _).runStream o t = _
  rw [Req.runStream_bind]
  show (match o t (.memFail 0) with
    | some _ => _
    | none => _ : Req StepResult).runStream o (t + 1) = _
  rw [hmf]
  simp only [heq, ↓reduceIte]
  rfl

end FV7z

namespace FV7z.Start
open ZellicX86

/-- `Ready` of a state with the same memory and thread, a break not below the lowest, `TF` and `AC` clear, without
an `rseq` area. -/
theorem ready_brk {feat : Features} {X Y : State} (hR : Ready feat X) (hmem : Y.proc.mm.mem = X.proc.mm.mem)
    (hbm : Y.proc.mm.brkMin = X.proc.mm.brkMin) (hbk : X.proc.mm.brkMin.toNat ≤ Y.proc.mm.brk.toNat)
    (htf : Y.cpu.rflags.tf = false) (hac : Y.cpu.rflags.ac = false) (hth : Y.thread = X.thread)
    (hrs : X.thread.rseq = none) : Ready feat Y := by
  obtain ⟨⟨-, -, h3, h4⟩, -, l1, l2, l3, -, l5, l6⟩ := hR
  refine ⟨⟨htf, hac, by rw [hth]; exact h3, by rw [hth]; exact h4⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RseqQuiet, hth, hrs]
  · rw [hmem]
    exact l1
  · rw [hmem]
    exact l2
  · rw [hbm]
    exact l3
  · rw [hbm]
    exact hbk
  · rw [hmem]
    exact l5
  · rw [hmem]
    exact l6

end FV7z.Start

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Start

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte} {lim : Nat} {b fsb : Addr} {k : Kst}

/-- `syscall` for `brk (b)` with `b` in the break's page, the kernel not refusing memory: the break is `b`, `rax` is
`b`, the bytes are as they were. The run goes on from the state after, `Y`, as a new start; `X'` is the state the
call was made in. -/
theorem s_brk_same (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 12)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlow : X.proc.mm.brkMin.toNat ≤ X.cpu.gpr.rdi.toNat)
    (heq : pageUp X.cpu.gpr.rdi.toNat / 4096 = pageUp X.proc.mm.brk.toNat / 4096)
    (hrs : s₀.thread.rseq = none)
    (k' : ∀ X' Y t', KeptW Wl s₀ X' → X'.cpu = X.cpu →
      Y = sysSt (brkSt0 X' X.cpu.gpr.rdi) len X.cpu.gpr.rdi →
      Seg prof F Wl L Y o → Agree F Y.proc.mm.mem V →
      GoG prof L o (gev ++ [sysEv X X.cpu.gpr.rdi]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  have hokX := c.foot.keptW c.ready.rseq c.hws hK' c.sub_self
  have hRX := c.ready.keptW c.foot c.hws hK'
  have hrsX : (X.withMem M).thread.rseq = none := by rw [hK'.thread]; exact hrs
  refine ⟨_, _, _, syscall_brk_same (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hlow (hmg _ _) heq,
    k' (X.withMem M) _ _ hK' rfl rfl ?_ (c.agreeK hK hA hM)⟩
  exact
    { foot := footOk_congr hokX rfl rfl rfl
      ready := ready_brk hRX rfl rfl hlow htf hac rfl hrsX
      env := c.env
      code := c.code
      own := c.own
      hww := c.hww }

/-- `syscall` for `brk (rdi)` within the break's page, from a start with `Base`, the kernel not refusing memory: the
run goes on from the state after, its own start, with the same footprint and bytes, and `Base` with the new break. -/
theorem b_brk_same (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 12)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hge : b.toNat ≤ X.cpu.gpr.rdi.toNat)
    (heq : pageUp X.cpu.gpr.rdi.toNat / 4096 = pageUp b.toNat / 4096)
    (k' : ∀ s₁ t', Seg prof F Wl L s₁ o → Base s₁ lim X.cpu.gpr.rdi fsb k → Agree F s₁.proc.mm.mem V →
      s₁.cpu.rip = e'.add (j + len) →
      s₁.cpu.gpr = (sysGpr X len).set 0 X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [sysEv X X.cpu.gpr.rdi]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  have hbk : X.proc.mm.brk = b := hK.brk.trans hB.brk
  obtain ⟨-, -, -, hlo, -⟩ := c.ready.layout
  have hlow : X.proc.mm.brkMin.toNat ≤ X.cpu.gpr.rdi.toNat := by
    rw [hK.brkMin]
    rw [hB.brk] at hlo
    omega
  subst hbk
  refine c.s_brk_same hK hA hin hj hrip hd hnr hmg hlow heq hB.rseq ?_
  rintro X' Y t' hK' hcpu rfl c' hA'
  refine k' _ t' c' ⟨?_, ?_, rfl, ?_, by rw [heq]; exact hB.le, hB.top, ?_, ?_, ?_, ?_, ?_, ?_⟩ hA' ?_ ?_
  · show X'.thread.rseq = none
    rw [hK'.thread]
    exact hB.rseq
  · show X'.cpu.pkru &&& 3 = 0
    rw [hK'.pkru]
    exact hB.pkru
  · show X'.cpu.seg.fsBase = fsb
    rw [hK'.seg]
    exact hB.fsb
  · intro p h1 h2
    show X'.proc.mm.mem.map p = none
    rw [hK'.mem_map]
    exact hB.free p (by rw [← heq]; exact h1) h2
  · show X'.thread.tid = k.tid
    rw [hK'.thread]
    exact hB.tid
  · show X'.thread.pending = []
    rw [hK'.thread]
    exact hB.tpend
  · show X'.proc.signal.pending = []
    rw [hK'.proc]
    exact hB.ppend
  · show X'.cpu.rflags.df = false
    rw [hK'.df]
    exact hB.df
  · show Relro X'.proc.mm.mem
    exact Relro.of_map hK'.mem_map hB.relro
  · show X'.cpu.rip.add len = _
    rw [hcpu, hrip, addr_add_add]
  · show ((X'.cpu.gpr.set 1 (X'.cpu.rip.add len)).set 11 ({ X'.cpu.rflags with rf := false } : Rflags).toBits).set 0
      X.cpu.gpr.rdi = _
    rw [hcpu]

end FV7z.Fn.Seg
