import FV7z.Start.Grow
import FV7z.Lemmas.SysMm
/-!
# `brk` and `arch_prctl (ARCH_SET_FS, …)`, steps of a run (PLAN.md G3, startup)

`Lemmas/SysMm.lean`'s system calls as steps of a run that `Fn.Seg` describes. A call that changes the layout or the
thread's `fs` base leaves a state that `KeptW` does not relate to the run's start. The run then goes on from that
state as a new start: the rest of the run is given `Fn.Seg` there (`Start/Grow.lean`), and the state the call was made
in (`X'`, which `KeptW` relates to the old start), with what the state after is in its terms.

- `footOk_congr`, `ready_cpu`: `Footprint.Ok` and `Ready` of a state with the same memory, key rights and thread.
- `free_le`, `free_congr`: fewer pages of free ones are free; `Memory.free` is of the page map.
- `Seg.s_brk_keep`: `brk (b)` with `b` below the lowest break; the run goes on from the same start.
- `Seg.s_brk_grow`: `brk (b)` that grows the break, the kernel not refusing memory: the run goes on with the new
  pages' regions `N` among what it may store into, their bytes 0.
- `Seg.s_set_fs`: `arch_prctl (ARCH_SET_FS, a)`.
-/
namespace FV7z.Start
open ZellicX86

theorem footOk_congr {feat : Features} {X Y : State} {F : Footprint} (hok : F.Ok feat X)
    (hm : Y.proc.mm.mem = X.proc.mm.mem) (hp : Y.cpu.pkru = X.cpu.pkru) (ht : Y.thread.rseq = X.thread.rseq) :
    F.Ok feat Y := by
  have hra : rseqArea Y = rseqArea X := by simp only [rseqArea, ht]
  refine ⟨hok.fits, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hok.codeApart, ?_⟩
  · intro r hr a ha
    rw [hm, hp]
    exact hok.writable r hr a ha
  · intro r hr a ha
    rw [hm, hp]
    exact hok.readable r hr a ha
  · intro c hc
    obtain ⟨h1, h2⟩ := hok.code c hc
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [hm, hp]
      exact h1 a ha
    · unfold Bytes at h2 ⊢
      rw [hm]
      exact h2
  · intro a ha m hmm
    rw [hm] at hmm ⊢
    exact hok.notKernel a ha m hmm
  · intro a b ha hb hne m n hma hmb
    rw [hra] at ha hb
    rw [hm] at hma hmb ⊢
    exact hok.noAlias a b ha hb hne m n hma hmb
  · intro a ha m hmm
    rw [hm] at hmm ⊢
    exact hok.notShared a ha m hmm
  · intro a ha
    rw [hm]
    exact hok.notFixed a ha
  · rw [hra]
    exact hok.rseqApart

/-- `Ready` of a state with the same process and thread, `TF` and `AC` clear, without an `rseq` area. -/
theorem ready_cpu {feat : Features} {X Y : State} (hR : Ready feat X) (hproc : Y.proc = X.proc)
    (hth : Y.thread = X.thread) (htf : Y.cpu.rflags.tf = false) (hac : Y.cpu.rflags.ac = false)
    (hrs : X.thread.rseq = none) : Ready feat Y := by
  obtain ⟨⟨-, -, h3, h4⟩, -, hl⟩ := hR
  refine ⟨⟨htf, hac, by rw [hth]; exact h3, by rw [hth]; exact h4⟩, ?_, ?_⟩
  · simp only [RseqQuiet, hth, hrs]
  · unfold LayoutOk at hl ⊢
    rw [hproc]
    exact hl

theorem free_le {m : Memory} {P n n' : Nat} (h : m.free P n' = true) (hle : n ≤ n') : m.free P n = true := by
  simp only [Memory.free, List.all_eq_true, List.mem_range] at h ⊢
  exact fun k hk => h k (by omega)

theorem free_congr {m M : Memory} (h : M.map = m.map) (P n : Nat) : M.free P n = m.free P n := by
  simp only [Memory.free, Memory.mapAt, h]

end FV7z.Start

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Start

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `brk (b)` with `b` below the lowest break: the break in `rax`, `rcx` and `r11` as `syscall` sets
them, no other change. -/
theorem s_brk_keep (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 12)
    (hlow : X.cpu.gpr.rdi.toNat < X.proc.mm.brkMin.toNat)
    (k' : ContG prof F Wl L s₀ o (gev ++ [sysEv X X.proc.mm.brk]) gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (sysGpr X len).set 0 X.proc.mm.brk) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ =>
    ⟨_, _, _, syscall_brk_keep (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hlow,
      k' _ _ (hK'.nx rfl rfl rfl) (c.agreeK hK hA hM) ⟨rip_add hrip M len, rfl⟩⟩

/-- `syscall` for `brk (b)` that grows the break, the kernel not refusing memory: the pages from the break's to
`b`'s are new zero pages, the break is `b`, `rax` is `b`. The run goes on from the state after, `Y`, as a new start,
with the regions `N` of the new pages among what it may store into; `X'` is the state the call was made in. -/
theorem s_brk_grow (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 12)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlow : X.proc.mm.brkMin.toNat ≤ X.cpu.gpr.rdi.toNat)
    (hgt : pageUp X.proc.mm.brk.toNat / 4096 < pageUp X.cpu.gpr.rdi.toNat / 4096)
    (htop : 4096 * (pageUp X.cpu.gpr.rdi.toNat / 4096) ≤ 2 ^ 47 - 4096)
    (hfree : X.proc.mm.mem.free (pageUp X.proc.mm.brk.toNat / 4096)
      (pageUp X.cpu.gpr.rdi.toNat / 4096 - pageUp X.proc.mm.brk.toNat / 4096 + 1) = true)
    (hrs : s₀.thread.rseq = none) (hp0 : s₀.cpu.pkru &&& 3 = 0)
    {N : List Rgn} (hN : ∀ r ∈ N, r.In (pageUp X.proc.mm.brk.toNat / 4096 * 4096)
      (pageUp X.cpu.gpr.rdi.toNat / 4096 * 4096))
    {V' : Addr → Byte} (h0 : ∀ a, Foot N a → V' a = 0) (hV : ∀ a, Foot F.data a → ¬ Foot N a → V' a = V a)
    (k' : ∀ X' Y t', KeptW Wl s₀ X' → X'.cpu = X.cpu →
      Y = sysSt (brkSt X' X.cpu.gpr.rdi) len X.cpu.gpr.rdi →
      Seg prof (withNew F N) (N ++ Wl) L Y o → Agree (withNew F N) Y.proc.mm.mem V' →
      GoG prof L o (gev ++ [sysEv X X.cpu.gpr.rdi]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  have hokX := c.foot.keptW c.ready.rseq c.hws hK' c.sub_self
  have hRX := c.ready.keptW c.foot c.hws hK'
  have hmap : M.map = X.proc.mm.mem.map := hM.map
  have hfree' : (X.withMem M).proc.mm.mem.free (pageUp X.proc.mm.brk.toNat / 4096)
      (pageUp X.cpu.gpr.rdi.toNat / 4096 - pageUp X.proc.mm.brk.toNat / 4096 + 1) = true := by
    show M.free _ _ = true
    rw [free_congr hmap]
    exact hfree
  have hfreeN := free_le hfree' (Nat.le_add_right _ 1)
  have hrsX : (X.withMem M).thread.rseq = none := by rw [hK'.thread]; exact hrs
  have hpkX : (X.withMem M).cpu.pkru &&& 3 = 0 := by rw [hK'.pkru]; exact hp0
  have hsum : pageUp X.proc.mm.brk.toNat / 4096 +
      (pageUp X.cpu.gpr.rdi.toNat / 4096 - pageUp X.proc.mm.brk.toNat / 4096) =
      pageUp X.cpu.gpr.rdi.toNat / 4096 := by omega
  have hN' : ∀ r ∈ N, r.In (pageUp X.proc.mm.brk.toNat / 4096 * 4096)
      ((pageUp X.proc.mm.brk.toNat / 4096 +
        (pageUp X.cpu.gpr.rdi.toNat / 4096 - pageUp X.proc.mm.brk.toNat / 4096)) * 4096) := by
    rw [hsum]
    exact hN
  have htsz := taskSize_ge prof.feat
  have htop' : 4096 * (pageUp X.cpu.gpr.rdi.toNat / 4096) ≤ taskSize prof.feat := by omega
  refine ⟨_, _, _, syscall_brk_grow (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hlow (hmg _ _) hgt
    htop' hfree', k' (X.withMem M) _ _ hK' rfl rfl ?_ ?_⟩
  · exact
      { foot := footOk_grow hokX hRX.layout hfreeN rfl rfl hpkX hrsX hrsX c.own hN' (by rw [hsum]; omega)
        ready := ready_grow hRX hfreeN rfl rfl hlow htf hac rfl hrsX (by rw [hsum]; omega)
        env := c.env
        code := c.code
        own := rfl
        hww := by
          intro y hy
          rcases foot_append_iff.1 hy with ⟨r, hr, hm⟩ | hy
          · exact ⟨r, List.mem_append_left _ hr, hm⟩
          · obtain ⟨q, hq, hm⟩ := c.hww y hy
            exact ⟨q, List.mem_append_right _ hq, hm⟩ }
  · exact agree_grow hokX hRX.layout hfreeN rfl c.own hN' (c.agreeK hK hA hM) h0 hV

/-- `syscall` for `arch_prctl (ARCH_SET_FS, a)`: the `fs` base is `a`, `rax` is 0. The run goes on from the state
after, `Y`, as a new start; `X'` is the state the call was made in. -/
theorem s_set_fs (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 158)
    (hopt : arg32 X.cpu.gpr.rdi = 0x1002) (ha : X.cpu.gpr.rsi.toNat < 2 ^ 47 - 4096)
    (hrs : s₀.thread.rseq = none)
    (k' : ∀ X' Y t', KeptW Wl s₀ X' → X'.cpu = X.cpu → Y = sysSt (fsSt X' X.cpu.gpr.rsi) len 0 →
      Seg prof F Wl L Y o → Agree F Y.proc.mm.mem V → GoG prof L o (gev ++ [sysEv X 0]) gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  have hokX := c.foot.keptW c.ready.rseq c.hws hK' c.sub_self
  have hRX := c.ready.keptW c.foot c.hws hK'
  have hrsX : (X.withMem M).thread.rseq = none := by rw [hK'.thread]; exact hrs
  have htsz := taskSize_ge prof.feat
  refine ⟨_, _, _, syscall_set_fs (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hopt
    (Nat.lt_of_lt_of_le ha htsz), k' (X.withMem M) _ _ hK' rfl rfl ?_ (c.agreeK hK hA hM)⟩
  exact
    { foot := footOk_congr hokX rfl rfl rfl
      ready := ready_cpu hRX rfl rfl htf hac hrsX
      env := c.env
      code := c.code
      own := c.own
      hww := c.hww }

end FV7z.Fn.Seg
