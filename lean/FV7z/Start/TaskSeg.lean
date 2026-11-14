import FV7z.Start.Base
import FV7z.Lemmas.SysTask
/-!
# System calls that change the kernel's record of the thread, steps of a run (PLAN.md G3, startup)

`Lemmas/SysTask.lean`'s system calls as steps of a run that `Fn.Seg` describes. `set_tid_address`,
`set_robust_list`, `rt_sigaction` and `rt_sigprocmask` change the thread or the process's signal actions, which
`KeptW` does not allow: the run goes on from the state after as a new start (as in `Start/SysSeg.lean`), with `Base`.

- `Seg.reroot`: a state with the address space, key rights, `rseq` area, shadow stack and `CPUID` faulting of one
  that `KeptW` relates to the start is a start of the run.
- `Base.next`: `Base` of such a state.
- `Seg.b_set_tid`, `Seg.b_set_robust`, `Seg.b_sigaction`, `Seg.b_sigunblock`: the four calls.
- `Seg.s_getrlimit`: `prlimit64 (0, r, 0, old)`; it changes memory only.
-/
namespace FV7z.Start
open ZellicX86

/-- `Base` of a state with the address space, signal state, key rights, segment bases and thread id of one that
`KeptW` relates to a start with `Base`, and its direction flag. -/
theorem Base.next {Wl : List Rgn} {s₀ X' Y : State} {lim : Nat} {b fsb : Addr} {k : Kst} (hB : Base s₀ lim b fsb k)
    (hK' : KeptW Wl s₀ X') (hmm : Y.proc.mm = X'.proc.mm) (hsg : Y.proc.signal = X'.proc.signal)
    (hp : Y.cpu.pkru = X'.cpu.pkru) (hseg : Y.cpu.seg = X'.cpu.seg) (hrq : Y.thread.rseq = X'.thread.rseq)
    (htid : Y.thread.tid = X'.thread.tid) (hpd : Y.thread.pending = X'.thread.pending)
    (hdf : Y.cpu.rflags.df = X'.cpu.rflags.df) : Base Y lim b fsb k := by
  refine ⟨hrq.trans ?_, ?_, ?_, ?_, hB.le, hB.top, fun p h1 h2 => ?_, htid.trans ?_, hpd.trans ?_, ?_, hdf.trans ?_,
    Relro.of_map (by rw [hmm, hK'.mem_map]) hB.relro⟩
  · rw [hK'.thread]
    exact hB.rseq
  · rw [hp, hK'.pkru]
    exact hB.pkru
  · rw [hmm, hK'.brk]
    exact hB.brk
  · rw [hseg, hK'.seg]
    exact hB.fsb
  · rw [hmm, hK'.mem_map]
    exact hB.free p h1 h2
  · rw [hK'.thread]
    exact hB.tid
  · rw [hK'.thread]
    exact hB.tpend
  · rw [hsg, hK'.proc]
    exact hB.ppend
  · rw [hK'.df]
    exact hB.df

end FV7z.Start

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf FV7z.Start

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte} {lim : Nat} {b fsb : Addr} {k : Kst}

/-- A state with the address space, key rights, `rseq` area, shadow stack and `CPUID` faulting of one that `KeptW`
relates to the start, `TF` and `AC` clear, is a start of the run. -/
theorem reroot (c : Seg prof F Wl L s₀ o) {X' Y : State} (hK' : KeptW Wl s₀ X') (hmm : Y.proc.mm = X'.proc.mm)
    (hp : Y.cpu.pkru = X'.cpu.pkru) (hrq : Y.thread.rseq = X'.thread.rseq) (hsh : Y.thread.shstk = X'.thread.shstk)
    (hcf : Y.thread.cpuidFaults = X'.thread.cpuidFaults) (htf : Y.cpu.rflags.tf = false)
    (hac : Y.cpu.rflags.ac = false) (hrs : s₀.thread.rseq = none) : Seg prof F Wl L Y o := by
  have hokX := c.foot.keptW c.ready.rseq c.hws hK' c.sub_self
  obtain ⟨⟨-, -, h3, h4⟩, -, hl⟩ := c.ready.keptW c.foot c.hws hK'
  have hrsX : X'.thread.rseq = none := by rw [hK'.thread]; exact hrs
  exact
    { foot := footOk_congr hokX (congrArg (·.mem) hmm) hp hrq
      ready := ⟨⟨htf, hac, hsh.trans h3, hcf.trans h4⟩, by simp only [RseqQuiet, hrq, hrsX], by
        unfold LayoutOk at hl ⊢
        rw [hmm]
        exact hl⟩
      env := c.env
      code := c.code
      own := c.own
      hww := c.hww }

/-- `syscall` for `set_tid_address (rdi)` from a start with `Base`: the thread's id in `rax`. The run goes on from the
state after, its own start. -/
theorem b_set_tid (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 218)
    (k' : ∀ s₁ t', Seg prof F Wl L s₁ o → Base s₁ lim b fsb k → Agree F s₁.proc.mm.mem V →
      s₁.cpu.rip = e'.add (j + len) → s₁.cpu.gpr = (sysGpr X len).set 0 (BitVec.ofNat 64 k.tid) →
      s₁.cpu.vec = X.cpu.vec →
      GoG prof L o (gev ++ [sysEv X (BitVec.ofNat 64 k.tid)]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  have htid : (X.withMem M).thread.tid = k.tid := by rw [hK'.thread]; exact hB.tid
  refine ⟨_, _, _, syscall_set_tid (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr, ?_⟩
  rw [htid]
  refine k' _ _ (c.reroot hK' rfl rfl rfl rfl rfl htf hac hB.rseq) (hB.next hK' rfl rfl rfl rfl rfl rfl rfl rfl)
    (c.agreeK hK hA hM) ?_ rfl rfl
  show X.cpu.rip.add len = _
  rw [hrip, addr_add_add]

/-- `syscall` for `set_robust_list (rdi, 24)` from a start with `Base`: `rax` is 0. The run goes on from the state
after, its own start. -/
theorem b_set_robust (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 273)
    (h24 : X.cpu.gpr.rsi.toNat = 24)
    (k' : ∀ s₁ t', Seg prof F Wl L s₁ o → Base s₁ lim b fsb k → Agree F s₁.proc.mm.mem V →
      s₁.cpu.rip = e'.add (j + len) → s₁.cpu.gpr = (sysGpr X len).set 0 0 → s₁.cpu.vec = X.cpu.vec →
      GoG prof L o (gev ++ [sysEv X 0]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  refine ⟨_, _, _, syscall_set_robust (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr h24, ?_⟩
  refine k' _ _ (c.reroot hK' rfl rfl rfl rfl rfl htf hac hB.rseq) (hB.next hK' rfl rfl rfl rfl rfl rfl rfl rfl)
    (c.agreeK hK hA hM) ?_ rfl rfl
  show X.cpu.rip.add len = _
  rw [hrip, addr_add_add]

/-- `syscall` for `rt_sigaction (n, rsi, 0, 8)` from a start with `Base`, the 32 bytes at `rsi` an action that does
not ignore the signal: `rax` is 0. The run goes on from the state after, its own start. -/
theorem b_sigaction (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len n : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 13)
    (h10 : X.cpu.gpr.r10.toNat = 8) (hact : X.cpu.gpr.rsi ≠ 0) (hold : X.cpu.gpr.rdx = 0)
    (hsig : argInt X.cpu.gpr.rdi = (n : Int)) (h1 : 1 ≤ n) (h64 : n ≤ 64) (h9 : n ≠ 9) (h19 : n ≠ 19)
    (htop : X.cpu.gpr.rsi.toNat + 32 ≤ userPtrMax prof.feat) (hl : ∀ i < 32, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hign : (actOf ((byteAddrs X.cpu.gpr.rsi 32).map V)).ignores n = false)
    (k' : ∀ s₁ t', Seg prof F Wl L s₁ o → Base s₁ lim b fsb k → Agree F s₁.proc.mm.mem V →
      s₁.cpu.rip = e'.add (j + len) → s₁.cpu.gpr = (sysGpr X len).set 0 0 → s₁.cpu.vec = X.cpu.vec →
      GoG prof L o (gev ++ [sysEv X 0]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' (c.agreeK hK hA hM) hl
  refine ⟨_, _, _, syscall_sigaction (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr h10 hact hold hsig h1 h64
    h9 h19 htop hrd (hv ▸ hign), ?_⟩
  refine k' _ _ (c.reroot hK' rfl rfl rfl rfl rfl htf hac hB.rseq) (hB.next hK' rfl rfl rfl rfl rfl rfl rfl rfl)
    (c.agreeK hK hA hM) ?_ rfl rfl
  show X.cpu.rip.add len = _
  rw [hrip, addr_add_add]

/-- `syscall` for `rt_sigprocmask (SIG_UNBLOCK, rsi, 0, 8)` from a start with `Base`: `rax` is 0. The run goes on
from the state after, its own start. -/
theorem b_sigunblock (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb k) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 14)
    (h10 : X.cpu.gpr.r10.toNat = 8) (hset : X.cpu.gpr.rsi ≠ 0) (hold : X.cpu.gpr.rdx = 0)
    (hhow : argInt X.cpu.gpr.rdi = 1) (htop : X.cpu.gpr.rsi.toNat + 8 ≤ userPtrMax prof.feat)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (k' : ∀ s₁ t', Seg prof F Wl L s₁ o → Base s₁ lim b fsb k → Agree F s₁.proc.mm.mem V →
      s₁.cpu.rip = e'.add (j + len) → s₁.cpu.gpr = (sysGpr X len).set 0 0 → s₁.cpu.vec = X.cpu.vec →
      GoG prof L o (gev ++ [sysEv X 0]) gP gE s₁ t') :
    GoG prof L o gev gP gE X t := by
  refine c.stepE hK hin hj hrip fun M hM hK' htf hac => ?_
  obtain ⟨hrd, -⟩ := c.load_ok (X := X.withMem M) hK' (c.agreeK hK hA hM) hl
  have htp : (X.withMem M).thread.pending = [] := by rw [hK'.thread]; exact hB.tpend
  have hpp : (X.withMem M).proc.signal.pending = [] := by rw [hK'.proc]; exact hB.ppend
  refine ⟨_, _, _, syscall_sigunblock (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr h10 hset hold hhow htop
    hrd htp hpp, ?_⟩
  refine k' _ _ (c.reroot hK' rfl rfl rfl rfl rfl htf hac hB.rseq) (hB.next hK' rfl rfl rfl rfl rfl rfl rfl rfl)
    (c.agreeK hK hA hM) ?_ rfl rfl
  show X.cpu.rip.add len = _
  rw [hrip, addr_add_add]

/-- `syscall` for `prlimit64 (0, r, 0, r10)`, the 16 bytes at `r10` in what the run may store into: they are the
limit `r` of the run's start, soft then hard; `rax` is 0, `rcx` and `r11` as `syscall` sets them. -/
theorem s_getrlimit (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len r : Nat} (hr : r < 16)
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 302)
    (hpid : argInt X.cpu.gpr.rdi = 0) (hres : arg32 X.cpu.gpr.rsi = r) (hnew : X.cpu.gpr.rdx = 0)
    (hold : X.cpu.gpr.r10 ≠ 0) (htop : X.cpu.gpr.r10.toNat + 16 ≤ userPtrMax prof.feat)
    (hst : ∀ i < 16, Foot Wl (Addr.add X.cpu.gpr.r10 i))
    (k' : ContG prof F Wl L s₀ o (gev ++ [sysEvOut X (s₀.proc.signal.rlimits ⟨r, hr⟩).bytes]) gP gE
      (Vst V X.cpu.gpr.r10 (s₀.proc.signal.rlimits ⟨r, hr⟩).bytes)
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 0) :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf _ => by
    have hlen := Rlimit.bytes_length (s₀.proc.signal.rlimits ⟨r, hr⟩)
    have e : (X.withMem M).proc.signal = s₀.proc.signal := by rw [hK'.proc]
    obtain ⟨hw, hK2, hA2⟩ := c.store_ok (a := X.cpu.gpr.r10) (bs := (s₀.proc.signal.rlimits ⟨r, hr⟩).bytes) hK'
      (c.agreeK hK hA hM) (by rw [hlen]; exact hst)
    rw [hlen] at hw
    refine ⟨_, _, _, syscall_getrlimit (s := X.withMem M) hr htf (c.dec hK' hin hrip hd) hnr hpid hres hnew hold
      htop hw, ?_⟩
    rw [e]
    exact k' _ _ (hK2.nx rfl rfl rfl) hA2 ⟨rip_add hrip M len, rfl⟩

end FV7z.Fn.Seg
