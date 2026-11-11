import FV7z.Lemmas.KeptW
import FV7z.Lemmas.LeafSteps
/-!
# A call of a function with a stack frame and an output (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

`Leaf.lean` for the contract `fn k W R pre post`: the System V convention, a stack of `k` bytes below the return
address's slot (`frame s k`), output regions `W`, regions read `R`, no system call, a postcondition on the state the
return leaves. The run may store into the stack below the slot and into `W` (`KeptW (ws k W s₀)`); the slot itself
it must leave alone (`Call.slot`, from the precondition: `W` apart from it).

The code of each step is given at the step (a segment `code` at `e` of the code segments `L`, `CodeIn L e code`), not
fixed by the call: the run may go through a callee's code, whose run the caller's proof follows step by step, with
its own invariant (a callee's lemma in the caller's terms), rather than through the callee's `ImplementsCall`, whose
frame condition is weaker than `KeptW`.
-/
namespace FV7z.Fn
open ZellicX86 Decode FV7z.Leaf

/-- A function with a stack of `k` bytes below its return address, writing `W` and reading `R` at the call, no system
call, `pre` at the call and `post` of the call's state and the return's. -/
def fn (k : Nat) (W R : State → List Rgn) (pre : State → Prop) (post : State → State → Prop) : Contract where
  conv := sysv
  reads := R
  writes s := frame s k :: W s
  pre := pre
  post := post
  events _ _ evs := evs = []

/-- The stack below the return address's slot: the `k` bytes from `rsp - k`. -/
def below (s : State) (k : Nat) : Rgn := ⟨s.cpu.gpr.rsp - BitVec.ofNat 64 k, k⟩

/-- What the run may store into: the stack below the slot, and `W`. -/
abbrev ws (k : Nat) (W : State → List Rgn) (s₀ : State) : List Rgn := below s₀ k :: W s₀

theorem below_frame {s : State} {k : Nat} {y : Addr} (h : (below s k).Mem y) : (frame s k).Mem y := by
  simp only [below, frame, Rgn.Mem] at h ⊢; omega

variable {k : Nat} {W R : State → List Rgn} {pre : State → Prop} {post : State → State → Prop}

/-- What every step of a run from `s₀` uses, a call's or a stretch of code inlined in another function's: the
footprint `F` at `s₀` (with code segments `L`, owning nothing), the environment, and what the run may store into, `Wl`,
written regions of `F`. -/
structure Seg (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) : Prop where
  foot : F.Ok prof.feat s₀
  ready : Ready prof.feat s₀
  env : Undisturbed o
  code : F.code = L
  own : F.own = []
  hww : ∀ y, Foot Wl y → ∃ q ∈ F.writes, q.Mem y

/-- The rest of the run, from `X` with answers from position `t` and the events `gev` so far, reaches the goal `gP`,
or ends as `gE` says, its `rip` in the code until then. -/
abbrev GoG (prof : Profile) (L : List (Addr × List Byte)) (o : Oracle) (gev : List Event)
    (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (X : State) (t : Nat) : Prop :=
  RunsFrom prof o (InCode L) gev X t gP gE

/-- The footprint of the call. -/
abbrev fp (k : Nat) (W R : State → List Rgn) (pre : State → Prop) (post : State → State → Prop)
    (L : List (Addr × List Byte)) (s₀ : State) : Footprint := (fn k W R pre post).footprint L s₀

/-- What every step of a run of a call uses: the call at `e`, the environment, and `W` apart from the return
address's slot. -/
structure Call (prof : Profile) (k : Nat) (W R : State → List Rgn) (pre : State → Prop) (post : State → State → Prop)
    (e : Addr) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) : Prop
    extends Seg prof (fp k W R pre post L s₀) (ws k W s₀) L s₀ o where
  call : CallOf prof e L (fn k W R pre post) s₀ ra
  slot : ∀ i < 8, ¬ Foot (W s₀) (Addr.add s₀.cpu.gpr.rsp i)

/-- The rest of the run, from `X` with answers from position `t`, returns as the contract says, its `rip` in the
code until then. -/
abbrev Go (prof : Profile) (k : Nat) (W R : State → List Rgn) (pre : State → Prop) (post : State → State → Prop)
    (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (X : State) (t : Nat) : Prop :=
  RunsFrom prof o (InCode L) [] X t (fun Y _ evs => Returned prof.feat (fn k W R pre post) s₀ ra Y evs)
    ((fn k W R pre post).ends s₀)

variable {prof : Profile} {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}
  {F : Footprint} {Wl : List Rgn} {gev : List Event} {gP : State → Nat → List Event → Prop}
  {gE : Outcome → List Event → Prop}

/-- A call, from its `CallOf`, its environment, and `W` apart from the return address's slot. -/
theorem Call.of (hcall : CallOf prof e L (fn k W R pre post) s₀ ra) (ho : Undisturbed o)
    (hslot : ∀ i < 8, ¬ Foot (W s₀) (Addr.add s₀.cpu.gpr.rsp i)) : Call prof k W R pre post e L s₀ ra o where
  foot := hcall.foot
  ready := hcall.ready
  env := ho
  code := rfl
  own := by simp [Contract.footprint, fn, Layout.owned]
  hww := by
    rintro y ⟨r, hr, hm⟩
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨frame s₀ k, by simp [Contract.footprint, fn], below_frame hm⟩
    · exact ⟨r, by simp [Contract.footprint, fn, hr], hm⟩
  call := hcall
  slot := hslot

namespace Seg

/-- What the run may store into is data of the footprint. -/
theorem hws (c : Seg prof F Wl L s₀ o) : ∀ y, Foot Wl y → Foot F.data y := by
  intro y hy
  obtain ⟨q, hq, hm⟩ := c.hww y hy
  exact ⟨q, by simp [Footprint.data, hq], hm⟩

/-- The code segments' bytes, at every state the run keeps. -/
theorem codeAt (c : Seg prof F Wl L s₀ o) {X : State} (hK : KeptW Wl s₀ X) {e' : Addr} {code : List Byte}
    (hin : CodeIn L e' code) : CodeAt prof.feat X.cpu.pkru X.proc.mm.mem e' code :=
  hK.codeAt c.foot c.ready.rseq c.hws (c.code ▸ hin)

/-- The instruction at the `j`-th byte of a code segment, from a state that `KeptW` relates to `s₀`. -/
theorem dec (c : Seg prof F Wl L s₀ o) {X : State} (hK : KeptW Wl s₀ X) {e' : Addr}
    {code : List Byte} (hin : CodeIn L e' code) {j : Nat} (hrip : X.cpu.rip = e'.add j) {i : Inst}
    (hd : Dec prof.feat code j i) : Decode.decode prof.feat (fetchByte prof.feat X) = .ok i :=
  decode_of_window (fetchByte_code (c.codeAt hK hin) hrip) (hd _)

/-- The `rseq` area is quiet at every state the run keeps. -/
theorem quiet (c : Seg prof F Wl L s₀ o) {X : State} (hK : KeptW Wl s₀ X) : Quiet prof.feat X :=
  hK.quiet c.foot c.ready.rseq c.hws (quiet_of_rseqQuiet c.ready.rseq c.foot.noAlias)

/-- A step: the instruction at the `j`-th byte of a code segment, from every state the kernel's ordinary events may
leave. -/
theorem step (c : Seg prof F Wl L s₀ o) {X : State} {t j : Nat} (hK : KeptW Wl s₀ X)
    {e' : Addr} {code : List Byte} (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → KeptW Wl s₀ (X.withMem M) →
      X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ Y t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧
        GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine runsFrom_insQ c.env (c.quiet hK) (inCode_of_codeIn hin hj hrip) fun M hM => ?_
  exact h M hM (hK.withMem hM) (hK.tf.trans c.ready.plain.1) (hK.ac.trans c.ready.plain.2.1)

end Seg

namespace Call

/-- The frame fits. -/
theorem frame_fits (c : Call prof k W R pre post e L s₀ ra o) : (frame s₀ k).Fits :=
  c.foot.fits (frame s₀ k) (by simp [Footprint.data, Contract.footprint, fn])

/-- A frame that fits lies below `rsp`, with the return address's slot. -/
theorem frame_arith {s : State} {k : Nat} (hf : (frame s k).Fits) :
    (s.cpu.gpr.rsp - BitVec.ofNat 64 k).toNat + k = s.cpu.gpr.rsp.toNat ∧ s.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 := by
  simp only [frame, Rgn.Fits] at hf
  have hk : k < 2 ^ 64 := by omega
  have hb := s.cpu.gpr.rsp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at hf ⊢
  by_cases h : k ≤ s.cpu.gpr.rsp.toNat
  · rw [show 2 ^ 64 - k + s.cpu.gpr.rsp.toNat = (s.cpu.gpr.rsp.toNat - k) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)] at hf ⊢
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hf
    omega

/-- The `i`-th byte of the return address's slot is the `k + i`-th of the frame. -/
theorem slot_mem (c : Call prof k W R pre post e L s₀ ra o) {i : Nat} (hi : i < 8) :
    (frame s₀ k).Mem (Addr.add s₀.cpu.gpr.rsp i) := by
  obtain ⟨h1, h2⟩ := frame_arith c.frame_fits
  simp only [frame, Rgn.Mem, toNat_add_of_fits hi h2]
  omega

/-- The slot's bytes lie in the footprint. -/
theorem slot_foot (c : Call prof k W R pre post e L s₀ ra o) {i : Nat} (hi : i < 8) :
    Foot ((fp k W R pre post L s₀).data ++ (fp k W R pre post L s₀).codeRgns) (Addr.add s₀.cpu.gpr.rsp i) :=
  ⟨frame s₀ k, by simp [Footprint.data, Contract.footprint, fn], c.slot_mem hi⟩

/-- The run stores into no byte of the slot. -/
theorem slot_not (c : Call prof k W R pre post e L s₀ ra o) {i : Nat} (hi : i < 8) :
    ¬ Foot (ws k W s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
  rintro ⟨r, hr, hm⟩
  simp only [List.mem_cons] at hr
  rcases hr with rfl | hr
  · obtain ⟨h1, h2⟩ := frame_arith c.frame_fits
    simp only [below, Rgn.Mem, toNat_add_of_fits hi h2] at hm
    omega
  · exact c.slot i hi ⟨r, hr, hm⟩

/-- The return address's slot can be read. -/
theorem slot_read (c : Call prof k W R pre post e L s₀ ra o) {X : State} (hK : KeptW (ws k W s₀) s₀ X)
    (hC : Callee s₀ X) : Readable prof X X.cpu.gpr.rsp 8 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  have hw := c.foot.writable (frame s₀ k) (by simp [Contract.footprint, fn]) (Addr.add s₀.cpu.gpr.rsp i)
    (c.slot_mem hi)
  rw [hC.2.1, hK.calm.check, hK.pkru]
  exact ⟨hw.1, check_read_of_write hw.2⟩

/-- The return address, as the slot holds it. -/
theorem slot_word (c : Call prof k W R pre post e L s₀ ra o) {X : State} (hK : KeptW (ws k W s₀) s₀ X)
    (hC : Callee s₀ X) : ofBytesLE 64 (readBytes X.proc.mm.mem X.cpu.gpr.rsp 8) = ra := by
  rw [hC.2.1, hK.calm.readBytes_apart c.foot c.ready.rseq c.hws (fun i hi => c.slot_foot hi)
    (fun i hi => c.slot_not hi)]
  exact c.call.shape.2.1

/-- The state `ret` leaves, from a state that kept the call's frame and callee-saved registers, is a return as the
contract says, if it satisfies the postcondition. -/
theorem returned (c : Call prof k W R pre post e L s₀ ra o) {X : State} (hK : KeptW (ws k W s₀) s₀ X)
    (hC : Callee s₀ X)
    (hpost : post s₀ (upd X ra (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) { X.cpu.rflags with rf := false })) :
    Returned prof.feat (fn k W R pre post) s₀ ra
      (upd X ra (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) { X.cpu.rflags with rf := false }) [] := by
  have hK' : KeptW (ws k W s₀) s₀ (upd X ra (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) { X.cpu.rflags with rf := false }) :=
    hK.upd rfl rfl rfl
  obtain ⟨-, -, -, -, hdf, hx87⟩ := c.call.shape
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hK'.keepsEnv, hK'.keepsSettings c.ready.plain, hK'.keepsProc,
    hK'.keepsFiles, hK'.changesOnly fun y hy => ?_⟩, hpost, rfl⟩
  · intro r hr
    simp only [fn, sysv, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hC.1
    · exact hC.2.2.1
    · exact hC.2.2.2.1
    · exact hC.2.2.2.2.1
    · exact hC.2.2.2.2.2.1
    · exact hC.2.2.2.2.2.2
  · show X.cpu.gpr.rsp + 8 = _
    rw [hC.2.1]
  · exact hK.df.trans hdf
  · exact hK.x87 ▸ hx87
  · show X.cpu.vec.mxcsr >>> 6 = _
    rw [hK.mxcsr]
  · show X.cpu.x87.fcw = _
    rw [hK.x87]
  · rcases hy with hy | ⟨r, hr, hm⟩
    · obtain ⟨r, hr, hm⟩ := IdAddr.foot_ids (RseqQuiet.fits c.ready.rseq) hy
      exact ⟨r, List.mem_append_right _ hr, hm⟩
    · simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨frame s₀ k, by simp [Contract.footprint, fn], below_frame hm⟩
      · exact ⟨r, by simp [Contract.footprint, fn, hr], hm⟩

/-- `ret`, at the `j`-th byte of a code segment, from a state that kept the call's frame and callee-saved registers,
if the state it leaves satisfies the postcondition. -/
theorem ret (c : Call prof k W R pre post e L s₀ ra o) {X : State} {t j : Nat} (hK : KeptW (ws k W s₀) s₀ X)
    (hC : Callee s₀ X) {e' : Addr} {code : List Byte} (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) (hd : Dec prof.feat code j (FV7z.mk .ret 64 [] 1))
    (hpost : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M →
      post s₀ (upd (X.withMem M) ra ((X.withMem M).cpu.gpr.set 4 ((X.withMem M).cpu.gpr.rsp + 8))
        { (X.withMem M).cpu.rflags with rf := false })) :
    Go prof k W R pre post L s₀ ra o X t :=
  c.step hK hin hj hrip fun M hM hK' htf hac =>
    ⟨_, _, FV7z.ret htf hac (c.dec hK' hin hrip hd) (by rw [hK'.thread]; exact c.ready.plain.2.2.1)
      (c.slot_word hK' hC) c.call.shape.2.2.1 (c.slot_read hK' hC),
      runsFrom_done (c.returned hK' hC (hpost M hM))⟩

end Call

end FV7z.Fn
