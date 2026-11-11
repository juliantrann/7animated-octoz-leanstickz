import FV7z.Lemmas.Ins
import FV7z.Memcmp.Order
/-!
# A call of `memcmp`, whatever its code (PLAN.md G2.1)

What every proof that some code implements `Memcmp.contract` uses at each step of the call's run, the code `code`
given: a step from a state that `Kept` relates to the call's (`Call.step`), the instruction it decodes to there
(`Call.dec`, from a fact `Dec` that evaluating the decoder on the code proves), the strings' bytes (`Call.read`), and
the return (`Call.ret`). Generalizes the run part of `Memcmp/GccOs.lean` (G2.0) to any code.
-/
namespace FV7z.MemcmpCall
open ZellicX86 Decode Memcmp

/-- The code decodes, on a processor with features `feat`, at its `k`-th byte to `i`, whatever bytes follow it. -/
def Dec (feat : Features) (code : List Byte) (k : Nat) (i : Inst) : Prop :=
  ∀ f : Nat → Option Byte, Decode.decode feat (fetchFrom (code.drop k) f) = .ok i

/-- The callee-saved registers and `rsp` as at the call. -/
def Callee (s₀ X : State) : Prop :=
  X.cpu.gpr.rbx = s₀.cpu.gpr.rbx ∧ X.cpu.gpr.rsp = s₀.cpu.gpr.rsp ∧ X.cpu.gpr.rbp = s₀.cpu.gpr.rbp ∧
    X.cpu.gpr.r12 = s₀.cpu.gpr.r12 ∧ X.cpu.gpr.r13 = s₀.cpu.gpr.r13 ∧ X.cpu.gpr.r14 = s₀.cpu.gpr.r14 ∧
    X.cpu.gpr.r15 = s₀.cpu.gpr.r15

/-- What every step of a run of a call uses: the call, where its code lies, the environment. -/
structure Call (prof : Profile) (code : List Byte) (e : Addr) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr)
    (o : Oracle) : Prop where
  call : CallOf prof e L contract s₀ ra
  code : CodeIn L e code
  env : Undisturbed o

/-- The rest of the run, from `X` with answers from position `t`, returns as `memcmp`'s contract says, its `rip` in
the code until then. -/
abbrev Go (prof : Profile) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (X : State)
    (t : Nat) : Prop :=
  RunsFrom prof o (InCode L) [] X t (fun Y _ evs => Returned prof.feat contract s₀ ra Y evs) (contract.ends s₀)

variable {prof : Profile} {code : List Byte} {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr}
  {o : Oracle}

namespace Call

/-- The instruction at the code's `j`-th byte, from a state that `Kept` relates to the call's. -/
theorem dec (c : Call prof code e L s₀ ra o) {X : State} (hK : Kept s₀ X) {j : Nat} (hrip : X.cpu.rip = e.add j)
    {i : Inst} (hd : Dec prof.feat code j i) : Decode.decode prof.feat (fetchByte prof.feat X) = .ok i :=
  decode_of_window (fetchByte_code (hK.codeAt c.call.foot c.call.ready.rseq c.code) hrip) (hd _)

/-- A step: the instruction at the code's `j`-th byte, from every state the kernel's ordinary events may leave. -/
theorem step (c : Call prof code e L s₀ ra o) {X : State} {t j : Nat} (hK : Kept s₀ X) (hj : j < code.length)
    (hrip : X.cpu.rip = e.add j)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → Kept s₀ (X.withMem M) →
      X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ Y t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧
        Go prof L s₀ ra o Y t') :
    Go prof L s₀ ra o X t := by
  refine runsFrom_ins c.env (quiet_of_rseqQuiet c.call.ready.rseq c.call.foot.noAlias) hK
    (inCode_of_codeIn c.code hj hrip) fun M hM => ?_
  exact h M hM (hK.withMem hM) (hK.tf.trans c.call.ready.plain.1) (hK.ac.trans c.call.ready.plain.2.1)

/-- The bytes of the return address's slot lie in the footprint. -/
theorem slot (c : Call prof code e L s₀ ra o) {i : Nat} (hi : i < 8) :
    Foot ((contract.footprint L s₀).data ++ (contract.footprint L s₀).codeRgns) (s₀.cpu.gpr.rsp.add i) := by
  have hf := c.call.foot.fits (frame s₀ 0) (by simp [Footprint.data, Contract.footprint, contract])
  simp only [frame, Rgn.Fits, BitVec.sub_zero] at hf
  refine ⟨frame s₀ 0, by simp [Footprint.data, Contract.footprint, contract], ?_⟩
  simp only [frame, BitVec.sub_zero]
  exact mem_add_of_fits hi hf

/-- The return address's slot can be read. -/
theorem slot_read (c : Call prof code e L s₀ ra o) {X : State} (hK : Kept s₀ X) (hC : Callee s₀ X) :
    Readable prof X X.cpu.gpr.rsp 8 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  have hw := c.call.foot.writable (frame s₀ 0) (by simp [Contract.footprint, contract]) (s₀.cpu.gpr.rsp.add i) (by
    have hf := c.call.foot.fits (frame s₀ 0) (by simp [Footprint.data, Contract.footprint, contract])
    simp only [frame, Rgn.Fits, BitVec.sub_zero] at hf ⊢
    exact mem_add_of_fits hi hf)
  rw [hC.2.1, hK.calm.check, hK.pkru]
  exact ⟨hw.1, check_read_of_write hw.2⟩

/-- The return address, as the slot holds it. -/
theorem slot_word (c : Call prof code e L s₀ ra o) {X : State} (hK : Kept s₀ X) (hC : Callee s₀ X) :
    ofBytesLE 64 (readBytes X.proc.mm.mem X.cpu.gpr.rsp 8) = ra := by
  rw [hC.2.1, hK.calm.readBytes_foot c.call.foot c.call.ready.rseq fun i hi => c.slot hi]
  exact c.call.shape.2.1

/-- The state `ret` leaves, from a state that kept the call's frame and callee-saved registers and holds `memcmp`'s
result, is a return as the contract says. -/
theorem returned (c : Call prof code e L s₀ ra o) {X : State} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hpost : contract.post s₀ X) :
    Returned prof.feat contract s₀ ra
      (upd X ra (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) { X.cpu.rflags with rf := false }) [] := by
  have hK' : Kept s₀ (upd X ra (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) { X.cpu.rflags with rf := false }) :=
    hK.upd rfl rfl rfl
  obtain ⟨-, -, -, -, hdf, hx87⟩ := c.call.shape
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hK'.keepsEnv, hK'.keepsSettings c.call.ready.plain, hK'.keepsProc,
    hK'.keepsFiles, hK'.changesOnly fun y hy => ?_⟩, hpost, rfl⟩
  · intro r hr
    simp only [contract, sysv, List.mem_cons, List.mem_nil_iff, or_false] at hr
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
  · obtain ⟨r, hr, hm⟩ := IdAddr.foot_ids (RseqQuiet.fits c.call.ready.rseq) hy
    exact ⟨r, List.mem_append_right _ hr, hm⟩

/-- `ret`, at the code's `k`-th byte, from a state that kept the call's frame and callee-saved registers and holds
`memcmp`'s result. -/
theorem ret (c : Call prof code e L s₀ ra o) {X : State} {t k : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hk : k < code.length) (hrip : X.cpu.rip = e.add k) (hd : Dec prof.feat code k (FV7z.mk .ret 64 [] 1))
    (hpost : contract.post s₀ X) : Go prof L s₀ ra o X t :=
  c.step hK hk hrip fun M _ hK' htf hac =>
    ⟨_, _, FV7z.ret htf hac (c.dec hK' hrip hd) (by rw [hK'.thread]; exact c.call.ready.plain.2.2.1)
      (c.slot_word hK' hC) c.call.shape.2.2.1 (c.slot_read hK' hC),
      runsFrom_done (c.returned hK' hC hpost)⟩

/-- The `i`-th byte of either string lies in the footprint, readable. -/
theorem str (c : Call prof code e L s₀ ra o) {r : Rgn} (hr : r ∈ strings s₀) {i : Nat} (hi : i < r.len) :
    Foot ((contract.footprint L s₀).data ++ (contract.footprint L s₀).codeRgns) (r.base.add i) ∧
      (r.base.add i).canonical prof.feat.la57 = true ∧
      s₀.proc.mm.mem.check prof.feat s₀.cpu.pkru .read (r.base.add i) = none := by
  have hr' : r ∈ (contract.footprint L s₀).reads := hr
  have hf := c.call.foot.fits r (by simp [Footprint.data, hr'])
  have hm : r.Mem (r.base.add i) := mem_add_of_fits hi hf
  exact ⟨⟨r, by simp [Footprint.data, hr'], hm⟩, c.call.foot.readable r hr' _ hm⟩

/-- The bytes `a` to `a + n - 1` of either string can be read, and are as at the call. -/
theorem read (c : Call prof code e L s₀ ra o) {X : State} (hK : Kept s₀ X) {r : Rgn} (hr : r ∈ strings s₀)
    {a n : Nat} (h : a + n ≤ r.len) :
    Readable prof X (r.base.add a) n ∧
      readBytes X.proc.mm.mem (r.base.add a) n = readBytes s₀.proc.mm.mem (r.base.add a) n := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hx
    obtain ⟨-, hcan, hck⟩ := c.str hr (i := a + j) (by omega)
    rw [addr_add_add, hK.calm.check, hK.pkru]
    exact ⟨hcan, hck⟩
  · refine hK.calm.readBytes_foot c.call.foot c.call.ready.rseq fun j hj => ?_
    rw [addr_add_add]
    exact (c.str hr (i := a + j) (by omega)).1

/-- The first string, `rdi` at the call. -/
theorem mem₁ : (⟨s₀.cpu.gpr.rdi, s₀.cpu.gpr.rdx.toNat⟩ : Rgn) ∈ strings s₀ := by simp [strings]
/-- The second string, `rsi` at the call. -/
theorem mem₂ : (⟨s₀.cpu.gpr.rsi, s₀.cpu.gpr.rdx.toNat⟩ : Rgn) ∈ strings s₀ := by simp [strings]

end Call

end FV7z.MemcmpCall
