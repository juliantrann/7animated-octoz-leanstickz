import FV7z.Lemmas.SysUname
import FV7z.Lemmas.SysLink
import FV7z.Lemmas.CallFn
/-!
# `write`: the process's bytes go to an open file (PLAN.md §M, M1)

What the instruction `syscall` leaves for `write (fd, buf, count)` on Zellic's model (`sysWrite`, `writeFile`), for an
open file not on the pages of a file (a terminal, a pipe, a socket: `FileMap.isPages` false) and a buffer the process
can read: the kernel reads the `count` bytes and asks the file (`Request.write`); the answer decides the end
(`wrEnd`): some of the bytes taken, an error, or a signal (`SIGPIPE` for a broken pipe, `SIGXFSZ` for a file too big
under a limit), which may end the run.

- `readableLead_all`: a buffer the process can read all of is read whole.
- `writeFile_np`, `syscall_write`: the call, one answer of the stream used.
- `wrEnd_cases`: the end is a return (`WrOk`) or a signal's (`sigEnd`).
- `Seg.stepR`: `step` for an instruction whose run may stop; `Seg.s_write`: the step of a run that `Fn.Seg`
  describes, the buffer in the footprint's data.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- A buffer the process can read all of is read whole by the kernel. -/
theorem readableLead_all {a : Addr} {n : Nat} (h : Readable prof s a n) : readableLead prof.feat s a n = n := by
  have hfr : firstRejected (fun i => (a.add i).canonical prof.feat.la57 &&
      (s.proc.mm.mem.check prof.feat s.cpu.pkru .read (a.add i)).isNone) 0 n = none :=
    firstRejected_none 0 fun i _ hi => by
      obtain ⟨h1, h2⟩ := h (a.add i) (mem_byteAddrs.2 ⟨i, by omega, rfl⟩)
      simp only [h1, h2, Option.isNone_none, Bool.and_self]
  unfold readableLead
  rw [hfr]
  rfl

theorem fsizeLimit_np {f : OpenFile} {n : Nat} {off? : Option Nat} (h : f.map.isPages = false) :
    fsizeLimit s f n off? = Pure.pure (.ok n) := by
  unfold fsizeLimit
  cases hm : f.map <;> first | rfl | simp [hm, FileMap.isPages] at h

theorem writeTarget_np {f : OpenFile} {fs : Files} (h : f.map.isPages = false) : f.writeTarget fs = none := by
  unfold OpenFile.writeTarget
  cases hm : f.map <;> first | rfl | simp [hm, FileMap.isPages] at h

theorem limitChecked_np {f : OpenFile} {fs : Files} (h : f.map.isPages = false) : f.limitChecked fs = false := by
  unfold OpenFile.limitChecked
  cases hm : f.map <;> first | rfl | simp [hm, FileMap.isPages] at h

theorem written_np {f : OpenFile} {tg : Option FileId} {bs : List Byte} {off? : Option Nat}
    (h : f.map.isPages = false) : writeFile.written s f tg bs off? = s := by
  unfold writeFile.written
  cases hm : f.map <;> first | rfl | simp [hm, FileMap.isPages] at h

/-- The end of a `write` that sends the signal `sig` (`SIGPIPE`, `SIGXFSZ`): when the run goes on, the call fails
with `e`. -/
def sigEnd (s : State) (sig : Signal) (e : Nat) : StepResult :=
  match writeSignal s sig with
  | .running s' _ => sysReturn s' (errRet e) [] []
  | r => r

/-- The end of a `write` of the bytes `bs` from `s` for the file's answer, the open file not on the pages of a file:
the first `k` bytes taken, an error, or a signal. -/
def wrEnd (s : State) (bs : List Byte) {n : Nat} : WriteResult n → StepResult
  | .wrote k _ => sysReturn s (BitVec.ofNat 64 k) (bs.take k) []
  | .error e => sysReturn s (errRet e.val) [] []
  | .brokenPipe => sigEnd s Signal.SIGPIPE EPIPE
  | .fileTooBig =>
    if (s.proc.signal.rlimits RLIMIT_FSIZE).cur = RLIM_INFINITY then sysReturn s (errRet EFBIG) [] []
    else sigEnd s Signal.SIGXFSZ EFBIG

theorem answer_np {f : OpenFile} {bs : List Byte} {n : Nat} (hp : f.map.isPages = false) (r : WriteResult n)
    (t : Nat) : (writeFile.answer s f none bs none false false r).runStream o t = (wrEnd s bs r, t) := by
  cases r with
  | wrote k h =>
    simp only [writeFile.answer, wrEnd, Bool.false_and, Bool.false_eq_true, ↓reduceIte, written_np hp]
    rfl
  | error e =>
    simp only [writeFile.answer, wrEnd, Bool.false_eq_true, ↓reduceIte]
    rfl
  | brokenPipe =>
    simp only [writeFile.answer, wrEnd, sigEnd, Bool.false_eq_true, ↓reduceIte]
    cases writeSignal s Signal.SIGPIPE <;> rfl
  | fileTooBig =>
    simp only [writeFile.answer, wrEnd, sigEnd, limitChecked_np hp, Bool.false_eq_true, or_false, ↓reduceIte]
    by_cases hc : (s.proc.signal.rlimits RLIMIT_FSIZE).cur = RLIM_INFINITY
    · simp only [if_pos hc]
      rfl
    · simp only [if_neg hc]
      cases writeSignal s Signal.SIGXFSZ <;> rfl

/-- `writeFile` (`write`, no offset) to an open file not on the pages of a file, from a buffer the process can read
all of: the file's answer to the bytes read decides the end. -/
theorem writeFile_np {f : OpenFile} {buf : Addr} {n : Nat} (hw : f.writable = true) (hp : f.map.isPages = false)
    (hacc : accessOk prof.feat buf n = true) (hn : n ≤ maxRwCount) (hr : Readable prof s buf n) :
    (writeFile prof s f buf n none).runStream o t =
      (wrEnd s (readBytes s.proc.mm.mem buf n) (o t (.write f.id (readBytes s.proc.mm.mem buf n))), t + 1) := by
  unfold writeFile
  simp only [hw, hacc, hp, Bool.not_true, Bool.false_eq_true, false_and, ↓reduceIte, Nat.min_eq_left hn,
    fsizeLimit_np hp, req_pure_bind, growFor_ok (acc := .read) hr, writeTarget_np hp, Option.any_none,
    readableLead_all hr, bne_self_eq_false, eq_self_iff_true]
  show (Req.bind (Req.request (.write f.id (readBytes s.proc.mm.mem buf n))) _).runStream o t = _
  rw [Req.runStream_bind, show (Req.request (Request.write f.id (readBytes s.proc.mm.mem buf n))).runStream o t =
    (o t (.write f.id (readBytes s.proc.mm.mem buf n)), t + 1) from rfl]
  exact answer_np hp _ _

/-- `syscall` for `write (rdi, rsi, rdx)` to an open file not on the pages of a file, `rdx` bytes at `rsi` that the
process can read: `wrEnd` for the file's answer. -/
theorem syscall_write {len : Nat} {f : OpenFile} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 1) (hf : s.proc.files.desc (s.cpu.gpr.rdi.toNat % 2 ^ 32) = some f)
    (hw : f.writable = true) (hp : f.map.isPages = false)
    (hacc : accessOk prof.feat s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat = true) (hn : s.cpu.gpr.rdx.toNat ≤ maxRwCount)
    (hr : Readable prof s s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat) :
    (instruction prof s).runStream o t =
      (wrEnd (nx s len (sysGpr s len) (rf0 s)) (readBytes s.proc.mm.mem s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat)
        (o t (.write f.id (readBytes s.proc.mm.mem s.cpu.gpr.rsi s.cpu.gpr.rdx.toNat))), t + 1) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hfs : (nx s len (sysGpr s len) (rf0 s)).proc.files = s.proc.files := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (1 ≥ 2 ^ 31) by decide, show ¬ (1 ≥ x32Bit) by decide, show ¬ (1 ≥ nrSyscalls) by decide,
    show niSyscall 1 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show (sysWrite prof (nx s len (sysGpr s len) (rf0 s))).runStream o t = _
  unfold sysWrite
  simp only [hrdi, hfs, hf]
  exact writeFile_np hw hp hacc hn hr

/-- What `write` returns from the bytes `bs`, and the bytes it took (`out`): the first `k`, or none with an error. -/
def WrOk (bs : List Byte) (v : BitVec 64) (out : List Byte) : Prop :=
  (∃ k ≤ bs.length, v = BitVec.ofNat 64 k ∧ out = bs.take k) ∨ ∃ e : Nat, v = errRet e ∧ out = []

/-- The end of `write` is a return (`WrOk`) or a signal's. -/
theorem wrEnd_cases (s : State) (bs : List Byte) (r : WriteResult bs.length) :
    (∃ v out, WrOk bs v out ∧ wrEnd s bs r = sysReturn s v out []) ∨
      ∃ (sig : Signal) (e : Nat), wrEnd s bs r = sigEnd s sig e := by
  cases r with
  | wrote k h => exact Or.inl ⟨BitVec.ofNat 64 k, bs.take k, Or.inl ⟨k, h, rfl, rfl⟩, rfl⟩
  | error e => exact Or.inl ⟨errRet e.val, [], Or.inr ⟨e.val, rfl, rfl⟩, rfl⟩
  | brokenPipe => exact Or.inr ⟨Signal.SIGPIPE, EPIPE, rfl⟩
  | fileTooBig =>
    by_cases hc : (s.proc.signal.rlimits RLIMIT_FSIZE).cur = RLIM_INFINITY
    · exact Or.inl ⟨errRet EFBIG, [], Or.inr ⟨EFBIG, rfl, rfl⟩, if_pos hc⟩
    · exact Or.inr ⟨Signal.SIGXFSZ, EFBIG, if_neg hc⟩

/-- The event of `write` from registers `g`, returning `v`, the bytes `out` taken. -/
abbrev wrEv (g : Gprs) (v : BitVec 64) (out : List Byte) : Event :=
  ⟨g.rax, [g.rdi, g.rsi, g.rdx, g.r10, g.r8, g.r9], v, out, []⟩

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `step` for an instruction whose run may go on or stop. -/
theorem stepR (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → KeptW Wl s₀ (X.withMem M) →
      X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ r t', (instruction prof (X.withMem M)).runStream o (t + 1) = (r, t') ∧
        match r with
        | .running Y ev => GoG prof L o (gev ++ ev.toList) gP gE Y t'
        | .stopped out => gE out gev) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨-, M, hkd, hc⟩ := envEvents_quiet prof.feat (evsAt prof o t) X (c.quiet hK)
    fun e he => c.env t prof.cpus e he
  obtain ⟨r, t', hr, k⟩ := h M hc (hK.withMem hc) (hK.tf.trans c.ready.plain.1) (hK.ac.trans c.ready.plain.2.1)
  have hs : (step prof X).runStream o t = (r, t') := by
    rw [step_runStream prof o t X c.env (c.quiet hK), hkd, hr]
  cases r with
  | running Y ev => exact runsFrom_step (inCode_of_codeIn hin hj hrip) hs k
  | stopped out => exact runsFrom_stop (inCode_of_codeIn hin hj hrip) hs k

/-- `syscall` for `write (rdi, rsi, rdx)` to an open file `f` not on the pages of a file, the `rdx` bytes at `rsi` in
the footprint's data: the run goes on with what the file took (`WrOk`, `kw`), or ends as the signal it sends
(`SIGPIPE`, `SIGXFSZ`) decides (`kp`). -/
theorem s_write (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len)) (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 1) {f : OpenFile}
    (hf : s₀.proc.files.desc (X.cpu.gpr.rdi.toNat % 2 ^ 32) = some f) (hw : f.writable = true)
    (hp : f.map.isPages = false) (hacc : accessOk prof.feat X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat = true)
    (hn : X.cpu.gpr.rdx.toNat ≤ maxRwCount) (hb : ∀ i < X.cpu.gpr.rdx.toNat, Foot F.data (X.cpu.gpr.rsi.add i))
    (kw : ∀ v out, WrOk ((byteAddrs X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat).map V) v out →
      ContG prof F Wl L s₀ o (gev ++ [wrEv X.cpu.gpr v out]) gP gE V fun Y =>
        Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = (sysGpr X len).set 0 v)
    (kp : ∀ (sig : Signal) (e : Nat) (M : Memory) (t' : Nat), KeptW Wl s₀ (X.withMem M) → Agree F M V →
      match sigEnd (nx (X.withMem M) len (sysGpr X len) (rf0 X)) sig e with
      | .running Y ev => GoG prof L o (gev ++ ev.toList) gP gE Y t'
      | .stopped out => gE out gev) :
    GoG prof L o gev gP gE X t :=
  c.stepR hK hin hj hrip fun M hM hK' htf _ => by
    have hA' := c.agreeK hK hA hM
    obtain ⟨hr, hbs⟩ := c.load_ok hK' hA' hb
    have hf' : (X.withMem M).proc.files.desc ((X.withMem M).cpu.gpr.rdi.toNat % 2 ^ 32) = some f := by
      rw [hK'.proc]
      exact hf
    have hbs' : readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi (X.withMem M).cpu.gpr.rdx.toNat =
        (byteAddrs X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat).map V := hbs
    refine ⟨_, _, syscall_write (s := X.withMem M) htf (c.dec hK' hin hrip hd) hnr hf' hw hp hacc hn hr, ?_⟩
    rcases wrEnd_cases (nx (X.withMem M) len (sysGpr (X.withMem M) len) (rf0 (X.withMem M)))
        (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi (X.withMem M).cpu.gpr.rdx.toNat)
        (o (t + 1) (.write f.id (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsi
          (X.withMem M).cpu.gpr.rdx.toNat))) with
      ⟨v, out, hv, he⟩ | ⟨sig, e, he⟩
    · rw [he]
      rw [hbs'] at hv
      show GoG prof L o (gev ++ [wrEv X.cpu.gpr v out]) gP gE (sysSt (X.withMem M) len v) (t + 1 + 1)
      exact kw v out hv _ _ (hK'.nx rfl rfl rfl) hA' ⟨rip_add hrip M len, rfl⟩
    · rw [he]
      exact kp sig e M _ hK' hA'

end FV7z.Fn.Seg
