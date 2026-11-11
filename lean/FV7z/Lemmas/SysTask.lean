import FV7z.Lemmas.SysUname
/-!
# System calls of a thread library's startup (PLAN.md G3, startup)

What the instruction `syscall` leaves, on Zellic's model, for the calls glibc's `__pthread_initialize_minimal` makes:

- `accessOk_le`, `copyIn_ok`: `copy_from_user` of a range below the end of the user address space, all readable,
  gives its bytes.
- `syscall_set_tid`: `set_tid_address (a)`: the kernel records `a`; the thread's id in `rax`.
- `syscall_set_robust`: `set_robust_list (a, 24)`: the kernel records `a`; `rax` is 0.
- `syscall_sigaction`: `rt_sigaction (n, act, 0, 8)` with an action that does not ignore the signal: the kernel
  stores the action (`actOf` of its 32 bytes); `rax` is 0.
- `nextIn_nil`, `nextSignal_quiet`, `deliverSignals_quiet`: with no entry in the thread's set of waiting signals or
  the process's, the kernel takes no signal, and a return to user mode delivers none.
- `syscall_sigunblock`: `rt_sigprocmask (SIG_UNBLOCK, set, 0, 8)` with no signal waiting: the set's signals leave
  the mask; `rax` is 0.
- `syscall_getrlimit`: `prlimit64 (0, r, 0, old)`: the limit's 16 bytes are at `old`; `rax` is 0.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

theorem accessOk_le {a : Addr} {n : Nat} (h : a.toNat + n ≤ userPtrMax prof.feat) :
    accessOk prof.feat a n = true := by
  have h47 : userPtrMax prof.feat ≤ 2 ^ 56 := by unfold userPtrMax; split <;> decide
  have e : (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  simp only [accessOk, e, decide_eq_true_eq, Bool.and_eq_true]
  omega

/-- `copy_from_user` of a range that passes `access_ok` and is all readable. -/
theorem copyIn_ok {a : Addr} {n : Nat} (hacc : accessOk prof.feat a n = true)
    (h : ∀ x ∈ byteAddrs a n, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none) :
    copyIn prof s a n = Pure.pure (s, some (readBytes s.proc.mm.mem a n)) := by
  have hk : kernelRead prof.feat s a n = some (readBytes s.proc.mm.mem a n) := by
    unfold kernelRead kernelReadable
    rw [ite_eq_left]
    simp only [List.all_eq_true, Bool.and_eq_true, Option.isNone_iff_eq_none]
    exact h
  unfold copyIn
  simp only [hacc, Bool.not_true, Bool.false_eq_true, ↓reduceIte, growFor_ok h]
  show (Pure.pure (s, kernelRead prof.feat s a n) : Req (State × Option (List Byte))) = _
  rw [hk]

/-- `set_tid_address (a)`: the kernel records `a`; the thread's id in `rax`. -/
theorem syscall_set_tid {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 218) :
    (instruction prof s).runStream o t =
      (.running (sysSt (s.modThread fun th => { th with clearChildTid := s.cpu.gpr.rdi }) len
        (BitVec.ofNat 64 s.thread.tid)) (some (sysEv s (BitVec.ofNat 64 s.thread.tid))), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (218 ≥ 2 ^ 31) by decide, show ¬ (218 ≥ x32Bit) by decide, show ¬ (218 ≥ nrSyscalls) by decide,
    show niSyscall 218 = false by decide, ↓reduceIte, Bool.false_eq_true]
  rfl

/-- `set_robust_list (a, 24)`: the kernel records `a`; `rax` is 0. -/
theorem syscall_set_robust {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 273) (h24 : s.cpu.gpr.rsi.toNat = 24) :
    (instruction prof s).runStream o t =
      (.running (sysSt (s.modThread fun th => { th with robustList := s.cpu.gpr.rdi }) len 0)
        (some (sysEv s 0)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (273 ≥ 2 ^ 31) by decide, show ¬ (273 ≥ x32Bit) by decide, show ¬ (273 ≥ nrSyscalls) by decide,
    show niSyscall 273 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysSetRobustList
  simp only [hrsi, h24, ne_eq, not_true_eq_false, ↓reduceIte]
  rfl

/-- The action `rt_sigaction` stores for the 32 bytes `bs` of a `struct sigaction`: with the flags the kernel knows,
its mask without `SIGKILL` and `SIGSTOP`. -/
def actOf (bs : List Byte) : SigAction :=
  { SigAction.ofBytes bs with
    flags := (SigAction.ofBytes bs).flags &&& uapiSaFlags, mask := (SigAction.ofBytes bs).mask.unblockable }

/-- `rt_sigaction (n, act, 0, 8)` for a signal `n` other than `SIGKILL` and `SIGSTOP`, with an action that does not
ignore it: the kernel stores the action; `rax` is 0. -/
theorem syscall_sigaction {len n : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 13) (h10 : s.cpu.gpr.r10.toNat = 8) (hact : s.cpu.gpr.rsi ≠ 0)
    (hold : s.cpu.gpr.rdx = 0) (hsig : argInt s.cpu.gpr.rdi = (n : Int)) (h1 : 1 ≤ n) (h64 : n ≤ 64) (h9 : n ≠ 9)
    (h19 : n ≠ 19) (htop : s.cpu.gpr.rsi.toNat + 32 ≤ userPtrMax prof.feat)
    (hr : ∀ x ∈ byteAddrs s.cpu.gpr.rsi 32, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none)
    (hign : (actOf (readBytes s.proc.mm.mem s.cpu.gpr.rsi 32)).ignores n = false) :
    (instruction prof s).runStream o t =
      (.running (sysSt (s.setAction n (actOf (readBytes s.proc.mm.mem s.cpu.gpr.rsi 32))) len 0)
        (some (sysEv s 0)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hrdx : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdx = s.cpu.gpr.rdx := rfl
  have hr10 : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.r10 = s.cpu.gpr.r10 := rfl
  have hci := copyIn_ok (s := nx s len (sysGpr s len) (rf0 s)) (accessOk_le htop) hr
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (13 ≥ 2 ^ 31) by decide, show ¬ (13 ≥ x32Bit) by decide, show ¬ (13 ≥ nrSyscalls) by decide,
    show niSyscall 13 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysRtSigaction
  simp only [hrdi, hrsi, hrdx, hr10, h10, hact, ne_eq, not_true_eq_false, ↓reduceIte, hci]
  have e1 : ¬ ((n : Int) < 1) := by omega
  have e2 : ¬ (64 < (n : Int)) := by omega
  have e3 : ¬ ((n : Int) = ((9 : Nat) : Int)) := by omega
  have e4 : ¬ ((n : Int) = ((19 : Nat) : Int)) := by omega
  simp only [bind, pure, Req.bind, Option.map, hsig, hold, e1, e2, e3, e4, Signal.SIGKILL, Signal.SIGSTOP,
    Int.toNat_natCast, or_self, and_false, ↓reduceIte]
  have hni : ¬ ((actOf (readBytes s.proc.mm.mem s.cpu.gpr.rsi 32)).ignores n = true) := by
    rw [hign]
    decide
  show Req.runStream o (Req.pure (sysReturn
    (if (actOf (readBytes s.proc.mm.mem s.cpu.gpr.rsi 32)).ignores n = true then _ else _) 0 [] [])) t = _
  simp only [hni]
  rfl

theorem nextIn_nil (mask : SigSet) : nextIn [] mask = none := by
  have h0 : SigPending.set [] = 0 := rfl
  have hf : ((List.range 64).map (· + 1)).filter (SigSet.mem (0 &&& ~~~mask)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a _
    simp [SigSet.mem]
  unfold nextIn
  simp only [h0, hf]
  rfl

/-- With no entry in the thread's set or the process's, the kernel takes no signal. -/
theorem nextSignal_quiet {s : State} (ht : s.thread.pending = []) (hp : s.proc.signal.pending = []) :
    nextSignal s = none := by
  have h0 : SigPending.set [] = 0 := rfl
  have hs : (syncSignals.any fun sig => SigSet.mem (0 : SigSet) sig && !s.thread.sigmask.mem sig) = false := by
    simp [SigSet.mem]
  unfold nextSignal
  simp only [ht, hp, h0, hs, Bool.false_eq_true, ↓reduceIte, nextIn_nil]

/-- With no signal waiting, a return to user mode delivers none. -/
theorem deliverSignals_quiet {ev : Option Event} (ht : s.thread.pending = []) (hp : s.proc.signal.pending = []) :
    deliverSignals prof none ev s = Pure.pure (.running s ev) := by
  unfold deliverSignals
  rw [ht, hp]
  show handleSignals prof none ev 2 false s = _
  unfold handleSignals
  simp only [nextSignal_quiet ht hp, Bool.false_eq_true, ↓reduceIte]

/-- `rt_sigprocmask (SIG_UNBLOCK, set, 0, 8)` with no signal waiting: the signals of the 8 bytes at `set` leave the
thread's mask; `rax` is 0. -/
theorem syscall_sigunblock {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 14) (h10 : s.cpu.gpr.r10.toNat = 8) (hset : s.cpu.gpr.rsi ≠ 0)
    (hold : s.cpu.gpr.rdx = 0) (hhow : argInt s.cpu.gpr.rdi = 1)
    (htop : s.cpu.gpr.rsi.toNat + 8 ≤ userPtrMax prof.feat)
    (hr : ∀ x ∈ byteAddrs s.cpu.gpr.rsi 8, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none)
    (htp : s.thread.pending = []) (hpp : s.proc.signal.pending = []) :
    (instruction prof s).runStream o t =
      (.running (sysSt (s.modThread fun th => { th with sigmask := (s.thread.sigmask &&&
          ~~~(SigSet.unblockable (ofBytesLE 64 (readBytes s.proc.mm.mem s.cpu.gpr.rsi 8)))).unblockable }) len 0)
        (some (sysEv s 0)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hrdx : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdx = s.cpu.gpr.rdx := rfl
  have hr10 : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.r10 = s.cpu.gpr.r10 := rfl
  have hci := copyIn_ok (s := nx s len (sysGpr s len) (rf0 s)) (accessOk_le htop) hr
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (14 ≥ 2 ^ 31) by decide, show ¬ (14 ≥ x32Bit) by decide, show ¬ (14 ≥ nrSyscalls) by decide,
    show niSyscall 14 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysRtSigprocmask
  simp only [hrdi, hrsi, hrdx, hr10, h10, hset, hhow, ne_eq, not_true_eq_false, ↓reduceIte, hci]
  simp only [bind, pure, Req.bind, SIG_BLOCK, SIG_UNBLOCK, show ¬ ((1 : Int) = 0) by decide, ↓reduceIte]
  simp only [hold, ↓reduceIte]
  unfold sysReturnSignals
  rw [deliverSignals_quiet (by exact htp) (by exact hpp)]
  rfl

/-- The event of a system call from `s` that returns 0 and passes the bytes `bs` to the process. -/
abbrev sysEvOut (s : State) (bs : List Byte) : Event :=
  ⟨s.cpu.gpr.rax, [s.cpu.gpr.rdi, s.cpu.gpr.rsi, s.cpu.gpr.rdx, s.cpu.gpr.r10, s.cpu.gpr.r8, s.cpu.gpr.r9], 0, [], bs⟩

theorem Rlimit.bytes_length (r : Rlimit) : r.bytes.length = 16 := by
  simp [Rlimit.bytes, toBytesLE_length]

/-- `prlimit64 (0, r, 0, old)` with `old`'s 16 bytes writable and below the end of the user address space: the
process's limit `r`, soft then hard, is in them; `rax` is 0. -/
theorem syscall_getrlimit {len r : Nat} (hr : r < 16) (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 302) (hpid : argInt s.cpu.gpr.rdi = 0) (hres : arg32 s.cpu.gpr.rsi = r)
    (hnew : s.cpu.gpr.rdx = 0) (hold : s.cpu.gpr.r10 ≠ 0) (htop : s.cpu.gpr.r10.toNat + 16 ≤ userPtrMax prof.feat)
    (hw : ∀ x ∈ byteAddrs s.cpu.gpr.r10 16, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .write x = none) :
    (instruction prof s).runStream o t =
      (.running (sysSt (s.withMem (writeBytes s.proc.mm.mem s.cpu.gpr.r10 (s.proc.signal.rlimits ⟨r, hr⟩).bytes))
        len 0) (some (sysEvOut s (s.proc.signal.rlimits ⟨r, hr⟩).bytes)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hrdx : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdx = s.cpu.gpr.rdx := rfl
  have hr10 : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.r10 = s.cpu.gpr.r10 := rfl
  have hlen := Rlimit.bytes_length (s.proc.signal.rlimits ⟨r, hr⟩)
  have hco := copyOut_ok (s := nx s len (sysGpr s len) (rf0 s)) (a := s.cpu.gpr.r10)
    (bs := (s.proc.signal.rlimits ⟨r, hr⟩).bytes) (accessOk_le (by rw [hlen]; exact htop)) (by rw [hlen]; exact hw)
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (302 ≥ 2 ^ 31) by decide, show ¬ (302 ≥ x32Bit) by decide, show ¬ (302 ≥ nrSyscalls) by decide,
    show niSyscall 302 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysPrlimit
  simp only [hrdi, hrsi, hrdx, hr10, hpid, hres, hnew, hold, hr, ↓reduceIte, ↓reduceDIte, bind, pure, Req.bind,
    show ¬ ((0 : Int) < 0) by decide, ne_eq, not_true_eq_false, false_and]
  show Req.runStream o ((copyOut prof (nx s len (sysGpr s len) (rf0 s)) s.cpu.gpr.r10
    (s.proc.signal.rlimits ⟨r, hr⟩).bytes).bind _) t = _
  rw [hco]
  show (sysReturn _ 0 [] (List.take (s.proc.signal.rlimits ⟨r, hr⟩).bytes.length
    (s.proc.signal.rlimits ⟨r, hr⟩).bytes), t) = _
  rw [List.take_length]
  rfl

end FV7z
