import FV7z.Lemmas.FnSys
/-!
# System calls that change the process: `brk` and `arch_prctl (ARCH_SET_FS, …)` (PLAN.md G3, startup)

What the instruction `syscall` leaves, on Zellic's model, for the calls glibc's startup makes before `main`:

- `instruction_syscall`: a `syscall` instruction is the kernel's `syscall` from the state with `rcx` and `r11` set.
- `syscall_brk_keep`: `brk (b)` with `b` below the lowest break (`brk (0)`, how `__sbrk` asks where the break is):
  no change, the break in `rax`.
- `syscall_brk_grow`: `brk (b)` with `b`'s page above the break's, when the kernel does not refuse memory (the answer
  to `Request.memFail` is `none`, `Heap.MemGranted`), the pages up to `b`'s and the one after are free and below the
  end of the user address space: the pages are mapped to new zero pages, readable and writable, the break is `b`,
  `rax` is `b`. One answer of the stream is used.
- `syscall_set_fs`: `arch_prctl (ARCH_SET_FS, a)` with `a` below the end of the user address space: the `fs` base is
  `a`, the selector 0, `rax` 0.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- A `syscall` instruction is the kernel's `syscall` from the state with `rcx` and `r11` set. -/
theorem instruction_syscall {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len)) :
    (instruction prof s).runStream o t = (syscall prof (nx s len (sysGpr s len) (rf0 s))).runStream o t := by
  have hex : ((exec prof (mk .syscall 32 [] len)).run prof.feat prof.linux.splitLock (advance s len)).runStream o t =
      (.ok .syscall (nx s len (sysGpr s len) (rf0 s)), t) := by
    simp only [exec, Sem.syscall, mk, bind, Prog.bind, Prog.readRip, Prog.readFlags, Prog.writeReg]
    rfl
  unfold instruction
  simp only [htf, Bool.false_eq_true, ↓reduceIte, hdec]
  unfold advance at hex
  show (Req.bind _ _).runStream o t = _
  rw [Req.runStream_bind, hex]

/-- The state a system call that changes nothing else returns `v` in. -/
abbrev sysSt (s : State) (len : Nat) (v : BitVec 64) : State := nx s len ((sysGpr s len).set 0 v) (rf0 s)

/-- The event of a system call from `s` that returns `v` and passes no bytes. -/
abbrev sysEv (s : State) (v : BitVec 64) : Event :=
  ⟨s.cpu.gpr.rax, [s.cpu.gpr.rdi, s.cpu.gpr.rsi, s.cpu.gpr.rdx, s.cpu.gpr.r10, s.cpu.gpr.r8, s.cpu.gpr.r9], v, [], []⟩

/-- `brk (b)` with `b` below the lowest break: no change, the break in `rax`. -/
theorem syscall_brk_keep {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 12) (hlow : s.cpu.gpr.rdi.toNat < s.proc.mm.brkMin.toNat) :
    (instruction prof s).runStream o t =
      (.running (sysSt s len s.proc.mm.brk) (some (sysEv s s.proc.mm.brk)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hbm : (nx s len (sysGpr s len) (rf0 s)).proc.mm.brkMin = s.proc.mm.brkMin := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (12 ≥ 2 ^ 31) by decide, show ¬ (12 ≥ x32Bit) by decide, show ¬ (12 ≥ nrSyscalls) by decide,
    show niSyscall 12 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysBrk
  simp only [hrdi, hbm, hlow, ↓reduceIte]
  rfl

/-- `s` with the pages from the break's to that of `b` mapped anew and the break at `b`. -/
abbrev brkSt (s : State) (b : Addr) : State :=
  s.withLayout (s.proc.mm.mem.mapAnon (pageUp s.proc.mm.brk.toNat / 4096)
    (pageUp b.toNat / 4096 - pageUp s.proc.mm.brk.toNat / 4096) ⟨true, true, false⟩) b

/-- `brk (b)` that grows the break, when the kernel does not refuse memory. -/
theorem syscall_brk_grow {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 12) (hlow : s.proc.mm.brkMin.toNat ≤ s.cpu.gpr.rdi.toNat)
    (hmf : o t (.memFail 0) = none)
    (hgt : pageUp s.proc.mm.brk.toNat / 4096 < pageUp s.cpu.gpr.rdi.toNat / 4096)
    (htop : 4096 * (pageUp s.cpu.gpr.rdi.toNat / 4096) ≤ taskSize prof.feat)
    (hfree : s.proc.mm.mem.free (pageUp s.proc.mm.brk.toNat / 4096)
      (pageUp s.cpu.gpr.rdi.toNat / 4096 - pageUp s.proc.mm.brk.toNat / 4096 + 1) = true) :
    (instruction prof s).runStream o t =
      (.running (sysSt (brkSt s s.cpu.gpr.rdi) len s.cpu.gpr.rdi) (some (sysEv s s.cpu.gpr.rdi)), t + 1) := by
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
  have h1 : ¬ (pageUp s.cpu.gpr.rdi.toNat / 4096 = pageUp s.proc.mm.brk.toNat / 4096) := by omega
  have h2 : ¬ (pageUp s.cpu.gpr.rdi.toNat / 4096 < pageUp s.proc.mm.brk.toNat / 4096) := by omega
  have h3 : ¬ (4096 * (pageUp s.cpu.gpr.rdi.toNat / 4096) > taskSize prof.feat) := by omega
  simp only [h1, h2, h3, hfree, ↓reduceIte, decide_false, Bool.not_true, Bool.or_self, Bool.false_eq_true]
  rfl

/-- `s` with the `fs` base at `a` and the selector 0. -/
abbrev fsSt (s : State) (a : Addr) : State :=
  s.modCpu fun c => { c with seg := { c.seg with fs := 0, fsBase := a } }

/-- `arch_prctl (ARCH_SET_FS, a)`, with `a` below the end of the user address space. -/
theorem syscall_set_fs {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 158) (hopt : arg32 s.cpu.gpr.rdi = 0x1002)
    (ha : s.cpu.gpr.rsi.toNat < userPtrMax prof.feat) :
    (instruction prof s).runStream o t =
      (.running (sysSt (fsSt s s.cpu.gpr.rsi) len 0) (some (sysEv s 0)), t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (158 ≥ 2 ^ 31) by decide, show ¬ (158 ≥ x32Bit) by decide, show ¬ (158 ≥ nrSyscalls) by decide,
    show niSyscall 158 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysArchPrctl
  simp only [hrdi, hrsi, hopt, show (0x1002 = ARCH_SET_FS) by decide, Nat.not_le.2 ha, true_or, ↓reduceIte]
  rfl

end FV7z
