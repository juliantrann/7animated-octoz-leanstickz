import FV7z.Lemmas.SysLseek
import FV7z.Lemmas.SysLink
/-!
# `openat`: a new descriptor, or an error (PLAN.md §M, M1)

`openat (dirfd, path, flags, mode)` on Zellic's model (`sysOpenat`), with flags that have none of `O_CREAT`,
`O_TRUNC` and `O_TMPFILE` (`0x400240`: the model stops at a call that may create or truncate a file) and a path name
the kernel can read all of (`m` nonzero bytes then a NUL, the word it ends in readable, below the end of the user
address space): the call returns a descriptor or an error, which the file system and the descriptor table decide.
It may change the descriptor table, the table's size and the open file descriptions, all part of the process, which
`KeptW` keeps; the address space, the thread and the processor (but `rax`) stay. So the run goes on from the state
after as a new start (`Seg.reroot`), as after `close` and `lseek`.

What `openat` returns is left open (`r`), and so are the bytes of the event (`bs`: the path read, or none).

- `land_sub_zero`, `hasFlag_v`, `hasFlag_pv`: flag bits that the flags (as the model masks them) do not have.
- `open_cps`: every way through the model's `sysOpenat` ends with the state after one of that shape.
- `syscall_openat`: what the instruction `syscall` leaves for `openat (rdi, rsi, rdx, r10)`.
- `Seg.s_openat_re`: the step of a run that `Fn.Seg` describes; the run goes on from the state after as a new start.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- Bits `b` within a mask `m` that `x` has none of. -/
theorem land_sub_zero {x m b : Nat} (hx : x &&& m = 0) (hb : m &&& b = b) : x &&& b = 0 := by
  rw [← hb, ← Nat.and_assoc, hx, Nat.zero_and]

/-- The flags as `openat` masks them, without `O_PATH`, have no bits `b` within `0x400240` if the flags have none of
`0x400240`. -/
theorem hasFlag_v {x b : Nat} (hx : x &&& 0x400240 = 0)
    (hb : 0x400240 &&& (VALID_OPEN_FLAGS &&& b) = VALID_OPEN_FLAGS &&& b) :
    hasFlag (x &&& VALID_OPEN_FLAGS) b = false := by
  unfold hasFlag
  rw [Nat.and_assoc, land_sub_zero hx hb]
  rfl

/-- The flags as `openat` masks them with `O_PATH` have no bits outside `O_PATH_FLAGS`. -/
theorem hasFlag_pv {y b : Nat} (hb : O_PATH_FLAGS &&& b = 0) : hasFlag (y &&& O_PATH_FLAGS) b = false := by
  unfold hasFlag
  rw [Nat.and_assoc, hb, Nat.and_zero]
  rfl

/-- `sysOpenat` with flags (`rdx`) that have none of `O_CREAT`, `O_TRUNC`, `O_TMPFILE` and the path name `p` read
from `rsi`: the state after has the processor of `u` with `rax` the answer, and `u`'s thread and address space. -/
theorem open_cps (u : State) {p : List Byte} (hx : arg32 u.cpu.gpr.rdx &&& 0x400240 = 0)
    (hu : userPath prof u u.cpu.gpr.rsi = Pure.pure (u, .ok p)) {P : StepResult × Nat → Prop}
    (hk : ∀ (Y : State) (r : BitVec 64) (bs : List Byte) (t' : Nat), Y.cpu = (u.setRax r).cpu →
      Y.thread = u.thread → Y.proc.mm = u.proc.mm →
      P (.running Y (some ⟨u.cpu.gpr.rax, syscallArgs u, r, bs, []⟩), t')) :
    P ((sysOpenat prof u).runStream o t) := by
  have v1 : hasFlag (arg32 u.cpu.gpr.rdx &&& VALID_OPEN_FLAGS) O_CREAT = false := hasFlag_v hx (by decide)
  have v2 : hasFlag (arg32 u.cpu.gpr.rdx &&& VALID_OPEN_FLAGS) O_TMPFILE_BIT = false := hasFlag_v hx (by decide)
  have v3 : hasFlag (arg32 u.cpu.gpr.rdx &&& VALID_OPEN_FLAGS) (O_CREAT ||| O_TRUNC ||| O_TMPFILE_BIT) = false :=
    hasFlag_v hx (by decide)
  have w1 : ∀ y, hasFlag (y &&& O_PATH_FLAGS) O_CREAT = false := fun _ => hasFlag_pv (by decide)
  have w2 : ∀ y, hasFlag (y &&& O_PATH_FLAGS) O_TMPFILE_BIT = false := fun _ => hasFlag_pv (by decide)
  have w3 : ∀ y, hasFlag (y &&& O_PATH_FLAGS) (O_CREAT ||| O_TRUNC ||| O_TMPFILE_BIT) = false :=
    fun _ => hasFlag_pv (by decide)
  unfold sysOpenat allocFd expandFiles
  simp only [hu, req_pure_bind]
  try dsimp only
  by_cases hp : hasFlag (arg32 u.cpu.gpr.rdx &&& VALID_OPEN_FLAGS) O_PATH = true
  · simp only [hp, ↓reduceIte, w1, w2, w3, Bool.and_false, Bool.false_and, Bool.false_eq_true]
    clear hu v1 v2 v3 w1 w2 w3 hx
    repeat' first
      | (refine hk _ _ _ _ ?_ ?_ ?_ <;> rfl)
      | (rw [runStream_req_bind]; try dsimp only)
      | (simp only [bind, pure, Req.request, Req.bind, Req.runStream]; try dsimp only)
      | (refine rs_ite (P := P) _ _ _ _ ?_ ?_)
      | split
  · simp only [hp, ↓reduceIte, v1, v2, v3, Bool.and_false, Bool.false_and, Bool.false_eq_true]
    clear hu v1 v2 v3 w1 w2 w3 hx
    repeat' first
      | (refine hk _ _ _ _ ?_ ?_ ?_ <;> rfl)
      | (rw [runStream_req_bind]; try dsimp only)
      | (simp only [bind, pure, Req.request, Req.bind, Req.runStream]; try dsimp only)
      | (refine rs_ite (P := P) _ _ _ _ ?_ ?_)
      | split

/-- `syscall` for `openat (rdi, rsi, rdx, r10)` with flags (`rdx`) that have none of `O_CREAT`, `O_TRUNC`,
`O_TMPFILE`, and a path name at `rsi` of `m` nonzero bytes then a NUL (the word it ends in readable, below the end of
the user address space): the state after has the processor after the `syscall` with `rax` the answer `r`, and the
thread and address space of before. -/
theorem syscall_openat {len m : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 257) (hx : arg32 s.cpu.gpr.rdx &&& 0x400240 = 0) (hm : m < pathMax)
    (htop : s.cpu.gpr.rsi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hr : Readable prof s s.cpu.gpr.rsi (8 * (m / 8 + 1)))
    (hnz : ∀ i < m, s.proc.mm.mem.readByte (s.cpu.gpr.rsi.add i) ≠ 0)
    (hz : s.proc.mm.mem.readByte (s.cpu.gpr.rsi.add m) = 0) :
    ∃ (Y : State) (r : BitVec 64) (bs : List Byte) (t' : Nat),
      (instruction prof s).runStream o t = (.running Y (some ⟨s.cpu.gpr.rax, syscallArgs s, r, bs, []⟩), t') ∧
      Y.cpu = (sysSt s len r).cpu ∧ Y.thread = s.thread ∧ Y.proc.mm = s.proc.mm := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (257 ≥ 2 ^ 31) by decide, show ¬ (257 ≥ x32Bit) by decide,
    show ¬ (257 ≥ nrSyscalls) by decide, show niSyscall 257 = false by decide, ↓reduceIte, Bool.false_eq_true]
  have hu := userPath_ok (s := nx s len (sysGpr s len) (rf0 s)) (a := s.cpu.gpr.rsi) hm htop hr hnz hz
  exact open_cps (nx s len (sysGpr s len) (rf0 s)) hx hu
    (P := fun res => ∃ (Y : State) (r : BitVec 64) (bs : List Byte) (t' : Nat),
      res = (.running Y (some ⟨s.cpu.gpr.rax, syscallArgs s, r, bs, []⟩), t') ∧
      Y.cpu = (sysSt s len r).cpu ∧ Y.thread = s.thread ∧ Y.proc.mm = s.proc.mm)
    fun Y r bs t' h1 h2 h3 => ⟨Y, r, bs, t', rfl, h1, h2, h3⟩

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `syscall` for `openat (rdi, rsi, rdx, r10)` (a start with no `rseq` area, flags in `rdx` without `O_CREAT`,
`O_TRUNC` and `O_TMPFILE`, a path name at `rsi` of `m` nonzero bytes then a NUL, the word it ends in the footprint's
data): the run goes on from the state after, its own start, with the processor after the `syscall` and some answer
`r` in `rax`, the address space of before; the event has some bytes `bs` from the process. -/
theorem s_openat_re (c : Seg prof F Wl L s₀ o) (hrs : s₀.thread.rseq = none) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j)
    {len m : Nat} (hd : Dec prof.feat code j (FV7z.mk .syscall 32 [] len))
    (hnr : X.cpu.gpr.rax.toNat % 2 ^ 32 = 257) (hx : arg32 X.cpu.gpr.rdx &&& 0x400240 = 0) (hm : m < pathMax)
    (htop : X.cpu.gpr.rsi.toNat + 8 * (m / 8 + 1) ≤ userPtrMax prof.feat)
    (hl : ∀ i < 8 * (m / 8 + 1), Foot F.data (X.cpu.gpr.rsi.add i))
    (hnz : ∀ i < m, V (X.cpu.gpr.rsi.add i) ≠ 0) (hz : V (X.cpu.gpr.rsi.add m) = 0)
    (k' : ∀ (M : Memory) (Y : State) (r : BitVec 64) (bs : List Byte) (t' : Nat), KeptW Wl s₀ (X.withMem M) →
      Y.cpu = (sysSt (X.withMem M) len r).cpu → Y.proc.mm = (X.withMem M).proc.mm →
      Seg prof F Wl L Y o → Agree F Y.proc.mm.mem V →
      GoG prof L o (gev ++ [⟨X.cpu.gpr.rax, syscallArgs X, r, bs, []⟩]) gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  c.stepE hK hin hj hrip fun M hM hK' htf hac => by
    have hA' := c.agreeK hK hA hM
    have hrd := (c.load_ok (X := X.withMem M) hK' hA' hl).1
    have hnz' : ∀ i < m, (X.withMem M).proc.mm.mem.readByte (X.cpu.gpr.rsi.add i) ≠ 0 := fun i hi => by
      show M.readByte _ ≠ 0
      rw [hA' _ (hl i (by omega))]
      exact hnz i hi
    have hz' : (X.withMem M).proc.mm.mem.readByte (X.cpu.gpr.rsi.add m) = 0 := by
      show M.readByte _ = 0
      rw [hA' _ (hl m (by omega))]
      exact hz
    obtain ⟨Y, r, bs, t', heq, hc, hth, hmm⟩ :=
      syscall_openat (s := X.withMem M) (o := o) (t := t + 1) htf (c.dec hK' hin hrip hd) hnr hx hm htop hrd hnz' hz'
    refine ⟨Y, t', _, heq, ?_⟩
    have hY : Seg prof F Wl L Y o :=
      c.reroot hK' hmm ((congrArg (·.pkru) hc).trans rfl) ((congrArg (·.rseq) hth).trans rfl)
        ((congrArg (·.shstk) hth).trans rfl) ((congrArg (·.cpuidFaults) hth).trans rfl)
        ((congrArg (·.rflags.tf) hc).trans htf) ((congrArg (·.rflags.ac) hc).trans hac) hrs
    exact k' M Y r bs t' hK' hc hmm hY (by rw [hmm]; exact hA')

end FV7z.Fn.Seg
