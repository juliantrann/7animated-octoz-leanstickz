import FV7z.Lemmas.SysMm
/-!
# `mprotect (a, n, PROT_READ)` (PLAN.md G3, startup)

What the instruction `syscall` leaves, on Zellic's model, for the call glibc's startup makes to protect the RELRO
segment (`_dl_protect_relro`, from `_dl_non_dynamic_init`).

- `takeWhile_all`: `List.takeWhile` of a list whose elements all pass.
- `roSt`: a state with pages made read-only, as `mprotect` leaves them (the protection, and new areas).
- `syscall_mprotect_ro`: `mprotect (a, len, PROT_READ)` with `a` a page's address, `len` not 0, every page of the
  range mapped, not special, and such that it may be made readable (`Mapping.maxProt`), when the kernel does not
  refuse (the answer to `Request.memFail` is `none`): the pages are read-only, `rax` is 0. One answer of the stream is
  used.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

theorem takeWhile_all {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = true) → l.takeWhile p = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.takeWhile_cons, h a List.mem_cons_self]
    simp only [↓reduceIte]
    rw [takeWhile_all fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- `s` with the mapped pages among the `n` from `first` read-only, in new areas. -/
abbrev roSt (s : State) (first n : Nat) : State :=
  s.withMem ((s.proc.mm.mem.protect first n ⟨true, false, false⟩).renumber first n)

/-- `mprotect (a, len, PROT_READ)` of mapped pages, when the kernel does not refuse. -/
theorem syscall_mprotect_ro {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 10) (hprot : s.cpu.gpr.rdx.toNat = 1)
    (hal : s.cpu.gpr.rdi.toNat % 4096 = 0) (hlen : 0 < s.cpu.gpr.rsi.toNat)
    (hwrap : s.cpu.gpr.rdi.toNat + pageUp s.cpu.gpr.rsi.toNat < 2 ^ 64)
    (hmf : o t (.memFail (pageUp s.cpu.gpr.rsi.toNat / 4096)) = none)
    (hmap : ∀ i < pageUp s.cpu.gpr.rsi.toNat / 4096, ∃ m,
      s.proc.mm.mem.mapAt (s.cpu.gpr.rdi.toNat / 4096 + i) = some m ∧ m.special = false ∧ m.maxProt.read = true) :
    (instruction prof s).runStream o t =
      (.running (sysSt (roSt s (s.cpu.gpr.rdi.toNat / 4096) (pageUp s.cpu.gpr.rsi.toNat / 4096)) len 0)
        (some (sysEv s 0)), t + 1) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hrdx : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdx = s.cpu.gpr.rdx := rfl
  have hme : (nx s len (sysGpr s len) (rf0 s)).proc.mm.mem = s.proc.mm.mem := rfl
  have hn0 : ¬ (pageUp s.cpu.gpr.rsi.toNat / 4096 = 0) := by
    unfold pageUp
    omega
  have hk : s.proc.mm.mem.leadMapped (s.cpu.gpr.rdi.toNat / 4096) (pageUp s.cpu.gpr.rsi.toNat / 4096) =
      pageUp s.cpu.gpr.rsi.toNat / 4096 := by
    unfold Memory.leadMapped
    rw [takeWhile_all, List.length_range]
    intro i hi
    obtain ⟨m, hm, -⟩ := hmap i (List.mem_range.1 hi)
    rw [hm]
    rfl
  have hsp : ((List.range (pageUp s.cpu.gpr.rsi.toNat / 4096)).any fun i =>
      (s.proc.mm.mem.mapAt (s.cpu.gpr.rdi.toNat / 4096 + i)).any (·.special)) = false := by
    rw [List.any_eq_false]
    intro i hi
    obtain ⟨m, hm, h1, -⟩ := hmap i (List.mem_range.1 hi)
    rw [hm]
    simp only [Option.any_some, h1, Bool.false_eq_true, not_false_eq_true]
  have hc : ((List.range (pageUp s.cpu.gpr.rsi.toNat / 4096)).takeWhile fun i =>
      (s.proc.mm.mem.mapAt (s.cpu.gpr.rdi.toNat / 4096 + i)).all fun m =>
        (protOf 1).within m.maxProt).length = pageUp s.cpu.gpr.rsi.toNat / 4096 := by
    rw [takeWhile_all, List.length_range]
    intro i hi
    obtain ⟨m, hm, -, h2⟩ := hmap i (List.mem_range.1 hi)
    rw [hm]
    simp only [Option.all_some, Prot.within, h2, show (protOf 1) = ⟨true, false, false⟩ by decide, Bool.not_true,
      Bool.not_false, Bool.or_true, Bool.true_or, Bool.and_self]
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (10 ≥ 2 ^ 31) by decide, show ¬ (10 ≥ x32Bit) by decide, show ¬ (10 ≥ nrSyscalls) by decide,
    show niSyscall 10 = false by decide, ↓reduceIte, Bool.false_eq_true]
  unfold sysMprotect
  simp only [hrdi, hrsi, hrdx, hme, hprot, hal, show anyBits 1 PROT_GROWSDOWN = false by decide,
    show anyBits 1 PROT_GROWSUP = false by decide, Bool.and_self, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    ne_eq, not_true_eq_false, Nat.ne_of_gt hlen, Nat.not_le.2 hwrap, ge_iff_le,
    show ¬ (16 ≤ 1 % 2 ^ 24 + 1 / 2 ^ 26 * 2 ^ 26) by decide, show (1 % 2 ^ 24 + 1 / 2 ^ 26 * 2 ^ 26) = 1 by decide,
    hk, hn0, hsp, show ¬ ((1 : Nat) = 4) by decide, decide_false, Bool.and_false, hc]
  refine (Req.runStream_bind o _ (Req.request (.memFail (pageUp s.cpu.gpr.rsi.toNat / 4096))) t).trans ?_
  have hrq : Req.runStream o (Req.request (.memFail (pageUp s.cpu.gpr.rsi.toNat / 4096))) t = (none, t + 1) := by
    show (o t (.memFail (pageUp s.cpu.gpr.rsi.toNat / 4096)), t + 1) = _
    rw [hmf]
    rfl
  rw [hrq]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rfl

end FV7z
