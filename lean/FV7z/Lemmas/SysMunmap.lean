import FV7z.Tcg.Sys
/-!
# `munmap (addr, len)`: what the instruction `syscall` leaves (PLAN.md §M, M1)

What the instruction `syscall` leaves for `munmap (rdi, rsi)` on Zellic's model (`sysMunmap`), when the pages of the
range are not special and none is the initial stack's first page (`Memory.touchesFixed`, whose change the model does
not follow and stops at): an error, nothing changed; 0 with nothing mapped there, nothing changed; or 0 with the pages
unmapped (`Memory.unmap`).

- `munFirst`, `munN`: the first page and the number of pages of the range.
- `syscall_munmap`: the instruction, its three kinds of outcome.
-/
namespace FV7z
open ZellicX86 Decode FV7z.Write

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- The first page `munmap (rdi, rsi)` unmaps. -/
abbrev munFirst (s : State) : Nat := s.cpu.gpr.rdi.toNat / 4096

/-- The number of pages `munmap (rdi, rsi)` unmaps: `rsi` rounded up to pages. -/
abbrev munN (s : State) : Nat := pageUp s.cpu.gpr.rsi.toNat / 4096

/-- `syscall` for `munmap (rdi, rsi)`, no page of the range special or the initial stack's first page: an error,
nothing changed; 0, nothing changed (nothing was mapped there); or 0 with the pages unmapped. -/
theorem syscall_munmap {len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .syscall 32 [] len))
    (hnr : s.cpu.gpr.rax.toNat % 2 ^ 32 = 11)
    (hfx : s.proc.mm.mem.touchesFixed (munFirst s) (munN s) = false) {P : StepResult × Nat → Prop}
    (h0 : ∀ (r : BitVec 64) (t' : Nat), WrErr r → P (.running (sysSt s len r) (some (sysEv s r)), t'))
    (h1 : ∀ t' : Nat, P (.running (sysSt s len 0) (some (sysEv s 0)), t'))
    (h2 : ∀ t' : Nat, P (.running (sysSt (s.withMem (s.proc.mm.mem.unmap (munFirst s) (munN s))) len 0)
      (some (sysEv s 0)), t')) :
    P ((instruction prof s).runStream o t) := by
  rw [instruction_syscall htf hdec]
  have hrax : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rax = s.cpu.gpr.rax := rfl
  have hrdi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rdi = s.cpu.gpr.rdi := rfl
  have hrsi : (nx s len (sysGpr s len) (rf0 s)).cpu.gpr.rsi = s.cpu.gpr.rsi := rfl
  have hme : (nx s len (sysGpr s len) (rf0 s)).proc.mm.mem = s.proc.mm.mem := rfl
  unfold syscall
  simp only [hrax, hnr]
  simp only [show ¬ (11 ≥ 2 ^ 31) by decide, show ¬ (11 ≥ x32Bit) by decide, show ¬ (11 ≥ nrSyscalls) by decide,
    show niSyscall 11 = false by decide, ↓reduceIte, Bool.false_eq_true]
  show P ((sysMunmap prof.feat (nx s len (sysGpr s len) (rf0 s))).runStream o t)
  dsimp only [sysMunmap]
  try simp only [hrdi, hrsi, hme]
  split
  · exact h0 (errRet EINVAL) t (errRet_err (by decide) (by decide))
  · split
    · exact h1 t
    · split
      · rename_i h
        exact absurd (h.symm.trans hfx) (by decide)
      · split
        · show P ((Req.bind cutError _).runStream o t)
          rw [Req.runStream_bind]
          unfold cutError
          rw [runStream_req_bind]
          split
          · rename_i e _
            exact h0 (errRet e.val) (t + 1) (errRet_err e.property.1 e.property.2)
          · exact h0 (errRet EINVAL) (t + 1) (errRet_err (by decide) (by decide))
        · rw [runStream_req_bind]
          split
          · rename_i e _
            exact h0 (errRet e.val) (t + 1) (errRet_err e.property.1 e.property.2)
          · exact h2 (t + 1)

end FV7z
