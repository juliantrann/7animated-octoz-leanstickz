import FV7z.Lemmas.SysMm
/-!
# Trial only (Lean v4.35.0 + Zellic R2): obligations not yet discharged

R2's `sysBrk` checks `RLIMIT_DATA` (`Mm.dataFits`) and `may_expand_vm` (`mayExpandVm`). The statement will assume
`LimitsUnlimited` of the entry state (as Zellic's own demo does) and carry it in the startup invariant; the second
needs `mayExpand_unlimited`, which R2 names but does not prove, and which `LayoutOk` alone does not give for
`RLIMIT_DATA` (the vsyscall page is not known to be read-only). Placeholders, so that the trial build goes past them
and shows what else breaks; never on `main` or `ci/full`.
-/
namespace FV7z
open ZellicX86

/-- TRIAL placeholder: `RLIMIT_DATA` is unlimited. -/
theorem trial_data_unlimited (s : State) : (s.proc.signal.rlimits RLIMIT_DATA).cur = RLIM_INFINITY := by
  sorry

/-- TRIAL placeholder: `may_expand_vm` lets `n` data pages through. -/
theorem trial_mayExpand (s : State) (n : Nat) :
    mayExpand (s.proc.signal.rlimits RLIMIT_AS) (s.proc.signal.rlimits RLIMIT_DATA) false s.proc.mm.mem.totalVm
      s.proc.mm.mem.dataVm n true = true := by
  sorry

end FV7z
