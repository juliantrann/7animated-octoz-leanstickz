import ZellicX86.Spec.Statement
import FV7z.Spec.OsVersion
import FV7z.Gor.Mem
/-!
# An environment for the theorem against vacuity (PLAN.md §M)

`launch_main_plt` asks of the oracle: no signal or other event that is not ordinary (`Undisturbed`), no symbolic
link as `/proc/self/exe` (`ProcSelfExe`) but the path of the program, short enough (`hok`), no allocation refused
(`hmg`), and a kernel that glibc runs on (`KernelNew`). `o0` has them: every system call that may fail fails with
`EIO` (5), no event comes, `/proc/self/exe` is `/`, and `uname` says Linux `6.18.0`.

- `e5`, `u0` (`u0_ok`, `u0_new`), `si0`, `o0`.
- `undisturbed0`, `pse0`, `ok0`, `mg0`, `un0`.
-/
namespace FV7z.Wit
open ZellicX86

/-- `EIO`. -/
def e5 : Errno := ⟨5, by decide⟩

/-- A `struct new_utsname` with only the release, `6.18.0`, at offset 130. -/
def u0 : List Byte := List.replicate 130 0 ++ [54, 46, 49, 56, 46, 48] ++ List.replicate 254 0

theorem u0_ok : UtsnameOk u0 := by decide +kernel

theorem u0_new : KernelNew u0 := by
  show 0x301ff < (osVersion u0).toInt
  decide +kernel

theorem zero_lt_cpus (c : Nat) : (0 : BitVec 32).toNat < max c 1 :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_max_right c 1)

/-- `sysinfo`: zeros. -/
def si0 : SysInfo where
  uptime := 0
  loads := (0, 0, 0)
  totalram := 0
  freeram := 0
  sharedram := 0
  bufferram := 0
  totalswap := 0
  freeswap := 0
  procs := 0
  totalhigh := 0
  freehigh := 0
  memUnit := 0

/-- The oracle: what may fail fails with `EIO`, no event, no time, no randomness beyond zeros. -/
def o0 (_ : Nat) : (r : Request) → r.Answer
  | .undefined w => (0 : BitVec w)
  | .pick n => (0 : Fin (n + 1))
  | .between cpus => (⟨[], fun _ h => absurd h List.not_mem_nil⟩ : { evs : List EnvEvent // ∀ e ∈ evs, e.OnCpus cpus })
  | .read _ n => (ReadResult.error e5 : ReadResult n)
  | .readFail _ n => (none : Option (Errno × Fin (n + 1)))
  | .write _ bs => (WriteResult.error e5 : WriteResult bs.length)
  | .writeRefused _ => (none : Option Errno)
  | .writeFault _ _ n => (WriteResult.error e5 : WriteResult n)
  | .fileAttrs _ => ({ noexec := false, append := false, swap := false, writeSealed := false } : FileAttrs)
  | .place _ => (0 : BitVec 64)
  | .memFail p => (none : Option (Errno × Fin (p + 1)))
  | .growFail _ => (false : Bool)
  | .hugeFail _ => (false : Bool)
  | .dataLimitIgnored => (false : Bool)
  | .tsc => (0 : BitVec 64)
  | .xinuse req => (⟨req, BitVec.and_self⟩ : { v : BitVec 64 // req &&& v = req })
  | .randomCount n => (Except.error e5 : Except Errno (Fin (n + 1)))
  | .randomBytes k => (⟨List.replicate k 0, List.length_replicate⟩ : { bs : List Byte // bs.length = k })
  | .readlink _ _ => LinkResult.procExe ⟨[], false⟩
  | .stat _ => (StatResult.error e5 : StatResult)
  | .statPath _ _ _ => (StatResult.error e5 : StatResult)
  | .dirents _ c => (DirentsResult.error e5 : DirentsResult c)
  | .cwd => (CwdResult.error e5 : CwdResult)
  | .uname => (⟨u0, u0_ok⟩ : { bs : List Byte // UtsnameOk bs })
  | .sysinfo => si0
  | .openAt _ _ _ => (OpenResult.error e5 : OpenResult)
  | .seekPast _ _ => (false : Bool)
  | .seek _ _ _ => (Except.error e5 : Except Errno (Fin (2 ^ 63)))
  | .ioctlGet _ _ n => (IoctlResult.error e5 : IoctlResult n)
  | .close _ => (none : Option Errno)
  | .fdGrow fd => (Except.error e5 : Except Errno { n : Nat // fd < n ∧ n ≤ (fd + 1).nextPowerOfTwo })
  | .fcntl _ _ _ => (none : Option Errno)
  | .positional _ _ => (false : Bool)
  | .resumeIds cpus => (⟨(0, 0, 0), ⟨zero_lt_cpus cpus, zero_lt_cpus cpus⟩⟩ :
      { ids : BitVec 32 × BitVec 32 × BitVec 32 // (EnvEvent.kernelEntry ids.1 ids.2.1 ids.2.2).OnCpus cpus })
  | .setRlimit _ _ => (none : Option Errno)
  | .queued _ => (false : Bool)
  | .initPkru => (⟨0, by decide⟩ : { v : BitVec 32 // v &&& 3 = 0 })
  | .clock _ => ({ sec := 0, nsec := 0 } : Timespec)
  | .rtcAlarm => (false : Bool)
  | .timezone => (0 : BitVec 64)
  | .cpuNode cpus => (⟨(0, 0), zero_lt_cpus cpus⟩ : { p : BitVec 32 × BitVec 32 // p.1.toNat < max cpus 1 })

theorem undisturbed0 : Undisturbed o0 := by
  intro t cpus e h
  change List.Mem e [] at h
  cases h

theorem pse0 : ProcSelfExe o0 := by
  intro t d bs h
  simp [o0] at h

theorem ok0 : ∀ t, ∃ x : ExePath, x.bytes.length < pathMax ∧ o0 t (.readlink none Gor.pse) = .procExe x :=
  fun _ => ⟨⟨[], false⟩, by decide, rfl⟩

theorem mg0 : ∀ t p, o0 t (.memFail p) = none := fun _ _ => rfl

theorem un0 : ∀ t, KernelNew (o0 t .uname).val := fun _ => u0_new

end FV7z.Wit
