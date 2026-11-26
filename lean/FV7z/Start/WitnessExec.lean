import FV7z.Start.WitnessProf
import FV7z.Start.Launch
import FV7z.Start.Ready
/-!
# A start of `7zzs` for the theorem against vacuity (PLAN.md §M)

`launch_main_plt` asks for a launch (`Launch.Of`: the file holds `7zzs`, `execve` of it starts the program, the
arguments are ones a caller can pass), with room on the stack (`StackRoom`), no secure exec, no signal waiting, and
the address-space and data limits unlimited (`LimitsUnlimited`). Here is one, on `prof0`:

- `files0`: every file holds the bytes of `7zzs`; `exe0` is inode 0 (`holds0`).
- `args0`: `/7zzs` with `argv` `["7zzs"]`, no environment, uid 1000, every limit `RLIM_INFINITY` (`args_ok0`,
  `room0`).
- `k0`: `vm.mmap_min_addr` 64 KiB, `init_pkru` as Linux sets it (`k0_valid`).
- `c0`: the stack's top at `2 ^ 47 - 4096`, the break at `brkBase` (`c0_valid`).
- `good0`: `execve` of them gives a state whose limits are unlimited, by the kernel's evaluation (`decide +kernel`
  reads only the ELF header, the program headers and what `execve` computes from them); `exec0`: so `ExecStart`.
-/
namespace FV7z.Wit
open ZellicX86 FV7z.Start

/-- Every file holds the bytes of `7zzs`. -/
noncomputable def files0 : Files where
  page := fun fp o => V2606.zzs.blob.bytes (4096 * fp.index + o.toNat)
  size := fun _ => V2606.zzs.blob.size
  denyWrite := fun _ => false
  regular := fun _ => true

def exe0 : FileId := .inode 0

/-- `/7zzs`, run as `7zzs` with no environment, no open descriptor, every limit unlimited. -/
def args0 : ExecArgs where
  filename := [0x2f, 0x37, 0x7a, 0x7a, 0x73]
  argv := [[0x37, 0x7a, 0x7a, 0x73]]
  envp := []
  uid := 1000
  euid := 1000
  gid := 1000
  egid := 1000
  secure := false
  files := fun _ => none
  fdMax := 0
  umask := 0o22
  filePos := fun _ => ⟨0, false, 0⟩
  sighand := fun _ => .default
  signal := ⟨[], fun _ => ⟨-1, -1⟩, false⟩
  sigmask := 0
  threadPending := []
  tid := 1
  personality := 0
  tscFaults := false
  altStackFlags := 0
  brkRandomized := false

def k0 : KernelConfig where
  mmapMinAddr := 65536
  initPkru := 0x55555554

def c0 : ExecChoice where
  stackTop := 2 ^ 47 - 4096
  stackAlign := 0
  random := 0
  vdsoBase := 0
  vdsoData := fun _ _ => 0
  brk := 0x7a9000
  nextOpen := 0

theorem holds0 : FileHolds files0 exe0 V2606.zzs.blob.bytes V2606.zzs.blob.size := by
  refine ⟨rfl, fun i hi => ?_⟩
  simp only [Files.byte, files0, hi, ↓reduceIte, BitVec.toNat_ofNat, Nat.reducePow]
  congr 1
  omega

theorem args_ok0 : args0.Ok :=
  ⟨by decide, by decide, by decide, by decide, by decide, fun _ => Nat.le_refl _, by decide, by decide, trivial⟩

theorem room0 : StackRoom args0 5000 := by
  unfold StackRoom
  decide +kernel

theorem k0_valid : k0.Valid := by
  unfold KernelConfig.Valid
  decide

theorem c0_valid : c0.Valid prof0.linux zzsPhdrs args0 k0 where
  stackTop := by decide +kernel
  stackAlign := by decide
  brk := by
    rw [zzs_brk.2]
    decide +kernel
  vdso h := absurd h (by decide)
  nextOpen _ _ h := by simp [args0] at h
  fail _ h := by simp [c0] at h

theorem within0 : args0.withinLimits = true := by decide +kernel

theorem elf0 : (readElf files0 exe0).isSome = true := by decide +kernel

/-- The loadable segments load. -/
theorem segs0 : (match loadRegions prof0.feat files0 exe0 k0 (stackLayout args0 prof0.linux c0).start c0.stackTop
    zzsPhdrs with
    | .ok _ => true
    | _ => false) = true := by decide +kernel

/-- `execve` starts the program, its address-space and data limits unlimited. -/
def good : ExecResult → Bool
  | .ok s => (s.proc.signal.rlimits RLIMIT_AS).cur == RLIM_INFINITY &&
      (s.proc.signal.rlimits RLIMIT_DATA).cur == RLIM_INFINITY
  | _ => false

theorem good0 : good (execve prof0 files0 exe0 args0 k0 c0) = true := by decide +kernel

theorem run0 : ∃ s, execve prof0 files0 exe0 args0 k0 c0 = .ok s ∧ LimitsUnlimited s := by
  have h := good0
  generalize execve prof0 files0 exe0 args0 k0 c0 = r at h ⊢
  cases r with
  | ok s =>
    simp only [good, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨s, rfl, h⟩
  | error e => simp [good] at h
  | stopped o => simp [good] at h

theorem exec0 : ∃ s, ExecStart prof0 files0 exe0 args0 k0 s ∧ LimitsUnlimited s := by
  obtain ⟨s, he, hl⟩ := run0
  refine ⟨s, ⟨k0_valid, c0, fun hdr phs hr => ?_, he⟩, hl⟩
  obtain ⟨-, rfl⟩ := readElf_zzs holds0 hr
  exact c0_valid

end FV7z.Wit
