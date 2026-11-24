import ZellicX86.Spec.Statement
/-!
# Part (B) of `Confined`: the system calls are a word of the command's policy (PLAN.md §5.2)

A policy is a small automaton over system-call events (`Policy`): each event either takes it to a new state or is
refused. A run satisfies it when no event so far was refused (`Policy.Accepts`): what `7zzs` does to the system,
whatever the archive, a seccomp filter with a state. The states are for the commands that write (`e`, `x`, R2:
where a created file may go, P6); the read-only commands need none.

`tPolicy`: `7zzs l` and `7zzs t` under the single-thread flags, from the system calls measured with `strace` (PLAN.md
§6.2), each with the arguments that keep it harmless:
- `write` only to standard output and standard error;
- `openat` only to read (no `O_WRONLY`, `O_RDWR`, `O_CREAT`, `O_TRUNC`);
- `mmap` and `mprotect` never with `PROT_EXEC`;
- `ioctl` only the terminal queries `TCGETS`, `TIOCGWINSZ`, `TCGETS2` (never `TIOCSTI`, which types into a terminal);
- `prlimit64` only to read a limit (no new limit);
- the rest (`read`, `close`, `stat`, `fstat`, `lseek`, `munmap`, `brk`, `rt_sigaction`, `rt_sigprocmask`, `madvise`,
  `uname`, `getcwd`, `readlink`, `umask`, `sysinfo`, `arch_prctl`, `futex`, `getdents64`, `set_tid_address`,
  `set_robust_list`, `exit_group`) with any arguments.
Every other call is refused: `execve`, `execveat`, `fork`, `vfork`, `clone`, `clone3`, `socket`, `connect`,
`ptrace`, `kill`, `unlink`, `rename`, `mkdir`, … . A call number is compared as the whole of `rax`, and an argument as
the whole register: stricter than the kernel (which reads some of them in 32 bits), so a run the policy accepts makes
only the calls listed. Checked on real runs by `tools/policy.py` (`strace` of `l` and `t` on eight formats, 2026-11-24:
every call accepted); `madvise` is bzip2's `MADV_HUGEPAGE`.
-/

namespace FV7z.Statement
open ZellicX86

/-- An automaton over system-call events: a state, and for each event the next state, or `none` (refused). -/
structure Policy where
  St : Type
  init : St
  step : St → Event → Option St

/-- The state after the events `evs`, if none was refused. -/
def Policy.run (A : Policy) (evs : List Event) : Option A.St :=
  evs.foldlM A.step A.init

/-- No event of `evs` is refused. -/
def Policy.Accepts (A : Policy) (evs : List Event) : Prop :=
  (A.run evs).isSome = true

instance (A : Policy) (evs : List Event) : Decidable (A.Accepts evs) :=
  inferInstanceAs (Decidable ((A.run evs).isSome = true))

/-- The argument register `i` of an event (`rdi rsi rdx r10 r8 r9`), 0 if absent. -/
def argOf (ev : Event) (i : Nat) : BitVec 64 :=
  ev.args.getD i 0

/-- The system calls `7zzs l` and `7zzs t` may make, with their arguments (see the module's comment). -/
def allowT (ev : Event) : Bool :=
  match ev.nr.toNat with
  -- read close stat fstat lseek munmap brk rt_sigaction rt_sigprocmask madvise uname getcwd readlink umask
  -- sysinfo arch_prctl futex getdents64 set_tid_address exit_group set_robust_list
  | 0 | 3 | 4 | 5 | 8 | 11 | 12 | 13 | 14 | 28 | 63 | 79 | 89 | 95 | 99 | 158 | 202 | 217 | 218 | 231 | 273 => true
  -- write: to standard output or standard error
  | 1 => argOf ev 0 == 1#64 || argOf ev 0 == 2#64
  -- mmap, mprotect: not PROT_EXEC
  | 9 | 10 => argOf ev 2 &&& 4#64 == 0#64
  -- ioctl: TCGETS, TIOCGWINSZ, TCGETS2
  | 16 => argOf ev 1 == 0x5401#64 || argOf ev 1 == 0x5413#64 || argOf ev 1 == 0x802c542a#64
  -- openat: read only (none of O_WRONLY 1, O_RDWR 2, O_CREAT 0x40, O_TRUNC 0x200)
  | 257 => argOf ev 2 &&& 0x243#64 == 0#64
  -- prlimit64: no new limit
  | 302 => argOf ev 2 == 0#64
  | _ => false

/-- The policy of `7zzs l` and `7zzs t`: `allowT`, with no state. -/
def tPolicy : Policy where
  St := Unit
  init := ()
  step _ ev := if allowT ev then some () else none

end FV7z.Statement
