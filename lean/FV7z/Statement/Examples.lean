import FV7z.Statement.Confined
/-!
# The parts of `Confined` are not empty, and refuse what they should (PLAN.md §5.2, item "non-vacuity")

On small examples: a path that calls and returns follows its graph, and one whose return goes elsewhere (ROP) does
not; the policy of `l`/`t` accepts a startup's and an output's calls and refuses `execve`, a file opened to write, an
executable mapping and `TIOCSTI`; `Done7z` admits exit code 0 and refuses exit code 3 and `SIGABRT`. The non-vacuity
of the whole statement for `7zzs` (its hypotheses can hold, and the run gets to `main`) comes with the theorems.
-/

namespace FV7z.Statement.Examples
open ZellicX86 FV7z.Statement

/-- `0x10: call 0x100` (returns to `0x15`), `0x15: jmp 0x20`, `0x100: ret`. -/
def toy : Cfg where
  entry := 0x10#64
  edges p := match p.toNat with
    | 0x10 => [.call 0x100#64 0x15#64]
    | 0x15 => [.go 0x20#64]
    | 0x100 => [.ret]
    | _ => []
  pads _ := []
  setjmps := []

/-- Call, return to the call's next instruction, jump. -/
example : toy.Follows [0x20#64, 0x15#64, 0x100#64, 0x10#64] :=
  ⟨[], .step (.step (.step .start (Cfg.step_call (by decide))) (Cfg.step_ret (by decide)))
    (Cfg.step_go (by decide))⟩

/-- A return to an address other than the one its call pushed (an overwritten return address) does not follow. -/
example : ¬ toy.Follows [0x666#64, 0x100#64, 0x10#64] := by
  rintro ⟨stk, h⟩
  obtain ⟨stk1, h1, hs⟩ := h.cons_cons
  obtain ⟨stk0, -, hs0⟩ := h1.cons_cons
  obtain ⟨e0, he0, hm0⟩ := hs0
  obtain ⟨e1, he1, hm1⟩ := hs
  have k0 : toy.edges 0x10#64 = [.call 0x100#64 0x15#64] := rfl
  have k1 : toy.edges 0x100#64 = [.ret] := rfl
  rw [k0, List.mem_singleton] at he0
  rw [k1, List.mem_singleton] at he1
  subst he0 he1
  obtain ⟨-, rfl⟩ := hm0
  obtain ⟨h15, -⟩ := List.cons.inj hm1
  exact absurd h15 (by decide)

/-- A system call with number `nr` and arguments `args`. -/
def ev (nr : Nat) (args : List (BitVec 64)) : Event :=
  { nr := BitVec.ofNat 64 nr, args := args, ret := 0, fromProc := [], toProc := [] }

/-- `brk(0)`, `write(1, …, 5)`, `exit_group(0)`. -/
example : tPolicy.Accepts [ev 12 [0], ev 1 [1, 0, 5], ev 231 [0]] := by decide

/-- `execve` after a `write`. -/
example : ¬ tPolicy.Accepts [ev 1 [1, 0, 5], ev 59 [0, 0, 0]] := by decide

/-- `openat(AT_FDCWD, …, O_WRONLY | O_CREAT | O_TRUNC)`. -/
example : ¬ tPolicy.Accepts [ev 257 [0xffffffffffffff9c, 0, 0x241]] := by decide

/-- `mmap(0, 4096, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS)`. -/
example : ¬ tPolicy.Accepts [ev 9 [0, 4096, 7, 0x22]] := by decide

/-- `ioctl(0, TIOCSTI, …)`: typing into the terminal. -/
example : ¬ tPolicy.Accepts [ev 16 [0, 0x5412, 0]] := by decide

/-- `write(3, …)`: a write to a descriptor other than standard output and standard error. -/
example : ¬ tPolicy.Accepts [ev 1 [3, 0, 5]] := by decide

example : Done7z (.exited .exitGroup 0) [] := Or.inl ⟨0, rfl, by decide⟩

example : ¬ Done7z (.exited .exitGroup 3) [] := by
  rintro (⟨s, h, hs⟩ | h)
  · cases h
    exact absurd hs (by decide)
  · simp [Outcome.KilledInWrite] at h

example : ¬ Done7z (.killed Signal.SIGABRT .self) [] := by
  rintro (⟨s, h, -⟩ | h)
  · cases h
  · simp [Outcome.KilledInWrite] at h

end FV7z.Statement.Examples
