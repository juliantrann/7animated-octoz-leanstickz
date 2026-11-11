import ZellicX86.Spec.Statement
/-!
# The contract of `_dl_debug_initialize` in `7zzs` (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/DebugInit.lean`).

`_dl_debug_initialize (ldbase, ns)` (glibc 2.31, `elf/dl-debug.c`) returns the address of the debugger's interface
`struct r_debug` of namespace `ns`, initialized if it was not yet or if `ldbase` is given: its version is 1, its
`r_ldbase` is `ldbase` (or what it was, without one), its `r_brk` the address of `_dl_debug_state`, and its `r_map`
the namespace's list of loaded objects. `__libc_start_main` calls it with `ldbase` and `ns` 0, before and after the
initializers. The contract is for the namespace 0, whose structure is `_r_debug`: a call

- reads `_r_debug` and `_dl_ns[0]._ns_loaded`;
- writes only `_r_debug` (its frame is the return address's slot);
- returns `&_r_debug` to its caller with the callee-saved registers kept, having made no system call.
-/
namespace FV7z.DebugInit
open ZellicX86

/-- `_r_debug` (`0x7a84c0`): `r_version` (an `int`), `r_map` at 8, `r_brk` at 16, `r_state` at 24, `r_ldbase` at 32. -/
def rDebug : Rgn := ⟨0x7a84c0, 40⟩
/-- `_dl_ns[0]._ns_loaded` (`0x793440`). -/
def rLoaded : Rgn := ⟨0x793440, 8⟩

/-- What a call reads besides what it writes. -/
def reads (_ : State) : List Rgn := [rLoaded]

/-- The 8 bytes at `a` as a number. -/
def word (m : Memory) (a : Addr) : BitVec 64 := ofBytesLE 64 (readBytes m a 8)

/-- What a call assumes: the namespace is 0, and the return address is not in `_r_debug`. -/
structure Pre (s : State) : Prop where
  ns : s.cpu.gpr.rsi = 0
  frameApart : Apart [frame s 0] [rDebug]

/-- `r_ldbase` after an initialization: `ldbase`, or what it was without one. -/
def ldbase (s : State) : BitVec 64 :=
  if s.cpu.gpr.rdi = 0 then word s.proc.mm.mem 0x7a84e0 else s.cpu.gpr.rdi

/-- What a call leaves: `rax` is `&_r_debug`. With a map already and no `ldbase` given, `_r_debug` is as it was
(`kept`). Else (`init`) its version is 1, its map that of namespace 0, its `r_brk` is `&_dl_debug_state` (`0x66e490`)
and its `r_ldbase` is `ldbase`; the 4 bytes after the version and `r_state` are as they were. -/
structure Post (s s' : State) : Prop where
  ret : s'.cpu.gpr.rax = 0x7a84c0
  kept : word s.proc.mm.mem 0x7a84c8 ≠ 0 → s.cpu.gpr.rdi = 0 →
    readBytes s'.proc.mm.mem 0x7a84c0 40 = readBytes s.proc.mm.mem 0x7a84c0 40
  init : word s.proc.mm.mem 0x7a84c8 = 0 ∨ s.cpu.gpr.rdi ≠ 0 →
    ofBytesLE 32 (readBytes s'.proc.mm.mem 0x7a84c0 4) = 1 ∧
    readBytes s'.proc.mm.mem 0x7a84c4 4 = readBytes s.proc.mm.mem 0x7a84c4 4 ∧
    word s'.proc.mm.mem 0x7a84c8 = word s.proc.mm.mem 0x793440 ∧
    word s'.proc.mm.mem 0x7a84d0 = 0x66e490 ∧
    readBytes s'.proc.mm.mem 0x7a84d8 8 = readBytes s.proc.mm.mem 0x7a84d8 8 ∧
    word s'.proc.mm.mem 0x7a84e0 = ldbase s

/-- `_dl_debug_initialize`'s contract, for the namespace 0: System V, no stack frame, no system call. -/
def contract : Contract where
  conv := sysv
  reads := reads
  writes s := [frame s 0, rDebug]
  pre := Pre
  post := Post
  events _ _ evs := evs = []

end FV7z.DebugInit
