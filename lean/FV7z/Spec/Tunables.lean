import ZellicX86.Spec.Statement
/-!
# The contract of `__tunables_init` in `7zzs` (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/TunablesInit.lean`).

`__tunables_init` (glibc 2.31, `elf/dl-tunables.c`) is called once by `__libc_start_main` with the environment
(`rdi`: the array of pointers to the strings `NAME=value`, ended by a null pointer). It looks in the environment for
`GLIBC_TUNABLES` and for the names that the list of tunables (`tunable_list`, 26 entries of 56 bytes at `0x791660`)
gives as environment aliases (`env_alias`), and sets the tunables they name.

The contract is for a start without them: with no string of the environment beginning with `GLIBC_TUNABLES=` or with
an alias followed by `=`, and `__libc_enable_secure` (`0x791ce0`) 0, a call

- reads only `__libc_enable_secure`, the string `GLIBC_TUNABLES` of the file (`0x6f32b3`), the list of tunables, the
  environment's array and strings, and the aliases' strings;
- writes only its stack frame (104 bytes);
- returns to its caller with the callee-saved registers kept, having made no system call.

So the tunables stay as the file has them. The contract has two parameters, what the caller knows of memory: the
environment `E` and the aliases `A`, each a list of strings with their addresses.
-/
namespace FV7z.Tunables
open ZellicX86

/-- `GLIBC_TUNABLES`. -/
def glibcTunables : List Byte := [0x47, 0x4c, 0x49, 0x42, 0x43, 0x5f, 0x54, 0x55, 0x4e, 0x41, 0x42, 0x4c, 0x45, 0x53]

/-- A C string at `p` in memory `m`: the bytes `bs`, none of them 0, then a 0. -/
def CStr (m : Memory) (p : Addr) (bs : List Byte) : Prop := 0 ∉ bs ∧ readBytes m p (bs.length + 1) = bs ++ [0]

/-- The 64-bit word at `a`. -/
def word (m : Memory) (a : Addr) : Addr := ofBytesLE 64 (readBytes m a 8)

/-- `tunable_list[i].env_alias`: the 8 bytes at `0x30` of the `i`-th entry. -/
def aliasPtr (m : Memory) (i : Nat) : Addr := word m (BitVec.ofNat 64 (0x791690 + 56 * i))

/-! ## The regions of a call from `s` -/

/-- `__libc_enable_secure`. -/
def rSecure : Rgn := ⟨0x791ce0, 4⟩
/-- The string `GLIBC_TUNABLES` of the file, with its 0. -/
def rName : Rgn := ⟨0x6f32b3, 15⟩
/-- `tunable_list`. -/
def rList : Rgn := ⟨0x791660, 1456⟩
/-- The environment's array: a pointer for each string, and the null pointer. -/
def rEnvp (E : List (Addr × List Byte)) (s : State) : Rgn := ⟨s.cpu.gpr.rdi, 8 * (E.length + 1)⟩
/-- A string with its 0. -/
def rStr (e : Addr × List Byte) : Rgn := ⟨e.1, e.2.length + 1⟩

/-- What a call reads besides its stack frame. -/
def reads (A E : List (Addr × List Byte)) (s : State) : List Rgn :=
  rSecure :: rName :: rList :: rEnvp E s :: (E.map rStr ++ A.map rStr)

/-- What a call assumes: `__libc_enable_secure` is 0; the file's `GLIBC_TUNABLES` is in memory; the environment's
array at `rdi` points to the strings `E` and ends with a null pointer; every tunable's alias is null or one of the
strings `A`; no string of the environment begins with `GLIBC_TUNABLES=` or with an alias and `=` (`0x3d`); and the
stack frame is apart from what is read. -/
structure Pre (A E : List (Addr × List Byte)) (s : State) : Prop where
  secure : readBytes s.proc.mm.mem 0x791ce0 4 = [0, 0, 0, 0]
  name : readBytes s.proc.mm.mem 0x6f32b3 15 = glibcTunables ++ [0]
  envp : ∀ i (h : i < E.length), word s.proc.mm.mem (Addr.add s.cpu.gpr.rdi (8 * i)) = E[i].1
  envEnd : word s.proc.mm.mem (Addr.add s.cpu.gpr.rdi (8 * E.length)) = 0
  nonNull : ∀ e ∈ E, e.1 ≠ 0
  strings : ∀ e ∈ E, CStr s.proc.mm.mem e.1 e.2
  alias : ∀ i, i < 26 → aliasPtr s.proc.mm.mem i = 0 ∨ ∃ a ∈ A, a.1 = aliasPtr s.proc.mm.mem i
  aliases : ∀ a ∈ A, CStr s.proc.mm.mem a.1 a.2
  noTunables : ∀ e ∈ E, ¬ (glibcTunables ++ [0x3d]) <+: e.2
  noAlias : ∀ a ∈ A, ∀ e ∈ E, ¬ (a.2 ++ [0x3d]) <+: e.2
  apart : Apart [frame s 104] (reads A E s)

/-- `__tunables_init`'s contract, for an environment `E` without `GLIBC_TUNABLES` and without the aliases `A` of
the tunables: System V, a stack frame of 104 bytes, no system call. -/
def contract (A E : List (Addr × List Byte)) : Contract where
  conv := sysv
  reads := reads A E
  writes s := [frame s 104]
  pre := Pre A E
  post _ _ := True
  events _ _ evs := evs = []

end FV7z.Tunables
