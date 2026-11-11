import ZellicX86.Spec.Statement
/-!
# The contract of `_dl_aux_init` in `7zzs` (PLAN.md G3, startup)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/AuxInit.lean`).

`_dl_aux_init` (glibc 2.31, `elf/dl-support.c`) is the first function `__libc_start_main` calls, with the auxiliary
vector the kernel leaves above the environment (`rdi`: entries of two 64-bit words, a type and a value, ended by an
entry of type 0, `AT_NULL`). It stores the vector's address (`_dl_auxv`) and goes through the entries; an entry of one
of eleven types sets a variable of the C library, the others are skipped. In the compiled code the `switch` is a jump
through a table of 31 offsets in `.rodata` (`0x6f3660`, types 3 to 33), and the variables are kept in registers and in
the red zone until the vector's end.

The contract is for a vector with an entry `AT_SECURE` (type 23; Linux always gives one). Then what `AT_UID`, `AT_EUID`,
`AT_GID` and `AT_EGID` say is not used, and a call

- reads only the vector and the jump table;
- writes only its stack frame (104 bytes), `_dl_auxv` and the twelve variables;
- returns to its caller with the callee-saved registers kept, having made no system call, `_dl_auxv` the vector's
  address and the variables as the entries set them one after the other (`step`), from what they were at the call.

So with a vector whose `AT_SECURE` entries are all 0, `__libc_enable_secure` is 0 after the call, whatever the file
has there. The contract's parameter is what the caller knows of memory: the vector's entries `X`.
-/
namespace FV7z.AuxInit
open ZellicX86

/-- The 64-bit word at `a`. -/
def word (m : Memory) (a : Addr) : BitVec 64 := ofBytesLE 64 (readBytes m a 8)

/-- The variables `_dl_aux_init` sets, by their names in glibc. -/
structure Vars where
  /-- `_dl_pagesize` (`0x7933d8`). -/
  pagesize : BitVec 64
  /-- `_dl_clktck` (`0x7a85c0`, an `int`). -/
  clktck : BitVec 32
  /-- `_dl_phdr` (`0x7a8580`). -/
  phdr : BitVec 64
  /-- `_dl_phnum` (`0x7a8598`). -/
  phnum : BitVec 64
  /-- `_dl_platform` (`0x7a8548`). -/
  platform : BitVec 64
  /-- `_dl_hwcap` (`0x7a4ac8`). -/
  hwcap : BitVec 64
  /-- `_dl_hwcap2` (`0x7a4ac0`). -/
  hwcap2 : BitVec 64
  /-- `_dl_sysinfo_dso` (`0x7a8508`). -/
  sysinfoDso : BitVec 64
  /-- `_dl_fpu_control` (`0x7933cc`, 16 bits). -/
  fpuControl : BitVec 16
  /-- `__libc_enable_secure` (`0x791ce0`, an `int`). -/
  secure : BitVec 32
  /-- `__libc_enable_secure_decided` (`0x7a85c4`, an `int`). -/
  decided : BitVec 32
  /-- `_dl_random` (`0x791ca0`). -/
  random : BitVec 64

/-- The variables in memory. -/
def vars (m : Memory) : Vars where
  pagesize := ofBytesLE 64 (readBytes m 0x7933d8 8)
  clktck := ofBytesLE 32 (readBytes m 0x7a85c0 4)
  phdr := ofBytesLE 64 (readBytes m 0x7a8580 8)
  phnum := ofBytesLE 64 (readBytes m 0x7a8598 8)
  platform := ofBytesLE 64 (readBytes m 0x7a8548 8)
  hwcap := ofBytesLE 64 (readBytes m 0x7a4ac8 8)
  hwcap2 := ofBytesLE 64 (readBytes m 0x7a4ac0 8)
  sysinfoDso := ofBytesLE 64 (readBytes m 0x7a8508 8)
  fpuControl := ofBytesLE 16 (readBytes m 0x7933cc 2)
  secure := ofBytesLE 32 (readBytes m 0x791ce0 4)
  decided := ofBytesLE 32 (readBytes m 0x7a85c4 4)
  random := ofBytesLE 64 (readBytes m 0x791ca0 8)

/-- What an entry of the vector, a type and a value, does to the variables: `AT_PHDR` (3), `AT_PHNUM` (5),
`AT_PAGESZ` (6, a value 0 is not taken), `AT_PLATFORM` (15), `AT_HWCAP` (16), `AT_CLKTCK` (17), `AT_FPUCW` (18),
`AT_SECURE` (23), `AT_RANDOM` (25), `AT_HWCAP2` (26), `AT_SYSINFO_EHDR` (33); the others nothing. -/
def step (v : Vars) (e : BitVec 64 × BitVec 64) : Vars :=
  if e.1 = 3 then { v with phdr := e.2 } else
  if e.1 = 5 then { v with phnum := e.2 } else
  if e.1 = 6 then (if e.2 = 0 then v else { v with pagesize := e.2 }) else
  if e.1 = 15 then { v with platform := e.2 } else
  if e.1 = 16 then { v with hwcap := e.2 } else
  if e.1 = 17 then { v with clktck := e.2.setWidth 32 } else
  if e.1 = 18 then { v with fpuControl := e.2.setWidth 16 } else
  if e.1 = 23 then { v with secure := e.2.setWidth 32, decided := 1 } else
  if e.1 = 25 then { v with random := e.2 } else
  if e.1 = 26 then { v with hwcap2 := e.2 } else
  if e.1 = 33 then { v with sysinfoDso := e.2 } else v

/-- `_dl_auxv` (`0x7a8540`) and the twelve variables. -/
def globals : List Rgn :=
  [⟨0x7a8540, 8⟩, ⟨0x7933d8, 8⟩, ⟨0x7a85c0, 4⟩, ⟨0x7a8580, 8⟩, ⟨0x7a8598, 8⟩, ⟨0x7a8548, 8⟩, ⟨0x7a4ac8, 8⟩,
    ⟨0x7a4ac0, 8⟩, ⟨0x7a8508, 8⟩, ⟨0x7933cc, 2⟩, ⟨0x791ce0, 4⟩, ⟨0x7a85c4, 4⟩, ⟨0x791ca0, 8⟩]

/-- The `switch`'s jump table in the file: for the types 3 to 33, the 32-bit offset from the table to the case. -/
def jumpTable : List Byte := [
  0x90, 0xc1, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0x70, 0xc1, 0xf7, 0xff, 0x40, 0xc1, 0xf7, 0xff,
  0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff,
  0x20, 0xc1, 0xf7, 0xff, 0x00, 0xc1, 0xf7, 0xff, 0xe0, 0xc0, 0xf7, 0xff, 0xc0, 0xc0, 0xf7, 0xff,
  0x98, 0xc0, 0xf7, 0xff, 0x70, 0xc0, 0xf7, 0xff, 0x48, 0xc0, 0xf7, 0xff, 0x20, 0xc0, 0xf7, 0xff,
  0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff,
  0xf0, 0xbf, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xa0, 0xbe, 0xf7, 0xff, 0xc8, 0xbf, 0xf7, 0xff,
  0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff,
  0xb0, 0xbe, 0xf7, 0xff, 0xb0, 0xbe, 0xf7, 0xff, 0xa0, 0xbf, 0xf7, 0xff]

/-- The vector: its entries and the type of the one that ends it. -/
def rVec (X : List (BitVec 64 × BitVec 64)) (s : State) : Rgn := ⟨s.cpu.gpr.rdi, 16 * X.length + 8⟩
/-- The jump table. -/
def rTable : Rgn := ⟨0x6f3660, 124⟩

/-- What a call reads besides what it writes. -/
def reads (X : List (BitVec 64 × BitVec 64)) (s : State) : List Rgn := [rVec X s, rTable]

/-- What a call assumes: the vector at `rdi` has the entries `X`, none of type 0, then a type 0; one of the entries is
`AT_SECURE` (23); the file's jump table is in memory; and the stack frame, the variables and what is read are
apart. -/
structure Pre (X : List (BitVec 64 × BitVec 64)) (s : State) : Prop where
  types : ∀ i (h : i < X.length), word s.proc.mm.mem (Addr.add s.cpu.gpr.rdi (16 * i)) = X[i].1
  values : ∀ i (h : i < X.length), word s.proc.mm.mem (Addr.add s.cpu.gpr.rdi (16 * i + 8)) = X[i].2
  nonNull : ∀ e ∈ X, e.1 ≠ 0
  vecEnd : word s.proc.mm.mem (Addr.add s.cpu.gpr.rdi (16 * X.length)) = 0
  secure : ∃ e ∈ X, e.1 = 23
  table : readBytes s.proc.mm.mem 0x6f3660 124 = jumpTable
  apart : Apart (frame s 104 :: globals) (reads X s)
  frameApart : Apart [frame s 104] globals

/-- What a call leaves: `_dl_auxv` is the vector's address, and the variables are as the entries set them. -/
structure Post (X : List (BitVec 64 × BitVec 64)) (s s' : State) : Prop where
  auxv : word s'.proc.mm.mem 0x7a8540 = s.cpu.gpr.rdi
  vars : vars s'.proc.mm.mem = X.foldl step (vars s.proc.mm.mem)

/-- `_dl_aux_init`'s contract, for a vector `X` with an `AT_SECURE` entry: System V, a stack frame of 104 bytes, no
system call. -/
def contract (X : List (BitVec 64 × BitVec 64)) : Contract where
  conv := sysv
  reads := reads X
  writes s := frame s 104 :: globals
  pre := Pre X
  post := Post X
  events _ _ evs := evs = []

end FV7z.AuxInit
