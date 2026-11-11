import ZellicX86.Spec.Linux.Syscall
import ZellicX86.Spec.Linux.Exec
/-!
# `systest`: the model's side of the differential test of the G1 system calls (PLAN.md §7 G1)

Not part of any statement: a test of the system calls added for the single-threaded `l`/`t` runs of `7zzs`
(`stat`, `readlink`, `getdents64`, `getcwd`, `sysinfo`, `uname`, `umask`, `ioctl(TCGETS)`, `madvise(MADV_HUGEPAGE)`)
against the kernel this
runs on. `tools/systest/run.py` makes the same calls natively (`syscall(2)` through `ctypes`) and compares.

The model's dispatcher (`syscall`) runs on a process whose memory is one read-write page at `base` (the page after it
unmapped), filled with the pattern `(7 * i + 3) % 256`, and whose descriptor table holds the one descriptor the case
names. What the model asks of the environment is answered from what the kernel answered to the same call with a
buffer it can write (the driver's reference run): the environment's part (the names, the file system, the terminal)
is the same on both sides, and the comparison is of what the model computes itself (layouts, checks, copies, results).
A partial copy (`Request.pick`) takes the most bytes the model allows (`rep movsb` stops at the faulting byte); a
failure the model does not track (`Request.memFail`) does not happen. The argument `thp` says the kernel has
transparent huge pages (`LinuxBoot.thp`).

Input, one case per line: `NR RDI RSI RDX R10 UMASK FD KEY=VALUE...`. A register is hex, or `b+HEX` for `base` plus
an offset; `FD` is `-` or `N:KIND` (`KIND` one of `pages`, `none`, `path`, `other`). The answers: `uname=HEX`,
`sysinfo=HEX`, `cwd=HEX`, `stat=HEX`, `link=HEX`, `dirents=HEX`, `ioctl=HEX` (the kernel's bytes), each also as
`KEY=!ERRNO` (decimal); `w=OFF:HEX` (any number) writes bytes into the page before the call. Output, one line per case: `ok RAX UMASK REQS PAGE` (`REQS` the requests made, `,`-separated,
a path in hex; `PAGE` the page after the call), or `nm REASON`, or `err REASON` (a request the case did not answer).
-/
namespace FV7z.SysTest
open ZellicX86

def base : Nat := 0x100000000

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else c.toNat - 'A'.toNat + 10
def ofHex (s : String) : Nat := s.foldl (fun n c => 16 * n + hexDigit c) 0
def bytesOfHex (s : String) : List Byte :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => BitVec.ofNat 8 (16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!)
def hexN (w : Nat) (n : Nat) : String :=
  let d := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (w - d.length) ++ d
def hexBytes (bs : List Byte) : String := String.join (bs.map fun b => hexN 2 b.toNat)

def reg (t : String) : BitVec 64 :=
  if t.startsWith "b+" then BitVec.ofNat 64 (base + ofHex (t.drop 2).toString) else BitVec.ofNat 64 (ofHex t)

def pattern : Frame := fun o => BitVec.ofNat 8 ((7 * o.toNat + 3) % 256)

def rw : Prot := ⟨true, true, false⟩

def falseFlags : Rflags :=
  ⟨false, false, false, false, false, false, true, false, false, 0, false, false, false, false, false, false, false⟩

def fdEntry (fd : String) : FdTable :=
  match fd.splitOn ":" with
  | [n, k] =>
    let map : FileMap := match k with
      | "pages" => .pages (.inode 0) | "none" => .none | "path" => .path | _ => .other
    fun i => if i = n.toNat! then some ⟨⟨1, k != "path", false, map⟩, false⟩ else none
  | _ => fun _ => none

/-- The page's first contents: the pattern, with the bytes `bs` at offset `o` for each `(o, bs)` of `ws`. -/
def frame (ws : List (Nat × List Byte)) : Frame := fun o =>
  ws.foldl (fun b (w : Nat × List Byte) => if w.1 ≤ o.toNat ∧ o.toNat < w.1 + w.2.length then w.2[o.toNat - w.1]! else b)
    (pattern o)

def state (r : List (BitVec 64)) (umask : Nat) (fd : String) (ws : List (Nat × List Byte)) : State :=
  let files : Files := ⟨fun _ => zeroFrame, fun _ => 0, fun _ => false, fun _ => true⟩
  let mem := regionsMemory [⟨base / 4096, 1, rw, fun _ => .priv (frame ws), false, fun _ => none, rw, false⟩] files []
  let g : Gprs := ⟨r[0]!, 0, r[3]!, 0, 0, 0, r[2]!, r[1]!, 0, 0, r[4]!, 0, 0, 0, 0, 0⟩
  { proc := { mm := ⟨mem, 0, 0⟩, files := fdEntry fd, opens := ⟨fun _ => ⟨0, false, 0⟩, 1000⟩
              sighand := fun _ => SigAction.dfl
              signal := ⟨[], fun _ => ⟨RLIM_INFINITY, RLIM_INFINITY⟩, false⟩, fdMax := 1024
              umask := BitVec.ofNat 9 umask }
    cpu := { gpr := g, rip := 0x401000, rflags := falseFlags, seg := ⟨0x33, 0x2b, 0, 0, 0, 0, 0, 0⟩
             x87 := ⟨fun _ => 0, 0x37f, 0, 0, 0, 0, 0⟩, vec := ⟨fun _ => 0, fun _ => 0, 0x1f80⟩, pkru := 0x55555554 }
    thread := { tid := 1, sigmask := 0, pending := [], altStack := AltStack.disabled, rseq := none
                clearChildTid := 0, robustList := 0, cpuidFaults := false, tscFaults := false, shstk := none
                uid := 1000 } }

abbrev M := StateT (List String) (Except String)

def note (s : String) : M Unit := modify (· ++ [s])

def answer (as : List (String × String)) (key : String) : M (Except Errno (List Byte)) := do
  match as.lookup key with
  | none => throw s!"no answer for {key}"
  | some v =>
    if v.startsWith "!" then
      let e := (v.drop 1).toString.toNat!
      if h : 0 < e ∧ e < 4096 then pure (.error ⟨e, h⟩) else throw s!"bad errno {v}"
    else pure (.ok (bytesOfHex v))

def word (bs : List Byte) (o n : Nat) (w : Nat) : BitVec w := ofBytesLE w ((bs.drop o).take n)

def stat (bs : List Byte) : Stat :=
  let q (o : Nat) : BitVec 64 := word bs o 8 64
  { dev := q 0, ino := q 8, nlink := q 16, mode := word bs 24 4 32, uid := word bs 28 4 32, gid := word bs 32 4 32
    rdev := q 40, size := q 48, blksize := q 56, blocks := q 64, atime := q 72, atimeNsec := q 80, mtime := q 88
    mtimeNsec := q 96, ctime := q 104, ctimeNsec := q 112 }

def sysinfo (bs : List Byte) : SysInfo :=
  let q (o : Nat) : BitVec 64 := word bs o 8 64
  { uptime := q 0, loads := (q 8, q 16, q 24), totalram := q 32, freeram := q 40, sharedram := q 48
    bufferram := q 56, totalswap := q 64, freeswap := q 72, procs := word bs 80 2 16, totalhigh := q 88
    freehigh := q 96, memUnit := word bs 104 4 32 }

/-- The entries of `struct linux_dirent64` records as the kernel wrote them. -/
partial def dirents (bs : List Byte) : Except String (List Dirent) :=
  if bs.isEmpty then pure [] else
  let reclen := (word bs 16 2 16 : BitVec 16).toNat
  let name := ((bs.drop 19).take (reclen - 19)).takeWhile (· != 0)
  if h : 0 < name.length ∧ name.length < 4096 ∧ 0x2f ∉ name then
    if reclen < 24 ∨ reclen > bs.length then throw "bad reclen" else
    let e : Dirent := ⟨word bs 0 8 64, word bs 8 8 64, ⟨(bs[18]!.toNat) % 16, Nat.mod_lt _ (by decide)⟩, name, h⟩
    if e.reclen ≠ reclen then throw s!"reclen {reclen} vs {e.reclen}" else
    return e :: (← dirents (bs.drop reclen))
  else throw "bad name"

def handle (as : List (String × String)) : (r : Request) → M r.Answer
  | .pick n => do note s!"pick{n}"; pure ⟨n, by omega⟩
  | .uname => do
    note "uname"
    match ← answer as "uname" with
    | .ok bs => if h : UtsnameOk bs then pure ⟨bs, h⟩ else throw "uname answer not UtsnameOk"
    | .error _ => throw "uname has no error"
  | .sysinfo => do
    note "sysinfo"
    match ← answer as "sysinfo" with
    | .ok bs => if bs.length = 112 then pure (sysinfo bs) else throw "sysinfo answer size"
    | .error _ => throw "sysinfo has no error"
  | .cwd => do
    note "cwd"
    match ← answer as "cwd" with
    | .ok bs => pure (.path (bs.takeWhile (· != 0)))
    | .error e => pure (.error e)
  | .statPath dir p follow => do
    note s!"statPath:{dir.isSome}:{hexBytes p}:{follow}"
    match ← answer as "stat" with
    | .ok bs => if bs.length = 144 then pure (.ok (stat bs)) else throw "stat answer size"
    | .error e => pure (.error e)
  | .readlink dir p => do
    note s!"readlink:{dir.isSome}:{hexBytes p}"
    match ← answer as "link" with
    | .ok bs => pure (.target bs)
    | .error e => pure (.error e)
  | .dirents f count => do
    note s!"dirents:{f}:{count}"
    match ← answer as "dirents" with
    | .ok bs =>
      match dirents bs with
      | .error m => throw m
      | .ok es => if h : (es.map Dirent.reclen).sum ≤ count then pure (.entries es h) else throw "dirents too long"
    | .error e => pure (.error e)
  | .ioctlGet f cmd n => do
    note s!"ioctl:{f}:{hexN 1 cmd}:{n}"
    match ← answer as "ioctl" with
    | .ok bs => if h : bs.length = n then pure (.ok bs h) else throw s!"ioctl answer size {bs.length}"
    | .error e => pure (.error e)
  | .memFail n => do note s!"memFail{n}"; pure none
  | _ => throw "unexpected request"

def runCase (prof : Profile) (l : String) : String :=
  match l.splitOn " " with
  | nr :: rdi :: rsi :: rdx :: r10 :: um :: fd :: rest =>
    let as := rest.filterMap fun t => match t.splitOn "=" with | [k, v] => some (k, v) | _ => none
    let ws := as.filterMap fun (k, v) => if k != "w" then none else
      match v.splitOn ":" with | [o, h] => some (ofHex o, bytesOfHex h) | _ => none
    let s := state [reg nr, reg rdi, reg rsi, reg rdx, reg r10] (ofHex um) fd ws
    match ((syscall prof s).interp (handle as)).run [] with
    | .error m => s!"err {m}"
    | .ok (.stopped o, _) => s!"nm {repr o}"
    | .ok (.running s' _, reqs) =>
      let page := (List.range 4096).map fun i => s'.proc.mm.mem.readByte (BitVec.ofNat 64 (base + i))
      s!"ok {hexN 16 s'.cpu.gpr.rax.toNat} {hexN 3 s'.proc.umask.toNat} {if reqs.isEmpty then "-" else ",".intercalate reqs} {hexBytes page}"
  | _ => "err bad line"

def prof (thp : Bool) : Profile where
  vendor := .intel; feat := { ssse3 := false, sse41 := false, sha := false, bmi1 := false, lzcnt := false, avx := false, avx512f := false, apx := false, pku := false, nx := false, la57 := false, sse42 := false, bmi2 := false, avx2 := false, avx512bw := false, avx512dq := false, avx512vl := false, movbe := false, rdtscp := false, sse3 := false, fma := false, cetSs := false, rtm := false, hle := false, aes := false, vaes := false, popcnt := false, mpx := false }
  aux := ⟨0, 0, 2048⟩; cpus := 1; cpuid := fun _ _ _ => ⟨0, 0, 0, 0⟩
  xcr0 := some 0x7; mxcsrMask := 0xffff; tscAux := fun _ => 0; fdpExcptnOnly := true; fcsDeprecated := true
  amdErrPtrs := false; linux := { vdsoData := fun _ => true, vdsoText := [], compatBrk := false, thp }

end FV7z.SysTest

def main (args : List String) : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    stdout.putStrLn (FV7z.SysTest.runCase (FV7z.SysTest.prof ("thp" ∈ args)) l.trimAsciiEnd.toString)
    stdout.flush
