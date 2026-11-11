import ZellicX86.Spec.Semantics
/-!
# `difftest`: the model's side of the differential test of instruction semantics (PLAN.md §6.4, G1)

Not part of any statement: a test of the model's extensions (and, as a control, of instructions it already had)
against the processor this runs on (`tools/difftest/native.c` runs the same cases natively; `tools/difftest/run.py`
generates the cases and compares).

Each case is one instruction with the general registers `rax` (the address of a 64-byte, 64-aligned buffer plus an
offset), `rcx` and `rdx`, `RFLAGS`, `YMM0`–`YMM7` and the buffer given. The instruction is decoded by the model's
decoder and its program (`exec`) run by `interp` below, which follows `Prog.run` (`Spec/Machine.lean`) for the
registers, flags, vector state and memory, on a memory of the buffer alone: an access outside it raises `#PF`, as an
unmapped page would. `Prog.run` itself is not run (it needs a whole process state): `interp` is a second reading of
the same operations, so this tests the `Sem.*` definitions and the decoder, not `Prog.run`. A value the manuals leave
undefined (`choose`) makes the case `undef`: it is run again with every such value all ones instead of all zeros, and
the comparison is of the bits the two runs agree on.

Input, one case per line: `BYTES RAX_OFF RCX RDX RFLAGS YMM0 ... YMM7 MEM` (hex; `YMMi` 64 digits, most significant
first; `MEM` 128 digits, byte 0 first). Output, one line per case: `ok RFLAGS RCX RDX YMM0 ... YMM7 MEM`, or
`exc NAME`, or `undef OK0 | OK1` (the two runs, each an `ok` line), or `nm REASON`.
Usage: `lake exe difftest [amd] FEATURE... < cases > results` (FEATURE: a field of `Features` the processor has;
`amd` on an AMD processor, else Intel)
-/
open ZellicX86 ZellicX86.Decode

namespace DiffTest

def base : Nat := 0x7f0000001000

structure St where
  gpr : Array (BitVec 64)
  rip : Addr
  fl : Rflags
  zmm : Array (BitVec 512)
  mxcsr : BitVec 32
  mem : ByteArray
  undef : Bool := false
  /-- What `choose` answers: all zeros, or all ones. -/
  ones : Bool := false

def Rflags.ofBits (v : Nat) : Rflags :=
  let b (i : Nat) := v.testBit i
  { cf := b 0, pf := b 2, af := b 4, zf := b 6, sf := b 7, tf := false, if_ := true, df := b 10, of := b 11,
    iopl := 0, nt := false, rf := false, vm := false, ac := false, vif := false, vip := false, id := b 21 }

/-- The exception of an access of `n` bytes at `a`: `#GP(0)`/`#SS(0)` for a non-canonical byte, `#PF` for a byte
outside the buffer. -/
def check (m : MemRef) (n : Nat) : Option Exception :=
  let as := (List.range n).map fun i => m.addr.add i
  if as.any (fun a => !a.canonical false) then some (if m.stack then .ss 0 else .gp 0)
  else match as.find? (fun a => !(base ≤ a.toNat ∧ a.toNat < base + 64)) with
    | some a => some (.pf a .read false)
    | none => none

def rd (s : St) (a : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => BitVec.ofNat 8 (s.mem.get! ((a.toNat + i) - base)).toNat

def wr (s : St) (a : Addr) (bs : List Byte) : St :=
  { s with mem := (bs.zipIdx).foldl (fun m (b, i) => m.set! ((a.toNat + i) - base) b.toNat.toUInt8) s.mem }

inductive Res | ok (s : St) | exc (e : Exception) | nm (w : NotModelled) | fuel

/-- `Prog.run`'s reading of the operations, on `St` (see the module comment). -/
def interp {α : Type} : Nat → Prog α → St → Res
  | 0, _, _ => .fuel
  | _, .pure _, s => .ok s
  | f + 1, .op o k, s =>
    match o, k with
    | .getReg r, k => interp f (k (s.gpr[r.val]! : BitVec 64)) s
    | .setReg r v, k => interp f (k ()) { s with gpr := s.gpr.set! r.val v }
    | .getRip, k => interp f (k (s.rip : Addr)) s
    | .setRip v, k => interp f (k ()) { s with rip := v }
    | .getFlags, k => interp f (k (s.fl : Rflags)) s
    | .setFlags v, k => interp f (k ()) { s with fl := v }
    | .getSegBase _, k => interp f (k (0 : Addr)) s
    | .getThread, _ => .nm (.feature "difftest: thread state")
    | .getZmm n, k => interp f (k (s.zmm[n.val]! : BitVec 512)) s
    | .setZmm n v, k => interp f (k ()) { s with zmm := s.zmm.set! n.val v }
    | .getK _, k => interp f (k (0 : BitVec 64)) s
    | .setK _ _, k => interp f (k ()) s
    | .getMxcsr, k => interp f (k (s.mxcsr : BitVec 32)) s
    | .setMxcsr v, k => interp f (k ()) { s with mxcsr := v }
    | .getX87, _ => .nm (.feature "difftest: x87 state")
    | .setX87 _, _ => .nm (.feature "difftest: x87 state")
    | .load m w _, k => match check m (w / 8) with
      | some e => .exc e
      | none => interp f (k (ofBytesLE w (rd s m.addr (w / 8)) : BitVec w)) s
    | .store m w v, k => match check m (w / 8) with
      | some e => .exc e
      | none => interp f (k ()) (wr s m.addr (toBytesLE v (w / 8)))
    | .loadSel .., _ | .storeSel .., _ => .nm (.feature "difftest: masked access")
    | .rmw m w g, k => match check m (w / 8) with
      | some e => .exc e
      | none =>
        let old := ofBytesLE w (rd s m.addr (w / 8))
        interp f (k (old : BitVec w)) (wr s m.addr (toBytesLE (g old) (w / 8)))
    | .checkAligned m n _ b mm, k =>
      if m.addr.toNat % n = 0 ∨ (mm ∧ s.mxcsr.getLsbD 17) then interp f (k ()) s
      else match check m b with
        | none => .exc (.gp 0)
        | some _ => .exc (.gp 0)   -- `Prog.run` picks between the two; the processor's choice is compared loosely
    | .checkAll as, k => match as.findSome? (fun (m, _, n) => check m n) with
      | some e => .exc e
      | none => interp f (k ()) s
    | .fence _, k => interp f (k ()) s
    | .choose w, k => interp f (k (if s.ones then BitVec.allOnes w else 0 : BitVec w)) { s with undef := true }
    | .pick n, k => interp f (k (0 : Fin (n + 1))) s
    | .tsc, _ => .nm (.feature "difftest: tsc")
    | .xinuse _, _ => .nm (.feature "difftest: xinuse")
    | .raise e, _ => .exc e
    | .notModelled w, _ => .nm w

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
def ofHex (s : String) : Nat := s.foldl (fun n c => 16 * n + hexDigit c) 0
def bytesOfHex (s : String) : List Nat :=
  let cs := s.toList
  (List.range (cs.length / 2)).map fun i => 16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!
def hexN (w : Nat) (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (w - s.length) '0') ++ s

def excName : Exception → String
  | .gp _ => "gp" | .ss _ => "ss" | .pf .. => "pf" | .ud => "ud" | .ac => "ac" | e => reprStr e

/-- The features of the processor the test runs on, named by `Features`' fields (`run.py` reads them from
`/proc/cpuinfo` and passes them as arguments), so that the model decodes as that processor does: an instruction it
lacks is `#UD` on both sides. -/
def featOf (has : String → Bool) : Features where
  ssse3 := has "ssse3"; sse41 := has "sse41"; sha := has "sha"; bmi1 := has "bmi1"; lzcnt := has "lzcnt"
  avx := has "avx"; avx512f := has "avx512f"; apx := has "apx"; pku := has "pku"; nx := has "nx"
  la57 := has "la57"; sse42 := has "sse42"; bmi2 := has "bmi2"; avx2 := has "avx2"; avx512bw := has "avx512bw"
  avx512dq := has "avx512dq"; avx512vl := has "avx512vl"; movbe := has "movbe"; rdtscp := has "rdtscp"
  sse3 := has "sse3"; fma := has "fma"; cetSs := has "cetSs"; rtm := has "rtm"; hle := has "hle"
  aes := has "aes"; vaes := has "vaes"; popcnt := has "popcnt"; mpx := has "mpx"

/-- The profile of the processor the test runs on: its vendor (`run.py` passes `amd` on an AMD processor, from
`/proc/cpuinfo`'s `vendor_id`; the model's semantics differ by vendor, e.g. `shaAligned`) and its features. -/
def prof (vendor : Vendor) (feat : Features) : Profile where
  vendor; feat; aux := ⟨0, 0, 2048⟩; cpus := 1; cpuid := fun _ _ _ => ⟨0, 0, 0, 0⟩
  xcr0 := some 0x7; mxcsrMask := 0xffff; tscAux := fun _ => 0; fdpExcptnOnly := true; fcsDeprecated := true
  amdErrPtrs := false; x87LoadsKnown := true; linux := { vdsoData := fun _ => true, vdsoText := [], compatBrk := false }

def runCase (vendor : Vendor) (feat : Features) (l : String) : String :=
  match l.splitOn " " with
  | bytes :: off :: rcx :: rdx :: fl :: rest =>
    let xs := rest.take 8
    let memHex := (rest.drop 8).headD ""
    let code := bytesOfHex bytes
    -- natively the stub's code follows the instruction (`pushfq; pop qword [rdi+272]; ...`), so up to 15 bytes
    -- can be fetched: the model's `#UD` for a form whose feature is missing needs that (`lengthNotSettled`)
    let code := code ++ [0x9c, 0x8f, 0x87, 0x10, 0x01, 0x00, 0x00, 0x48, 0x89, 0x8f, 0x18, 0x01, 0x00, 0x00, 0x48]
    let fetch : Nat → Option Byte := fun i => if i < 15 then (code[i]?).map (BitVec.ofNat 8) else none
    match decode feat fetch with
    | .ok i =>
      let gpr := (Array.replicate 16 (0 : BitVec 64))
        |>.set! 0 (BitVec.ofNat 64 (base + ofHex off)) |>.set! 1 (BitVec.ofNat 64 (ofHex rcx))
        |>.set! 2 (BitVec.ofNat 64 (ofHex rdx))
      let zmm := (Array.replicate 32 (0 : BitVec 512)).mapIdx fun j z =>
        if h : j < xs.length then BitVec.ofNat 512 (ofHex xs[j]) else z
      let s : St := { gpr, rip := BitVec.ofNat 64 (0x401000 + i.len), fl := Rflags.ofBits (ofHex fl), zmm,
                      mxcsr := 0x1f80, mem := ⟨(bytesOfHex memHex).toArray.map Nat.toUInt8⟩ }
      let line (s' : St) : String :=
        let flm := s'.fl.toBits.toNat &&& 0x8d5
        let xmm := (List.range 8).map fun j => hexN 64 ((s'.zmm[j]!).toNat % 2 ^ 256)
        let mem := String.join (s'.mem.toList.map fun b => hexN 2 b.toNat)
        s!"ok {hexN 3 flm} {hexN 16 (s'.gpr[1]!).toNat} {hexN 16 (s'.gpr[2]!).toNat} {" ".intercalate xmm} {mem}"
      let res (r : Res) : String := match r with
        | .ok s' => line s'
        | .exc e => s!"exc {excName e}"
        | .nm w => s!"nm {(reprStr w).replace " " "_"}"
        | .fuel => "nm fuel"
      match interp 100000 (exec (prof vendor feat) i) s with
      | .ok s' =>
        if s'.undef then s!"undef {line s'} | {res (interp 100000 (exec (prof vendor feat) i) { s with ones := true })}"
        else line s'
      | r => res r
    | .ud => "exc ud"
    | .nm m o => s!"nm encoding_{hexN 2 m}_{hexN 2 o}"
    | _ => "exc decode"
  | _ => "bad"

end DiffTest

def main (args : List String) : IO Unit := do
  let feat := DiffTest.featOf (args.contains ·)
  let vendor : Vendor := if args.contains "amd" then .amd else .intel
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    stdout.putStrLn (DiffTest.runCase vendor feat l.trimAsciiEnd.toString)
