import ZellicX86.Spec.Semantics
/-!
# `xsavetest`: the model's side of the differential test of `XSAVE`, `XSAVEC` and `XRSTOR` (PLAN.md §6.4, G1)

Not part of any statement: a test of the model's `Sem.xsave` and `Sem.xrstor` (`Spec/Semantics/X87.lean`,
`Spec/Xsave.lean`, FV_7zip G1) against the processor this runs on (`tools/xsavetest/native.c` runs the same cases
natively, `tools/xsavetest/run.py` generates them and compares). `tools/difftest` cannot: its cases have a 64-byte
buffer and no x87 or opmask state.

Each case is one instruction with its area at `rdi` in a 4096-byte page (an access outside it raises `#PF`, as the
unmapped page after it does natively), `EDX:EAX` the instruction mask, and the whole x87, SSE, AVX and AVX-512 state
given. As in `difftest`, the instruction's program runs in `interp`, a second reading of `Prog.run`'s operations on
this state. A choice the model leaves open (`choose`: reserved bytes, the bits of `XINUSE` the manuals leave open;
`pick`: which of two faults is raised) makes the case `undef`: it is run once for each pattern of its choices (each
all zeros or all ones, the first alternative or the last), and `run.py` accepts the processor's result if it is that
of some pattern, or agrees with two patterns `P ⊆ Q` on every bit where they agree (the choices of `Q` but not `P`
then free). `XINUSE` is `HINT` when given (`run.py` gives the `XSTATE_BV` the processor's `XSAVE` or `XSAVEC` wrote:
its witness of the choice, which the model still bounds by the components not in their initial configuration).

Input, one case per line (hex): `OP RAX RDX OFF LEGACY YMMH ZMMH ZHI K MEM [HINT]`. `OP`: `xsave`, `xsave64`, `xsavec`,
`xsavec64`, `xrstor`, `xrstor64`. `LEGACY`: a 512-byte `FXSAVE64` image the x87 and SSE state is loaded from (as
`FXRSTOR64` loads it); `YMMH`: bits 255–128 of `ZMM0`–`ZMM15` (16 × 16 bytes); `ZMMH`: bits 511–256 of `ZMM0`–`ZMM15`
(16 × 32 bytes); `ZHI`: `ZMM16`–`ZMM31` (16 × 64 bytes); `K`: `k0`–`k7` (8 × 8 bytes); `MEM`: the page (4096 bytes),
the area at offset `OFF`. Every value is bytes, least significant first.

Output, one line per case: `ok MEM LEGACY Z K`, the page and the state after: `LEGACY` the image `FXSAVE64` would
store (its reserved bytes zero), `Z` `ZMM0`–`ZMM31` (32 × 64 bytes), `K` `k0`–`k7`; or `exc NAME`, `nm REASON`,
`undef R0 | R1 | ...` (`Rj` the result of pattern `j`).

Usage: `lake exe xsavetest KEY=VALUE...`, the processor's profile as `native info` prints it (`xcr0`, `mxcsrmask`,
`amd`, `amderr`, `fcsdep`, `fdpexc`, and `dI=EAX,EBX,ECX` for `CPUID.(EAX=0DH,ECX=I)`).
-/
open ZellicX86 ZellicX86.Decode

namespace XsaveTest

def base : Nat := 0x7f0000000000

structure St where
  gpr : Array (BitVec 64)
  x87 : X87
  zmm : Array (BitVec 512)
  k : Array (BitVec 64)
  mxcsr : BitVec 32
  mem : ByteArray
  /-- The choices (`choose` and `pick`) made so far; choice `j` is all ones (`pick`: its last alternative) if bit `j`
  of `pat` is set, all zeros (its first) otherwise, but the first 64-bit `choose` is `hint` when that is given. -/
  idx : Nat := 0
  pat : Nat := 0
  hint : Option (BitVec 64) := none

/-- The exception of an access to the bytes of `[a, a + n)` that `sel` selects: `#GP(0)`/`#SS(0)` for a
non-canonical byte, `#PF` for a byte outside the page. -/
def check (m : MemRef) (n : Nat) (sel : Nat → Bool := fun _ => true) : Option Exception :=
  let as := ((List.range n).filter sel).map m.addr.add
  if as.any (fun a => !a.canonical false) then some (if m.stack then .ss 0 else .gp 0)
  else match as.find? (fun a => !(base ≤ a.toNat ∧ a.toNat < base + 4096)) with
    | some a => some (.pf a .read false)
    | none => none

def rdByte (s : St) (a : Nat) : Byte := BitVec.ofNat 8 (s.mem.get! (a - base)).toNat

def wrBytes (s : St) (a : Addr) (bs : List (Option Byte)) : St :=
  { s with mem := bs.zipIdx.foldl (fun m (b, i) => match b with
      | some b => m.set! ((a.toNat + i) - base) b.toNat.toUInt8
      | none => m) s.mem }

/-- A result; `exc` with the number of choices made before it. -/
inductive Res | ok (s : St) | exc (e : Exception) (n : Nat) | nm (w : NotModelled) | fuel

/-- `Prog.run`'s reading of the operations, on `St`. -/
def interp {α : Type} : Nat → Prog α → St → Res
  | 0, _, _ => .fuel
  | _, .pure _, s => .ok s
  | f + 1, .op o k, s =>
    match o, k with
    | .getReg r, k => interp f (k (s.gpr[r.val]! : BitVec 64)) s
    | .setReg r v, k => interp f (k ()) { s with gpr := s.gpr.set! r.val v }
    | .getRip, k => interp f (k (0x401000 : Addr)) s
    | .setRip _, k => interp f (k ()) s
    | .getFlags, _ => .nm (.feature "xsavetest: flags")
    | .setFlags _, _ => .nm (.feature "xsavetest: flags")
    | .getSegBase _, k => interp f (k (0 : Addr)) s
    | .getThread, _ => .nm (.feature "xsavetest: thread state")
    | .getZmm n, k => interp f (k (s.zmm[n.val]! : BitVec 512)) s
    | .setZmm n v, k => interp f (k ()) { s with zmm := s.zmm.set! n.val v }
    | .getK n, k => interp f (k (s.k[n.val]! : BitVec 64)) s
    | .setK n v, k => interp f (k ()) { s with k := s.k.set! n.val v }
    | .getMxcsr, k => interp f (k (s.mxcsr : BitVec 32)) s
    | .setMxcsr v, k => interp f (k ()) { s with mxcsr := v }
    | .getX87, k => interp f (k (s.x87 : X87)) s
    | .setX87 x, k => interp f (k ()) { s with x87 := x }
    | .load m w _, k => match check m (w / 8) with
      | some e => .exc e s.idx
      | none => interp f (k (ofBytesLE w ((List.range (w / 8)).map fun i => rdByte s (m.addr.toNat + i)) : BitVec w)) s
    | .store m w v, k => match check m (w / 8) with
      | some e => .exc e s.idx
      | none => interp f (k ()) (wrBytes s m.addr ((toBytesLE v (w / 8)).map some))
    | .loadSel m n sel _, k => match check m n (sel.getLsbD ·) with
      | some e => .exc e s.idx
      | none => interp f (k (ofBytesLE (8 * n) ((List.range n).map fun i =>
          if sel.getLsbD i then rdByte s (m.addr.toNat + i) else 0) : BitVec (8 * n))) s
    | .storeSel m n sel v, k => match check m n (sel.getLsbD ·) with
      | some e => .exc e s.idx
      | none => interp f (k ()) (wrBytes s m.addr ((toBytesLE v n).zipIdx.map fun (b, i) =>
          if sel.getLsbD i then some b else none))
    | .rmw .., _ => .nm (.feature "xsavetest: rmw")
    | .checkAligned m n _ b _, k =>
      if m.addr.toNat % n = 0 then interp f (k ()) s
      else match check m b with
        | none => .exc (.gp 0) s.idx
        | some _ => .exc (.gp 0) s.idx   -- `Prog.run` picks between the two; `run.py` accepts either
    | .checkAll as, k => match as.findSome? (fun (m, _, n) => check m n) with
      | some e => .exc e s.idx
      | none => interp f (k ()) s
    | .fence _, k => interp f (k ()) s
    | .choose w, k =>
      match s.hint with
      | some h =>
        if hw : w = 64 then interp f (k (hw ▸ h : BitVec w)) { s with hint := none }
        else interp f (k (if s.pat.testBit s.idx then BitVec.allOnes w else 0 : BitVec w)) { s with idx := s.idx + 1 }
      | none => interp f (k (if s.pat.testBit s.idx then BitVec.allOnes w else 0 : BitVec w)) { s with idx := s.idx + 1 }
    | .pick n, k =>
      if n = 0 then interp f (k (0 : Fin (n + 1))) s
      else interp f (k (if s.pat.testBit s.idx then Fin.last n else (0 : Fin (n + 1)))) { s with idx := s.idx + 1 }
    | .tsc, _ => .nm (.feature "xsavetest: tsc")
    | .xinuse _, _ => .nm (.feature "xsavetest: xinuse")
    | .raise e, _ => .exc e s.idx
    | .notModelled w, _ => .nm w

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
def ofHex (s : String) : Nat := s.foldl (fun n c => 16 * n + hexDigit c) 0
def bytesOfHex (s : String) : Array Byte :=
  let cs := s.toList.toArray
  (Array.range (cs.size / 2)).map fun i => BitVec.ofNat 8 (16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!)
def hexN (w n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (w - s.length) '0') ++ s
def hexBytes (bs : List Byte) : String := String.join (bs.map fun b => hexN 2 b.toNat)

def excName : Exception → String
  | .gp _ => "gp" | .ss _ => "ss" | .pf .. => "pf" | .ud => "ud" | .ac => "ac" | e => reprStr e

/-- The processor's profile from `native info`'s `KEY=VALUE` words. -/
def prof (kv : String → Nat) : Profile where
  vendor := if kv "amd" = 1 then .amd else .intel
  feat := default
  aux := ⟨0, 0, 2048⟩; cpus := 1
  cpuid := fun _ leaf sub =>
    if leaf = 0xD then ⟨BitVec.ofNat 32 (kv s!"d{sub.toNat}.eax"), BitVec.ofNat 32 (kv s!"d{sub.toNat}.ebx"),
                        BitVec.ofNat 32 (kv s!"d{sub.toNat}.ecx"), 0⟩
    else ⟨0, 0, 0, 0⟩
  xcr0 := some (BitVec.ofNat 64 (kv "xcr0")); mxcsrMask := BitVec.ofNat 32 (kv "mxcsrmask"); tscAux := fun _ => 0
  fdpExcptnOnly := kv "fdpexc" = 1; fcsDeprecated := kv "fcsdep" = 1; amdErrPtrs := kv "amderr" = 1
  x87LoadsKnown := true
  linux := { vdsoData := fun _ => true, vdsoText := [], compatBrk := false }

def opBytes : String → Option (List Nat)
  | "xsave" => some [0x0F, 0xAE, 0x27] | "xsave64" => some [0x48, 0x0F, 0xAE, 0x27]
  | "xsavec" => some [0x0F, 0xC7, 0x27] | "xsavec64" => some [0x48, 0x0F, 0xC7, 0x27]
  | "xrstor" => some [0x0F, 0xAE, 0x2F] | "xrstor64" => some [0x48, 0x0F, 0xAE, 0x2F]
  | _ => none

/-- The output line of state `s`: the page, then the image `FXSAVE64` stores (`xsaveRuns` of x87 and SSE, reserved
bytes zero), `ZMM0`–`ZMM31` and `k0`–`k7`. -/
def line (p : Profile) (s : St) : String :=
  let v : VecRegs := ⟨fun j => s.zmm[j.val]!, fun j => s.k[j.val]!, s.mxcsr⟩
  let runs := xsaveRuns p s.x87 v 0 3 (0 : BitVec 4096) true
  let leg := (List.range 512).map fun o =>
    (runs.findSome? fun (q, bs) => if q ≤ o then bs[o - q]? else none).getD 0
  s!"ok {hexBytes (s.mem.toList.map fun b => BitVec.ofNat 8 b.toNat)} {hexBytes leg} " ++
  s!"{String.join ((List.range 32).map fun j => hexBytes (toBytesLE s.zmm[j]! 64))} " ++
  s!"{String.join ((List.range 8).map fun j => hexBytes (toBytesLE s.k[j]! 8))}"

def runCase (p : Profile) (l : String) : String :=
  match l.splitOn " " with
  | op :: rax :: rdx :: off :: legH :: ymmhH :: zmmhH :: zhiH :: kH :: memH :: rest =>
    match opBytes op with
    | none => "bad"
    | some code =>
    let fetch : Nat → Option Byte := fun i => (code[i]?).map (BitVec.ofNat 8)
    match decode p.feat fetch with
    | .ok i =>
      let leg := bytesOfHex legH; let ymmh := bytesOfHex ymmhH; let zmmh := bytesOfHex zmmhH
      let zhi := bytesOfHex zhiH; let ks := bytesOfHex kH
      let w (a : Array Byte) (o n : Nat) (m : Nat) : BitVec m := ofBytesLE m ((List.range n).map fun k => a[o + k]!)
      let x := x87Load p X87.init (fun o => leg[o]!) true
      let zmm := (Array.range 32).map fun j =>
        if j < 16 then w leg (160 + 16 * j) 16 512 ||| (w ymmh (16 * j) 16 512 <<< 128) ||| (w zmmh (32 * j) 32 512 <<< 256)
        else w zhi (64 * (j - 16)) 64 512
      let gpr := (Array.replicate 16 (0 : BitVec 64)) |>.set! 0 (BitVec.ofNat 64 (ofHex rax))
        |>.set! 2 (BitVec.ofNat 64 (ofHex rdx)) |>.set! 7 (BitVec.ofNat 64 (base + ofHex off))
      let s : St := { gpr, x87 := x, zmm, k := (Array.range 8).map fun j => w ks (8 * j) 8 64,
                      mxcsr := w leg 24 4 32, mem := ⟨(bytesOfHex memH).map (·.toNat.toUInt8)⟩,
                      hint := rest.head?.map fun h => BitVec.ofNat 64 (ofHex h) }
      let res (r : Res) : String := match r with
        | .ok s' => line p s'
        | .exc e _ => s!"exc {excName e}"
        | .nm w => s!"nm {(reprStr w).replace " " "_" |>.replace "\n" "_"}"
        | .fuel => "nm fuel"
      let count : Res → Nat := fun | .ok s' => s'.idx | .exc _ n => n | _ => 0
      -- every pattern of the choices made (at most 6): until no run makes more than the patterns cover
      let rec go : Nat → Nat → List Res
        | fuel, c =>
          let rs := (List.range (2 ^ c)).map fun q => interp 100000 (exec p i) { s with pat := q }
          let c' := min 6 (rs.foldl (fun n r => max n (count r)) c)
          match fuel with
          | 0 => rs
          | fuel + 1 => if c' ≤ c then rs else go fuel c'
      match go 6 0 with
      | [r] => res r
      | rs => "undef " ++ " | ".intercalate (rs.map res)
    | .ud => "exc ud"
    | .nm m o => s!"nm encoding_{hexN 2 m}_{hexN 2 o}"
    | _ => "exc decode"
  | _ => "bad"

end XsaveTest

def main (args : List String) : IO Unit := do
  let kv (k : String) : Nat :=
    match args.find? (·.startsWith (k ++ "=")) with
    | some a => XsaveTest.ofHex ((a.drop (k.length + 1)).toString)
    | none => 0
  -- `dI=EAX,EBX,ECX` as `dI.eax=`, `dI.ebx=`, `dI.ecx=`
  let args := args.flatMap fun a =>
    match a.splitOn "=" with
    | [k, v] => match v.splitOn "," with
      | [e, b, c] => [s!"{k}.eax={e}", s!"{k}.ebx={b}", s!"{k}.ecx={c}"]
      | _ => [a]
    | _ => [a]
  let kv (k : String) : Nat :=
    match args.find? (·.startsWith (k ++ "=")) with
    | some a => XsaveTest.ofHex ((a.drop (k.length + 1)).toString)
    | none => kv k
  let p := XsaveTest.prof kv
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    stdout.putStrLn (XsaveTest.runCase p l.trimAsciiEnd.toString)
