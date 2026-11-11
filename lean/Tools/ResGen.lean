import ZellicX86.Spec.Semantics
/-!
# `resgen`: the code and decoding facts of a byte range of `7zzs`, as Lean (PLAN.md G2, "Dispatch theo CPUID")

Not part of any statement: a tool that writes the parts of a proof that are only transcription. For `START` (hex, a
virtual address of `7zzs`, whose file is mapped at `0x400000`) and `LEN` bytes, prints Lean source: the bytes as
`def NAME : List Byte`, the theorem that they are the file's (`Exe.bytesAt`, by `decide +kernel`), and for each
instruction (decoded one after the other from offset 0 under the feature set `full`) a theorem `NAME_dK : ∀ feat, Dec
feat NAME K i`, `i` written with `FV7z.mk`, `gr`, `gh`, `mrip`, `mbd` where it can be; the proof (`rfl` for every
`feat`) is Lean's: an instruction whose decoding depends on the processor fails to build, and is then written by
hand. Padding after the last instruction (`nop`) is decoded too; a proof need not use it.

Usage: `lake exe resgen BINARY NAME START LEN`
-/
open ZellicX86 ZellicX86.Decode

def featFull : Features where
  ssse3 := true; sse41 := true; sha := true; bmi1 := true; lzcnt := true; avx := true; avx512f := true
  apx := false; pku := true; nx := true; la57 := false; sse42 := true; bmi2 := true; avx2 := true
  avx512bw := true; avx512dq := true; avx512vl := true; movbe := true; rdtscp := true; sse3 := true; fma := true
  cetSs := false; rtm := true; hle := true; aes := true; vaes := true; popcnt := true; mpx := false

def ofHex (s : String) : Nat :=
  s.foldl (fun n c => 16 * n + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- `reprStr` on one line. -/
def flat (s : String) : String :=
  " ".intercalate ((s.splitOn "\n").map String.trim)

def showMem (m : MemOp) : String :=
  if m.seg.isNone && m.index.isNone && m.scale == 1 && !m.addr32 then
    if m.ripRel && m.base.isNone then s!"(mrip {m.disp} {m.width})"
    else match m.base with
      | some b => if m.ripRel then flat (reprStr m) else s!"(mbd {b} {m.disp} {m.width})"
      | none => s!"({flat (reprStr m)})"
  else s!"({flat (reprStr m)})"

def showOpd : Opd → String
  | .reg r => if r.high8 then s!"gh {r.num}" else s!"gr {r.width} {r.num}"
  | .imm w v => s!".imm {w} {v}"
  | .rel v => s!".rel {v}"
  | .mem m => s!".mem {showMem m}"
  | o => flat (reprStr o)

def showInst (i : Inst) : String :=
  if i.rep.isNone && !i.lock && i.mask.isNone && !i.zero && i.fop == 0 then
    s!"FV7z.mk ({flat (reprStr i.mn)}) {i.opsz} [{", ".intercalate (i.ops.map showOpd)}] {i.len}"
  else s!"({flat (reprStr i)} : Inst)"

def main (args : List String) : IO UInt32 := do
  let [bin, name, start, len] := args | IO.eprintln "usage: resgen BINARY NAME START LEN"; return 2
  let img ← IO.FS.readBinFile bin
  let a0 := ofHex start
  let n := len.toNat!
  let bytes : List Nat := (List.range n).map fun i => (img.get! (a0 + i - 0x400000)).toNat
  let hb (b : Nat) := "0x" ++ (if b < 16 then "0" else "") ++ hex b
  let rows := (List.range ((n + 15) / 16)).map fun r => ", ".intercalate ((bytes.drop (16 * r)).take 16 |>.map hb)
  IO.println s!"/-- The {n} bytes of `7zzs` at `0x{hex a0}`. -/"
  IO.println s!"def {name} : List Byte := [\n  {",\n  ".intercalate rows}]\n"
  IO.println s!"theorem {name}_pin : Exe.bytesAt V2606.zzs.blob 0x{hex a0} {n} = some {name} := by decide +kernel\n"
  IO.println s!"theorem {name}_length : {name}.length = {n} := rfl\n"
  let mut k := 0
  while k < n do
    let fetch : Nat → Option Byte := fun i =>
      if k + i < n then some (BitVec.ofNat 8 (img.get! (a0 + k + i - 0x400000)).toNat) else none
    match decode featFull fetch with
    | .ok i =>
      IO.println s!"theorem {name}_d{k} : ∀ feat, Dec feat {name} {k} ({showInst i}) := by intro feat f; rfl"
      k := k + (if i.len > 0 then i.len else 1)
    | _ => IO.println s!"-- {k}: does not decode"; k := k + 1
  return 0
