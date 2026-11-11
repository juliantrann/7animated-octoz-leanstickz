import ZellicX86.Spec.Semantics
/-!
# `decshow`: what Zellic's decoder makes of the instructions of a byte range of a binary (PLAN.md G2)

Not part of any statement: a tool for writing the decoding facts of a proof (`Dec`). From `START` (hex, a virtual
address of `7zzs`, whose file is mapped at `0x400000`), decodes instruction after instruction for `LEN` bytes under
the feature sets `min` and `full` of `insncov`, and prints each instruction's offset and `Inst` (once if the two
agree).

Usage: `lake exe decshow BINARY START LEN`
-/
open ZellicX86 ZellicX86.Decode

def featFull : Features where
  ssse3 := true; sse41 := true; sha := true; bmi1 := true; lzcnt := true; avx := true; avx512f := true
  apx := false; pku := true; nx := true; la57 := false; sse42 := true; bmi2 := true; avx2 := true
  avx512bw := true; avx512dq := true; avx512vl := true; movbe := true; rdtscp := true; sse3 := true; fma := true
  cetSs := false; rtm := true; hle := true; aes := true; vaes := true; popcnt := true; mpx := false

def featMin : Features where
  ssse3 := false; sse41 := false; sha := false; bmi1 := false; lzcnt := false; avx := false; avx512f := false
  apx := false; pku := false; nx := true; la57 := false; sse42 := false; bmi2 := false; avx2 := false
  avx512bw := false; avx512dq := false; avx512vl := false; movbe := false; rdtscp := false; sse3 := false
  fma := false; cetSs := false; rtm := false; hle := false; aes := false; vaes := false; popcnt := false; mpx := false

def ofHex (s : String) : Nat :=
  s.foldl (fun n c => 16 * n + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def main (args : List String) : IO UInt32 := do
  let [bin, start, len] := args | IO.eprintln "usage: decshow BINARY START LEN"; return 2
  let img ← IO.FS.readBinFile bin
  let a0 := ofHex start
  let n := len.toNat!
  let mut k := 0
  let bytes : List Nat := (List.range n).map fun i => (img.get! (a0 + i - 0x400000)).toNat
  IO.println s!"bytes {hex a0} {n}: {bytes.map (fun b => "0x" ++ (if b < 16 then "0" else "") ++ hex b)}"
  while k < n do
    let fetch : Nat → Option Byte := fun i =>
      if k + i < n then some (BitVec.ofNat 8 (img.get! (a0 + k + i - 0x400000)).toNat) else none
    let show1 (r : Decoded) : String × Nat := match r with
      | .ok i => (reprStr i, i.len)
      | .ud => ("#UD", 1)
      | .nm m o => (s!"notModelled {m} {o}", 1)
      | _ => ("fault", 1)
    let (s1, l1) := show1 (decode featMin fetch)
    let (s2, l2) := show1 (decode featFull fetch)
    if s1 == s2 then IO.println s!"{k} ({hex (a0 + k)}): {s2}"
    else IO.println s!"{k} ({hex (a0 + k)}): min {s1}\n    full {s2}"
    k := k + (if l2 > 0 then l2 else 1)
    let _ := l1
  return 0
