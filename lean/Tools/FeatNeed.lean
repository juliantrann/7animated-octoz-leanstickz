import ZellicX86.Spec.Semantics
import Std.Data.HashMap
/-!
# `featneed`: which optional processor features each function of a binary needs (PLAN.md G2, "Dispatch theo CPUID")

Not part of any statement: a measurement tool. For each function of `FUNCS.TSV` (start, size in hex/decimal, as
`insncov`'s per-function output), every instruction of `INSNS.TSV` (objdump's linear sweep: address, length,
mnemonic) inside it is decoded by the model's decoder (`Decode.decode`) under the feature set `full` (`insncov`'s)
and under `full` with one optional feature turned off. A feature is *needed* by the function if turning it off alone
makes one of its instructions fail to decode (`#UD`, or a length that differs from objdump's). The features that
change what an instruction does without making it fault (`bmi1`: `TZCNT` is `BSF` without it; `lzcnt`) are reported
apart, as `alt`.

Usage: `lake exe featneed BINARY INSNS.TSV FUNCS.TSV OUT`; writes `OUT` (one line per function: start, size,
instructions, needed features, features that change semantics only).
-/
open ZellicX86 ZellicX86.Decode

def featFull : Features where
  ssse3 := true; sse41 := true; sha := true; bmi1 := true; lzcnt := true; avx := true; avx512f := true
  apx := false; pku := true; nx := true; la57 := false; sse42 := true; bmi2 := true; avx2 := true
  avx512bw := true; avx512dq := true; avx512vl := true; movbe := true; rdtscp := true; sse3 := true; fma := true
  cetSs := false; rtm := true; hle := true; aes := true; vaes := true; popcnt := true; mpx := false

/-- The optional features, each with `full` without it. -/
def drops : List (String × Features) :=
  let f := featFull
  [("sse3", { f with sse3 := false }), ("ssse3", { f with ssse3 := false }), ("sse41", { f with sse41 := false }),
   ("sse42", { f with sse42 := false }), ("popcnt", { f with popcnt := false }), ("movbe", { f with movbe := false }),
   ("aes", { f with aes := false }), ("sha", { f with sha := false }), ("avx", { f with avx := false }),
   ("avx2", { f with avx2 := false }), ("fma", { f with fma := false }), ("vaes", { f with vaes := false }),
   ("avx512f", { f with avx512f := false }), ("avx512bw", { f with avx512bw := false }),
   ("avx512dq", { f with avx512dq := false }), ("avx512vl", { f with avx512vl := false }),
   ("bmi1", { f with bmi1 := false }), ("bmi2", { f with bmi2 := false }), ("lzcnt", { f with lzcnt := false }),
   ("rdtscp", { f with rdtscp := false }), ("rtm", { f with rtm := false }), ("hle", { f with hle := false }),
   ("pku", { f with pku := false })]

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def ofHex (s : String) : Nat :=
  s.foldl (fun n c => 16 * n + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

/-- `ok` if the instruction at `a` decodes under `feat` to objdump's length `n`; `alt` if it decodes to that length
but to another instruction than under `full`; `bad` otherwise. -/
def classify (feat : Features) (img : ByteArray) (base a n : Nat) : String :=
  let fetch : Nat → Option Byte := fun i =>
    let o := a + i - base
    if o < img.size then some (BitVec.ofNat 8 (img.get! o).toNat) else none
  match decode feat fetch, decode featFull fetch with
  | .ok i, .ok j => if i.len != n then "bad" else if reprStr i == reprStr j then "ok" else "alt"
  | _, _ => "bad"

def main (args : List String) : IO UInt32 := do
  let [bin, insnsF, funcsF, out] := args | IO.eprintln "usage: featneed BINARY INSNS.TSV FUNCS.TSV OUT"; return 2
  let img ← IO.FS.readBinFile bin
  let base := 0x400000
  let fns : Array (Nat × Nat) := (← IO.FS.lines funcsF).filterMap fun l =>
    match l.splitOn "\t" with
    | a :: n :: _ => if n.isNat then some (ofHex a, n.toNat!) else none
    | _ => none
  let fns := fns.qsort (fun x y => x.1 < y.1)
  let insns := (← IO.FS.lines insnsF).filterMap fun l =>
    match l.splitOn "\t" with
    | a :: n :: _ => if n.isNat then some (ofHex a, n.toNat!) else none
    | _ => none
  let mut lines : Array String := #["start\tsize\tinsns\tneeds\talt"]
  let mut j := 0
  let mut acc : Std.HashMap Nat (Nat × List String × List String) := {}
  for (a, n) in insns do
    while j < fns.size && fns[j]!.1 + fns[j]!.2 ≤ a do j := j + 1
    if j < fns.size && fns[j]!.1 ≤ a then
      let s := fns[j]!.1
      let (c, need, alt) := acc.getD s (0, [], [])
      let mut need := need
      let mut alt := alt
      if classify featFull img base a n != "ok" then need := if need.contains "FULL" then need else need ++ ["FULL"]
      for (name, feat) in drops do
        match classify feat img base a n with
        | "bad" => if !need.contains name then need := need ++ [name]
        | "alt" => if !alt.contains name then alt := alt ++ [name]
        | _ => pure ()
      acc := acc.insert s (c + 1, need, alt)
  for (s, sz) in fns do
    let (c, need, alt) := acc.getD s (0, [], [])
    lines := lines.push s!"{hex s}\t{sz}\t{c}\t{String.intercalate "," need}\t{String.intercalate "," alt}"
  IO.FS.writeFile out (String.intercalate "\n" lines.toList ++ "\n")
  IO.println s!"featneed: {fns.size} functions"
  return 0
