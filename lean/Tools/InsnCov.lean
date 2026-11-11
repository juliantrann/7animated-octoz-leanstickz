import ZellicX86.Spec.Semantics
import Std.Data.HashMap
/-!
# `insncov`: which instructions of a binary Zellic's model decodes and executes (PLAN.md §6.1, G0)

Not part of any statement: a measurement tool. The instruction boundaries are objdump's linear sweep of the
executable sections (`INSNS.TSV`: address, length, mnemonic); each instruction is decoded at its address by the
model's own decoder (`Decode.decode`), its length compared with objdump's, and the model's semantics (`exec`) run
along two paths: every value the program asks for answered by 0 on the one and by 1 on the other, every open choice
by its first alternative. A `notModelled` that depends on values neither path takes is not seen; bytes of data that
objdump sweeps as code are reported as instructions too. Each instruction is attributed to the function of
`FUNCS.TSV` (`tools/ehframe_funcs.py`) containing it, if any.

Usage: `lake exe insncov BINARY INSNS.TSV FUNCS.TSV OUT`; writes `OUT.summary` and per feature set `OUT.<set>`
(per function) and `OUT.<set>.insns` (every instruction with an issue).
-/
open ZellicX86 ZellicX86.Decode

deriving instance Inhabited for Rflags
deriving instance Inhabited for X87

/-- The feature sets measured: `full` a current x86-64 server CPU (no APX, no CET shadow stack, 4-level paging),
`min` the baseline x86-64 without any optional extension (PLAN.md §5.3, H-CPU-min). -/
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

/-- The thread on the explored path: the initial thread of a process after `execve`. -/
def thread0 : ThreadK where
  tid := 1; sigmask := 0; pending := []; altStack := AltStack.disabled; rseq := none; clearChildTid := 0
  robustList := 0; cpuidFaults := false; tscFaults := false; shstk := none; uid := 1000

/-- The answer to `o` on the path where values are `z`; `none` where the step stops the program. -/
def answer (z : Nat) : (o : Op) → Option o.Ret
  | .getReg _ => some (BitVec.ofNat 64 z) | .getRip => some (BitVec.ofNat 64 z) | .getFlags => some (default : Rflags)
  | .getSegBase _ => some (BitVec.ofNat 64 z) | .getThread => some thread0
  | .getZmm _ => some (BitVec.ofNat 512 z) | .getK _ => some (BitVec.ofNat 64 z) | .getMxcsr => some (0x1f80 : BitVec 32)
  | .getX87 => some (default : X87) | .load _ w _ => some (BitVec.ofNat w z) | .loadSel _ n _ _ => some (BitVec.ofNat (8 * n) z)
  | .rmw _ w _ => some (BitVec.ofNat w z) | .choose w => some (BitVec.ofNat w z) | .pick n => some (0 : Fin (n + 1))
  | .tsc => some (BitVec.ofNat 64 z) | .xinuse _ => some (BitVec.ofNat 64 z)
  | .raise _ | .notModelled _ => none
  | .setReg .. | .setRip _ | .setFlags _ | .setZmm .. | .setK .. | .setMxcsr _ | .setX87 _ | .store ..
  | .storeSel .. | .checkAligned .. | .checkAll _ | .fence _ => some (() : Unit)

/-- The `notModelled` the program reaches on the path where values are `z`, within `fuel` steps. -/
def firstNm {α : Type} (z : Nat) : Nat → Prog α → Option NotModelled
  | 0, _ => none
  | _, .pure _ => none
  | _ + 1, .op (.notModelled w) _ => some w
  | fuel + 1, .op o k => (answer z o).elim none fun v => firstNm z fuel (k v)

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def ofHex (s : String) : Nat :=
  s.foldl (fun n c => 16 * n + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10)) 0

def nmStr : NotModelled → String
  | .encoding m o => s!"decode: not modelled (map {hex m}, opcode {hex o})"
  | .form s => s!"exec: form {s}"
  | w => "exec: " ++ ((reprStr w).replace "ZellicX86.NotModelled." "" |>.replace "ZellicX86.Decode." "")

/-- The issue of the instruction at `a` (objdump's length `n`), if any. -/
def check (feat : Features) (prof : Profile) (img : ByteArray) (base a n : Nat) : Option String :=
  let fetch : Nat → Option Byte := fun i =>
    let o := a + i - base
    if o < img.size then some (BitVec.ofNat 8 (img.get! o).toNat) else none
  match decode feat fetch with
  | .ok i =>
    if i.len != n then some s!"decode: length {i.len}, objdump {n}" else
    match firstNm 0 4096 (exec prof i), firstNm 1 4096 (exec prof i) with
    | some w, some _ => some (nmStr w)
    | some w, none => some (nmStr w ++ " [on the 0 path only]")
    | none, some w => some (nmStr w ++ " [on the 1 path only]")
    | none, none => none
  | .ud => some "decode: #UD"
  | .nm m o => some (nmStr (.encoding m o))
  | _ => some "decode: #GP or #PF"

/-- A profile with feature set `feat`. Only `feat` matters to decoding; `exec` reads the rest at `CPUID`, `XGETBV`,
`RDTSCP`, `LDMXCSR` and the x87 save and restore instructions, whose outcome on the zero path is not the point here. -/
def mkProf (feat : Features) : Profile where
  vendor := .intel; feat := feat; aux := ⟨0, 0, 2048⟩; cpus := 1; cpuid := fun _ _ _ => ⟨0, 0, 0, 0⟩
  xcr0 := some 0xe7; mxcsrMask := 0xffff; tscAux := fun _ => 0; fdpExcptnOnly := true; fcsDeprecated := true
  amdErrPtrs := false; x87LoadsKnown := true; linux := { vdsoData := fun _ => true, vdsoText := [], compatBrk := false }

structure Fn where
  start : Nat
  size : Nat
  kind : String
  sec : String
  insns : Nat := 0
  issues : Nat := 0
  first : List String := []
  deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let [bin, insnsF, funcsF, out] := args | IO.eprintln "usage: insncov BINARY INSNS.TSV FUNCS.TSV OUT"; return 2
  let img ← IO.FS.readBinFile bin
  -- the file is mapped at its first PT_LOAD's p_vaddr - p_offset: 0x400000 for 7zzs (`readelf -l`)
  let base := 0x400000
  let insns := (← IO.FS.lines insnsF).filterMap fun l =>
    match l.splitOn "\t" with
    | a :: n :: m :: _ => if n.isNat then some (ofHex a, n.toNat!, m) else none
    | _ => none
  let fns0 : Array Fn := (← IO.FS.lines funcsF).filterMap fun l =>
    match l.splitOn "\t" with
    | a :: n :: k :: s :: _ => if n.isNat then some (Fn.mk (ofHex a) n.toNat! k s 0 0 []) else none
    | _ => none
  let mut report := s!"insncov {bin}: {insns.size} instructions (objdump), {fns0.size} functions\n"
  for (name, feat) in [("full", featFull), ("min", featMin)] do
    let prof := mkProf feat
    let mut fns := fns0
    let mut j := 0           -- the first function not ending at or before the current instruction
    let mut tally : Std.HashMap String (Nat × Nat × String) := {}   -- issue ↦ (count, first address, objdump mnemonics)
    let mut byMn : Std.HashMap String Nat := {}
    let mut bad : Array String := #["addr\tlen\tobjdump\tfunction\tissue"]
    let mut nIssues := 0
    let mut outside := 0
    for (a, n, m) in insns do
      while j < fns.size && fns[j]!.start + fns[j]!.size ≤ a do j := j + 1
      let inFn := j < fns.size && fns[j]!.start ≤ a
      if !inFn then outside := outside + 1
      match check feat prof img base a n with
      | none => if inFn then fns := fns.modify j fun f => { f with insns := f.insns + 1 }
      | some s =>
        nIssues := nIssues + 1
        let mnKey := m.splitOn " " |>.head!
        let key := s!"{s}\t{mnKey}"
        tally := tally.insert key (match tally.get? key with
          | some (c, a0, ms) => (c + 1, a0, ms) | none => (1, a, m))
        byMn := byMn.insert mnKey (byMn.getD mnKey 0 + 1)
        let fname := if inFn then hex fns[j]!.start else "-"
        bad := bad.push s!"{hex a}\t{n}\t{m}\t{fname}\t{s}"
        if inFn then
          let note := s!"{hex a} {m}: {s}"
          fns := fns.modify j fun f =>
            let first := if f.first.length < 3 then f.first ++ [note] else f.first
            { f with insns := f.insns + 1, issues := f.issues + 1, first := first }
    let fnLines := fns.toList.map fun f =>
      s!"{hex f.start}\t{f.size}\t{f.kind}\t{f.sec}\t{f.insns}\t{f.issues}\t{String.intercalate " | " f.first}"
    IO.FS.writeFile s!"{out}.{name}"
      (String.intercalate "\n" ("start\tsize\tkind\tsection\tinsns\tissues\tfirst_issues" :: fnLines) ++ "\n")
    IO.FS.writeFile s!"{out}.{name}.insns" (String.intercalate "\n" bad.toList ++ "\n")
    let badFns := fns.foldl (fun c f => if f.issues > 0 then c + 1 else c) 0
    report := report ++ s!"\n== feature set {name}: {nIssues} instructions with an issue, in {badFns} functions" ++
      s!" ({outside} instructions in no function of FUNCS.TSV: alignment padding)\n"
    report := report ++ "  count\tobjdump\tissue\t(first at)\n"
    let issues := tally.toArray.qsort (fun x y => x.2.1 > y.2.1)
    for (k, c, a, _) in issues do
      match k.splitOn "\t" with
      | [s, mn] => report := report ++ s!"  {c}\t{mn}\t{s}\t({hex a})\n"
      | _ => pure ()
  IO.println report
  IO.FS.writeFile s!"{out}.summary" report
  return 0
