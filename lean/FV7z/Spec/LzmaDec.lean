import ZellicX86.Spec.Statement
/-!
# The contract of `LzmaDec_DecodeReal_3` in `7zzs` (PLAN.md G2.2)

Only definitions, on Zellic's model alone, for a challenge to import (`Challenges/V2606/LzmaDecodeReal3.lean`).

`LzmaDec_DecodeReal_3` (`Asm/x86/LzmaDecOpt.asm`) is the loop of the LZMA decoder: `rdi` holds the `CLzmaDec`,
`rsi` the `limit` (an index into the dictionary's buffer) and `rdx` `bufLimit`. It decodes symbols until `dicPos`
reaches `limit` or `buf` reaches `bufLimit`.

The contract is about memory, not about what is decoded: whatever bytes the input holds, a call

- reads only the `CLzmaDec`, the dictionary's buffer, the array of probabilities, and the input from `buf` up to 20
  bytes past `bufLimit` (`LZMA_REQUIRED_INPUT_MAX`: the loop checks `buf < bufLimit` between two symbols, and one
  symbol takes at most 20 bytes);
- writes only its stack frame (303 bytes), the dictionary's buffer from `dicPos` to `limit`, the array of
  probabilities, and the fields of the `CLzmaDec` from `dicPos` to `remainLen`;
- returns to its caller with the callee-saved registers kept, 0 or 1 in `rax`, and the `CLzmaDec` again as `Pre`
  wants it, but for `buf`, which may have passed `bufLimit` by up to 20 bytes, and, after an error (1), the `reps`.

What it assumes of the `CLzmaDec` (`Pre`) is what `LzmaDec.c` keeps between calls: `lc ≤ 8`, `lp ≤ 4`, `pb ≤ 4`,
`dicPos < limit ≤ dicBufSize`, a range of at least `2^24`, a state below 12, `reps` and `checkDicSize` no larger
than the dictionary's buffer, every probability in `[31, 2017]` (which the update of a probability keeps), and, while
`checkDicSize` is 0, room for `processedPos` up to `limit`.
-/
namespace FV7z.LzmaDec
open ZellicX86

/-! ## The fields of the `CLzmaDec` at `p`, in memory `m` (`LzmaDec.h`, x86-64) -/

def lc (m : Memory) (p : Addr) : Nat := (ofBytesLE 8 (readBytes m p 1)).toNat
def lp (m : Memory) (p : Addr) : Nat := (ofBytesLE 8 (readBytes m (p + 1) 1)).toNat
def pb (m : Memory) (p : Addr) : Nat := (ofBytesLE 8 (readBytes m (p + 2) 1)).toNat
/-- `probs_1664`: the array of probabilities, from its 1664th. -/
def probs1664 (m : Memory) (p : Addr) : Addr := ofBytesLE 64 (readBytes m (p + 16) 8)
def dic (m : Memory) (p : Addr) : Addr := ofBytesLE 64 (readBytes m (p + 24) 8)
def dicBufSize (m : Memory) (p : Addr) : Nat := (ofBytesLE 64 (readBytes m (p + 32) 8)).toNat
def dicPos (m : Memory) (p : Addr) : Nat := (ofBytesLE 64 (readBytes m (p + 40) 8)).toNat
def buf (m : Memory) (p : Addr) : Addr := ofBytesLE 64 (readBytes m (p + 48) 8)
def range (m : Memory) (p : Addr) : Nat := (ofBytesLE 32 (readBytes m (p + 56) 4)).toNat
def processedPos (m : Memory) (p : Addr) : Nat := (ofBytesLE 32 (readBytes m (p + 64) 4)).toNat
def checkDicSize (m : Memory) (p : Addr) : Nat := (ofBytesLE 32 (readBytes m (p + 68) 4)).toNat
/-- `reps[i]`. -/
def rep (m : Memory) (p : Addr) (i : Nat) : Nat :=
  (ofBytesLE 32 (readBytes m (p + BitVec.ofNat 64 (72 + 4 * i)) 4)).toNat
def state (m : Memory) (p : Addr) : Nat := (ofBytesLE 32 (readBytes m (p + 88) 4)).toNat
def remainLen (m : Memory) (p : Addr) : Nat := (ofBytesLE 32 (readBytes m (p + 92) 4)).toNat

/-- The number of probabilities: `LzmaProps_GetNumProbs`, `NUM_BASE_PROBS + (0x300 << (lc + lp))`. -/
def numProbs (m : Memory) (p : Addr) : Nat := 1984 + 768 * 2 ^ (lc m p + lp m p)

/-- The array of probabilities: `probs_1664` less 1664 probabilities of 2 bytes. -/
def probsBase (m : Memory) (p : Addr) : Addr := probs1664 m p - 3328

/-- The `i`-th probability of the array at `base`. -/
def prob (m : Memory) (base : Addr) (i : Nat) : Nat := (ofBytesLE 16 (readBytes m (base.add (2 * i)) 2)).toNat

/-! ## The regions of a call from `s` -/

/-- The `CLzmaDec`, up to `remainLen`. -/
def rDec (s : State) : Rgn := ⟨s.cpu.gpr.rdi, 96⟩
/-- The fields the call writes: `dicPos`, `buf`, `range`, `code`, `processedPos`, `checkDicSize`, `reps`, `state`,
`remainLen`. -/
def rDecW (s : State) : Rgn := ⟨s.cpu.gpr.rdi + 40, 56⟩
/-- The array of probabilities. -/
def rProbs (s : State) : Rgn := ⟨probsBase s.proc.mm.mem s.cpu.gpr.rdi, 2 * numProbs s.proc.mm.mem s.cpu.gpr.rdi⟩
/-- The dictionary's buffer. -/
def rDic (s : State) : Rgn := ⟨dic s.proc.mm.mem s.cpu.gpr.rdi, dicBufSize s.proc.mm.mem s.cpu.gpr.rdi⟩
/-- The dictionary's buffer from `dicPos` to `limit`. -/
def rOut (s : State) : Rgn :=
  ⟨dic s.proc.mm.mem s.cpu.gpr.rdi + BitVec.ofNat 64 (dicPos s.proc.mm.mem s.cpu.gpr.rdi),
    s.cpu.gpr.rsi.toNat - dicPos s.proc.mm.mem s.cpu.gpr.rdi⟩
/-- The input: from `buf` to 20 bytes past `bufLimit`. -/
def rIn (s : State) : Rgn :=
  ⟨buf s.proc.mm.mem s.cpu.gpr.rdi, s.cpu.gpr.rdx.toNat + 20 - (buf s.proc.mm.mem s.cpu.gpr.rdi).toNat⟩

/-- What a call reads besides what it writes. -/
def reads (s : State) : List Rgn := [rDec s, rDic s, rIn s]
/-- What a call writes besides its stack frame. -/
def writes (s : State) : List Rgn := [rOut s, rProbs s, rDecW s]

/-- What a call assumes: the `CLzmaDec` at `rdi` as `LzmaDec.c` keeps it between calls, `limit` in `rsi`, `bufLimit`
in `rdx`, and the stack frame, the array of probabilities, the dictionary's buffer and the `CLzmaDec` apart from
each other. -/
structure Pre (s : State) : Prop where
  lc : lc s.proc.mm.mem s.cpu.gpr.rdi ≤ 8
  lp : lp s.proc.mm.mem s.cpu.gpr.rdi ≤ 4
  pb : pb s.proc.mm.mem s.cpu.gpr.rdi ≤ 4
  probs : 3328 ≤ (probs1664 s.proc.mm.mem s.cpu.gpr.rdi).toNat
  valid : ∀ i, i < numProbs s.proc.mm.mem s.cpu.gpr.rdi →
    31 ≤ prob s.proc.mm.mem (probsBase s.proc.mm.mem s.cpu.gpr.rdi) i ∧
      prob s.proc.mm.mem (probsBase s.proc.mm.mem s.cpu.gpr.rdi) i ≤ 2017
  pos : dicPos s.proc.mm.mem s.cpu.gpr.rdi < s.cpu.gpr.rsi.toNat
  limit : s.cpu.gpr.rsi.toNat ≤ dicBufSize s.proc.mm.mem s.cpu.gpr.rdi
  buf : (buf s.proc.mm.mem s.cpu.gpr.rdi).toNat ≤ s.cpu.gpr.rdx.toNat
  bufLimit : s.cpu.gpr.rdx.toNat + 20 < 2 ^ 64
  range : 2 ^ 24 ≤ range s.proc.mm.mem s.cpu.gpr.rdi
  state : state s.proc.mm.mem s.cpu.gpr.rdi < 12
  reps : ∀ i, i < 4 → rep s.proc.mm.mem s.cpu.gpr.rdi i ≤ dicBufSize s.proc.mm.mem s.cpu.gpr.rdi
  check : checkDicSize s.proc.mm.mem s.cpu.gpr.rdi ≤ dicBufSize s.proc.mm.mem s.cpu.gpr.rdi
  processed : checkDicSize s.proc.mm.mem s.cpu.gpr.rdi = 0 →
    processedPos s.proc.mm.mem s.cpu.gpr.rdi + (s.cpu.gpr.rsi.toNat - dicPos s.proc.mm.mem s.cpu.gpr.rdi) ≤
      dicBufSize s.proc.mm.mem s.cpu.gpr.rdi
  apartFrame : Apart [frame s 303] [rProbs s, rDic s, rDec s]
  apartProbs : Apart [rProbs s] [rDic s, rDec s]
  apartDic : Apart [rDic s] [rDec s]

/-- What holds at the return `X` of a call from `s`: 0 or 1 in `rax`; the probabilities in `[31, 2017]`; `dicPos`
between its value at the call and `limit`; `buf` between its value at the call and 20 bytes past `bufLimit`; a range
of at least `2^24`; a state below 12; while `checkDicSize` is 0, `processedPos` grew no more than `dicPos`; after 0
the `reps` are no larger than the dictionary's buffer; after 1 (an error) `remainLen` is at least 514
(`kMatchSpecLen_Error_Data`), with which `LzmaDec.c` decodes no further. -/
structure Post (s X : State) : Prop where
  ret : X.cpu.gpr.rax = 0 ∨ X.cpu.gpr.rax = 1
  valid : ∀ i, i < numProbs s.proc.mm.mem s.cpu.gpr.rdi →
    31 ≤ prob X.proc.mm.mem (probsBase s.proc.mm.mem s.cpu.gpr.rdi) i ∧
      prob X.proc.mm.mem (probsBase s.proc.mm.mem s.cpu.gpr.rdi) i ≤ 2017
  pos : dicPos s.proc.mm.mem s.cpu.gpr.rdi ≤ dicPos X.proc.mm.mem s.cpu.gpr.rdi ∧
    dicPos X.proc.mm.mem s.cpu.gpr.rdi ≤ s.cpu.gpr.rsi.toNat
  buf : (buf s.proc.mm.mem s.cpu.gpr.rdi).toNat ≤ (buf X.proc.mm.mem s.cpu.gpr.rdi).toNat ∧
    (buf X.proc.mm.mem s.cpu.gpr.rdi).toNat ≤ s.cpu.gpr.rdx.toNat + 20
  range : 2 ^ 24 ≤ range X.proc.mm.mem s.cpu.gpr.rdi
  state : state X.proc.mm.mem s.cpu.gpr.rdi < 12
  processed : checkDicSize s.proc.mm.mem s.cpu.gpr.rdi = 0 →
    processedPos X.proc.mm.mem s.cpu.gpr.rdi + (s.cpu.gpr.rsi.toNat - dicPos X.proc.mm.mem s.cpu.gpr.rdi) ≤
      processedPos s.proc.mm.mem s.cpu.gpr.rdi + (s.cpu.gpr.rsi.toNat - dicPos s.proc.mm.mem s.cpu.gpr.rdi)
  ok : X.cpu.gpr.rax = 0 → ∀ i, i < 4 → rep X.proc.mm.mem s.cpu.gpr.rdi i ≤ dicBufSize s.proc.mm.mem s.cpu.gpr.rdi
  err : X.cpu.gpr.rax = 1 → 514 ≤ remainLen X.proc.mm.mem s.cpu.gpr.rdi

/-- `LzmaDec_DecodeReal_3`'s contract: System V, a stack frame of 303 bytes, no system call. -/
def contract : Contract where
  conv := sysv
  reads := reads
  writes s := frame s 303 :: writes s
  pre := Pre
  post := Post
  events _ _ evs := evs = []

end FV7z.LzmaDec
