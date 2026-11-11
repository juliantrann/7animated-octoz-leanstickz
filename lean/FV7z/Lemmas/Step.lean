import FV7z.Lemmas.Env
/-!
# One instruction (PLAN.md G2.0)

The pieces of a step a proof takes for each instruction of its code:
- fetch: where the code's bytes lie in memory, fetchable (`CodeAt`), the bytes `fetchByte` gives from `rip` are the
  code's (`fetchByte_code`), and decoding them needs only those bytes (`decode_of_window`, over `fetchFrom`): the
  decoder then runs on a concrete list, by evaluation;
- execution: an instruction that goes on to the next (`instruction_next`), a memory access that passes its checks
  (`checkAccess_ok`, `run_load`);
- the step: the environment's ordinary events, then the instruction (`step_next`).

The names follow the lemmas of Zellic's proof exports (`fetch_code`, `decode_of_window`, `instruction_eq`,
`checkAccess_ok`, `run_load`); the definitions and proofs here are this project's.
-/
namespace FV7z
open ZellicX86

/-! ## Fetch and decode -/

/-- The bytes `bs`, and beyond them those of `f`. -/
def fetchFrom (bs : List Byte) (f : Nat → Option Byte) (i : Nat) : Option Byte :=
  if i < bs.length then bs[i]? else f i

theorem fetchFrom_eq {bs : List Byte} {f : Nat → Option Byte} (h : ∀ i < bs.length, f i = bs[i]?) :
    fetchFrom bs f = f := by
  funext i
  unfold fetchFrom
  split
  · next hi => exact (h i hi).symm
  · rfl

/-- Decoding from bytes that begin with `bs` gives what decoding `bs` (and, beyond them, the same bytes) gives: with
`bs` concrete, the right side evaluates as far as the instruction reaches into `bs`. -/
theorem decode_of_window {feat : Features} {bs : List Byte} {f : Nat → Option Byte} {d : Decode.Decoded}
    (h : ∀ i < bs.length, f i = bs[i]?) (hd : Decode.decode feat (fetchFrom bs f) = d) : Decode.decode feat f = d := by
  rw [← fetchFrom_eq h]; exact hd

/-- The bytes `bs` lie at `a` in memory `m`, and each can be fetched. -/
def CodeAt (feat : Features) (pkru : BitVec 32) (m : Memory) (a : Addr) (bs : List Byte) : Prop :=
  ∀ j < bs.length, (a.add j).canonical feat.la57 = true ∧ m.check feat pkru .fetch (a.add j) = none ∧
    bs[j]? = some (m.readByte (a.add j))

/-- The bytes fetched at `rip`, `k` bytes into code `bs` at `a`, are the code's from there. -/
theorem fetchByte_code {feat : Features} {s : State} {a : Addr} {bs : List Byte} {k : Nat}
    (hc : CodeAt feat s.cpu.pkru s.proc.mm.mem a bs) (hrip : s.cpu.rip = a.add k) :
    ∀ i < (bs.drop k).length, fetchByte feat s i = (bs.drop k)[i]? := by
  intro i hi
  simp only [List.length_drop] at hi
  obtain ⟨hcan, hchk, hb⟩ := hc (k + i) (by omega)
  unfold fetchByte
  rw [hrip, addr_add_add, if_pos (by simp [hcan, hchk]), List.getElem?_drop, hb]

/-- The calm changes of memory keep the code. -/
theorem CodeAt.of_calm {A : Addr → Prop} {feat : Features} {pkru : BitVec 32} {m M : Memory} {a : Addr}
    {bs : List Byte} (hc : CodeAt feat pkru m a bs) (h : Calm A m M)
    (hk : ∀ j < bs.length, StableAt m (a.add j) ∧ ∀ y, A y → locOf m y ≠ locOf m (a.add j)) :
    CodeAt feat pkru M a bs := fun j hj =>
  ⟨(hc j hj).1, by rw [h.check]; exact (hc j hj).2.1,
    by rw [h.byte _ (hk j hj).1 (hk j hj).2]; exact (hc j hj).2.2⟩

/-! ## Execution -/

/-- `s` with `rip` past an instruction of `len` bytes and `RF` cleared, as `instruction` starts its execution. -/
def advance (s : State) (len : Nat) : State :=
  s.modCpu fun c => { c with rip := c.rip.add len, rflags := { c.rflags with rf := false } }

theorem Req.runStream_bind {α β : Type} (o : Oracle) (f : α → Req β) :
    ∀ (x : Req α) (t : Nat), (x.bind f).runStream o t = (f (x.runStream o t).1).runStream o (x.runStream o t).2
  | .pure _, _ => rfl
  | .ask r k, t => Req.runStream_bind o f (k (o t r)) (t + 1)

/-- An instruction that decodes to `i` and runs to the next one, with state `s₂`, its answers (undefined flags, …)
from position `t` of the stream to `t'` (no system call, no repeat). -/
theorem instruction_next {prof : Profile} {o : Oracle} {t t' : Nat} {s s₂ : State} {i : Decode.Inst}
    (htf : s.cpu.rflags.tf = false) (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok i)
    (hex : ((exec prof i).run prof.feat prof.linux.splitLock (advance s i.len)).runStream o t = (.ok .next s₂, t')) :
    (instruction prof s).runStream o t = (.running s₂ none, t') := by
  unfold instruction
  simp only [htf, Bool.false_eq_true, ↓reduceIte, hdec]
  unfold advance at hex
  show (Req.bind _ _).runStream o t = _
  rw [Req.runStream_bind, hex]
  rfl

/-- No byte of `l` faults. -/
theorem faultingPages_nil {feat : Features} {pkru : BitVec 32} {mem : Memory} {acc : Access} :
    ∀ {l : List Addr}, (∀ x ∈ l, mem.check feat pkru acc x = none) → faultingPages feat pkru mem acc l = []
  | [], _ => rfl
  | x :: l, h => by
    unfold faultingPages
    rw [h x List.mem_cons_self]
    exact faultingPages_nil fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- An access whose bytes are canonical and pass their checks, without alignment checking, passes. -/
theorem checkAccess_ok {feat : Features} {s : State} {m : MemRef} {acc : Access} {n : Nat}
    (hac : s.cpu.rflags.ac = false)
    (h : ∀ x ∈ byteAddrs m.addr n, x.canonical feat.la57 = true ∧ s.proc.mm.mem.check feat s.cpu.pkru acc x = none) :
    checkAccess feat s m acc n = Pure.pure none := by
  unfold checkAccess checkBytes
  rw [if_neg (by simp [hac]), if_neg (by simpa using fun x hx => (h x hx).1),
    faultingPages_nil fun x hx => (h x hx).2]

/-- A load that passes its checks reads memory. -/
theorem run_load {feat : Features} {sl : SplitLock} {s : State} {m : MemRef} {w : Nat} {acc : Access} {α : Type}
    {k : BitVec w → Prog α} (hc : checkAccess feat s m acc (w / 8) = Pure.pure none) :
    Prog.run feat sl (.op (.load m w acc) k) s =
      Prog.run feat sl (k (ofBytesLE w (readBytes s.proc.mm.mem m.addr (w / 8)))) s := by
  simp only [Prog.run, hc]
  rfl

/-! ## The step -/

/-- A step of an undisturbed run, from a state whose `rseq` area is quiet, whose instruction, from the state the
environment's events leave, runs to the next with state `s₂` and answers up to position `t'`. -/
theorem step_next {prof : Profile} {o : Oracle} {t t' : Nat} {s s₂ : State} (hU : Undisturbed o)
    (hq : Quiet prof.feat s)
    (h : (instruction prof (kdata prof.feat s (evsAt prof o t))).runStream o (t + 1) = (.running s₂ none, t')) :
    (step prof s).runStream o t = (.running s₂ none, t') := by
  rw [step_runStream prof o t s hU hq, h]

end FV7z
