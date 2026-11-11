import FV7z.Lemmas.Exec
import Examples.Memcmp.Statement
/-!
# `memcmp`, GCC `-Os` (PLAN.md G2.0)

A proof, written in this project, of the statement of Zellic's release challenge `memcmp_gcc_os`
(`Memcmp.holds Memcmp.gccOs`): the 37 bytes of `Examples/Memcmp/Code.lean` compare as `memcmp` does
(`Memcmp.contract`) wherever they lie in the code of a process, on every processor and every Linux the model allows.

```
 0  mov r8, rsi            13  movzx eax, byte [rdi+rdx]   26  sub eax, ecx        34  xor eax, eax
 3  mov rsi, rdx           17  movzx ecx, byte [r8+rdx]    28  ret                 36  ret
 6  xor edx, edx           22  cmp al, cl                  29  inc rdx
 8  cmp rdx, rsi           24  je 29                       32  jmp 8
11  je 34
```

First what each instruction does (`i0` … `i36`, by symbolic execution of the model's decoder and semantics), then the
run: the entry block to the loop's head, the loop (its invariant `Head`, the variant `n - i`), the two returns.
-/
namespace FV7z.MemcmpGccOs
open ZellicX86 Decode Memcmp

/-! ## The instructions -/

def r64 (n : Nat) : Opd := .reg ⟨64, n, false⟩
def r32 (n : Nat) : Opd := .reg ⟨32, n, false⟩
def r8 (n : Nat) : Opd := .reg ⟨8, n, false⟩
def mk (mn : Mn) (opsz : Nat) (ops : List Opd) (len : Nat) : Inst :=
  { mn, opsz, ops, len, rep := none, lock := false, mask := none, zero := false, fop := 0 }
/-- The byte at `[b + i]`. -/
def mbi (b i : Nat) : MemOp :=
  { seg := none, base := some b, index := some i, scale := 1, disp := 0, ripRel := false, addr32 := false, width := 8 }

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State} {e : Addr}

/-- The code at `e`, fetchable, in the state `s` an instruction starts from. -/
abbrev Code (prof : Profile) (s : State) (e : Addr) : Prop := CodeAt prof.feat s.cpu.pkru s.proc.mm.mem e gccOs

/-- `mov r8, rsi`. -/
theorem i0 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 0) (htf : s.cpu.rflags.tf = false) :
    (instruction prof s).runStream o t =
      (.running (nx s 3 (s.cpu.gpr.set 8 s.cpu.gpr.rsi) { s.cpu.rflags with rf := false }) none, t) :=
  instruction_next htf (show Decode.decode _ _ = .ok (mk .mov 64 [r64 8, r64 6] 3) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl

/-- `mov rsi, rdx`. -/
theorem i3 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 3) (htf : s.cpu.rflags.tf = false) :
    (instruction prof s).runStream o t =
      (.running (nx s 3 (s.cpu.gpr.set 6 s.cpu.gpr.rdx) { s.cpu.rflags with rf := false }) none, t) :=
  instruction_next htf (show Decode.decode _ _ = .ok (mk .mov 64 [r64 6, r64 2] 3) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl

/-- `xor edx, edx` (`AF` undefined: one answer of the stream). -/
theorem i6 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 6) (htf : s.cpu.rflags.tf = false) :
    ∃ v fl, (instruction prof s).runStream o t = (.running (nx s 2 (s.cpu.gpr.set 2 v) fl) none, t + 1) ∧
      v = 0 ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨_, _, instruction_next htf (show Decode.decode _ _ = .ok (mk .xor 32 [r32 2, r32 2] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl, ?_, rfl, rfl, rfl⟩
  change (BitVec.setWidth 64 (BitVec.setWidth 32 s.cpu.gpr.rdx ^^^ BitVec.setWidth 32 s.cpu.gpr.rdx) : BitVec 64) = 0
  simp

/-- `cmp rdx, rsi`. -/
theorem i8 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 8) (htf : s.cpu.rflags.tf = false) :
    ∃ fl, (instruction prof s).runStream o t = (.running (nx s 3 s.cpu.gpr fl) none, t) ∧
      fl.zf = decide (s.cpu.gpr.rdx = s.cpu.gpr.rsi) ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧
      fl.df = s.cpu.rflags.df := by
  refine ⟨_, instruction_next htf (show Decode.decode _ _ = .ok (mk .cmp 64 [r64 2, r64 6] 3) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl, ?_, rfl, rfl, rfl⟩
  change ((BitVec.setWidth 64 s.cpu.gpr.rdx - BitVec.setWidth 64 s.cpu.gpr.rsi -
    (BitVec.ofBool false).setWidth 64) == 0) = _
  simp [bv_sub_beq_zero]

/-- `je 34`, taken. -/
theorem i11t (hc : Code prof s e) (hrip : s.cpu.rip = e.add 11) (htf : s.cpu.rflags.tf = false)
    (hz : s.cpu.rflags.zf = true) (hcan : (e.add 34).canonical prof.feat.la57 = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (e.add 34) s.cpu.gpr { s.cpu.rflags with rf := false }) none, t) := by
  refine instruction_next htf (show Decode.decode _ _ = .ok (mk (.jcc 4) 64 [.rel 21] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) ?_
  have ht : (e.add 11).add 2 + BitVec.ofNat 64 21 = e.add 34 := by simp only [Addr.add]; bv_omega
  simp only [exec, Sem.jcc, mk, Prog.run, bind, Prog.bind, Prog.readFlags, Prog.readRip, advance, State.modCpu, hrip,
    hz, ht, Rflags.cond, jumpTo, hcan, Bool.false_eq_true, ↓reduceIte, Prog.writeRip, done]
  rfl

/-- `je 34`, not taken. -/
theorem i11n (hc : Code prof s e) (hrip : s.cpu.rip = e.add 11) (htf : s.cpu.rflags.tf = false)
    (hz : s.cpu.rflags.zf = false) :
    (instruction prof s).runStream o t = (.running (nx s 2 s.cpu.gpr { s.cpu.rflags with rf := false }) none, t) := by
  refine instruction_next htf (show Decode.decode _ _ = .ok (mk (.jcc 4) 64 [.rel 21] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) ?_
  simp only [exec, Sem.jcc, mk, Prog.run, bind, Prog.bind, Prog.readFlags, Prog.readRip, advance, State.modCpu, hz,
    Rflags.cond, Bool.false_eq_true, ↓reduceIte, done]
  rfl

/-- `movzx eax, byte [rdi+rdx]`. -/
theorem i13 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 13) (htf : s.cpu.rflags.tf = false)
    (hac : s.cpu.rflags.ac = false)
    (hld : ∀ x ∈ byteAddrs (s.cpu.gpr.rdi + s.cpu.gpr.rdx) 1, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none) :
    (instruction prof s).runStream o t =
      (.running (nx s 4 (s.cpu.gpr.set 0
        (((ofBytesLE 8 (readBytes s.proc.mm.mem (s.cpu.gpr.rdi + s.cpu.gpr.rdx) 1)).setWidth 32).setWidth 64))
        { s.cpu.rflags with rf := false }) none, t) := by
  refine instruction_next htf (show Decode.decode _ _ = .ok (mk .movzx 32 [r32 0, .mem (mbi 7 2)] 4) from
    decode_of_window (fetchByte_code hc hrip) rfl) ?_
  simp only [exec, Sem.movzx, mk, mbi, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef, effOffset,
    pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, BitVec.add_zero, get_regOf_7, get_regOf_2]
  rw [checkAccess_ok (s := advance s 4) hac hld]
  rfl

/-- `movzx ecx, byte [r8+rdx]`. -/
theorem i17 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 17) (htf : s.cpu.rflags.tf = false)
    (hac : s.cpu.rflags.ac = false)
    (hld : ∀ x ∈ byteAddrs (s.cpu.gpr.r8 + s.cpu.gpr.rdx) 1, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none) :
    (instruction prof s).runStream o t =
      (.running (nx s 5 (s.cpu.gpr.set 1
        (((ofBytesLE 8 (readBytes s.proc.mm.mem (s.cpu.gpr.r8 + s.cpu.gpr.rdx) 1)).setWidth 32).setWidth 64))
        { s.cpu.rflags with rf := false }) none, t) := by
  refine instruction_next htf (show Decode.decode _ _ = .ok (mk .movzx 32 [r32 1, .mem (mbi 8 2)] 5) from
    decode_of_window (fetchByte_code hc hrip) rfl) ?_
  simp only [exec, Sem.movzx, mk, mbi, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef, effOffset,
    pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, BitVec.add_zero, get_regOf_8, get_regOf_2]
  rw [checkAccess_ok (s := advance s 5) hac hld]
  rfl

/-- `cmp al, cl`. -/
theorem i22 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 22) (htf : s.cpu.rflags.tf = false) :
    ∃ fl, (instruction prof s).runStream o t = (.running (nx s 2 s.cpu.gpr fl) none, t) ∧
      fl.zf = decide (s.cpu.gpr.rax.setWidth 8 = s.cpu.gpr.rcx.setWidth 8) ∧ fl.tf = s.cpu.rflags.tf ∧
      fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨_, instruction_next htf (show Decode.decode _ _ = .ok (mk .cmp 8 [r8 0, r8 1] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl, ?_, rfl, rfl, rfl⟩
  change ((BitVec.setWidth 8 s.cpu.gpr.rax - BitVec.setWidth 8 s.cpu.gpr.rcx -
    (BitVec.ofBool false).setWidth 8) == 0) = _
  simp [bv_sub_beq_zero]

/-- `je 29`, taken. -/
theorem i24t (hc : Code prof s e) (hrip : s.cpu.rip = e.add 24) (htf : s.cpu.rflags.tf = false)
    (hz : s.cpu.rflags.zf = true) (hcan : (e.add 29).canonical prof.feat.la57 = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (e.add 29) s.cpu.gpr { s.cpu.rflags with rf := false }) none, t) := by
  refine instruction_next htf (show Decode.decode _ _ = .ok (mk (.jcc 4) 64 [.rel 3] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) ?_
  have ht : (e.add 24).add 2 + BitVec.ofNat 64 3 = e.add 29 := by simp only [Addr.add]; bv_omega
  simp only [exec, Sem.jcc, mk, Prog.run, bind, Prog.bind, Prog.readFlags, Prog.readRip, advance, State.modCpu, hrip,
    hz, ht, Rflags.cond, jumpTo, hcan, Bool.false_eq_true, ↓reduceIte, Prog.writeRip, done]
  rfl

/-- `je 29`, not taken. -/
theorem i24n (hc : Code prof s e) (hrip : s.cpu.rip = e.add 24) (htf : s.cpu.rflags.tf = false)
    (hz : s.cpu.rflags.zf = false) :
    (instruction prof s).runStream o t = (.running (nx s 2 s.cpu.gpr { s.cpu.rflags with rf := false }) none, t) := by
  refine instruction_next htf (show Decode.decode _ _ = .ok (mk (.jcc 4) 64 [.rel 3] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) ?_
  simp only [exec, Sem.jcc, mk, Prog.run, bind, Prog.bind, Prog.readFlags, Prog.readRip, advance, State.modCpu, hz,
    Rflags.cond, Bool.false_eq_true, ↓reduceIte, done]
  rfl

/-- `sub eax, ecx`. -/
theorem i26 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 26) (htf : s.cpu.rflags.tf = false) :
    ∃ v fl, (instruction prof s).runStream o t = (.running (nx s 2 (s.cpu.gpr.set 0 v) fl) none, t) ∧
      v = (s.cpu.gpr.rax.setWidth 32 - s.cpu.gpr.rcx.setWidth 32).setWidth 64 ∧ fl.tf = s.cpu.rflags.tf ∧
      fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨_, _, instruction_next htf (show Decode.decode _ _ = .ok (mk .sub 32 [r32 0, r32 1] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl, ?_, rfl, rfl, rfl⟩
  change (BitVec.setWidth 64 (BitVec.setWidth 32 s.cpu.gpr.rax - BitVec.setWidth 32 s.cpu.gpr.rcx -
    (BitVec.ofBool false).setWidth 32) : BitVec 64) = _
  simp

/-- `ret`, to `ra`, the word on top of the stack. -/
theorem iret {k : Nat} (hc : Code prof s e) (hrip : s.cpu.rip = e.add k)
    (hk : (gccOs.drop k).take 1 = [0xc3]) (htf : s.cpu.rflags.tf = false)
    (hac : s.cpu.rflags.ac = false) (hsh : s.thread.shstk = none) {ra : Addr}
    (hw : ofBytesLE 64 (readBytes s.proc.mm.mem s.cpu.gpr.rsp 8) = ra) (hcan : ra.canonical prof.feat.la57 = true)
    (hld : ∀ x ∈ byteAddrs s.cpu.gpr.rsp 8, x.canonical prof.feat.la57 = true ∧
      s.proc.mm.mem.check prof.feat s.cpu.pkru .read x = none) :
    (instruction prof s).runStream o t =
      (.running (upd s ra (s.cpu.gpr.set 4 (s.cpu.gpr.rsp + 8)) { s.cpu.rflags with rf := false }) none, t) := by
  have hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .ret 64 [] 1) := by
    refine decode_of_window (bs := [0xc3]) (fun i hi => ?_) rfl
    have hi1 : i = 0 := by simpa using hi
    subst hi1
    have hlen : 0 < (gccOs.drop k).length := by
      rcases h : gccOs.drop k with _ | ⟨b, l⟩
      · rw [h] at hk; simp at hk
      · simp
    rw [fetchByte_code hc hrip 0 hlen]
    rcases h : gccOs.drop k with _ | ⟨b, l⟩
    · rw [h] at hlen; simp at hlen
    · rw [h] at hk; simpa using hk
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.ret, mk, Prog.run, bind, Prog.bind, Prog.readThread, Prog.readReg, Prog.read, pure,
    show (advance s 1).thread.shstk = none from hsh, Bool.false_eq_true, ↓reduceIte]
  rw [checkAccess_ok (s := advance s 1) hac hld]
  have hw' : ofBytesLE 64 (readBytes (advance s 1).proc.mm.mem ((advance s 1).cpu.gpr.get 4) 8) = ra := hw
  simp only [Nat.reduceDiv, hw', hcan, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- `inc rdx`. -/
theorem i29 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 29) (htf : s.cpu.rflags.tf = false) :
    ∃ v fl, (instruction prof s).runStream o t = (.running (nx s 3 (s.cpu.gpr.set 2 v) fl) none, t) ∧
      v = s.cpu.gpr.rdx + 1 ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨_, _, instruction_next htf (show Decode.decode _ _ = .ok (mk .inc 64 [r64 2] 3) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl, ?_, rfl, rfl, rfl⟩
  change (BitVec.setWidth 64 (BitVec.setWidth 64 s.cpu.gpr.rdx + (1 : BitVec 64) +
    (BitVec.ofBool false).setWidth 64) : BitVec 64) = _
  simp

/-- `jmp 8`. -/
theorem i32 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 32) (htf : s.cpu.rflags.tf = false)
    (hcan : (e.add 8).canonical prof.feat.la57 = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (e.add 8) s.cpu.gpr { s.cpu.rflags with rf := false }) none, t) := by
  refine instruction_next htf (show Decode.decode _ _ = .ok (mk .jmp 64 [.rel 18446744073709551590] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) ?_
  have ht : (e.add 32).add 2 + BitVec.ofNat 64 18446744073709551590 = e.add 8 := by
    simp only [Addr.add]; bv_omega
  simp only [exec, Sem.jmp, mk, Prog.run, bind, Prog.bind, Prog.readRip, advance, State.modCpu, hrip, ht,
    jumpTo, hcan, Bool.false_eq_true, ↓reduceIte, Prog.writeRip, done]
  rfl

/-- `xor eax, eax` (`AF` undefined: one answer of the stream). -/
theorem i34 (hc : Code prof s e) (hrip : s.cpu.rip = e.add 34) (htf : s.cpu.rflags.tf = false) :
    ∃ v fl, (instruction prof s).runStream o t = (.running (nx s 2 (s.cpu.gpr.set 0 v) fl) none, t + 1) ∧
      v = 0 ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨_, _, instruction_next htf (show Decode.decode _ _ = .ok (mk .xor 32 [r32 0, r32 0] 2) from
    decode_of_window (fetchByte_code hc hrip) rfl) rfl, ?_, rfl, rfl, rfl⟩
  change (BitVec.setWidth 64 (BitVec.setWidth 32 s.cpu.gpr.rax ^^^ BitVec.setWidth 32 s.cpu.gpr.rax) : BitVec 64) = 0
  simp

/-! ## Bytes and their order -/

theorem cmpBytes_self : ∀ xs : List Byte, cmpBytes xs xs = .eq
  | [] => rfl
  | x :: xs => by simp [cmpBytes, cmpBytes_self xs]

theorem cmpBytes_diff : ∀ (xs ys : List Byte) (i : Nat) (hx : i < xs.length) (hy : i < ys.length),
    xs.take i = ys.take i → xs[i] ≠ ys[i] → cmpBytes xs ys = compare xs[i].toNat ys[i].toNat
  | [], _, _, hx, _, _, _ => by simp at hx
  | _ :: _, [], _, _, hy, _, _ => by simp at hy
  | x :: xs, y :: ys, 0, _, _, _, hne => by
    simp only [List.getElem_cons_zero] at hne ⊢
    simp [cmpBytes, hne]
  | x :: xs, y :: ys, i + 1, hx, hy, hp, hne => by
    simp only [List.take_succ_cons, List.cons.injEq] at hp
    simp only [List.getElem_cons_succ] at hne ⊢
    simp only [cmpBytes, hp.1, ↓reduceIte]
    exact cmpBytes_diff xs ys i (by simpa using hx) (by simpa using hy) hp.2 hne

theorem readBytes_length (m : Memory) (a : Addr) (n : Nat) : (readBytes m a n).length = n := by
  simp [readBytes, byteAddrs]

theorem readBytes_getElem (m : Memory) (a : Addr) (n i : Nat) (h : i < (readBytes m a n).length) :
    (readBytes m a n)[i] = m.readByte (a.add i) := by
  simp [readBytes, byteAddrs]

theorem readBytes_take (m : Memory) (a : Addr) (n i : Nat) (h : i ≤ n) :
    (readBytes m a n).take i = readBytes m a i := by
  simp [readBytes, byteAddrs, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem readBytes_succ (m : Memory) (a : Addr) (i : Nat) :
    readBytes m a (i + 1) = readBytes m a i ++ [m.readByte (a.add i)] := by
  simp [readBytes, byteAddrs, List.range_succ]

theorem post_diff (x y : BitVec 8) :
    compare ((((((x.setWidth 32).setWidth 64).setWidth 32 - ((y.setWidth 32).setWidth 64).setWidth 32).setWidth 64)).setWidth 32).toInt 0 =
      compare x.toNat y.toNat := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toInt_eq_toNat_cond, BitVec.toNat_setWidth, BitVec.toNat_sub]
  rcases Nat.lt_trichotomy x.toNat y.toNat with h | h | h
  · rw [Nat.compare_eq_lt.2 h, Int.compare_eq_lt.2]
    split <;> omega
  · rw [Nat.compare_eq_eq.2 h, Int.compare_eq_eq.2]
    split <;> omega
  · rw [Nat.compare_eq_gt.2 h, Int.compare_eq_gt.2]
    split <;> omega

/-! ## The run -/

/-- The callee-saved registers and `rsp` as at the call. -/
def Callee (s₀ X : State) : Prop :=
  X.cpu.gpr.rbx = s₀.cpu.gpr.rbx ∧ X.cpu.gpr.rsp = s₀.cpu.gpr.rsp ∧ X.cpu.gpr.rbp = s₀.cpu.gpr.rbp ∧
    X.cpu.gpr.r12 = s₀.cpu.gpr.r12 ∧ X.cpu.gpr.r13 = s₀.cpu.gpr.r13 ∧ X.cpu.gpr.r14 = s₀.cpu.gpr.r14 ∧
    X.cpu.gpr.r15 = s₀.cpu.gpr.r15

/-- What every step of a run of a call uses: the call, where its code lies, the environment. -/
structure Call (prof : Profile) (e : Addr) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) :
    Prop where
  call : CallOf prof e L contract s₀ ra
  code : CodeIn L e gccOs
  env : Undisturbed o

/-- The rest of the run, from `X` with answers from position `t`, returns as `memcmp`'s contract says, its `rip` in
the code until then. -/
abbrev Go (prof : Profile) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (X : State)
    (t : Nat) : Prop :=
  RunsFrom prof o (InCode L) [] X t (fun Y _ evs => Returned prof.feat contract s₀ ra Y evs) (contract.ends s₀)

variable {prof : Profile} {e : Addr} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

namespace Call

/-- A step: the instruction at the code's `j`-th byte, from every state the kernel's ordinary events may leave. -/
theorem step (c : Call prof e L s₀ ra o) {X : State} {t j : Nat} (hK : Kept s₀ X) (hj : j < gccOs.length)
    (hrip : X.cpu.rip = e.add j)
    (h : ∀ M, Calm (IdAddr X.thread.rseq) X.proc.mm.mem M → Code prof (X.withMem M) e → Kept s₀ (X.withMem M) →
      X.cpu.rflags.tf = false → X.cpu.rflags.ac = false →
      ∃ Y t', (instruction prof (X.withMem M)).runStream o (t + 1) = (.running Y none, t') ∧
        Go prof L s₀ ra o Y t') :
    Go prof L s₀ ra o X t := by
  refine runsFrom_ins c.env (quiet_of_rseqQuiet c.call.ready.rseq c.call.foot.noAlias) hK
    (inCode_of_codeIn c.code hj hrip) fun M hM => ?_
  have hK' := hK.withMem hM
  exact h M hM (hK'.codeAt c.call.foot c.call.ready.rseq c.code) hK'
    (hK.tf.trans c.call.ready.plain.1) (hK.ac.trans c.call.ready.plain.2.1)

/-- The bytes of the return address's slot lie in the footprint. -/
theorem slot (c : Call prof e L s₀ ra o) {i : Nat} (hi : i < 8) :
    Foot ((contract.footprint L s₀).data ++ (contract.footprint L s₀).codeRgns) (s₀.cpu.gpr.rsp.add i) := by
  have hf := c.call.foot.fits (frame s₀ 0) (by simp [Footprint.data, Contract.footprint, contract])
  simp only [frame, Rgn.Fits, BitVec.sub_zero] at hf
  refine ⟨frame s₀ 0, by simp [Footprint.data, Contract.footprint, contract], ?_⟩
  simp only [frame, BitVec.sub_zero]
  exact mem_add_of_fits hi hf

/-- The return address's slot can be read. -/
theorem slot_read (c : Call prof e L s₀ ra o) {X : State} (hK : Kept s₀ X) (hC : Callee s₀ X) :
    ∀ x ∈ byteAddrs X.cpu.gpr.rsp 8, x.canonical prof.feat.la57 = true ∧
      X.proc.mm.mem.check prof.feat X.cpu.pkru .read x = none := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  have hw := c.call.foot.writable (frame s₀ 0) (by simp [Contract.footprint, contract]) (s₀.cpu.gpr.rsp.add i) (by
    have hf := c.call.foot.fits (frame s₀ 0) (by simp [Footprint.data, Contract.footprint, contract])
    simp only [frame, Rgn.Fits, BitVec.sub_zero] at hf ⊢
    exact mem_add_of_fits hi hf)
  rw [hC.2.1, hK.calm.check, hK.pkru]
  exact ⟨hw.1, check_read_of_write hw.2⟩

/-- The return address, as the slot holds it. -/
theorem slot_word (c : Call prof e L s₀ ra o) {X : State} (hK : Kept s₀ X) (hC : Callee s₀ X) :
    ofBytesLE 64 (readBytes X.proc.mm.mem X.cpu.gpr.rsp 8) = ra := by
  rw [hC.2.1, hK.calm.readBytes_foot c.call.foot c.call.ready.rseq fun i hi => c.slot hi]
  exact c.call.shape.2.1

/-- The state `ret` leaves, from a state that kept the call's frame and callee-saved registers and holds `memcmp`'s
result, is a return as the contract says. -/
theorem returned (c : Call prof e L s₀ ra o) {X : State} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hpost : contract.post s₀ X) :
    Returned prof.feat contract s₀ ra
      (upd X ra (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) { X.cpu.rflags with rf := false }) [] := by
  have hK' : Kept s₀ (upd X ra (X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) { X.cpu.rflags with rf := false }) :=
    hK.upd rfl rfl rfl
  obtain ⟨-, -, -, -, hdf, hx87⟩ := c.call.shape
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hK'.keepsEnv, hK'.keepsSettings c.call.ready.plain, hK'.keepsProc,
    hK'.keepsFiles, hK'.changesOnly fun y hy => ?_⟩, hpost, rfl⟩
  · intro r hr
    simp only [contract, sysv, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hC.1
    · exact hC.2.2.1
    · exact hC.2.2.2.1
    · exact hC.2.2.2.2.1
    · exact hC.2.2.2.2.2.1
    · exact hC.2.2.2.2.2.2
  · show X.cpu.gpr.rsp + 8 = _
    rw [hC.2.1]
  · exact hK.df.trans hdf
  · exact hK.x87 ▸ hx87
  · show X.cpu.vec.mxcsr >>> 6 = _
    rw [hK.mxcsr]
  · show X.cpu.x87.fcw = _
    rw [hK.x87]
  · obtain ⟨r, hr, hm⟩ := IdAddr.foot_ids (RseqQuiet.fits c.call.ready.rseq) hy
    exact ⟨r, List.mem_append_right _ hr, hm⟩

/-- `ret`, at the code's `k`-th byte, from a state that kept the call's frame and callee-saved registers and holds
`memcmp`'s result. -/
theorem ret (c : Call prof e L s₀ ra o) {X : State} {t k : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hk : k < gccOs.length) (hrip : X.cpu.rip = e.add k) (hb : (gccOs.drop k).take 1 = [0xc3])
    (hpost : contract.post s₀ X) : Go prof L s₀ ra o X t :=
  c.step hK hk hrip fun M hM hc hK' htf hac =>
    ⟨_, _, iret hc hrip hb htf hac (by rw [hK'.thread]; exact c.call.ready.plain.2.2.1)
      (c.slot_word hK' hC) c.call.shape.2.2.1 (c.slot_read hK' hC),
      runsFrom_done (c.returned hK' hC hpost)⟩

end Call

/-- In the loop, at index `i`: the call's frame and callee-saved registers kept, `rdi` and `r8` the strings, `rsi`
the length, `rdx` the index, and the first `i` bytes of the strings equal. -/
structure At (s₀ : State) (i : Nat) (X : State) : Prop where
  kept : Kept s₀ X
  callee : Callee s₀ X
  rdi : X.cpu.gpr.rdi = s₀.cpu.gpr.rdi
  r8 : X.cpu.gpr.r8 = s₀.cpu.gpr.rsi
  rsi : X.cpu.gpr.rsi = s₀.cpu.gpr.rdx
  rdx : X.cpu.gpr.rdx = BitVec.ofNat 64 i
  le : i ≤ s₀.cpu.gpr.rdx.toNat
  same : readBytes s₀.proc.mm.mem s₀.cpu.gpr.rdi i = readBytes s₀.proc.mm.mem s₀.cpu.gpr.rsi i

namespace At
variable {i : Nat} {X : State} {M : Memory} {len : Nat} {fl : Rflags}

theorem next (h : At s₀ i X) (hK : Kept s₀ (X.withMem M)) (htf : fl.tf = X.cpu.rflags.tf)
    (hac : fl.ac = X.cpu.rflags.ac) (hdf : fl.df = X.cpu.rflags.df) : At s₀ i (nx (X.withMem M) len X.cpu.gpr fl) :=
  ⟨hK.nx htf hac hdf, h.callee, h.rdi, h.r8, h.rsi, h.rdx, h.le, h.same⟩

theorem jump (h : At s₀ i X) (hK : Kept s₀ (X.withMem M)) {r : Addr} :
    At s₀ i (upd (X.withMem M) r X.cpu.gpr { X.cpu.rflags with rf := false }) :=
  ⟨hK.upd rfl rfl rfl, h.callee, h.rdi, h.r8, h.rsi, h.rdx, h.le, h.same⟩

theorem rax (h : At s₀ i X) (hK : Kept s₀ (X.withMem M)) {v : BitVec 64} (htf : fl.tf = X.cpu.rflags.tf)
    (hac : fl.ac = X.cpu.rflags.ac) (hdf : fl.df = X.cpu.rflags.df) :
    At s₀ i (nx (X.withMem M) len (X.cpu.gpr.set 0 v) fl) :=
  ⟨hK.nx htf hac hdf, h.callee, h.rdi, h.r8, h.rsi, h.rdx, h.le, h.same⟩

theorem rcx (h : At s₀ i X) (hK : Kept s₀ (X.withMem M)) {v : BitVec 64} (htf : fl.tf = X.cpu.rflags.tf)
    (hac : fl.ac = X.cpu.rflags.ac) (hdf : fl.df = X.cpu.rflags.df) :
    At s₀ i (nx (X.withMem M) len (X.cpu.gpr.set 1 v) fl) :=
  ⟨hK.nx htf hac hdf, h.callee, h.rdi, h.r8, h.rsi, h.rdx, h.le, h.same⟩

end At

theorem setWidth_zext (x : BitVec 8) : ((x.setWidth 32).setWidth 64).setWidth 8 = x := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem ofNat_succ (i : Nat) : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat_eq_iff {i : Nat} {n : BitVec 64} (h : i ≤ n.toNat) : BitVec.ofNat 64 i = n ↔ i = n.toNat := by
  have := n.isLt
  constructor
  · intro e; subst e; simp only [BitVec.toNat_ofNat] at h ⊢; omega
  · intro e; subst e; simp

namespace Call

/-- The `i`-th byte of either string lies in the footprint, readable. -/
theorem str (c : Call prof e L s₀ ra o) {r : Rgn} (hr : r ∈ strings s₀) {i : Nat} (hi : i < r.len) :
    Foot ((contract.footprint L s₀).data ++ (contract.footprint L s₀).codeRgns) (r.base.add i) ∧
      (r.base.add i).canonical prof.feat.la57 = true ∧
      s₀.proc.mm.mem.check prof.feat s₀.cpu.pkru .read (r.base.add i) = none := by
  have hr' : r ∈ (contract.footprint L s₀).reads := hr
  have hf := c.call.foot.fits r (by simp [Footprint.data, hr'])
  have hm : r.Mem (r.base.add i) := mem_add_of_fits hi hf
  exact ⟨⟨r, by simp [Footprint.data, hr'], hm⟩, c.call.foot.readable r hr' _ hm⟩

/-- A load of the `i`-th byte of either string passes its checks and reads the byte as at the call. -/
theorem load (c : Call prof e L s₀ ra o) {X : State} (hK : Kept s₀ X) {r : Rgn} (hr : r ∈ strings s₀) {i : Nat}
    (hi : i < r.len) :
    (∀ x ∈ byteAddrs (r.base.add i) 1, x.canonical prof.feat.la57 = true ∧
      X.proc.mm.mem.check prof.feat X.cpu.pkru .read x = none) ∧
      ofBytesLE 8 (readBytes X.proc.mm.mem (r.base.add i) 1) = s₀.proc.mm.mem.readByte (r.base.add i) := by
  obtain ⟨hf, hcan, hck⟩ := c.str hr hi
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hx
    obtain rfl : j = 0 := by omega
    rw [addr_add_add, hK.calm.check, hK.pkru]
    exact ⟨hcan, hck⟩
  · rw [ofBytesLE_one, hK.calm.readByte_foot c.call.foot c.call.ready.rseq hf]

/-- `xor eax, eax; ret`: the strings are equal. -/
theorem at34 (c : Call prof e L s₀ ra o) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 34)
    (heq : cmpBytes (readBytes s₀.proc.mm.mem s₀.cpu.gpr.rdi s₀.cpu.gpr.rdx.toNat)
      (readBytes s₀.proc.mm.mem s₀.cpu.gpr.rsi s₀.cpu.gpr.rdx.toNat) = .eq) : Go prof L s₀ ra o X t :=
  c.step (j := 34) hK (by decide) hrip fun M _ hc hK' htf _ => by
    obtain ⟨v, fl, hr, hv, htf', hac', hdf'⟩ := i34 (o := o) (t := t + 1) hc hrip htf
    refine ⟨_, _, hr, c.ret (k := 36) (hK'.nx htf' hac' hdf') hC (by decide) (by
      show X.cpu.rip.add 2 = _; rw [hrip, addr_add_add]) rfl ?_⟩
    show compare ((v.setWidth 32).toInt) 0 = _
    rw [hv, heq]
    rfl

/-- `sub eax, ecx; ret`: the strings differ first at bytes `x` and `y`. -/
theorem at26 (c : Call prof e L s₀ ra o) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 26) {x y : BitVec 8} (hax : X.cpu.gpr.rax = (x.setWidth 32).setWidth 64)
    (hcx : X.cpu.gpr.rcx = (y.setWidth 32).setWidth 64)
    (hxy : compare x.toNat y.toNat = cmpBytes (readBytes s₀.proc.mm.mem s₀.cpu.gpr.rdi s₀.cpu.gpr.rdx.toNat)
      (readBytes s₀.proc.mm.mem s₀.cpu.gpr.rsi s₀.cpu.gpr.rdx.toNat)) : Go prof L s₀ ra o X t :=
  c.step (j := 26) hK (by decide) hrip fun M _ hc hK' htf _ => by
    obtain ⟨v, fl, hr, hv, htf', hac', hdf'⟩ := i26 (o := o) (t := t + 1) hc hrip htf
    refine ⟨_, _, hr, c.ret (k := 28) (hK'.nx htf' hac' hdf') hC (by decide) (by
      show X.cpu.rip.add 2 = _; rw [hrip, addr_add_add]) rfl ?_⟩
    show compare ((v.setWidth 32).toInt) 0 = _
    rw [hv]
    show compare (((X.cpu.gpr.rax.setWidth 32 - X.cpu.gpr.rcx.setWidth 32).setWidth 64).setWidth 32).toInt 0 = _
    rw [hax, hcx, post_diff, hxy]

/-- `inc rdx; jmp 8`: on to the next index. -/
theorem at29 (c : Call prof e L s₀ ra o) {X : State} {t i : Nat} (h : At s₀ i X) (hrip : X.cpu.rip = e.add 29)
    (hlt : i < s₀.cpu.gpr.rdx.toNat)
    (hs : readBytes s₀.proc.mm.mem s₀.cpu.gpr.rdi (i + 1) = readBytes s₀.proc.mm.mem s₀.cpu.gpr.rsi (i + 1))
    (ih : ∀ Y t, At s₀ (i + 1) Y → Y.cpu.rip = e.add 8 → Go prof L s₀ ra o Y t) : Go prof L s₀ ra o X t :=
  c.step (j := 29) h.kept (by decide) hrip fun M _ hc hK' htf _ => by
    obtain ⟨v, fl, hr, hv, htf', hac', hdf'⟩ := i29 (o := o) (t := t + 1) hc hrip htf
    have hrip' : (nx (X.withMem M) 3 (X.cpu.gpr.set 2 v) fl).cpu.rip = e.add 32 := by
      show X.cpu.rip.add 3 = _; rw [hrip, addr_add_add]
    refine ⟨_, _, hr, c.step (j := 32) (hK'.nx htf' hac' hdf') (by decide) hrip' fun M₂ _ hc₂ hK₂ htf₂ _ =>
      ⟨_, _, i32 hc₂ hrip' htf₂ (hc₂ 8 (by decide)).1, ih _ _ ⟨hK₂.upd rfl rfl rfl, h.callee, h.rdi, h.r8, h.rsi,
        hv.trans (by show X.cpu.gpr.rdx + 1 = _; rw [h.rdx, ofNat_succ]), by omega, hs⟩ rfl⟩⟩

/-- `je 29`: the `i`-th bytes, `x` in `rax` and `y` in `rcx`, are equal or not. -/
theorem at24 (c : Call prof e L s₀ ra o) {X : State} {t i : Nat} (h : At s₀ i X) (hrip : X.cpu.rip = e.add 24)
    (hlt : i < s₀.cpu.gpr.rdx.toNat)
    (hax : X.cpu.gpr.rax = ((s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rdi i)).setWidth 32).setWidth 64)
    (hcx : X.cpu.gpr.rcx = ((s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rsi i)).setWidth 32).setWidth 64)
    (hz : X.cpu.rflags.zf =
      decide (s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rdi i) = s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rsi i)))
    (ih : ∀ Y t, At s₀ (i + 1) Y → Y.cpu.rip = e.add 8 → Go prof L s₀ ra o Y t) : Go prof L s₀ ra o X t := by
  by_cases hxy : s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rdi i) = s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rsi i)
  · exact c.step (j := 24) h.kept (by decide) hrip fun M _ hc hK' htf _ =>
      ⟨_, _, i24t hc hrip htf (hz.trans (decide_eq_true hxy)) (hc 29 (by decide)).1,
        c.at29 (h.jump hK') rfl hlt (by rw [readBytes_succ, readBytes_succ, h.same, hxy]) ih⟩
  · refine c.step (j := 24) h.kept (by decide) hrip fun M _ hc hK' htf _ =>
      ⟨_, _, i24n hc hrip htf (hz.trans (decide_eq_false hxy)), c.at26 (hK'.nx rfl rfl rfl) h.callee
        (by show X.cpu.rip.add 2 = _; rw [hrip, addr_add_add]) hax hcx ?_⟩
    have hl : ∀ a, i < (readBytes s₀.proc.mm.mem a s₀.cpu.gpr.rdx.toNat).length := fun a => by
      rw [readBytes_length]; exact hlt
    rw [cmpBytes_diff _ _ i (hl _) (hl _) (by rw [readBytes_take _ _ _ _ (Nat.le_of_lt hlt), readBytes_take _ _ _ _ (Nat.le_of_lt hlt), h.same])
      (by simp only [readBytes_getElem]; exact hxy)]
    simp only [readBytes_getElem]

/-- `cmp al, cl`. -/
theorem at22 (c : Call prof e L s₀ ra o) {X : State} {t i : Nat} (h : At s₀ i X) (hrip : X.cpu.rip = e.add 22)
    (hlt : i < s₀.cpu.gpr.rdx.toNat)
    (hax : X.cpu.gpr.rax = ((s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rdi i)).setWidth 32).setWidth 64)
    (hcx : X.cpu.gpr.rcx = ((s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rsi i)).setWidth 32).setWidth 64)
    (ih : ∀ Y t, At s₀ (i + 1) Y → Y.cpu.rip = e.add 8 → Go prof L s₀ ra o Y t) : Go prof L s₀ ra o X t :=
  c.step (j := 22) h.kept (by decide) hrip fun M _ hc hK' htf _ => by
    obtain ⟨fl, hr, hz, htf', hac', hdf'⟩ := i22 (o := o) (t := t + 1) hc hrip htf
    refine ⟨_, _, hr, c.at24 (h.next hK' htf' hac' hdf') (by show X.cpu.rip.add 2 = _; rw [hrip, addr_add_add])
      hlt hax hcx ?_ ih⟩
    rw [nx_rflags, hz]
    show decide (X.cpu.gpr.rax.setWidth 8 = X.cpu.gpr.rcx.setWidth 8) = _
    rw [hax, hcx, setWidth_zext, setWidth_zext]

/-- `movzx ecx, byte [r8+rdx]`. -/
theorem at17 (c : Call prof e L s₀ ra o) {X : State} {t i : Nat} (h : At s₀ i X) (hrip : X.cpu.rip = e.add 17)
    (hlt : i < s₀.cpu.gpr.rdx.toNat)
    (hax : X.cpu.gpr.rax = ((s₀.proc.mm.mem.readByte (Addr.add s₀.cpu.gpr.rdi i)).setWidth 32).setWidth 64)
    (ih : ∀ Y t, At s₀ (i + 1) Y → Y.cpu.rip = e.add 8 → Go prof L s₀ ra o Y t) : Go prof L s₀ ra o X t :=
  c.step (j := 17) h.kept (by decide) hrip fun M _ hc hK' htf hac => by
    have hL := c.load hK' (r := ⟨s₀.cpu.gpr.rsi, s₀.cpu.gpr.rdx.toNat⟩) (by simp [strings]) hlt
    have ha : (X.withMem M).cpu.gpr.r8 + (X.withMem M).cpu.gpr.rdx = Addr.add s₀.cpu.gpr.rsi i := by
      show X.cpu.gpr.r8 + X.cpu.gpr.rdx = _; rw [h.r8, h.rdx]; rfl
    refine ⟨_, _, i17 (o := o) (t := t + 1) hc hrip htf hac (by rw [ha]; exact hL.1),
      c.at22 (h.rcx hK' rfl rfl rfl) (by show X.cpu.rip.add 5 = _; rw [hrip, addr_add_add]) hlt hax ?_ ih⟩
    show ((ofBytesLE 8 (readBytes M ((X.withMem M).cpu.gpr.r8 + (X.withMem M).cpu.gpr.rdx) 1)).setWidth 32).setWidth 64 = _
    rw [ha]
    exact congrArg (fun x : BitVec 8 => (x.setWidth 32).setWidth 64) hL.2

/-- `movzx eax, byte [rdi+rdx]`. -/
theorem at13 (c : Call prof e L s₀ ra o) {X : State} {t i : Nat} (h : At s₀ i X) (hrip : X.cpu.rip = e.add 13)
    (hlt : i < s₀.cpu.gpr.rdx.toNat)
    (ih : ∀ Y t, At s₀ (i + 1) Y → Y.cpu.rip = e.add 8 → Go prof L s₀ ra o Y t) : Go prof L s₀ ra o X t :=
  c.step (j := 13) h.kept (by decide) hrip fun M _ hc hK' htf hac => by
    have hL := c.load hK' (r := ⟨s₀.cpu.gpr.rdi, s₀.cpu.gpr.rdx.toNat⟩) (by simp [strings]) hlt
    have ha : (X.withMem M).cpu.gpr.rdi + (X.withMem M).cpu.gpr.rdx = Addr.add s₀.cpu.gpr.rdi i := by
      show X.cpu.gpr.rdi + X.cpu.gpr.rdx = _; rw [h.rdi, h.rdx]; rfl
    refine ⟨_, _, i13 (o := o) (t := t + 1) hc hrip htf hac (by rw [ha]; exact hL.1),
      c.at17 (h.rax hK' rfl rfl rfl) (by show X.cpu.rip.add 4 = _; rw [hrip, addr_add_add]) hlt ?_ ih⟩
    show ((ofBytesLE 8 (readBytes M ((X.withMem M).cpu.gpr.rdi + (X.withMem M).cpu.gpr.rdx) 1)).setWidth 32).setWidth 64 = _
    rw [ha]
    exact congrArg (fun x : BitVec 8 => (x.setWidth 32).setWidth 64) hL.2

/-- The loop's head, `cmp rdx, rsi; je 34`: at the end of the strings, or on to the `i`-th bytes. -/
theorem at8 (c : Call prof e L s₀ ra o) {X : State} {t i : Nat} (h : At s₀ i X) (hrip : X.cpu.rip = e.add 8)
    (ih : ∀ Y t, At s₀ (i + 1) Y → Y.cpu.rip = e.add 8 → Go prof L s₀ ra o Y t) : Go prof L s₀ ra o X t :=
  c.step (j := 8) h.kept (by decide) hrip fun M _ hc hK' htf _ => by
    obtain ⟨fl, hr, hz, htf', hac', hdf'⟩ := i8 (o := o) (t := t + 1) hc hrip htf
    have hK₁ := hK'.nx (len := 3) (g := X.cpu.gpr) htf' hac' hdf'
    have hrip₁ : (nx (X.withMem M) 3 X.cpu.gpr fl).cpu.rip = e.add 11 := by
      show X.cpu.rip.add 3 = _; rw [hrip, addr_add_add]
    have hz' : fl.zf = decide (i = s₀.cpu.gpr.rdx.toNat) := by
      rw [hz]; show decide (X.cpu.gpr.rdx = X.cpu.gpr.rsi) = _
      rw [h.rdx, h.rsi]; exact decide_eq_decide.2 (ofNat_eq_iff h.le)
    refine ⟨_, _, hr, ?_⟩
    by_cases hi : i = s₀.cpu.gpr.rdx.toNat
    · exact c.step (j := 11) hK₁ (by decide) hrip₁ fun M₁ _ hc₁ hK₁' htf₁ _ =>
        ⟨_, _, i11t hc₁ hrip₁ htf₁ (hz'.trans (decide_eq_true hi)) (hc₁ 34 (by decide)).1,
          c.at34 (hK₁'.upd rfl rfl rfl) h.callee rfl (by rw [← hi, h.same]; exact cmpBytes_self _)⟩
    · exact c.step (j := 11) hK₁ (by decide) hrip₁ fun M₁ _ hc₁ hK₁' htf₁ _ =>
        ⟨_, _, i11n hc₁ hrip₁ htf₁ (hz'.trans (decide_eq_false hi)),
          c.at13 ((h.next hK' htf' hac' hdf').next hK₁' rfl rfl rfl)
            (by show (X.cpu.rip.add 3).add 2 = _; rw [hrip, addr_add_add, addr_add_add]) (by have := h.le; omega) ih⟩

/-- The loop, by the number of bytes left. -/
theorem loop (c : Call prof e L s₀ ra o) :
    ∀ d i X t, s₀.cpu.gpr.rdx.toNat - i = d → At s₀ i X → X.cpu.rip = e.add 8 → Go prof L s₀ ra o X t := by
  intro d
  induction d with
  | zero => intro i X t hd h hrip; exact c.at8 h hrip fun Y t' h' _ => absurd h'.le (by have := h.le; omega)
  | succ d ih => intro i X t hd h hrip; exact c.at8 h hrip fun Y t' h' hr => ih (i + 1) Y t' (by omega) h' hr

/-- The entry, `mov r8, rsi; mov rsi, rdx; xor edx, edx`, then the loop from index 0. -/
theorem entry (c : Call prof e L s₀ ra o) {t : Nat} : Go prof L s₀ ra o s₀ t := by
  have hrip : s₀.cpu.rip = e.add 0 := by rw [c.call.shape.1]; simp [Addr.add]
  refine c.step (j := 0) (Kept.refl s₀) (by decide) hrip fun M _ hc hK htf _ =>
    ⟨_, _, i0 (o := o) (t := t + 1) hc hrip htf, ?_⟩
  have hrip₁ : (nx (s₀.withMem M) 3 (s₀.cpu.gpr.set 8 s₀.cpu.gpr.rsi) { s₀.cpu.rflags with rf := false }).cpu.rip =
      e.add 3 := by
    show s₀.cpu.rip.add 3 = _; rw [hrip, addr_add_add]
  refine c.step (j := 3) (hK.nx rfl rfl rfl) (by decide) hrip₁ fun M₁ _ hc₁ hK₁ htf₁ _ =>
    ⟨_, _, i3 hc₁ hrip₁ htf₁, ?_⟩
  refine c.step (j := 6) (hK₁.nx rfl rfl rfl) (by decide) (by show (s₀.cpu.rip.add 3).add 3 = _; rw [hrip,
    addr_add_add, addr_add_add]) fun M₂ _ hc₂ hK₂ htf₂ _ => ?_
  obtain ⟨v, fl, hr, hv, htf', hac', hdf'⟩ := i6 (o := o) (t := t + 1 + 1 + 1) hc₂ (by
    show (s₀.cpu.rip.add 3).add 3 = _; rw [hrip, addr_add_add, addr_add_add]) htf₂
  refine ⟨_, _, hr, c.loop _ 0 _ _ rfl ⟨hK₂.nx htf' hac' hdf', ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
    hv, Nat.zero_le _, by simp [readBytes, byteAddrs]⟩ ?_⟩
  show ((s₀.cpu.rip.add 3).add 3).add 2 = _
  rw [hrip, addr_add_add, addr_add_add, addr_add_add]

end Call

/-- `memcmp`, compiled by GCC with `-Os`, meets the C standard's contract (Zellic's release challenge
`memcmp_gcc_os`). -/
theorem gccOs_holds : Memcmp.holds Memcmp.gccOs := by
  intro L prof e hin s₀ ra hcall
  exact reachOrEndsIn_of_runsFrom fun o ho t => (Call.mk hcall hin ho).entry

end FV7z.MemcmpGccOs
