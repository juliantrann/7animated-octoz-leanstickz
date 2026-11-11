import FV7z.Lemmas.Rmw2
import FV7z.Lemmas.InsMem
/-!
# Read-modify-writes of a word a register points to (PLAN.md G3, pthread)

The instructions of `pthread_mutex_lock`'s and `pthread_mutex_unlock`'s plain paths on the mutex `rdi` points to
(measured with `tools/blk_gen.py`).

- `lockCmpxchgB32`, `lock_cmpxchg_bd32`, `Seg.s_lock_cmpxchg_bd32`: `lock cmpxchg dword [b + d], r32` where the word
  is `eax`: it becomes the register, `ZF` is set. As in `Lemmas/Lock.lean`, the word within one cache line.
- `add_mi32`, `Seg.s_add_mi32`: `add dword [b + d], imm`; `sub_mi32`, `Seg.s_sub_mi32`: `sub dword [b + d], imm`.
- `xchg_bd32`, `Seg.s_xchg_bd32`: `xchg dword [b + d], r32`, the word within one cache line.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `lock cmpxchg dword [b + d], r32` as the decoder gives it. -/
abbrev lockCmpxchgB32 (b d r len : Nat) : Inst :=
  { mn := .cmpxchg, opsz := 32, len, rep := none, lock := true, mask := none, zero := false, fop := 0,
    ops := [.mem (mbd b d 32), .reg ⟨32, r, false⟩] }

/-- `lock cmpxchg dword [b + d], r32`, the word being `eax`. -/
theorem lock_cmpxchg_bd32 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (lockCmpxchgB32 b d r len))
    (hsl : (eaD s b d).toNat % 64 + 4 ≤ 64) (hwr : Writable prof s (eaD s b d) 4)
    (hold : ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4) = rv s 32 0) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d) (toBytesLE (rv s 32 r) 4)) len s.cpu.gpr fl) none, t') ∧
      fl.zf = true ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  have hns : ¬ ((eaD s b d).toNat % 64 + 32 / 8 > 64 ∧ prof.linux.splitLock ≠ .atomic) := by
    intro h; have := h.1; omega
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3, ?h4⟩
  case h =>
    simp only [exec, execLocked, Sem.cmpxchg, accOf, subOp, mbd, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.run, writeOp,
      Prog.readFlags, Prog.writeFlags, Prog.lockedRmw, BitVec.mul_one, done]
    rw [eaD_adv]
    have hold' : ofBytesLE 32 (readBytes (advance s len).proc.mm.mem (eaD s b d) 4) =
        BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf 0)) := hold
    simp only [hns, ↓reduceIte, Nat.reduceDiv, hc, hold']
    rfl
  case h1 =>
    simp
  all_goals rfl

/-- `add dword [b + d], imm`: a read-modify-write. -/
theorem add_mi32 {b d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 32 [.mem (mbd b d 32), .imm 32 v] len))
    (hwr : Writable prof s (eaD s b d) 4) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d)
          (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4) + BitVec.ofNat 32 v) 4)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.add, alu, addOp, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      Prog.writeFlags, BitVec.mul_one, done]
    rw [eaD_adv]
    have z : BitVec.setWidth 32 (BitVec.ofBool false) = 0#32 := rfl
    simp only [Nat.reduceDiv, hc, z, BitVec.add_zero]
    rfl
  all_goals rfl

/-- `sub dword [b + d], imm`: a read-modify-write. -/
theorem sub_mi32 {b d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub 32 [.mem (mbd b d 32), .imm 32 v] len))
    (hwr : Writable prof s (eaD s b d) 4) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d)
          (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4) - BitVec.ofNat 32 v) 4)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.sub, alu, subOp, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      Prog.writeFlags, BitVec.mul_one, done]
    rw [eaD_adv]
    have z : BitVec.setWidth 32 (BitVec.ofBool false) = 0#32 := rfl
    simp only [Nat.reduceDiv, hc, z, BitVec.sub_zero]
    rfl
  all_goals rfl

/-- `xchg dword [b + d], r32`: locked whether or not it has the prefix. -/
theorem xchg_bd32 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .xchg 32 [.mem (mbd b d 32), gr 32 r] len))
    (hsl : (eaD s b d).toNat % 64 + 4 ≤ 64) (hwr : Writable prof s (eaD s b d) 4) :
    ∃ t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d) (toBytesLE (rv s 32 r) 4)) len
          (s.cpu.gpr.set (regOf r) ((ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4)).setWidth 64)) (rf0 s))
          none, t') := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  have hns : ¬ ((eaD s b d).toNat % 64 + 32 / 8 > 64 ∧ prof.linux.splitLock ≠ .atomic) := by
    intro h; have := h.1; omega
  refine ⟨?t', instruction_next htf hdec ?h⟩
  case h =>
    simp only [exec, Sem.xchg, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.run, writeOp,
      Prog.lockedRmw, BitVec.mul_one, done]
    rw [eaD_adv]
    simp only [hns, ↓reduceIte, Nat.reduceDiv, hc]
    rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `lock cmpxchg dword [b + d], r32` on a word the run may store into that is `eax`: the lock is taken. -/
theorem s_lock_cmpxchg_bd32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (lockCmpxchgB32 b d r len)) (hsl : (eaD X b d).toNat % 64 + 4 ≤ 64)
    (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (hold : ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) = rv X 32 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.rflags.zf = true) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 32 r) 4) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨fl, t', hr, hz, h1, h2, h3⟩ := lock_cmpxchg_bd32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) hsl hwr (by
        rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv]; exact hold)
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl, hz⟩) k'

/-- `add dword [b + d], imm` on a word the run may store into. -/
theorem s_add_mi32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 32 [.mem (mbd b d 32), .imm 32 v] len))
    (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) + BitVec.ofNat 32 v) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) + BitVec.ofNat 32 v) 4) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := add_mi32 (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

/-- `sub dword [b + d], imm` on a word the run may store into. -/
theorem s_sub_mi32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 32 [.mem (mbd b d 32), .imm 32 v] len))
    (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) - BitVec.ofNat 32 v) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) - BitVec.ofNat 32 v) 4) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := sub_mi32 (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

/-- `xchg dword [b + d], r32` on a word the run may store into: the word becomes the register, the register the
word. -/
theorem s_xchg_bd32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .xchg 32 [.mem (mbd b d 32), gr 32 r] len))
    (hsl : (eaD X b d).toNat % 64 + 4 ≤ 64) (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧
        Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 32 r) 4) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨t', hr⟩ := xchg_bd32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) hsl hwr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
