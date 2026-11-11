import FV7z.Lemmas.Lock
/-!
# Read-modify-writes of a word at a fixed address (PLAN.md G3, startup)

The lock of `__register_atfork` in a process with one thread (`lll_lock`, `lll_unlock` with `SINGLE_THREAD_P`): the
instructions without the `lock` prefix, on a word of `.bss`.

- `cmpxchg_rip32`, `Seg.s_cmpxchg_rip32`: `cmpxchg dword [rip + d], r32` where the word is `eax`: it becomes the
  register, `ZF` is set.
- `sub_rip32`, `Seg.s_sub_rip32`: `sub dword [rip + d], imm`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `cmpxchg dword [rip + d], r32`, the word being `eax`. -/
theorem cmpxchg_rip32 {d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cmpxchg 32 [.mem (mrip d 32), gr 32 r] len))
    (hwr : Writable prof s (eaR s len d) 4)
    (hold : ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) = rv s 32 0) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d) (toBytesLE (rv s 32 r) 4)) len s.cpu.gpr fl) none, t') ∧
      fl.zf = true ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 4) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3, ?h4⟩
  case h =>
    simp only [exec, Sem.cmpxchg, accOf, subOp, mk, mrip, gr, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readRip, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp,
      Prog.readFlags, Prog.writeFlags, BitVec.mul_one, done]
    rw [eaR_adv]
    have hold' : ofBytesLE 32 (readBytes (advance s len).proc.mm.mem (eaR s len d) 4) =
        BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf 0)) := hold
    simp only [↓reduceIte, Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc, hold']
    rfl
  case h1 =>
    simp
  all_goals rfl

/-- `sub dword [rip + d], imm`. -/
theorem sub_rip32 {d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub 32 [.mem (mrip d 32), .imm 32 v] len))
    (hwr : Writable prof s (eaR s len d) 4) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d)
          (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaR s len d) 4) - BitVec.ofNat 32 v) 4)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 4) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.sub, alu, subOp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      Prog.writeFlags, BitVec.mul_one, done]
    rw [eaR_adv]
    have z : BitVec.setWidth 32 (BitVec.ofBool false) = 0#32 := rfl
    simp only [Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc, z, BitVec.sub_zero]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `cmpxchg dword [rip + d], r32` on a word the run may store into that is `eax`: the word becomes the register. -/
theorem s_cmpxchg_rip32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmpxchg 32 [.mem (mrip d 32), gr 32 r] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g)
    (hst : ∀ i < 4, Foot Wl (g.add i)) (hold : ofBytesLE 32 ((byteAddrs g 4).map V) = rv X 32 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V g (toBytesLE (rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.rflags.zf = true) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 32 r) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, hz, h1, h2, h3⟩ := cmpxchg_rip32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) hwr (by rw [he, hv]; exact hold)
    rw [he] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl, hz⟩) k'

/-- `sub dword [rip + d], imm` on a word the run may store into. -/
theorem s_sub_rip32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 32 [.mem (mrip d 32), .imm 32 v] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 4, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V g (toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) - BitVec.ofNat 32 v) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs g 4).map V) - BitVec.ofNat 32 v) 4) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := sub_rip32 (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
