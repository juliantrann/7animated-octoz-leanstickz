import FV7z.Lemmas.Lock2
/-!
# `cmpxchg` on a word a register points to, not locked (PLAN.md G3, `malloc`)

`tcache_init` takes the arena's lock with one thread (`fs:0x18` is 0) by an unlocked `cmpxchg [rbp], edx`
(`__libc_lock_lock` of glibc 2.31 for one thread).

- `cmpxchg_bd32`, `Seg.s_cmpxchg_bd32`: `cmpxchg dword [b + d], r32` where the word is `eax`: it becomes the
  register, `ZF` is set.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `cmpxchg dword [b + d], r32`, not locked, the word being `eax`. -/
theorem cmpxchg_bd32 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .cmpxchg 32 [.mem (mbd b d 32), gr 32 r] len))
    (hwr : Writable prof s (eaD s b d) 4)
    (hold : ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4) = rv s 32 0) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d) (toBytesLE (rv s 32 r) 4)) len s.cpu.gpr fl) none, t') ∧
      fl.zf = true ∧ fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3, ?h4⟩
  case h =>
    simp only [exec, Sem.cmpxchg, accOf, subOp, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp,
      Prog.readFlags, Prog.writeFlags, BitVec.mul_one, done]
    rw [eaD_adv]
    have hold' : ofBytesLE 32 (readBytes (advance s len).proc.mm.mem (eaD s b d) 4) =
        BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf 0)) := hold
    simp only [↓reduceIte, Nat.reduceDiv, hc, hold']
    rfl
  case h1 =>
    simp
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `cmpxchg dword [b + d], r32`, not locked, on a word the run may store into that is `eax`: the word becomes the
register. -/
theorem s_cmpxchg_bd32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .cmpxchg 32 [.mem (mbd b d 32), gr 32 r] len))
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
    obtain ⟨fl, t', hr, hz, h1, h2, h3⟩ := cmpxchg_bd32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) hwr (by
        rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv]; exact hold)
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl, hz⟩) k'

end FV7z.Fn.Seg
