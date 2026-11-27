import FV7z.Lemmas.Lock2
/-!
# `sub dword [b + d], r32` (PLAN.md §M, M1)

A read-modify-write of a word with a register: 7-Zip's `UString::Delete` takes `count` from `_len`
(`sub [rbp + 8], ebx`).

- `sub_mr32`: the instruction's step; `Seg.s_sub_mr32`: on a word the run may store into.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {s : State} {o : Oracle} {t : Nat}

/-- `sub dword [b + d], r32`: a read-modify-write. -/
theorem sub_mr32 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub 32 [.mem (mbd b d 32), gr 32 r] len))
    (hwr : Writable prof s (eaD s b d) 4) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d)
          (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4) - rv s 32 r) 4)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.sub, alu, subOp, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      Prog.writeFlags, BitVec.mul_one, done]
    rw [eaD_adv]
    have z : BitVec.setWidth 32 (BitVec.ofBool false) = 0#32 := rfl
    simp only [Nat.reduceDiv, hc, z, BitVec.sub_zero]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ X : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte} {t : Nat} {e' : Addr} {code : List Byte} {j : Nat}

/-- `sub dword [b + d], r32` on a word the run may store into. -/
theorem s_sub_mr32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 32 [.mem (mbd b d 32), gr 32 r] len))
    (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) - rv X 32 r) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) - rv X 32 r) 4) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := sub_mr32 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, show rv (X.withMem M) 32 r = rv X 32 r from rfl,
      hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
