import FV7z.Lemmas.Rmw2
/-!
# `add qword [rip + d], imm` (PLAN.md G3, startup)

The counter `__new_exitfn_called` of `__new_exitfn`: `add_rip64`, `Seg.s_add_rip64`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `add qword [rip + d], imm`. -/
theorem add_rip64 {d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 64 [.mem (mrip d 64), .imm 64 v] len))
    (hwr : Writable prof s (eaR s len d) 8) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d)
          (toBytesLE (ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8) + BitVec.ofNat 64 v) 8)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 8) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.add, alu, addOp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      Prog.writeFlags, BitVec.mul_one, done]
    rw [eaR_adv]
    have z : BitVec.setWidth 64 (BitVec.ofBool false) = 0#64 := rfl
    simp only [Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc, z, BitVec.add_zero]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `add qword [rip + d], imm` on a quadword the run may store into. -/
theorem s_add_rip64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 64 [.mem (mrip d 64), .imm 64 v] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 8, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V g (toBytesLE (ofBytesLE 64 ((byteAddrs g 8).map V) + BitVec.ofNat 64 v) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs g 8).map V) + BitVec.ofNat 64 v) 8) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := add_rip64 (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
