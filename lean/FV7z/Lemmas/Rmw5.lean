import FV7z.Lemmas.Rmw4
/-!
# `or qword [b + i + d], imm` (PLAN.md G3, startup)

The stack probe after an `alloca` of `_dl_important_hwcaps` (`or qword [rsp + rax - 8], 0`, GCC's
`-fstack-clash-protection`): `or_mi64i`, `Seg.s_or_mi64i`, as `Rmw4.lean`'s with an index.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `or qword [b + i + d], imm`. -/
theorem or_mi64i {b ix d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .or 64 [.mem (mbi b ix d 64), .imm 64 v] len))
    (hwr : Writable prof s (eaI s b ix d) 8) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaI s b ix d)
          (toBytesLE (ofBytesLE 64 (readBytes s.proc.mm.mem (eaI s b ix d) 8) ||| BitVec.ofNat 64 v) 8)) len
          s.cpu.gpr fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.or, alu, logicOp, mk, mbi, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      BitVec.mul_one]
    rw [checkAccess_ok (s := advance s len) hac hwr]
    simp only [Prog.undefinedBit, Prog.undefined, bind, pure, Prog.bind, Prog.run, Req.bind, Prog.writeFlags, done]
    have hc := checkAccess_ok (feat := prof.feat) (s := advance s len)
      (m := ⟨eaI s b ix d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 8)
      hac hwr
    simp only [Nat.reduceDiv, hc]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `or qword [b + i + d], imm`, bytes the run may store into. -/
theorem s_or_mi64i (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b ix d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .or 64 [.mem (mbi b ix d 64), .imm 64 v] len))
    (hst : ∀ i < 8, Foot Wl ((eaI X b ix d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaI X b ix d) (toBytesLE (ofBytesLE 64 ((byteAddrs (eaI X b ix d) 8).map V) ||| BitVec.ofNat 64 v) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs (eaI X b ix d) 8).map V) ||| BitVec.ofNat 64 v) 8) (a := eaI X b ix d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := eaI X b ix d) (n := 8)
      fun i hi => c.hws _ (hst i hi)
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := or_mi64i (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf hac
      (c.dec hK' hin hrip hd) hwr
    refine ⟨_, _, hr, ?_, ?_, rip_add hrip M len, rfl⟩
    · rw [show readBytes (X.withMem M).proc.mm.mem (eaI (X.withMem M) b ix d) 8 = _ from hv]
      exact hKs.nx h1 h2 h3
    · rw [show readBytes (X.withMem M).proc.mm.mem (eaI (X.withMem M) b ix d) 8 = _ from hv]
      exact hAs) k'

end FV7z.Fn.Seg
