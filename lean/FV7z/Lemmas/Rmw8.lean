import FV7z.Lemmas.Lock2
/-!
# `sub qword [b + d], imm` (PLAN.md §M, M1)

`SortFileNames`'s heap build steps a counter it keeps on the stack (`sub qword [rsp + 0x20], 2`).

- `sub_mi64`, `Seg.s_sub_mi64`: as `Lock2.lean`'s `sub_mi32`, `Seg.s_sub_mi32`, for a quadword (the immediate
  sign-extended by the decoder: `.imm 64 v`).
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `sub qword [b + d], imm`. -/
theorem sub_mi64 {b d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub 64 [.mem (mbd b d 64), .imm 64 v] len))
    (hwr : Writable prof s (eaD s b d) 8) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d)
          (toBytesLE (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8) - BitVec.ofNat 64 v) 8)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 8) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.sub, alu, subOp, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      Prog.writeFlags, BitVec.mul_one, done]
    rw [eaD_adv]
    have z : BitVec.setWidth 64 (BitVec.ofBool false) = 0#64 := rfl
    simp only [Nat.reduceDiv, hc, z, BitVec.sub_zero]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `sub qword [b + d], imm` on a quadword the run may store into. -/
theorem s_sub_mi64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 64 [.mem (mbd b d 64), .imm 64 v] len))
    (hst : ∀ i < 8, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) - BitVec.ofNat 64 v) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) - BitVec.ofNat 64 v) 8) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := sub_mi64 (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
