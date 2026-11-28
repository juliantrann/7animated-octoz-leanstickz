import FV7z.Lemmas.Lock2
/-!
# `sub dword [b + d], imm` with its flags (PLAN.md §M, M1)

`CLocalProgress::Init` drops a reference count with `sub dword [r + 8], 1` and branches on `ZF`: `Lock2.lean`'s
`sub_mi32` keeps the flags hidden. `sub_mi32f`, `Seg.s_sub_mi32f`: the same, the flags those of `cmp` of the word with
the immediate (`subF`, as `Op.cmpmi`).
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `sub dword [b + d], imm`: a read-modify-write, the flags `subF` of the word and the immediate. -/
theorem sub_mi32f {b d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub 32 [.mem (mbd b d 32), .imm 32 v] len))
    (hwr : Writable prof s (eaD s b d) 4) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d)
          (toBytesLE (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4) - BitVec.ofNat 32 v) 4)) len s.cpu.gpr fl)
          none, t') ∧
      fl = subF (rfz s.cpu.rflags) (ofBytesLE 32 (readBytes s.proc.mm.mem (eaD s b d) 4)) (BitVec.ofNat 32 v) ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 4) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?hz, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.sub, alu, subOp, mk, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
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

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `sub dword [b + d], imm` on a word the run may store into, the flags `subF` of the word and the immediate. -/
theorem s_sub_mi32f (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 32 [.mem (mbd b d 32), .imm 32 v] len))
    (hst : ∀ i < 4, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) - BitVec.ofNat 32 v) 4))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
        Y.cpu.rflags = subF (rfz X.cpu.rflags) (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V)) (BitVec.ofNat 32 v)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 32 ((byteAddrs (eaD X b d) 4).map V) - BitVec.ofNat 32 v) 4) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨fl, t', hr, hz, h1, h2, h3⟩ := sub_mi32f (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr hz
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl, hz⟩) k'

end FV7z.Fn.Seg
