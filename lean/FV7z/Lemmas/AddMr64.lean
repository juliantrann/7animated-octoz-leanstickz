import FV7z.Lemmas.FnMem
/-!
# `add qword [b + d], r64` (PLAN.md §M, M1)

A read-modify-write of a quadword with a register: 7-Zip's `CDummyOutStream::Write` adds the processed size to
`_size` (`add [rbx + 0x18], rcx`), `ReadStream` to `*processedSize` (`add [r14], rdx`). As `add_mr32`
(`InsMem.lean`) and `Seg.s_add_mr32` (`FnMem.lean`) on 8 bytes.

- `add_mr64`: the instruction's step; `Seg.s_add_mr64`: on a quadword the run may store into.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {s : State} {o : Oracle} {t : Nat}

/-- `add qword [b + d], r64`: a read-modify-write. -/
theorem add_mr64 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .add 64 [.mem (mbd b d 64), gr 64 r] len))
    (hwr : Writable prof s (eaD s b d) 8) :
    (instruction prof s).runStream o t = (.running (nx (st s (eaD s b d)
      (toBytesLE (addR (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)) (rv s 64 r)) 8)) len s.cpu.gpr
      (addF (rf0 s) (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)) (rv s 64 r))) none, t) := by
  refine instruction_next htf hdec ?_
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 8) hac hwr
  have hp : ∀ {α : Type} (x : α), Req.runStream o (pure x : Req α) t = (x, t) := fun _ => rfl
  simp only [exec, Sem.add, alu, addOp, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr, Req.runStream_bind]
  simp only [hp, Prog.run, Prog.readFlags, Prog.write, Prog.writeFlags, Prog.bind, Nat.reduceDiv]
  simp only [Prog.bind, Prog.run, Req.runStream, bind, pure]
  simp only [Prog.run, eaD_adv, Nat.reduceDiv]
  rw [hc]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ X : State}
  {o : Oracle} {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V : Addr → Byte} {t : Nat} {e' : Addr} {code : List Byte} {j : Nat}

/-- `add qword [b + d], r64` on a quadword the run may store into. -/
theorem s_add_mr64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .add 64 [.mem (mbd b d 64), gr 64 r] len))
    (hst : ∀ i < 8, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) + rv X 64 r) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) + rv X 64 r) 8) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    have hr := add_mr64 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf hac (c.dec hK' hin hrip hd) hwr
    simp only [withMem_cpu, addR_eq] at hr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
