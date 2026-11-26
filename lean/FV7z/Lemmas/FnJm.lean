import FV7z.Lemmas.CallM
/-!
# `jmp qword [b + d]` (PLAN.md §M, M1)

7-Zip's COM forwarders end in a tail call through a vtable: `mov rax, [rdi]; jmp qword [rax + d]`
(`CArchiveExtractCallback::SetRatioInfo`). `jmp_m` is the instruction on Zellic's model (as `jmp_mrip` with a base
register), `Seg.s_jmp_mx` the step of a run: to the address read, the registers kept.
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `jmp qword [b + d]`: to the address read. -/
theorem jmp_m {b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .jmp 64 [.mem (mbd b d 64)] len))
    (hld : Readable prof s (eaD s b d) 8)
    (hcan : Addr.canonical prof.feat.la57 (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)) = true) :
    (instruction prof s).runStream o t =
      (.running (upd s (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)) s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.jmp, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, memRef, effOffset,
    pure, Prog.readRip, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, jumpTo]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rw [show (advance s len).proc.mm.mem = s.proc.mm.mem from rfl, hcan]
  simp only [↓reduceIte, Prog.writeRip, done, Prog.run, Prog.bind, pure]
  rfl

end

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
  {t j : Nat} {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `jmp qword [b + d]` to the `tgt`-th byte of a segment, the 8 bytes read from the footprint's data. -/
theorem s_jmp_mx (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .jmp 64 [.mem (mbd b d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaD X b d).add i))
    {e₂ : Addr} {code₂ : List Byte} {tgt : Nat} (hin₂ : CodeIn L e₂ code₂) (ht : tgt < code₂.length)
    (htgt : ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) = e₂.add tgt)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add tgt ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have hca := ((c.codeAt hK' hin₂) tgt ht).1
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hT : ofBytesLE 64 (readBytes (X.withMem M).proc.mm.mem (eaD (X.withMem M) b d) 8) = e₂.add tgt :=
      (congrArg (ofBytesLE 64) hv).trans htgt
    have hr := jmp_m (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd) hrd
      (by rw [hT]; exact hca)
    rw [hT] at hr
    exact ⟨_, _, hr, hK'.upd rfl rfl rfl, hA', rfl, rfl⟩) k'

end FV7z.Fn.Seg
