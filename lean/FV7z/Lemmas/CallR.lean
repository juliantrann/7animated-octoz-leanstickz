import FV7z.Lemmas.CallM
import FV7z.Lemmas.InsRip
/-!
# `call qword [rip + d]` (PLAN.md G3, `malloc`)

`sysmalloc` calls `__morecore` through its pointer (`call *0x162bf4(%rip)`, the word at `0x7932d8`).
`call_rip` is the instruction on Zellic's model, `Seg.s_callR` the step of a run: the target is read from the
footprint's data at the address after the instruction plus `d`.
-/
namespace FV7z
open ZellicX86 Decode

section
variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `call qword [rip + d]`: the target is read, then the return address pushed. -/
theorem call_rip {d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .call 64 [.mem (mrip d 64)] len))
    (hsh : s.thread.shstk = none) (hld : Readable prof s (eaR s len d) 8)
    (hcan : Addr.canonical prof.feat.la57 (ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8)) = true)
    (hw : Writable prof s (s.cpu.gpr.rsp - 8) 8) :
    (instruction prof s).runStream o t = (.running (upd (st s (s.cpu.gpr.rsp - 8) (toBytesLE (s.cpu.rip.add len) 8))
      (ofBytesLE 64 (readBytes s.proc.mm.mem (eaR s len d) 8)) (s.cpu.gpr.set 4 (s.cpu.gpr.rsp - 8)) (rf0 s)) none,
      t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.call, push64, mrip, Prog.run, bind, Prog.bind, Prog.readThread, Prog.readRip, Prog.readReg,
    Prog.write, Prog.writeReg, Prog.writeRip, pure, show (advance s len).thread.shstk = none from hsh,
    Bool.false_eq_true, ↓reduceIte, done, readOp, memRef, effOffset, Prog.read, BitVec.mul_one]
  rw [eaR_adv, checkAccess_ok (s := advance s len) hac hld]
  rw [show (advance s len).proc.mm.mem = s.proc.mm.mem from rfl, hcan]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Prog.run, bind, pure]
  rw [checkAccess_ok (s := advance s len) hac hw]
  rfl

end

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t j : Nat}
  {e' : Addr} {code : List Byte} {V : Addr → Byte}

/-- `call qword [rip + d]` to a segment's first byte, the target read from the footprint's data, pushing into bytes
the run may store into. -/
theorem s_callR (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .call 64 [.mem (mrip d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((e'.add (j + len) + BitVec.ofNat 64 d).add i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (htgt : ofBytesLE 64 ((byteAddrs (e'.add (j + len) + BitVec.ofNat 64 d) 8).map V) = e₂)
    (hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (e'.add (j + len)) 8))
      fun Y => Y.cpu.rip = e₂ ∧ Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp - 8)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have hra : (X.withMem M).cpu.rip.add len = e'.add (j + len) := rip_add hrip M len
    have hea : eaR (X.withMem M) len d = e'.add (j + len) + BitVec.ofNat 64 d := by
      show (X.withMem M).cpu.rip.add len + _ = _
      rw [hra]
    have hca := ((c.codeAt hK' hin₂) 0 h₂).1
    rw [addr_add_zero] at hca
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    rw [← hea] at hrd hv
    have hT : ofBytesLE 64 (readBytes (X.withMem M).proc.mm.mem (eaR (X.withMem M) len d) 8) = e₂ := by
      rw [hv, hea]
      exact htgt
    obtain ⟨hw, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (e'.add (j + len)) 8) (a := X.cpu.gpr.rsp - 8) (by simpa using hst)
    rw [toBytesLE_length] at hw
    have hr := call_rip (s := X.withMem M) (o := o) (t := t + 1) htf hac (c.dec hK' hin hrip hd)
      (by rw [hK'.thread]; exact c.ready.plain.2.2.1) hrd (by rw [hT]; exact hca) hw
    rw [hra, hT] at hr
    exact ⟨_, _, hr, hKs.upd rfl rfl rfl, hAs, rfl, rfl⟩) k'

end FV7z.Fn.Seg
