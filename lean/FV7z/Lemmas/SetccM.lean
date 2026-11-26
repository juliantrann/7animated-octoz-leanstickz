import FV7z.Lemmas.BlkOps4
/-!
# `setcc byte [b + d]` (PLAN.md §M, M1)

7-Zip's `CDecoder::SetOutStreamSizeResume` stores a flag with `setne byte [rdi + 0x46]`. The `Op`s of `Blk.lean` store
bytes of the registers only, not of the flags, so the instruction is a step of its own (`hand` in
`tools/blk_gen.py`), as `Seg.s_movups_st` (`FV7z/Lemmas/BlkOps4.lean`).

- `setcc_m8`: the instruction; `Seg.s_setcc_m8`: the step, the registers kept and the flags with `RF` cleared.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `setcc byte [b + d]`: the byte 1 if the condition holds, else 0. -/
theorem setcc_m8 {c : Cond} {b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.setcc c) 8 [.mem (mbd b d 8)] len))
    (hwr : Writable prof s (eaD s b d) 1) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaD s b d) (toBytesLE ((BitVec.ofBool (s.cpu.rflags.cond c)).setWidth 8) 1)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.setcc, mbd, bind, Prog.bind, Bool.false_eq_true, ↓reduceIte, memRef,
    effOffset, pure, Prog.readReg, Prog.readFlags, Prog.write, Prog.run, BitVec.mul_one, writeOp]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `setcc byte [b + d]`, into a byte the run may store into. -/
theorem s_setcc_m8 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {cc : Cond} {b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.setcc cc) 8 [.mem (mbd b d 8)] len))
    (hst : ∀ i < 1, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE ((BitVec.ofBool (X.cpu.rflags.cond cc)).setWidth 8) 1))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.rflags = rf0 X) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE ((BitVec.ofBool (X.cpu.rflags.cond cc)).setWidth 8) 1) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, setcc_m8 (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

end FV7z.Fn.Seg
