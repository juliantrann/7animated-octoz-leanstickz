import FV7z.Lemmas.Xmm3
import FV7z.Lemmas.BlkOps2
/-!
# Non-temporal stores, prefetches and fences (PLAN.md M, `__memmove_sse2_unaligned`)

Above the non-temporal threshold the copy stores with `movntdq xmmword [b + d], xmmN`, hints `prefetcht0` ahead
of its loads and ends with `sfence`. In the model `movntdq` is an aligned move like `movaps`, and a prefetch or a
fence changes no register or byte.

- `movntdq_st`, `Seg.s_movntdq_stv`: as `movaps_st`, `Seg.s_movaps_stv` (`Lemmas/Xmm3.lean`).
- `OpI.prefetch`, `OpI.sfence`: as `OpI.endbr`, steps of a block that change nothing.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `movntdq xmmword [b + d], xmmN`, the address a multiple of 16. -/
theorem movntdq_st {n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movntdq) 16 [.mem (mbd b d 128), .xmm n] len))
    (hal : (eaD s b d).toNat % 16 = 0) (hwr : Writable prof s (eaD s b d) 16) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaD s b d) (toBytesLE ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 16)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movntdq, moveAligned, aligned16, Prog.alignedTo, mbd, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, BitVec.mul_one,
    writeOp, Prog.readZmm, eaD_adv, hal, true_or]
  rw [checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- `prefetchh [m]`: a hint, nothing changed. -/
theorem OpI.prefetch {h len : Nat} {m : MemOp} : OpI prof (mk (.prefetch h) 32 [.mem m] len) Op.nop :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

/-- `sfence`: an ordering of stores, nothing changed. -/
theorem OpI.sfence {len : Nat} : OpI prof (mk .sfence 32 [] len) Op.nop :=
  fun _ _ _ htf hdec => ⟨_, _, instruction_next htf hdec rfl, rfl, rfl, rfl, rfl⟩

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `movntdq xmmword [b + d], xmmN`, at a multiple of 16, into bytes the run may store into; the vector registers
are kept. -/
theorem s_movntdq_stv (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movntdq) 16 [.mem (mbd b d 128), .xmm n] len))
    (hal : (eaD X b d).toNat % 16 = 0) (hst : ∀ i < 16, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movntdq_st (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hal hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

end FV7z.Fn.Seg
