import FV7z.Lemmas.Xmm2
/-!
# An aligned store of an `xmm` register (PLAN.md G3, malloc)

`movaps xmmword [b + d], xmmN`, the instruction of `ptmalloc_init`'s loop over the bins of `main_arena` (measured with
`tools/blk_gen.py`): a general-protection fault unless the address is a multiple of 16.

- `movaps_st`: the instruction at an address that is; `Seg.s_movaps_stv`: as a step of a run, into bytes the run may
  store into, the vector registers kept.
- `Seg.runB`: a stretch of the general registers' code between such moves, the vector registers kept.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `movaps xmmword [b + d], xmmN`, the address a multiple of 16. -/
theorem movaps_st {n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movaps) 32 [.mem (mbd b d 128), .xmm n] len))
    (hal : (eaD s b d).toNat % 16 = 0) (hwr : Writable prof s (eaD s b d) 16) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaD s b d) (toBytesLE ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 16)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movaps, moveAligned, aligned16, Prog.alignedTo, mbd, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, BitVec.mul_one,
    writeOp, Prog.readZmm, eaD_adv, hal, true_or]
  rw [checkAccess_ok (s := advance s len) hac hwr]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `movaps xmmword [b + d], xmmN`, at a multiple of 16, into bytes the run may store into; the vector registers are
kept. -/
theorem s_movaps_stv (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movaps) 32 [.mem (mbd b d 128), .xmm n] len))
    (hal : (eaD X b d).toNat % 16 = 0) (hst : ∀ i < 16, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movaps_st (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hal hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

end FV7z.Fn.Seg

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- A stretch of straight-line code between moves of an `xmm` register: from what holds after it (`Q`), with the
vector registers kept. -/
theorem runB (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j j' : Nat} {ops : List Op}
    (hb : Blk prof code j j' ops) (hkv : ops.all Op.kv = true) (Q : Gprs → Rflags → (Addr → Byte) → Prop)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add j)
    (vc : wp F Wl ops Q X.cpu.gpr X.cpu.rflags V)
    (k : ∀ g fl V', Q g fl V' → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
      Y.cpu.gpr = g → Y.cpu.vec = X.cpu.vec → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t :=
  c.s_blkA_v hin (hb.at e') X.cpu.vec hK hA hrip rfl hkv
    (wp_mono ops (fun g fl V' hq Y t' hKY hAY hrY hg _ hv => k g fl V' hq Y t' hKY hAY hrY hg hv) vc)

end FV7z.Fn.Seg
