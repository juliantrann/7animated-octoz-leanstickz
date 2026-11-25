import FV7z.Strlen.Steps
import FV7z.Lemmas.Sse2b
/-!
# `bsr r64, q64` (PLAN.md G2, `__strrchr_sse2`)

`__strrchr_sse2` ends with `bsr` of a 64-bit mask, the place of the last match: with a source not 0, the index of its
highest set bit, a step of its own (with a source 0 the destination is not said).
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile}

theorem bsr64_rr {s : State} {o : Oracle} {t r q len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.bit .bsr) 64 [gr 64 r, gr 64 q] len))
    (hx : rv s 64 q ≠ 0) :
    ∃ fl t', (instruction prof s).runStream o t = (.running (nx s len (s.cpu.gpr.set (regOf r)
      (BitVec.ofNat 64 (highestSetBit (rv s 64 q)))) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨?_, ?_, instruction_next htf hdec ?_, ?_, ?_, ?_⟩
  case refine_3 =>
    have hx' : ((advance s len).cpu.gpr.get (regOf q)).setWidth 64 ≠ 0 := hx
    simp only [exec, execBits, Sem.bsr, bitScan, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      pure, Prog.readReg, Prog.run, writeOp]
    simp only [hx', ↓reduceIte]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `bsr r64, q` of `q` not 0. -/
theorem s_bsr64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {r q len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.bit .bsr) 64 [gr 64 r, gr 64 q] len)) (hx : rv X 64 q ≠ 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = X.cpu.gpr.set (regOf r) (BitVec.ofNat 64 (highestSetBit (rv X 64 q)))) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := bsr64_rr (s := X.withMem M) (o := o) (t := t + 1) (r := r) (q := q) htf
      (c.dec hK' hin hrip hd) hx
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
