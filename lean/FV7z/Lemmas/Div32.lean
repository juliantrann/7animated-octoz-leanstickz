import FV7z.Lemmas.BlkOps4
/-!
# 32-bit `div` (PLAN.md §M, M1)

`div r32` as `find_module_idx` has it (`div ebx`, `div esi`: `hval % hash_size` and `hval % (hash_size - 2)`):
`edx:eax` divided by the register, the quotient in `eax` and the remainder in `edx`, both zero-extended.

- `div32`: with `edx` 0 and a divisor not 0 the quotient fits, so the instruction does not fault.
- `Seg.s_div32`: the step, as `Seg.s_div64`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `div r32` with `rdx` 0 and a divisor not 0. -/
theorem div32 {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .div 32 [gr 32 r] len))
    (h0 : s.cpu.gpr.rdx = 0) (hne : rv s 32 r ≠ 0) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx s len ((s.cpu.gpr.set (regOf 0)
          ((BitVec.ofNat 32 ((rv s 32 0).toNat / (rv s 32 r).toNat)).setWidth 64)).set (regOf 2)
          ((BitVec.ofNat 32 ((rv s 32 0).toNat % (rv s 32 r).toNat)).setWidth 64)) fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  suffices h : ∃ fl t', ((exec prof (mk .div 32 [gr 32 r] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len ((s.cpu.gpr.set (regOf 0)
          ((BitVec.ofNat 32 ((rv s 32 0).toNat / (rv s 32 r).toNat)).setWidth 64)).set (regOf 2)
          ((BitVec.ofNat 32 ((rv s 32 0).toNat % (rv s 32 r).toNat)).setWidth 64)) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, h1, h2, h3⟩
  simp only [exec, Sem.div, dividend, divResult, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, accOf, Nat.reduceEqDiff, true_or]
  have e2 : BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf 2)) = 0 := by
    show BitVec.setWidth 32 s.cpu.gpr.rdx = 0
    rw [h0]
    rfl
  have e0 : BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf 0)) = rv s 32 0 := rfl
  have er : BitVec.setWidth 32 ((advance s len).cpu.gpr.get (regOf r)) = rv s 32 r := rfl
  have hn : (BitVec.setWidth (2 * 32) ((0 : BitVec 32) ++ rv s 32 0)).toNat = (rv s 32 0).toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_append]
    simp <;> omega
  have hlt : (rv s 32 0).toNat / (rv s 32 r).toNat < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (rv s 32 0).isLt
  rw [e2, e0, er, hn]
  simp only [hne, Nat.not_le.2 hlt, ↓reduceIte]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `div r32` with `rdx` 0 and a divisor not 0. -/
theorem s_div32 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .div 32 [gr 32 r] len)) (h0 : X.cpu.gpr.rdx = 0) (hne : rv X 32 r ≠ 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (X.cpu.gpr.set (regOf 0)
        ((BitVec.ofNat 32 ((rv X 32 0).toNat / (rv X 32 r).toNat)).setWidth 64)).set (regOf 2)
        ((BitVec.ofNat 32 ((rv X 32 0).toNat % (rv X 32 r).toNat)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ :=
      div32 (s := X.withMem M) (o := o) (t := t + 1) htf (c.dec hK' hin hrip hd) h0 hne
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg
