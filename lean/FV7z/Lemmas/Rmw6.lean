import FV7z.Lemmas.Rmw2
import FV7z.Lemmas.Sp
/-!
# `sub byte [rip + d], imm` (PLAN.md §M, constructors)

The constructor `csuTg 61` takes one from a byte of `.data` before it registers its handler: `sub_rip8`,
`Seg.s_sub_rip8`, as `Rmw2.lean`'s `sub_rip32` for a byte; `Sp.sub_rip8_then`: the same as a piece of code for
`Seg.cfg`, then a piece from its end.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `sub byte [rip + d], imm`. -/
theorem sub_rip8 {d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .sub 8 [.mem (mrip d 8), .imm 8 v] len))
    (hwr : Writable prof s (eaR s len d) 1) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaR s len d)
          (toBytesLE (ofBytesLE 8 (readBytes s.proc.mm.mem (eaR s len d) 1) - BitVec.ofNat 8 v) 1)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat) (m := ⟨eaR s len d, false⟩) (acc := .write)
    (n := 1) hac hwr
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.sub, alu, subOp, mk, mrip, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readRip, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      Prog.writeFlags, BitVec.mul_one, done]
    rw [eaR_adv]
    have z : BitVec.setWidth 8 (BitVec.ofBool false) = 0#8 := rfl
    simp only [Nat.reduceDiv, Bool.not_true, Bool.and_false, Bool.false_and, hc, z, BitVec.sub_zero]
    rfl
  all_goals rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `sub byte [rip + d], imm` on a byte the run may store into. -/
theorem s_sub_rip8 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .sub 8 [.mem (mrip d 8), .imm 8 v] len)) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (hst : ∀ i < 1, Foot Wl (g.add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V g (toBytesLE (ofBytesLE 8 ((byteAddrs g 1).map V) - BitVec.ofNat 8 v) 1))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    have he : eaR (X.withMem M) len d = g := by
      show X.cpu.rip.add len + _ = _
      rw [hrip, addr_add_add, hg]
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 8 ((byteAddrs g 1).map V) - BitVec.ofNat 8 v) 1) (a := g) (by simpa using hst)
    rw [toBytesLE_length, ← he] at hwr
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := sub_rip8 (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf
      hac (c.dec hK' hin hrip hd) hwr
    rw [he, hv] at hr
    exact ⟨_, _, hr, hKs.nx h1 h2 h3, hAs, rip_add hrip M len, rfl⟩) k'

end FV7z.Fn.Seg

namespace FV7z
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

variable {prof : Profile} {code : List Byte} {e' : Addr}

/-- `sub byte [rip + d], imm` at the `j`-th byte, the byte at `g` in `Wl`, then a piece from its end: the piece's
condition for any flags and the byte one less. -/
theorem Sp.sub_rip8_then {j d v len : Nat} {W : Wpt}
    (hd : Dec prof.feat code j (FV7z.mk .sub 8 [.mem (mrip d 8), .imm 8 v] len)) (hj : j < code.length) {g : Addr}
    (hg : e'.add (j + len) + BitVec.ofNat 64 d = g) (h : Sp prof code e' (j + len) W) :
    Sp prof code e' j fun F Wl Q gr _ V => (∀ i < 1, Foot Wl (g.add i)) ∧
      ∀ fl, W F Wl Q gr fl (Vst V g (toBytesLE (ofBytesLE 8 ((byteAddrs g 1).map V) - BitVec.ofNat 8 v) 1)) :=
  ⟨fun c hin _ _ _ Q hK hA hrip hW k => c.s_sub_rip8 hK hA hin hj hrip hd hg hW.1
    fun Y _ hKY hAY ⟨hrY, hgY⟩ => h.run c hin Q hKY hAY hrY (by rw [hgY]; exact hW.2 _) k⟩

end FV7z
