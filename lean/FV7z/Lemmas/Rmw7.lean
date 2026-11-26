import FV7z.Lemmas.Rmw4
import FV7z.Lemmas.Lock2
import FV7z.Lemmas.Xmm2
/-!
# `and qword [b + d], imm` and `xchg qword [b + d], r64` (PLAN.md §M, M1)

`malloc_consolidate`'s `clear_inuse_bit_at_offset` (`and qword [r12 + 8], -2`) and its `atomic_exchange_acq`
that empties a fastbin (`xchg qword [r13], rbx`).

- `and_mi64`, `Seg.s_and_mi64`: as `Rmw4.lean`'s `or_mi64`, `Seg.s_or_mi64`.
- `xchg_bd64`, `Seg.s_xchg_bd64`: as `Lock2.lean`'s `xchg_bd32`, `Seg.s_xchg_bd32`, for a quadword (within one cache
  line).
- `pxor_xx`, `Seg.s_pxor`: `pxor xmmN, xmmM` with the register's new low 128 bits (`p->fd_nextsize = NULL`,
  `p->bk_nextsize = NULL` store a register cleared so), as `Xmm2.lean`'s `movq_rx`, `Seg.s_movq_rx`.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `and qword [b + d], imm`. -/
theorem and_mi64 {b d v len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .and 64 [.mem (mbd b d 64), .imm 64 v] len))
    (hwr : Writable prof s (eaD s b d) 8) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d)
          (toBytesLE (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8) &&& BitVec.ofNat 64 v) 8)) len
          s.cpu.gpr fl) none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.and, alu, logicOp, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
      memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.write, Prog.run, writeOp, Prog.readFlags,
      BitVec.mul_one]
    rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr]
    simp only [Prog.undefinedBit, Prog.undefined, bind, pure, Prog.bind, Prog.run, Req.bind, Prog.writeFlags, done]
    have hc := checkAccess_ok (feat := prof.feat) (s := advance s len)
      (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 8)
      hac hwr
    simp only [eaD_adv, Nat.reduceDiv, hc]
    rfl
  all_goals rfl

/-- `xchg qword [b + d], r64`: locked whether or not it has the prefix. -/
theorem xchg_bd64 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .xchg 64 [.mem (mbd b d 64), gr 64 r] len))
    (hsl : (eaD s b d).toNat % 64 + 8 ≤ 64) (hwr : Writable prof s (eaD s b d) 8) :
    ∃ t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d) (toBytesLE (rv s 64 r) 8)) len
          (s.cpu.gpr.set (regOf r) ((ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)).setWidth 64)) (rf0 s))
          none, t') := by
  have hc := checkAccess_ok (s := advance s len) (feat := prof.feat)
    (m := ⟨eaD s b d, (some b == some 4 || some b == some 5) && !false && !false⟩) (acc := .write) (n := 8) hac hwr
  have hns : ¬ ((eaD s b d).toNat % 64 + 64 / 8 > 64 ∧ prof.linux.splitLock ≠ .atomic) := by
    intro h; have := h.1; omega
  refine ⟨?t', instruction_next htf hdec ?h⟩
  case h =>
    simp only [exec, Sem.xchg, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true,
      ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.run, writeOp,
      Prog.lockedRmw, BitVec.mul_one, done]
    rw [eaD_adv]
    simp only [hns, ↓reduceIte, Nat.reduceDiv, hc]
    rfl

/-- `pxor xmmN, xmmM`: the low 128 bits of the first register are the two registers' `xor`. -/
theorem pxor_xx {w n m len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.sse .pxor) w [.xmm n, .xmm m] len)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ (xlo s n ^^^ xlo s m)))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.pxor, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `and qword [b + d], imm`, bytes the run may store into. -/
theorem s_and_mi64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d v len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .and 64 [.mem (mbd b d 64), .imm 64 v] len))
    (hst : ∀ i < 8, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) &&& BitVec.ofNat 64 v) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) &&& BitVec.ofNat 64 v) 8) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := eaD X b d) (n := 8)
      fun i hi => c.hws _ (hst i hi)
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := and_mi64 (s := X.withMem M) (o := o) (t := t + 1) (v := v) htf hac
      (c.dec hK' hin hrip hd) hwr
    refine ⟨_, _, hr, ?_, ?_, rip_add hrip M len, rfl⟩
    · rw [show readBytes (X.withMem M).proc.mm.mem (eaD (X.withMem M) b d) 8 = _ from hv]
      exact hKs.nx h1 h2 h3
    · rw [show readBytes (X.withMem M).proc.mm.mem (eaD (X.withMem M) b d) 8 = _ from hv]
      exact hAs) k'

/-- `xchg qword [b + d], r64` on a quadword the run may store into: the word becomes the register, the register
the word. -/
theorem s_xchg_bd64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .xchg 64 [.mem (mbd b d 64), gr 64 r] len))
    (hsl : (eaD X b d).toNat % 64 + 8 ≤ 64) (hst : ∀ i < 8, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (rv X 64 r) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧
        Y.cpu.gpr = X.cpu.gpr.set (regOf r) ((ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V)).setWidth 64)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (fun i hi => c.hws _ (hst i hi))
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (rv X 64 r) 8) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨t', hr⟩ := xchg_bd64 (s := X.withMem M) (o := o) (t := t + 1) (r := r) htf
      hac (c.dec hK' hin hrip hd) hsl hwr
    rw [show eaD (X.withMem M) b d = eaD X b d from rfl, hv] at hr
    exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M len, rfl⟩) k'

/-- `pxor xmmN, xmmM`. -/
theorem s_pxor (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {w n m len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .pxor) w [.xmm n, .xmm m] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      xlo Y n = xlo X n ^^^ xlo X m ∧ ∀ q, xmmOf q ≠ xmmOf n → xlo Y q = xlo X q) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    have hr := pxor_xx (s := X.withMem M) (o := o) (t := t + 1) (n := n) (m := m) htf (c.dec hK' hin hrip hd)
    refine ⟨_, _, hr, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA', rip_add hrip M len, rfl, ?_, fun q hq => ?_⟩
    · show (withZmm _ _ _ _).setWidth 128 = _
      rw [xlo_with]
      rfl
    · show (withZmm _ _ _ _).setWidth 128 = _
      rw [withZmm_ne _ _ _ _ hq]
      rfl) k'

end FV7z.Fn.Seg
