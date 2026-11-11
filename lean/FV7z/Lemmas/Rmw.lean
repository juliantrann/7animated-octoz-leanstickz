import FV7z.Lemmas.Xmm2
/-!
# Instructions that read and write memory, and `rep stos` (PLAN.md G3, startup)

Instructions of `__pthread_initialize_minimal` (measured with `tools/blk_gen.py`) that are steps of their own, the
`Op`s of `Blk.lean` being a load or a store, of one instruction of one step:

- `or_mr64`, `Seg.s_or_mr64`: `or qword [b + d], r64`.
- `repStosq`, `instruction_again`, `rep_stosq_exec`, `Seg.s_rep_stosq`: `rep stos qword [rdi], rax`, a step of the
  model for each quadword; `Vfill` is what the footprint's bytes are after.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `or qword [b + d], r64`. -/
theorem or_mr64 {b d r len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .or 64 [.mem (mbd b d 64), gr 64 r] len))
    (hwr : Writable prof s (eaD s b d) 8) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx (st s (eaD s b d)
          (toBytesLE (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8) ||| rv s 64 r) 8)) len s.cpu.gpr fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  refine ⟨?fl, ?t', instruction_next htf hdec ?h, ?h1, ?h2, ?h3⟩
  case h =>
    simp only [exec, Sem.or, alu, logicOp, mk, mbd, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
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
/-- `rep stos qword [rdi], rax` as the decoder gives it. -/
abbrev repStosq (len : Nat) : Inst :=
  { mn := .str .stos, opsz := 64, len, rep := some .rep, lock := false, mask := none, zero := false, fop := 0,
    ops := [.mem ⟨some .es, some 7, none, 1, 0, false, false, 64⟩, .reg ⟨64, 0, false⟩] }

theorem instruction_again {prof : Profile} {o : Oracle} {t t' : Nat} {s s₂ : State} {i : Decode.Inst}
    (htf : s.cpu.rflags.tf = false) (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok i)
    (hex : ((exec prof i).run prof.feat prof.linux.splitLock (advance s i.len)).runStream o t = (.ok .again s₂, t'))
    (hc : readBytes s₂.proc.mm.mem s.cpu.rip i.len = readBytes s.proc.mm.mem s.cpu.rip i.len) :
    (instruction prof s).runStream o t = (.running (s₂.modCpu fun c => { c with rip := s.cpu.rip }) none, t') := by
  unfold instruction
  simp only [htf, Bool.false_eq_true, ↓reduceIte, hdec]
  unfold advance at hex
  show (Req.bind _ _).runStream o t = _
  rw [Req.runStream_bind, hex]
  simp only [hc, ↓reduceIte]
  rfl

theorem rep_stosq_exec {len : Nat} (hac : s.cpu.rflags.ac = false) (hdf : s.cpu.rflags.df = false)
    (hc : s.cpu.gpr.rcx ≠ 0) (hwr : Writable prof s s.cpu.gpr.rdi 8) :
    ((exec prof (repStosq len)).run prof.feat prof.linux.splitLock (advance s len)).runStream o t =
      (.ok (if s.cpu.gpr.rcx - 1 = 0 then .next else .again)
        ((st s s.cpu.gpr.rdi (toBytesLE s.cpu.gpr.rax 8)).modCpu fun c =>
          { c with rip := c.rip.add len, rflags := rf0 s,
                   gpr := (s.cpu.gpr.set 7 (s.cpu.gpr.rdi + 8)).set 1 (s.cpu.gpr.rcx - 1) }), t) := by
  simp only [exec, execString, stringOp, repStosq, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.write, writeOp, Prog.readFlags,
    BitVec.mul_one, readAddrReg, writeAddrReg, Inst.addr32, List.any, ZellicX86.advance, Prog.writeReg]
  simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte, Prog.bind, Prog.run]
  have hc' : (advance s len).cpu.gpr.get 1 ≠ 0 := hc
  have hdf' : (advance s len).cpu.rflags.df = false := hdf
  simp only [hc', hdf', Bool.false_eq_true, ↓reduceIte, Prog.bind, Prog.run]
  have ha : (advance s len).cpu.gpr.get (regOf 7) + 0 + 0#64 = s.cpu.gpr.rdi := by
    show s.cpu.gpr.rdi + 0 + 0#64 = _
    simp
  have hk := checkAccess_ok (feat := prof.feat) (s := advance s len)
    (m := ⟨s.cpu.gpr.rdi, (some 7 == some 4 || some 7 == some 5) && !false && !false⟩) (acc := .write) (n := 8)
    hac hwr
  simp only [ha, Nat.reduceDiv, hk]
  have e1 : (advance s len).cpu.gpr.get 1 = s.cpu.gpr.rcx := rfl
  rw [e1]
  by_cases h : s.cpu.gpr.rcx - 1 = 0
  · simp only [h, ↓reduceIte]
    rfl
  · simp only [h, ↓reduceIte]
    rfl

/-- `V` with `n` copies of the quadword `v` from `a` on. -/
def Vfill (V : Addr → Byte) (a : Addr) (v : BitVec 64) : Nat → Addr → Byte
  | 0 => V
  | n + 1 => Vfill (Vst V a (toBytesLE v 8)) (a + 8) v n

theorem Vfill_succ (V : Addr → Byte) (a : Addr) (v : BitVec 64) (n : Nat) :
    Vfill V a v (n + 1) = Vfill (Vst V a (toBytesLE v 8)) (a + 8) v n := rfl

theorem readBytes_congr {m m' : Memory} : ∀ (n : Nat) (a : Addr),
    (∀ i < n, m.readByte (a.add i) = m'.readByte (a.add i)) → readBytes m a n = readBytes m' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    rw [addr_add_zero] at h0
    have ih : readBytes m (a.add 1) n = readBytes m' (a.add 1) n := readBytes_congr n (a.add 1) fun i hi => by
      have h1 := h (i + 1) (by omega)
      rw [Nat.add_comm i 1, ← addr_add_add] at h1
      exact h1
    rw [readBytes_succ, readBytes_succ]
    exact congr (congrArg _ h0) ih

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `or qword [b + d], r64`, bytes the run may store into. -/
theorem s_or_mr64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {b d r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .or 64 [.mem (mbd b d 64), gr 64 r] len))
    (hst : ∀ i < 8, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE
      (Vst V (eaD X b d) (toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) ||| rv X 64 r) 8))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) ||| rv X 64 r) 8) (a := eaD X b d)
      (by simpa using hst)
    rw [toBytesLE_length] at hwr
    obtain ⟨-, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' (a := eaD X b d) (n := 8)
      fun i hi => c.hws _ (hst i hi)
    obtain ⟨fl, t', hr, h1, h2, h3⟩ := or_mr64 (s := X.withMem M) (o := o) (t := t + 1) htf hac
      (c.dec hK' hin hrip hd) hwr
    refine ⟨_, _, hr, ?_, ?_, rip_add hrip M len, rfl⟩
    · rw [show readBytes (X.withMem M).proc.mm.mem (eaD (X.withMem M) b d) 8 = _ from hv]
      exact hKs.nx h1 h2 h3
    · rw [show readBytes (X.withMem M).proc.mm.mem (eaD (X.withMem M) b d) 8 = _ from hv]
      exact hAs) k'

/-- `rep stos qword [rdi], rax` with `rcx` `n + 1` and the direction flag clear: `n + 1` quadwords `rax` from
`rdi` on, into bytes the run may store into; `rdi` is past them and `rcx` 0. -/
theorem s_rep_stosq (c : Seg prof F Wl L s₀ o) (hdf : s₀.cpu.rflags.df = false) (hin : CodeIn L e' code) {len : Nat}
    (hjl : j + len ≤ code.length) (hj : j < code.length) (hd : Dec prof.feat code j (repStosq len)) :
    ∀ (n : Nat) {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = e'.add j → X.cpu.gpr.rcx.toNat = n + 1 → (∀ i < 8 * (n + 1), Foot Wl (Addr.add X.cpu.gpr.rdi i)) →
      ContG prof F Wl L s₀ o gev gP gE (Vfill V X.cpu.gpr.rdi X.cpu.gpr.rax (n + 1))
        (fun Y => Y.cpu.rip = e'.add (j + len) ∧
          Y.cpu.gpr = (X.cpu.gpr.set 7 (X.cpu.gpr.rdi + BitVec.ofNat 64 (8 * (n + 1)))).set 1 0) →
      GoG prof L o gev gP gE X t := by
  intro n
  induction n with
  | zero =>
    intro X t V hK hA hrip hc hst k'
    have hc1 : X.cpu.gpr.rcx = 1 := BitVec.eq_of_toNat_eq hc
    refine c.next hK hA hin hj hrip (fun M hK' hA' htf hac => ?_) k'
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE X.cpu.gpr.rax 8) (a := X.cpu.gpr.rdi) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    have hx := rep_stosq_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
      (hK'.df.trans hdf) (by show X.cpu.gpr.rcx ≠ 0; rw [hc1]; decide) hwr
    have e0 : (X.withMem M).cpu.gpr.rcx - 1 = 0 := by show X.cpu.gpr.rcx - 1 = 0; rw [hc1]; decide
    rw [e0] at hx
    simp only [↓reduceIte] at hx
    refine ⟨_, _, instruction_next htf (c.dec hK' hin hrip hd) hx, hKs.modCpu rfl rfl rfl rfl rfl rfl rfl, hAs,
      rip_add hrip M len, rfl⟩
  | succ n ih =>
    intro X t V hK hA hrip hc hst k'
    have hne : X.cpu.gpr.rcx ≠ 0 := fun h => by rw [h] at hc; simp at hc
    have hc' : (X.cpu.gpr.rcx - 1).toNat = n + 1 := by
      have h1 : (1 : BitVec 64).toNat = 1 := rfl
      rw [BitVec.toNat_sub, hc, h1]
      omega
    have hne' : X.cpu.gpr.rcx - 1 ≠ 0 := fun h => by rw [h] at hc'; simp at hc'
    refine c.next hK hA hin hj hrip (V' := Vst V X.cpu.gpr.rdi (toBytesLE X.cpu.gpr.rax 8))
      (Pr := fun Y => Y.cpu.rip = e'.add j ∧
        Y.cpu.gpr = (X.cpu.gpr.set 7 (X.cpu.gpr.rdi + 8)).set 1 (X.cpu.gpr.rcx - 1))
      (fun M hK' hA' htf hac => ?_) ?_
    · obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
        (bs := toBytesLE X.cpu.gpr.rax 8) (a := X.cpu.gpr.rdi)
        (by intro i hi; rw [toBytesLE_length] at hi; exact hst i (by omega))
      rw [toBytesLE_length] at hwr
      have hx := rep_stosq_exec (prof := prof) (o := o) (t := t + 1) (s := X.withMem M) (len := len) hac
        (hK'.df.trans hdf) hne hwr
      have e0 : ¬ ((X.withMem M).cpu.gpr.rcx - 1 = 0) := hne'
      simp only [e0, ↓reduceIte] at hx
      have hcA := c.codeAt hK' hin
      have hcB := c.codeAt hKs hin
      have hcode : readBytes (st (X.withMem M) X.cpu.gpr.rdi (toBytesLE X.cpu.gpr.rax 8)).proc.mm.mem
          (X.withMem M).cpu.rip len = readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.rip len := by
        refine readBytes_congr len _ fun i hi => ?_
        rw [show (X.withMem M).cpu.rip = e'.add j from hrip, addr_add_add]
        obtain ⟨-, -, h1⟩ := hcA (j + i) (by omega)
        obtain ⟨-, -, h2⟩ := hcB (j + i) (by omega)
        rw [h1] at h2
        exact (Option.some.inj h2).symm
      refine ⟨_, _, instruction_again htf (c.dec hK' hin hrip hd) hx hcode,
        (hKs.modCpu rfl rfl rfl rfl rfl rfl rfl).modCpu rfl rfl rfl rfl rfl rfl rfl, hAs, hrip, rfl⟩
    · rintro Y t' hKY hAY ⟨hrY, hgY⟩
      have hdi : Y.cpu.gpr.rdi = X.cpu.gpr.rdi + 8 := by rw [hgY]; rfl
      have hax : Y.cpu.gpr.rax = X.cpu.gpr.rax := by rw [hgY]; rfl
      have hcx : Y.cpu.gpr.rcx = X.cpu.gpr.rcx - 1 := by rw [hgY]; rfl
      refine ih hKY hAY hrY (by rw [hcx]; exact hc') (fun i hi => ?_) ?_
      · rw [hdi]
        have := hst (8 + i) (by omega)
        rw [← addr_add_add] at this
        exact this
      · rw [hdi, hax]
        intro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
        refine k' Z t'' hKZ (by rw [Vfill_succ]; exact hAZ) ⟨hrZ, ?_⟩
        rw [hgZ, hgY]
        have ea : X.cpu.gpr.rdi + 8 + BitVec.ofNat 64 (8 * (n + 1)) =
            X.cpu.gpr.rdi + BitVec.ofNat 64 (8 * (n + 1 + 1)) := by
          rw [BitVec.add_assoc]
          congr 1
          apply BitVec.eq_of_toNat_eq
          simp [Nat.add_mod]
          omega
        rw [ea]
        rfl

end FV7z.Fn.Seg
