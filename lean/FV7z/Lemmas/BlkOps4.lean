import FV7z.Lemmas.BlkOps3
/-!
# 64-bit `imul` and `div`, and the moves of an `xmm` register (PLAN.md G3, startup)

Instructions of `__libc_setup_tls` (measured with `tools/blk_gen.py`: `div rbp`, `imul rax, rbp`,
`movq xmm0, [rsp + 8]`, `movhps xmm0, [rsp + 16]`, `movups [r14 + 0x430], xmm0`).

- `Op.imul64`: `imul r64, q` as an `Op` of `Blk.lean`, the flags unconstrained; `imul64_eq`: its result is the product.
- `div64`, `Seg.s_div64`: `div r64` with `rdx` 0 and a divisor not 0, a step of its own: the `Op`s of `Blk.lean` have
  no condition on the registers, and `div` faults when the divisor is 0.
- `movq_ld`, `movhps_ld`, `movups_st` and `Seg.s_movq_ld`, `Seg.s_movhps_ld`, `Seg.s_movups_st`: steps of their own
  too, `Op`s being of the general registers; `xlo s n` is the low 128 bits of the `n`-th vector register.
- `Seg.s_blkA_v`: `Seg.s_blkA` with what it does not say, that a stretch of `Op`s keeps the vector registers: for the
  stretches between the three moves.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `imul r64, q`. -/
def Op.imul64 (r q : Nat) : Op :=
  .reg (fun g _ => wr g r (((gv g 64 r).signExtend (2 * 64) * (gv g 64 q).signExtend (2 * 64)).setWidth 64))
    fun _ _ _ => True

theorem OpI.imul64 {r q len : Nat} :
    OpI prof (mk .imul 64 [gr 64 r, gr 64 q] len) (Op.imul64 r q) := fun _ _ _ htf hdec =>
  ⟨_, _, instruction_next htf hdec rfl, trivial, rfl, rfl, rfl⟩

theorem imul64_eq (x y : BitVec 64) : (x.signExtend (2 * 64) * y.signExtend (2 * 64)).setWidth 64 = x * y := by
  rw [BitVec.setWidth_mul _ _ (by decide)]
  have e : ∀ z : BitVec 64, BitVec.setWidth 64 (BitVec.signExtend (2 * 64) z) = z := by
    intro z
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_signExtend, hi]
    omega
  rw [e, e]

theorem udiv_eq (x d : BitVec 64) : x / d = BitVec.setWidth 64 (BitVec.ofNat 64 (x.toNat / d.toNat)) := by
  have hlt : x.toNat / d.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_udiv, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem umod_eq (x d : BitVec 64) : x % d = BitVec.setWidth 64 (BitVec.ofNat 64 (x.toNat % d.toNat)) := by
  have hlt : x.toNat % d.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- `div r64` with `rdx` 0 and a divisor not 0. -/
theorem div64 {r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .div 64 [gr 64 r] len))
    (h0 : s.cpu.gpr.rdx = 0) (hne : rv s 64 r ≠ 0) :
    ∃ fl t', (instruction prof s).runStream o t =
        (.running (nx s len ((s.cpu.gpr.set 0 (s.cpu.gpr.rax / rv s 64 r)).set 2 (s.cpu.gpr.rax % rv s 64 r)) fl)
          none, t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df := by
  suffices h : ∃ fl t', ((exec prof (mk .div 64 [gr 64 r] len)).run prof.feat prof.linux.splitLock
      (advance s len)).runStream o t = (.ok .next (nx s len ((s.cpu.gpr.set 0 (s.cpu.gpr.rax / rv s 64 r)).set 2
        (s.cpu.gpr.rax % rv s 64 r)) fl), t') ∧
      fl.tf = s.cpu.rflags.tf ∧ fl.ac = s.cpu.rflags.ac ∧ fl.df = s.cpu.rflags.df by
    obtain ⟨fl, t', h, h1, h2, h3⟩ := h
    exact ⟨fl, t', instruction_next htf hdec h, h1, h2, h3⟩
  simp only [exec, Sem.div, dividend, divResult, mk, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    pure, Prog.readReg, Prog.run, writeOp, Prog.readFlags, accOf, Nat.reduceEqDiff, true_or]
  have e2 : (advance s len).cpu.gpr.get (regOf 2) = 0 := h0
  have e0 : (advance s len).cpu.gpr.get (regOf 0) = s.cpu.gpr.rax := rfl
  have er : BitVec.setWidth 64 ((advance s len).cpu.gpr.get (regOf r)) = rv s 64 r := rfl
  have hn : (BitVec.setWidth (2 * 64) (BitVec.setWidth 64 (0 : BitVec 64) ++
      BitVec.setWidth 64 s.cpu.gpr.rax)).toNat = s.cpu.gpr.rax.toNat := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_append]
    simp <;> omega
  have hlt : s.cpu.gpr.rax.toNat / (rv s 64 r).toNat < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) s.cpu.gpr.rax.isLt
  rw [e2, e0, er, hn, udiv_eq, umod_eq]
  simp only [hne, Nat.not_le.2 hlt, ↓reduceIte]
  exact ⟨_, _, rfl, rfl, rfl, rfl⟩

/-- `movq xmmN, qword [b + d]`: the low 128 bits of the register are the 8 bytes, zero-extended. -/
theorem movq_ld {n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movq) 32 [.xmm n, .mem (mbd b d 64)] len))
    (hld : Readable prof s (eaD s b d) 8) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
          (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8)).setWidth 128))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movq, moveBits, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `movhps xmmN, qword [b + d]`: the high quadword of the low 128 bits is the 8 bytes. -/
theorem movhps_ld {n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movhps) 32 [.xmm n, .mem (mbd b d 64)] len))
    (hld : Readable prof s (eaD s b d) 8) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
          (ofBytesLE 64 (readBytes s.proc.mm.mem (eaD s b d) 8) ++
            lane 64 ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 0).setWidth 128))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movhps, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.read, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm, Prog.writeZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hld]
  rfl

/-- `movups xmmword [b + d], xmmN`. -/
theorem movups_st {n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movups) 32 [.mem (mbd b d 128), .xmm n] len))
    (hwr : Writable prof s (eaD s b d) 16) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaD s b d) (toBytesLE ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 16)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movups, moveBits, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- The low 128 bits of the `n`-th vector register. -/
abbrev xlo (s : State) (n : Nat) : BitVec 128 := (s.cpu.vec.zmm (xmmOf n)).setWidth 128

theorem xlo_with (z : Fin 32 → BitVec 512) (k : Fin 32) (hi : BitVec 384) (v : BitVec 128) :
    (withZmm z k (hi ++ v) k).setWidth 128 = v := by
  simp only [withZmm, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
  simp [hi']

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `div r64` with `rdx` 0 and a divisor not 0. -/
theorem s_div64 (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk .div 64 [gr 64 r] len)) (h0 : X.cpu.gpr.rdx = 0) (hne : rv X 64 r ≠ 0)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧
      Y.cpu.gpr = (X.cpu.gpr.set 0 (X.cpu.gpr.rax / rv X 64 r)).set 2 (X.cpu.gpr.rax % rv X 64 r)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    obtain ⟨fl, t', hr, h1, h2, h3⟩ :=
      div64 (s := X.withMem M) (o := o) (t := t + 1) htf (c.dec hK' hin hrip hd) h0 hne
    exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M len, rfl⟩) k'

/-- `movq xmmN, qword [b + d]`, from bytes of the footprint's data. -/
theorem s_movq_ld (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movq) 32 [.xmm n, .mem (mbd b d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      xlo Y n = (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V)).setWidth 128) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hr := movq_ld (s := X.withMem M) (o := o) (t := t + 1) (n := n) htf hac (c.dec hK' hin hrip hd) hrd
    refine ⟨_, _, hr, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA', rip_add hrip M len, rfl, ?_⟩
    show (withZmm _ _ _ _).setWidth 128 = _
    rw [xlo_with]
    exact congrArg (fun z => (ofBytesLE 64 z).setWidth 128) hv) k'

/-- `movhps xmmN, qword [b + d]`, from bytes of the footprint's data. -/
theorem s_movhps_ld (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movhps) 32 [.xmm n, .mem (mbd b d 64)] len))
    (hl : ∀ i < 8, Foot F.data ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      xlo Y n = (ofBytesLE 64 ((byteAddrs (eaD X b d) 8).map V) ++ lane 64 (xlo X n) 0).setWidth 128) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hr := movhps_ld (s := X.withMem M) (o := o) (t := t + 1) (n := n) htf hac (c.dec hK' hin hrip hd) hrd
    refine ⟨_, _, hr, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA', rip_add hrip M len, rfl, ?_⟩
    show (withZmm _ _ _ _).setWidth 128 = _
    rw [xlo_with]
    exact congrArg (fun z => (ofBytesLE 64 z ++ lane 64 (xlo X n) 0).setWidth 128) hv) k'

/-- `movups xmmword [b + d], xmmN`, into bytes the run may store into. -/
theorem s_movups_st (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movups) 32 [.mem (mbd b d 128), .xmm n] len))
    (hst : ∀ i < 16, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movups_st (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl⟩) k'

/-- A stretch of straight-line code, at the code's place: it keeps the vector registers. -/
theorem s_blkA_v (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' code) {j j' : Nat} {ops : List Op}
    (hb : BlkA prof code e' j j' ops) (v : VecRegs) :
    ∀ {X : State} {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = e'.add j →
      X.cpu.vec = v → ops.all Op.kv = true →
      wp F Wl ops (fun g fl V' => ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V' → Y.cpu.rip = e'.add j' →
        Y.cpu.gpr = g → Y.cpu.rflags = fl → Y.cpu.vec = v → GoG prof L o gev gP gE Y t') X.cpu.gpr X.cpu.rflags V →
      GoG prof L o gev gP gE X t := by
  induction hb with
  | nil j => intro X t V hK hA hrip hv _ h; exact h X t hK hA hrip rfl rfl hv
  | @cons j j' i op ops hd ho hj _ ih =>
    intro X t V hK hA hrip hv hkv h
    rw [List.all_cons, Bool.and_eq_true] at hkv
    cases op with
    | reg hh P =>
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        P X.cpu.gpr X.cpu.rflags Y.cpu.rflags ∧ Y.cpu.gpr = hh X.cpu.gpr X.cpu.rflags ∧ Y.cpu.vec = v)
        hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) ?_
      · obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ := ho (X.withMem M) o (t + 1) hrip htf (c.dec hK' hin hrip hd)
        exact ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M i.len, hp, rfl, hv⟩
      · rintro Y t' hKY hAY ⟨hrY, hpY, hgY, hvY⟩
        exact ih hKY hAY hrY hvY hkv.2 (by rw [hgY]; exact h _ hpY)
    | load n ea hh P =>
      obtain ⟨hl, h⟩ := h
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        P X.cpu.gpr X.cpu.rflags ((byteAddrs (ea X.cpu.gpr) n).map V) Y.cpu.rflags ∧
        Y.cpu.gpr = hh X.cpu.gpr X.cpu.rflags ((byteAddrs (ea X.cpu.gpr) n).map V) ∧ Y.cpu.vec = v) hK hA hin hj hrip
        (fun M hK' hA' htf hac => ?_) ?_
      · obtain ⟨hrd, hv'⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
        obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ := ho (X.withMem M) o (t + 1) hrip htf hac (c.dec hK' hin hrip hd) hrd
        refine ⟨_, _, hr, hK'.nx h1 h2 h3, hA', rip_add hrip M i.len, ?_, ?_, hv⟩
        · rw [← hv']; exact hp
        · rw [← hv']; rfl
      · rintro Y t' hKY hAY ⟨hrY, hpY, hgY, hvY⟩
        exact ih hKY hAY hrY hvY hkv.2 (by rw [hgY]; exact h _ hpY)
    | store n ea val hh =>
      obtain ⟨hlen, hst, h⟩ := h
      refine c.next (V' := Vst V (ea X.cpu.gpr) (val X.cpu.gpr)) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        Y.cpu.rflags = rfz X.cpu.rflags ∧ Y.cpu.gpr = hh X.cpu.gpr ∧ Y.cpu.vec = v) hK hA hin hj hrip
        (fun M hK' hA' htf hac => ?_) ?_
      · obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
          (bs := val X.cpu.gpr) (a := ea X.cpu.gpr) (by rw [hlen]; exact hst)
        rw [hlen] at hwr
        obtain ⟨t', hr⟩ := ho (X.withMem M) o (t + 1) hrip htf hac (c.dec hK' hin hrip hd) hlen hwr
        exact ⟨_, _, hr, hKs.nx rfl rfl rfl, hAs, rip_add hrip M i.len, rfl, rfl, hv⟩
      · rintro Y t' hKY hAY ⟨hrY, hfY, hgY, hvY⟩
        exact ih hKY hAY hrY hvY hkv.2 (by rw [hgY, hfY]; exact h)
    | vld n ea => simp [Op.kv] at hkv
    | vst n ea =>
      obtain ⟨hst, h⟩ := h
      refine c.step hK hin hj hrip fun M hM hK' htf hac => ?_
      have hA' := c.agreeK hK hA hM
      obtain ⟨hwr, -, -⟩ := c.store_ok (X := X.withMem M) hK' hA' (bs := List.replicate n 0) (a := ea X.cpu.gpr)
        (by rw [List.length_replicate]; exact hst)
      rw [List.length_replicate] at hwr
      obtain ⟨bs, t', hlen, hr⟩ := ho (X.withMem M) o (t + 1) hrip htf hac (c.dec hK' hin hrip hd) hwr
      obtain ⟨-, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA' (bs := bs) (a := ea X.cpu.gpr)
        (by rw [hlen]; exact hst)
      exact ⟨_, _, hr, ih (hKs.nx rfl rfl rfl) hAs (rip_add hrip M i.len) hv hkv.2 (h bs hlen)⟩

end FV7z.Fn.Seg
