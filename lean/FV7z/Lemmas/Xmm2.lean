import FV7z.Lemmas.BlkOps6
import FV7z.Lemmas.BlkOps4
/-!
# More moves of an `xmm` register (PLAN.md G3, startup)

Instructions of `__pthread_initialize_minimal` (measured with `tools/blk_gen.py`): `movq xmm0, r8`,
`punpcklqdq xmm0, xmm0`, and `movups` stores of registers whose values are set long before, across system calls.

- `movq_rx`, `punpcklqdq_xx`: the two instructions; `Seg.s_movq_rx`, `Seg.s_punpcklqdq`: as steps of a run, with the
  register's new low 128 bits and the other registers' kept.
- `Seg.s_movups_stv`: `Seg.s_movups_st` with what it does not say, that the vector registers are kept.
- `Seg.s_blkF_v`: `Seg.s_blkF` likewise (as `Seg.s_blkA_v` for `Seg.s_blkA`).
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `movq xmmN, r64`: the low 128 bits of the register are the general register's value, zero-extended. -/
theorem movq_rx {n r len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk (.sse .movq) 64 [.xmm n, gr 64 r] len)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++ (rv s 64 r).setWidth 128))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movq, moveBits, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    pure, Prog.readReg, Prog.run, writeOp]
  rfl

/-- `punpcklqdq xmmN, xmmM`: the low quadwords of the two registers, the first one's low. -/
theorem punpcklqdq_xx {n m len : Nat} (htf : s.cpu.rflags.tf = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .punpcklqdq) 16 [.xmm n, .xmm m] len)) :
    (instruction prof s).runStream o t =
      (.running (nxz s len s.cpu.gpr (rf0 s) (withZmm s.cpu.vec.zmm (xmmOf n)
        ((s.cpu.vec.zmm (xmmOf n)).extractLsb' 128 384 ++
          (lane 64 ((s.cpu.vec.zmm (xmmOf m)).setWidth 128) 0 ++
            lane 64 ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 0)))) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.punpcklqdq, packedOp, packed, aligned16, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, pure, Prog.run, writeOp, Prog.readZmm]
  rfl

theorem withZmm_ne (z : Fin 32 → BitVec 512) (k k' : Fin 32) (v : BitVec 512) (h : k' ≠ k) :
    withZmm z k v k' = z k' := by
  simp only [withZmm, h, ↓reduceIte]

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' fb : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `movq xmmN, r64`. -/
theorem s_movq_rx (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n r len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movq) 64 [.xmm n, gr 64 r] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      xlo Y n = (rv X 64 r).setWidth 128 ∧ ∀ m, xmmOf m ≠ xmmOf n → xlo Y m = xlo X m) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    have hr := movq_rx (s := X.withMem M) (o := o) (t := t + 1) (n := n) htf (c.dec hK' hin hrip hd)
    refine ⟨_, _, hr, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA', rip_add hrip M len, rfl, ?_, fun m hm => ?_⟩
    · show (withZmm _ _ _ _).setWidth 128 = _
      rw [xlo_with]
      rfl
    · show (withZmm _ _ _ _).setWidth 128 = _
      rw [withZmm_ne _ _ _ _ hm]
      rfl) k'

/-- `punpcklqdq xmmN, xmmM`. -/
theorem s_punpcklqdq (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n m len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .punpcklqdq) 16 [.xmm n, .xmm m] len))
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧
      xlo Y n = lane 64 (xlo X m) 0 ++ lane 64 (xlo X n) 0 ∧ ∀ q, xmmOf q ≠ xmmOf n → xlo Y q = xlo X q) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf _ => by
    have hr := punpcklqdq_xx (s := X.withMem M) (o := o) (t := t + 1) (n := n) (m := m) htf
      (c.dec hK' hin hrip hd)
    refine ⟨_, _, hr, hK'.modCpu rfl rfl rfl rfl rfl rfl rfl, hA', rip_add hrip M len, rfl, ?_, fun q hq => ?_⟩
    · show (withZmm _ _ _ _).setWidth 128 = _
      rw [xlo_with]
      rfl
    · show (withZmm _ _ _ _).setWidth 128 = _
      rw [withZmm_ne _ _ _ _ hq]
      rfl) k'

/-- `movups xmmword [b + d], xmmN`, into bytes the run may store into; the vector registers are kept. -/
theorem s_movups_stv (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movups) 32 [.mem (mbd b d 128), .xmm n] len))
    (hst : ∀ i < 16, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movups_st (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

/-- A stretch of straight-line code in a run whose start has the `fs` base `fb`: it keeps the vector registers. -/
theorem s_blkF_v (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L e' code) {j j' : Nat}
    {ops : List Op} (hb : BlkF prof code e' fb j j' ops) (v : VecRegs) :
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
    have hf : ∀ M, KeptW Wl s₀ (X.withMem M) → (X.withMem M).cpu.seg.fsBase = fb :=
      fun M hK' => by rw [hK'.seg]; exact hfs
    cases op with
    | reg hh P =>
      refine c.next (V' := V) (Pr := fun Y => Y.cpu.rip = e'.add (j + i.len) ∧
        P X.cpu.gpr X.cpu.rflags Y.cpu.rflags ∧ Y.cpu.gpr = hh X.cpu.gpr X.cpu.rflags ∧ Y.cpu.vec = v)
        hK hA hin hj hrip (fun M hK' hA' htf _ => ?_) ?_
      · obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ :=
          ho (X.withMem M) o (t + 1) hrip (hf M hK') htf (c.dec hK' hin hrip hd)
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
        obtain ⟨fl, t', hr, hp, h1, h2, h3⟩ :=
          ho (X.withMem M) o (t + 1) hrip (hf M hK') htf hac (c.dec hK' hin hrip hd) hrd
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
        obtain ⟨t', hr⟩ := ho (X.withMem M) o (t + 1) hrip (hf M hK') htf hac (c.dec hK' hin hrip hd) hlen hwr
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
      obtain ⟨bs, t', hlen, hr⟩ := ho (X.withMem M) o (t + 1) hrip (hf M hK') htf hac (c.dec hK' hin hrip hd) hwr
      obtain ⟨-, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA' (bs := bs) (a := ea X.cpu.gpr)
        (by rw [hlen]; exact hst)
      exact ⟨_, _, hr, ih (hKs.nx rfl rfl rfl) hAs (rip_add hrip M i.len) hv hkv.2 (h bs hlen)⟩

end FV7z.Fn.Seg
