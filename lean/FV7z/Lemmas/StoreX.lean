import FV7z.Lemmas.Sse2b
/-!
# Stores of an `xmm` register, and bytes set to one value (PLAN.md M, `memset`)

glibc's `__memset_sse2_unaligned(_erms)` spreads the byte over `xmm0` and stores it, 16 bytes at a time, with
`movdqu xmmword [rdi + d], xmm0`, `movdqu xmmword [rdi + rdx + d], xmm0` and, in its loop, `movdqa xmmword [rcx + d],
xmm0`; under 16 bytes it moves the low 64 bits to `rcx` (`movq rcx, xmm0`) and stores those, and it returns with
`repz ret`.

- `movdqu_std`, `movdqu_sti`, `movdqa_std` and `Seg.s_movdqu_std`, `Seg.s_movdqu_sti`, `Seg.s_movdqa_std`: the stores,
  as steps of a run into bytes it may store into, the registers kept; `VOp.movqr`: `movq r64, xmmN`.
- `ret_len`, `Seg.s_retL`: a `ret` of any length (`repz ret` is 2 bytes).
- `ByteAll v b`: each byte of `v` is `b`; `FillP V V₂ a n b P`: the bytes `V₂` are `V` outside the `n` bytes from
  `a`, and `b` at those of them whose offsets are in `P`; `FillP.st`: a store of bytes `b` among them adds its
  offsets.
-/
namespace FV7z
open ZellicX86 Decode

variable {prof : Profile} {o : Oracle} {t : Nat} {s : State}

/-- `movdqu xmmword [b + d], xmmN`. -/
theorem movdqu_std {w n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movdqu) w [.mem (mbd b d 128), .xmm n] len))
    (hwr : Writable prof s (eaD s b d) 16) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaD s b d) (toBytesLE ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 16)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movdqu, moveBits, mbd, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [eaD_adv, checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- `movdqu xmmword [b + i + d], xmmN`. -/
theorem movdqu_sti {w n b i d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movdqu) w [.mem (mbi b i d 128), .xmm n] len))
    (hwr : Writable prof s (eaI s b i d) 16) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaI s b i d) (toBytesLE ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 16)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movdqu, moveBits, mbi, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte,
    memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, BitVec.mul_one, writeOp, Prog.readZmm]
  rw [checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- `movdqa xmmword [b + d], xmmN`, the address a multiple of 16. -/
theorem movdqa_std {w n b d len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) =
      .ok (mk (.sse .movdqa) w [.mem (mbd b d 128), .xmm n] len))
    (hal : (eaD s b d).toNat % 16 = 0) (hwr : Writable prof s (eaD s b d) 16) :
    (instruction prof s).runStream o t =
      (.running (nx (st s (eaD s b d) (toBytesLE ((s.cpu.vec.zmm (xmmOf n)).setWidth 128) 16)) len
        s.cpu.gpr (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, execSse, Sem.movdqa, moveAligned, aligned16, Prog.alignedTo, mbd, bind, Prog.bind, readOp,
    Bool.false_eq_true, ↓reduceIte, memRef, effOffset, pure, Prog.readReg, Prog.write, Prog.run, BitVec.mul_one,
    writeOp, Prog.readZmm, eaD_adv, hal, true_or]
  rw [checkAccess_ok (s := advance s len) hac hwr]
  rfl

/-- `ret`, of any length. -/
theorem ret_len {ra : Addr} {len : Nat} (htf : s.cpu.rflags.tf = false) (hac : s.cpu.rflags.ac = false)
    (hdec : Decode.decode prof.feat (fetchByte prof.feat s) = .ok (mk .ret 64 [] len))
    (hsh : s.thread.shstk = none)
    (hw : ofBytesLE 64 (readBytes s.proc.mm.mem s.cpu.gpr.rsp 8) = ra) (hcan : ra.canonical prof.feat.la57 = true)
    (hld : Readable prof s s.cpu.gpr.rsp 8) :
    (instruction prof s).runStream o t =
      (.running (upd s ra (s.cpu.gpr.set 4 (s.cpu.gpr.rsp + 8)) (rf0 s)) none, t) := by
  refine instruction_next htf hdec ?_
  simp only [exec, Sem.ret, Prog.run, bind, Prog.bind, Prog.readThread, Prog.readReg, Prog.read, pure,
    show (advance s len).thread.shstk = none from hsh, Bool.false_eq_true, ↓reduceIte]
  rw [checkAccess_ok (s := advance s len) hac hld]
  have hw' : ofBytesLE 64 (readBytes (advance s len).proc.mm.mem ((advance s len).cpu.gpr.get 4) 8) = ra := hw
  simp only [Nat.reduceDiv, hw', hcan, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl

namespace VOp
/-- `movq r64, xmmN`: the register's low 64 bits. -/
def movqr (r n : Nat) : VOp :=
  .v 0 false (fun _ => 0) (fun g x _ => g.set (regOf r) ((x (xmmOf n)).setWidth 64)) fun _ x _ => x
end VOp

theorem VOpI.movqr {w r n len : Nat} :
    VOpI prof (mk (.sse .movq) w [gr 64 r, .xmm n] len) (VOp.movqr r n) := by
  intro s o t htf _ hdec _ _
  refine ⟨s.cpu.vec.zmm, t, instruction_next htf hdec ?_, rfl⟩
  simp only [exec, execSse, Sem.movq, moveBits, gr, bind, Prog.bind, readOp, Bool.false_eq_true, ↓reduceIte, pure,
    Prog.run, writeOp, Prog.readZmm, xsOf, BitVec.setWidth_setWidth_of_le _ (show 64 ≤ 128 by omega)]
  rfl

/-! ## Bytes of one value -/

/-- Each byte of `v` is `b`. -/
def ByteAll {w : Nat} (v : BitVec w) (b : Byte) : Prop := ∀ i, 8 * i + 8 ≤ w → v.extractLsb' (8 * i) 8 = b

theorem extractLsb'_setWidth' {w m : Nat} (x : BitVec w) {s l : Nat} (h : s + l ≤ m) :
    (x.setWidth m).extractLsb' s l = x.extractLsb' s l := by
  ext k hk
  simp [show s + k < m by omega]

theorem ByteAll.setWidth {w m : Nat} {v : BitVec w} {b : Byte} (h : ByteAll v b) (hm : m ≤ w) :
    ByteAll (v.setWidth m) b :=
  fun i hi => by rw [extractLsb'_setWidth' _ hi]; exact h i (by omega)

theorem ByteAll.bytes {w : Nat} {v : BitVec w} {b : Byte} (h : ByteAll v b) {n : Nat} (hn : 8 * n ≤ w) :
    ∀ x ∈ toBytesLE v n, x = b := by
  intro x hx
  simp only [toBytesLE, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [← h i (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]

/-- The spread byte. -/
theorem ByteAll.bcast (c : BitVec 64) :
    ByteAll (ofDwords fun j => lane 32 (ofWords (interleave 16 0
      (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128)))
      (ofBytes (interleave 8 0 ((c.setWidth 32).setWidth 128) ((c.setWidth 32).setWidth 128))))) (0 / 4 ^ j % 4))
      (c.setWidth 8) :=
  fun i hi => lane_bcast c (i := i) (by omega)

/-! ## Filling -/

/-- The bytes `V₂` are `V` outside the `n` bytes from `a`, and `b` at those of them at the offsets `P`. -/
def FillP (V V₂ : Addr → Byte) (a : Addr) (n : Nat) (b : Byte) (P : Nat → Prop) : Prop :=
  (∀ i < n, P i → V₂ (a.add i) = b) ∧ ∀ x : Addr, ¬ (a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n) → V₂ x = V x

theorem FillP.start (V : Addr → Byte) (a : Addr) (n : Nat) (b : Byte) : FillP V V a n b fun _ => False :=
  ⟨fun _ _ h => h.elim, fun _ _ => rfl⟩

theorem FillP.mono {V V₂ : Addr → Byte} {a : Addr} {n : Nat} {b : Byte} {P Q : Nat → Prop} (h : FillP V V₂ a n b P)
    (hq : ∀ i < n, Q i → P i) : FillP V V₂ a n b Q :=
  ⟨fun i hi hQ => h.1 i hi (hq i hi hQ), h.2⟩

theorem Vst_const {bs : List Byte} {b : Byte} (hb : ∀ x ∈ bs, x = b) (V : Addr → Byte) {a : Addr}
    (hf : a.toNat + bs.length ≤ 2 ^ 64) {k : Nat} (hk : k < bs.length) : Vst V a bs (a.add k) = b := by
  have hm : Vst V a bs (a.add k) ∈ (byteAddrs a bs.length).map (Vst V a bs) :=
    List.mem_map_of_mem (mem_byteAddrs.2 ⟨k, hk, rfl⟩)
  rw [Vst_self bs V a hf] at hm
  exact hb _ hm

/-- A store of `k` bytes `b` at offset `o` of the `n` bytes. -/
theorem FillP.st {V V₂ : Addr → Byte} {a : Addr} {n : Nat} {b : Byte} {P : Nat → Prop} (h : FillP V V₂ a n b P)
    (hn : a.toNat + n ≤ 2 ^ 64) {o k : Nat} {bs : List Byte} (hl : bs.length = k) (ho : o + k ≤ n)
    (hb : ∀ x ∈ bs, x = b) : FillP V (Vst V₂ (a.add o) bs) a n b fun i => P i ∨ (o ≤ i ∧ i < o + k) := by
  subst hl
  have hao : (a.add o).toNat = a.toNat + o ∨ bs.length = 0 := by
    rcases Nat.eq_zero_or_pos bs.length with h0 | h0
    · exact .inr h0
    · exact .inl (toNat_add_of_fits (n := n) (by omega) hn)
  refine ⟨fun i hi hp => ?_, fun x hx => ?_⟩
  · by_cases hio : o ≤ i ∧ i < o + bs.length
    · have e : a.add i = (a.add o).add (i - o) := by rw [addr_add_add]; congr 1; omega
      rw [e]
      refine Vst_const hb V₂ ?_ (by omega)
      rcases hao with h1 | h1
      · rw [h1]; omega
      · omega
    · rcases hp with hp | hp
      · rw [Vst_apart bs _ _ _ fun k hk e => ?_]
        · exact h.1 i hi hp
        · have h1 := congrArg BitVec.toNat e
          rw [toNat_add_of_fits (n := n) hi hn, addr_add_add, toNat_add_of_fits (n := n) (by omega) hn] at h1
          omega
      · exact absurd hp hio
  · rw [Vst_apart bs _ _ _ fun k hk e => hx ?_]
    · exact h.2 x hx
    · rw [e, addr_add_add, toNat_add_of_fits (n := n) (by omega) hn]
      omega

end FV7z

namespace FV7z.Fn.Seg
open ZellicX86 Decode FV7z.Leaf

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {code : List Byte} {X : State} {t j : Nat} {V : Addr → Byte}

/-- `movdqu xmmword [b + d], xmmN`, into bytes the run may store into. -/
theorem s_movdqu_std (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {w n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movdqu) w [.mem (mbd b d 128), .xmm n] len))
    (hst : ∀ i < 16, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movdqu_std (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

/-- `movdqu xmmword [b + i + d], xmmN`, into bytes the run may store into. -/
theorem s_movdqu_sti (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {w n b i d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movdqu) w [.mem (mbi b i d 128), .xmm n] len))
    (hst : ∀ k < 16, Foot Wl ((eaI X b i d).add k))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaI X b i d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaI X b i d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movdqu_sti (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

/-- `movdqa xmmword [b + d], xmmN`, at a multiple of 16, into bytes the run may store into. -/
theorem s_movdqa_std (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hin : CodeIn L e' code) (hj : j < code.length) (hrip : X.cpu.rip = e'.add j) {w n b d len : Nat}
    (hd : Dec prof.feat code j (FV7z.mk (.sse .movdqa) w [.mem (mbd b d 128), .xmm n] len))
    (hal : (eaD X b d).toNat % 16 = 0) (hst : ∀ i < 16, Foot Wl ((eaD X b d).add i))
    (k' : ContG prof F Wl L s₀ o gev gP gE (Vst V (eaD X b d) (toBytesLE (xlo X n) 16))
      fun Y => Y.cpu.rip = e'.add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec = X.cpu.vec) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hwr, hKs, hAs⟩ := c.store_ok (X := X.withMem M) hK' hA'
      (bs := toBytesLE (xlo X n) 16) (a := eaD X b d) (by simpa using hst)
    rw [toBytesLE_length] at hwr
    exact ⟨_, _, movdqa_std (s := X.withMem M) htf hac (c.dec hK' hin hrip hd) hal hwr, hKs.nx rfl rfl rfl, hAs,
      rip_add hrip M len, rfl, rfl⟩) k'

/-- `ret`, of any length (`repz ret`). -/
theorem s_retL (c : Seg prof F Wl L s₀ o) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hin : CodeIn L e' code) (hj : j < code.length)
    (hrip : X.cpu.rip = e'.add j) {len : Nat} (hd : Dec prof.feat code j (FV7z.mk .ret 64 [] len))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k' : ContG prof F Wl L s₀ o gev gP gE V fun Y => Y.cpu.rip = e₂.add j₂ ∧
      Y.cpu.gpr = X.cpu.gpr.set 4 (X.cpu.gpr.rsp + 8)) :
    GoG prof L o gev gP gE X t :=
  c.next hK hA hin hj hrip (fun M hK' hA' htf hac => by
    obtain ⟨hrd, hv⟩ := c.load_ok (X := X.withMem M) hK' hA' hl
    have hca := ((c.codeAt hK' hin₂) j₂ h₂).1
    have hw : ofBytesLE 64 (readBytes (X.withMem M).proc.mm.mem (X.withMem M).cpu.gpr.rsp 8) = e₂.add j₂ := by
      exact (congrArg (ofBytesLE 64) hv).trans hra
    exact ⟨_, _, FV7z.ret_len htf hac (c.dec hK' hin hrip hd) (by rw [hK'.thread]; exact c.ready.plain.2.2.1)
      hw hca hrd, hK'.upd rfl rfl rfl, hA', rfl, rfl⟩) k'

end FV7z.Fn.Seg
