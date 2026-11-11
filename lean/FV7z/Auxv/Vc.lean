import FV7z.Auxv.Inv
import FV7z.Lemmas.Wp
/-!
# The conditions of `_dl_aux_init`'s cut points (PLAN.md G3, startup)

For each of the 31 cut points: from its invariant (`Inv.lean`) the condition `W_*` of the code from it (`Cuts.lean`),
with at each exit the invariant there and a smaller measure, `Ret` at the `ret`, and at the offset the proof does not
go past (1040: the vector is empty) a contradiction with the precondition. `vcAll`: these together, for `Seg.cfg`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.AuxInit
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.Auxv
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {m n : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}
  {v : Vars}

/-! ## Addresses -/

theorem add_k (a : Addr) (j k : Nat) : a.add j + BitVec.ofNat 64 k = a.add (j + k) := by
  simp only [Addr.add]; bv_omega

/-- The red zone's slots, from `rsp`. -/
theorem e0 (K : Ctx) : K.sp + 56#64 + 18446744073709551560#64 = K.sp := by bv_omega
theorem e8 (K : Ctx) : K.sp + 56#64 + 18446744073709551568#64 = K.sp + 8#64 := by bv_omega
theorem e16 (K : Ctx) : K.sp + 56#64 + 18446744073709551576#64 = K.sp + 16#64 := by bv_omega
theorem e24 (K : Ctx) : K.sp + 56#64 + 18446744073709551584#64 = K.sp + 24#64 := by bv_omega
theorem e32 (K : Ctx) : K.sp + 56#64 + 18446744073709551592#64 = K.sp + 32#64 := by bv_omega
theorem e34 (K : Ctx) : K.sp + 56#64 + 18446744073709551594#64 = K.sp + 34#64 := by bv_omega
theorem e35 (K : Ctx) : K.sp + 56#64 + 18446744073709551595#64 = K.sp + 35#64 := by bv_omega
theorem e36 (K : Ctx) : K.sp + 56#64 + 18446744073709551596#64 = K.sp + 36#64 := by bv_omega
theorem e40 (K : Ctx) : K.sp + 56#64 + 18446744073709551600#64 = K.sp + 40#64 := by bv_omega
theorem e48 (K : Ctx) : K.sp + 56#64 + 18446744073709551608#64 = K.sp + 48#64 := by bv_omega
theorem e52 (K : Ctx) : K.sp + 56#64 + 18446744073709551612#64 = K.sp + 52#64 := by bv_omega
theorem e53 (K : Ctx) : K.sp + 56#64 + 18446744073709551613#64 = K.sp + 53#64 := by bv_omega
theorem e54 (K : Ctx) : K.sp + 56#64 + 18446744073709551614#64 = K.sp + 54#64 := by bv_omega
theorem e55 (K : Ctx) : K.sp + 56#64 + 18446744073709551615#64 = K.sp + 55#64 := by bv_omega

/-! ## Loads after stores into the frame -/

theorem rd_ff (hK : K.Ok) (V : Addr → Byte) (c' c n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 104)
    (h2 : c + n ≤ 104) (h : c' + bs.length ≤ c ∨ c + n ≤ c') :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.sp + BitVec.ofNat 64 c) n) := by
  have := hK.hsp
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

/-- The same with the store at the frame's first byte. -/
theorem rd_f0f (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (h2 : c + n ≤ 104) (h : bs.length ≤ c) :
    List.map (Vst V K.sp bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.sp + BitVec.ofNat 64 c) n) := by
  have := hK.hsp
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

/-- The same with the load at the frame's first byte. -/
theorem rd_ff0 (hK : K.Ok) (V : Addr → Byte) (c' n : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 104)
    (h : n ≤ c') :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs K.sp n) = List.map V (byteAddrs K.sp n) := by
  have := hK.hsp
  exact rd_Vst _ _ _ _ _ (by bv_omega) (by bv_omega) (by bv_omega)

theorem rd_fself (hK : K.Ok) (V : Addr → Byte) (c n : Nat) (bs : List Byte) (hn : bs.length = n) (h : c + n ≤ 104) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c) bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) = bs := by
  have := hK.hsp
  exact rd_Vst_self _ _ _ hn (by bv_omega)

theorem rd_f0self (hK : K.Ok) (V : Addr → Byte) (n : Nat) (bs : List Byte) (hn : bs.length = n) (h : n ≤ 104) :
    List.map (Vst V K.sp bs) (byteAddrs K.sp n) = bs := by
  have := hK.hsp
  exact rd_Vst_self _ _ _ hn (by omega)

/-- A load outside the frame after a store into the frame. -/
theorem rd_fo (hK : K.Ok) {a : Addr} {n : Nat} (hf : a.toNat + n ≤ 2 ^ 64) (h : Off K a.toNat n)
    (V : Addr → Byte) (c' : Nat) (bs : List Byte) (h1 : c' + bs.length ≤ 104) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs a n) = List.map V (byteAddrs a n) := by
  have := hK.hsp
  simp only [Off] at h
  exact rd_Vst _ _ _ _ _ (by bv_omega) hf (by bv_omega)

theorem rd_f0o (hK : K.Ok) {a : Addr} {n : Nat} (hf : a.toNat + n ≤ 2 ^ 64) (h : Off K a.toNat n)
    (V : Addr → Byte) (bs : List Byte) (h1 : bs.length ≤ 104) :
    List.map (Vst V K.sp bs) (byteAddrs a n) = List.map V (byteAddrs a n) := by
  have := hK.hsp
  simp only [Off] at h
  exact rd_Vst _ _ _ _ _ (by omega) hf (by omega)

/-- A store into the frame: where it may store. -/
theorem Env.wr (hE : Env K F Wl) (hK : K.Ok) (c n : Nat) (hc : c + n ≤ 104) :
    ∀ i, i < n → Foot Wl ((K.sp + BitVec.ofNat 64 c).add i) := by
  intro i hi
  have := hK.hsp
  have e := toNat_add_of_fits (a := K.sp + BitVec.ofNat 64 c) hi (by bv_omega)
  exact hE.fr _ (by bv_omega) (by bv_omega)

theorem Env.wr0 (hE : Env K F Wl) (hK : K.Ok) (n : Nat) (hc : n ≤ 104) :
    ∀ i, i < n → Foot Wl (K.sp.add i) := by
  intro i hi
  have := hK.hsp
  have e := toNat_add_of_fits (a := K.sp) hi (by omega)
  exact hE.fr _ (by omega) (by omega)

/-- A store into the frame keeps the bytes outside it. -/
theorem Out.st (hO : Out K V) (hK : K.Ok) {a : Addr} {bs : List Byte} (c : Nat) (ha : a.toNat = K.sp.toNat + c)
    (hc : c + bs.length ≤ 104) : Out K (Vst V a bs) := by
  have hsp := hK.hsp
  intro x hx hx'
  rw [Vst_out _ _ _ _ (by omega) (by simp only [InFr] at hx; omega)]
  exact hO x hx hx'

/-- `n` bytes outside the frame and `_dl_auxv` are those at the call. -/
theorem Out.rd (hO : Out K V) {a : Addr} {n : Nat} (hf : a.toNat + n ≤ 2 ^ 64) (h : Off K a.toNat n)
    (hx : a.toNat + n ≤ 0x7a8540 ∨ 0x7a8548 ≤ a.toNat) :
    List.map V (byteAddrs a n) = List.map K.V0 (byteAddrs a n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits hj hf
  simp only [Off] at h
  exact hO _ (by simp only [InFr]; omega) (by omega)

/-! ## The vector -/

/-- The `n`-th entry's words lie in the vector. -/
theorem Ctx.Ok.at (hK : K.Ok) {n c : Nat} (hn : n ≤ K.N) (hc : c + 8 ≤ 16 * (K.N - n) + 8) :
    (K.av.add (16 * n + c)).toNat = K.av.toNat + (16 * n + c) := by
  have := hK.hfit
  rw [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A word of the vector, read. -/
theorem Out.vec (hO : Out K V) (hK : K.Ok) {n c : Nat} (hn : n ≤ K.N) (hc : c + 8 ≤ 16 * (K.N - n) + 8) :
    List.map V (byteAddrs (K.av.add (16 * n + c)) 8) = List.map K.V0 (byteAddrs (K.av.add (16 * n + c)) 8) := by
  have e := hK.at hn hc
  have h1 := hK.hfit
  have h2 := hK.aAv
  have h3 := hK.xAv
  simp only [Off] at h2
  exact hO.rd (by omega) (by simp only [Off]; omega) (by omega)

/-- Where a word of the vector may be read. -/
theorem Env.rvec (hE : Env K F Wl) (hK : K.Ok) {n c : Nat} (hn : n ≤ K.N) (hc : c + 8 ≤ 16 * (K.N - n) + 8) :
    ∀ i, i < 8 → Foot F.data ((K.av.add (16 * n + c)).add i) := by
  intro i hi
  have e := hK.at hn hc
  have h1 := hK.hfit
  have e' := toNat_add_of_fits (a := K.av.add (16 * n + c)) hi (by omega)
  exact hE.vec _ (by omega) (by omega)

/-! ## The low bytes of a word -/

theorem shl_ofBytesLE_append (v : Nat) : ∀ (l r : List Byte) (k : Nat), v ≤ 8 * l.length + k →
    (ofBytesLE v (l ++ r)) <<< k = (ofBytesLE v l) <<< k
  | [], r, k, h => by
    have hk : v ≤ k := by simpa using h
    rw [BitVec.shiftLeft_eq_zero hk, BitVec.shiftLeft_eq_zero hk]
  | b :: l, r, k, h => by
    simp only [List.cons_append, ofBytesLE, BitVec.shiftLeft_or_distrib]
    rw [← BitVec.shiftLeft_add, ← BitVec.shiftLeft_add, shl_ofBytesLE_append v l r (8 + k) (by simp at h; omega)]

theorem ofBytesLE_append (v : Nat) (l r : List Byte) (h : v ≤ 8 * l.length) : ofBytesLE v (l ++ r) = ofBytesLE v l := by
  simpa using shl_ofBytesLE_append v l r 0 (by omega)

theorem setWidth_ofBytesLE {v w : Nat} (h : v ≤ w) : ∀ l : List Byte, (ofBytesLE w l).setWidth v = ofBytesLE v l
  | [] => by simp [ofBytesLE]
  | b :: l => by
    simp only [ofBytesLE, BitVec.setWidth_or]
    rw [← setWidth_ofBytesLE h l]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]
    · apply BitVec.eq_of_toNat_eq
      simp [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h), Nat.mul_mod]

/-- The 4 bytes at `a` are the low half of the 8. -/
theorem rd32_lo (V : Addr → Byte) (a : Addr) : rdd(V, a) = (rdq(V, a)).setWidth 32 := by
  rw [setWidth_ofBytesLE (by decide)]
  exact (ofBytesLE_append 32 (List.map V (byteAddrs a 4)) (List.map V [a.add 4, a.add 5, a.add 6, a.add 7])
    (by simp [byteAddrs])).symm

/-- The 2 bytes at `a` are the low quarter of the 8. -/
theorem rd16_lo (V : Addr → Byte) (a : Addr) : rdw(V, a) = (rdq(V, a)).setWidth 16 := by
  rw [setWidth_ofBytesLE (by decide)]
  exact (ofBytesLE_append 16 (List.map V (byteAddrs a 2))
    (List.map V [a.add 2, a.add 3, a.add 4, a.add 5, a.add 6, a.add 7]) (by simp [byteAddrs])).symm

/-! ## The variables in memory -/

/-- Bytes at a fixed address outside the frame and `_dl_auxv`. -/
theorem Out.rdc (hO : Out K V) (a n : Nat) (ha : a + n ≤ 2 ^ 64) (h : Off K a n)
    (hx : a + n ≤ 0x7a8540 ∨ 0x7a8548 ≤ a) :
    List.map V (byteAddrs (BitVec.ofNat 64 a) n) = List.map K.V0 (byteAddrs (BitVec.ofNat 64 a) n) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
    exact hO.rd (by omega) (by rw [e]; exact h) (by omega)

/-- In the loop, the variables in memory are those at the call. -/
theorem Out.gl (hO : Out K V) (hK : K.Ok) : Gl V (K.vs 0) :=
  ⟨by rw [hO.rdc 0x7933d8 8 (by decide) hK.oPs (by decide)]; exact hK.hgl.pagesize,
   by rw [hO.rdc 0x7a85c0 4 (by decide) hK.oCk (by decide)]; exact hK.hgl.clktck,
   by rw [hO.rdc 0x7a8580 8 (by decide) hK.oPh (by decide)]; exact hK.hgl.phdr,
   by rw [hO.rdc 0x7a8598 8 (by decide) hK.oPn (by decide)]; exact hK.hgl.phnum,
   by rw [hO.rdc 0x7a8548 8 (by decide) hK.oPl (by decide)]; exact hK.hgl.platform,
   by rw [hO.rdc 0x7a4ac8 8 (by decide) hK.oHw (by decide)]; exact hK.hgl.hwcap,
   by rw [hO.rdc 0x7a4ac0 8 (by decide) hK.oH2 (by decide)]; exact hK.hgl.hwcap2,
   by rw [hO.rdc 0x7a8508 8 (by decide) hK.oSy (by decide)]; exact hK.hgl.sysinfoDso,
   by rw [hO.rdc 0x7933cc 2 (by decide) hK.oFp (by decide)]; exact hK.hgl.fpuControl,
   by rw [hO.rdc 0x791ce0 4 (by decide) hK.oSe (by decide)]; exact hK.hgl.secure,
   by rw [hO.rdc 0x7a85c4 4 (by decide) hK.oDe (by decide)]; exact hK.hgl.decided,
   by rw [hO.rdc 0x791ca0 8 (by decide) hK.oRa (by decide)]; exact hK.hgl.random⟩

/-- The bytes outside the frame and `_dl_auxv` are outside the frame, `_dl_auxv` and the variables. -/
theorem Out.outG (h : Out K V) : OutG K V := by
  intro a hf hg
  refine h a hf ?_
  rcases Nat.lt_or_ge a.toNat 0x7a8540 with h1 | h1
  · exact Or.inl h1
  · rcases Nat.lt_or_ge a.toNat 0x7a8548 with h2 | h2
    · exact absurd ⟨⟨0x7a8540, 8⟩, .head _, ⟨h1, h2⟩⟩ hg
    · exact Or.inr h2

/-- The loop's end. -/
theorem Lp.ex (hK : K.Ok) (h : Lp K K.N g V) : Ex K (K.vs 0) g V :=
  ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.gl hK, ⟨h.2.2.2.2.2.1, Out.outG h.2.2.2.2.1⟩, h.2.2.2.2.2.2 hK.hsn⟩

/-! ## Stores into the frame in the loop -/

/-- A store into the frame keeps the bytes outside it and `_dl_auxv`. -/
theorem keep (hK : K.Ok) (h : Out K V ∧ rdq(V, 0x7a8540#64) = K.av) (c : Nat) (bs : List Byte)
    (hc : c + bs.length ≤ 104) :
    Out K (Vst V (K.sp + BitVec.ofNat 64 c) bs) ∧ rdq(Vst V (K.sp + BitVec.ofNat 64 c) bs, 0x7a8540#64) = K.av := by
  have := hK.hsp
  refine ⟨h.1.st hK c (by bv_omega) hc, ?_⟩
  rw [rd_fo hK (a := 0x7a8540#64) (n := 8) (by decide) hK.oAx _ _ _ hc]
  exact h.2

theorem keep0 (hK : K.Ok) (h : Out K V ∧ rdq(V, 0x7a8540#64) = K.av) (bs : List Byte) (hc : bs.length ≤ 104) :
    Out K (Vst V K.sp bs) ∧ rdq(Vst V K.sp bs, 0x7a8540#64) = K.av := by
  refine ⟨h.1.st hK 0 (by omega) (by omega), ?_⟩
  rw [rd_f0o hK (a := 0x7a8540#64) (n := 8) (by decide) hK.oAx _ _ hc]
  exact h.2

/-- The fields of `RF` after stores into the frame: those stored, and the others as before. -/
macro "rf_tac" hK:ident hF:ident : tactic => `(tactic|
  (constructor <;>
    (try simp only [rd_ff $hK, rd_ff0 $hK, rd_f0f $hK, rd_fself $hK, rd_f0self $hK, toBytesLE_length, Nat.reduceAdd,
      Nat.reduceMul, Nat.reduceLeDiff, true_or, or_true, ofBytesLE_toBytesLE, BitVec.reduceEq, false_imp_iff,
      and_self]) <;>
    first
    | done | with_reducible exact RF.platform $hF | with_reducible exact RF.hwcap $hF
    | with_reducible exact RF.hwcap2 $hF | with_reducible exact RF.sysinfo $hF | with_reducible exact RF.fpu $hF
    | with_reducible exact RF.secure $hF | with_reducible exact RF.random $hF | with_reducible exact RF.decided $hF
    | with_reducible exact RF.fHwcap2 $hF | with_reducible exact RF.fFpu $hF | with_reducible exact RF.fHwcap $hF
    | with_reducible exact RF.fSysinfo $hF | with_reducible exact RF.fSecure $hF
    | with_reducible exact RF.fRandom $hF | with_reducible exact RF.v0 $hF | with_reducible exact RF.v1 $hF
    | with_reducible exact RF.v2 $hF | with_reducible exact RF.v3 $hF | with_reducible exact RF.v4 $hF
    | with_reducible exact RF.v5 $hF))

theorem RF.set_hwcap (hK : K.Ok) (hF : RF K v V) (x : BitVec 64) :
    RF K { v with hwcap := x } (Vst (Vst V (K.sp + 52#64) (toBytesLE (1#8) 1)) (K.sp + 8#64) (toBytesLE x 8)) := by
  rf_tac hK hF

theorem RF.set_hwcap2 (hK : K.Ok) (hF : RF K v V) (x : BitVec 64) :
    RF K { v with hwcap2 := x } (Vst (Vst V (K.sp + 34#64) (toBytesLE (1#8) 1)) (K.sp + 16#64) (toBytesLE x 8)) := by
  rf_tac hK hF

theorem RF.set_sysinfo (hK : K.Ok) (hF : RF K v V) (x : BitVec 64) :
    RF K { v with sysinfoDso := x }
      (Vst (Vst V (K.sp + 53#64) (toBytesLE (1#8) 1)) (K.sp + 24#64) (toBytesLE x 8)) := by
  rf_tac hK hF

theorem RF.set_random (hK : K.Ok) (hF : RF K v V) (x : BitVec 64) :
    RF K { v with random := x } (Vst (Vst V (K.sp + 55#64) (toBytesLE (1#8) 1)) (K.sp + 40#64) (toBytesLE x 8)) := by
  rf_tac hK hF

theorem RF.set_fpu (hK : K.Ok) (hF : RF K v V) (x : BitVec 16) :
    RF K { v with fpuControl := x }
      (Vst (Vst V (K.sp + 35#64) (toBytesLE (1#8) 1)) (K.sp + 32#64) (toBytesLE x 2)) := by
  rf_tac hK hF

theorem RF.set_secure (hK : K.Ok) (hF : RF K v V) (x : BitVec 32) :
    RF K { v with secure := x, decided := 1 }
      (Vst (Vst (Vst V (K.sp + 54#64) (toBytesLE (1#8) 1)) (K.sp + 48#64) (toBytesLE (1#32) 4)) (K.sp + 36#64)
        (toBytesLE x 4)) := by
  rf_tac hK hF

theorem RF.set_platform (hK : K.Ok) (hF : RF K v V) (x : BitVec 64) :
    RF K { v with platform := x } (Vst V K.sp (toBytesLE x 8)) := by
  rf_tac hK hF

/-! ## The loop -/

/-- After an entry: to the next, or the vector's end. -/
theorem next (hK : K.Ok) {Q : Post} (hn : n < K.N) {x : BitVec 64}
    (hx : x = rdq(K.V0, K.av.add (16 * n + 16))) {g' : Gprs} {V' : Addr → Byte} (hL : Lp K (n + 1) g' V')
    (hdi : g'.rdi = K.av.add (16 * n + 16)) (hrax : g'.rax = x) (hm : 3 * (K.N - n) + 300 ≤ m)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') (fl1 fl2 : Rflags) :
    ((!(x &&& x == 0)) = true → Q 216 g' fl1 V') ∧ ((!(x &&& x == 0)) = false → Q 272 g' fl2 V') := by
  subst hx
  have e16 : 16 * n + 16 = 16 * (n + 1) := by omega
  rw [e16] at hdi hrax ⊢
  rcases Nat.lt_or_ge (n + 1) K.N with h | h
  · rw [hK.hty _ h] at hrax ⊢
    have hz := hK.hnz _ h
    refine ⟨fun _ => h216 _ _ _ _ (by omega) ⟨n + 1, h, hL, hdi, hrax, rfl⟩, fun hc => ?_⟩
    simp at hc
    exact absurd hc hz
  · have hN : n + 1 = K.N := by omega
    rw [hN, hK.hend]
    rw [hN] at hL
    refine ⟨fun hc => ?_, fun _ => h272 _ _ _ _ (by omega) ⟨hL.ex hK, rfl⟩⟩
    simp at hc

/-- The length of what a store stores, for its place in the frame. -/
macro "ln" : tactic => `(tactic| (simp only [toBytesLE_length]; decide))

/-- The registers of `RR` and the variables they hold, kept. -/
theorem RR.mv {g g' : Gprs} {v v' : Vars} (h : RR K v g) (e10 : g'.r10 = g.r10) (e9 : g'.r9 = g.r9)
    (ebp : g'.rbp = g.rbp) (e11 : g'.r11 = g.r11) (e13 : g'.r13 = g.r13) (ebx : g'.rbx = g.rbx)
    (e15 : g'.r15 = g.r15) (e12 : g'.r12 = g.r12) (e14 : g'.r14 = g.r14) (ps : v'.pagesize = v.pagesize)
    (ck : v'.clktck = v.clktck) (ph : v'.phdr = v.phdr) (pn : v'.phnum = v.phnum)
    (pl : v'.platform = v.platform) : RR K v' g' :=
  ⟨by rw [e10, ps]; exact h.r10, by rw [e9, ps]; exact h.f9, by rw [ebp, ck]; exact h.rbp,
    by rw [e11, ck]; exact h.f11, by rw [e13, ph]; exact h.r13, by rw [ebx, ph]; exact h.fbx,
    by rw [e15, pn]; exact h.r15, by rw [e12, pn]; exact h.f12, by rw [e14, pl]; exact h.f14⟩

/-- `AT_SECURE` seen, one entry on. -/
theorem sec_next (hK : K.Ok) {P : Prop} (hs : K.sn < n → P) (ht : K.ty n ≠ 23) : K.sn < n + 1 → P := by
  intro h
  rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
  · exact hs h
  · exact absurd (h ▸ hK.hsec) ht

/-- What the code reads of the vector at its `n`-th entry: the value, and the next entry's type, also after stores
into the frame. -/
theorem vecAt (hK : K.Ok) (hE : Env K F Wl) (hO : Out K V) (hn : n < K.N) :
    rdq(V, K.av.add (16 * n + 8)) = K.val n ∧
    (∀ i, i < 8 → Foot F.data ((K.av.add (16 * n + 8)).add i)) ∧
    (∀ i, i < 8 → Foot F.data ((K.av.add (16 * n + 16)).add i)) ∧
    List.map V (byteAddrs (K.av.add (16 * n + 16)) 8) = List.map K.V0 (byteAddrs (K.av.add (16 * n + 16)) 8) ∧
    (∀ (V : Addr → Byte) (c' : Nat) (bs : List Byte), c' + bs.length ≤ 104 →
      List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs (K.av.add (16 * n + 16)) 8) =
        List.map V (byteAddrs (K.av.add (16 * n + 16)) 8)) ∧
    (∀ (V : Addr → Byte) (bs : List Byte), bs.length ≤ 104 →
      List.map (Vst V K.sp bs) (byteAddrs (K.av.add (16 * n + 16)) 8) =
        List.map V (byteAddrs (K.av.add (16 * n + 16)) 8)) := by
  have hle := Nat.le_of_lt hn
  have e := hK.at (c := 16) hle (by omega)
  have h1 := hK.hfit
  have h2 := hK.aAv
  simp only [Off] at h2
  refine ⟨by rw [hO.vec hK hle (by omega)]; exact hK.hval n hn, hE.rvec hK hle (by omega), hE.rvec hK hle (by omega),
    hO.vec hK hle (by omega), rd_fo hK (by omega) (by simp only [Off]; omega),
    rd_f0o hK (by omega) (by simp only [Off]; omega)⟩

theorem sw16 (x : BitVec 64) : ((x.setWidth 16).setWidth 32).setWidth 16 = x.setWidth 16 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem one8 : ¬ (BitVec.setWidth 64 1#32).setWidth 8 = 0#8 := by decide
theorem ff32 : (BitVec.setWidth 64 4294967295#32).setWidth 32 = 4294967295#32 := by decide
theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]

theorem sw16b (x : BitVec 16) : (x.setWidth 32).setWidth 16 = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem sw8 (x : BitVec 64) : ((x.setWidth 32).setWidth 64).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

/-- `or ecx, k` after `AT_SECURE`. -/
theorem or_ff (c : BitVec 64) (k : BitVec 32) (h : c.setWidth 32 = 0xffffffff#32) :
    (BitVec.setWidth 64 (c.setWidth 32 ||| k)).setWidth 32 = 0xffffffff#32 := by
  have e : (4294967295#32 : BitVec 32) = BitVec.allOnes 32 := by decide
  rw [sw32, h, e, BitVec.allOnes_or]

/-- The frame's variables, kept. -/
theorem RF.mv {v v' : Vars} (h : RF K v V) (pl : v'.platform = v.platform) (hw : v'.hwcap = v.hwcap)
    (h2 : v'.hwcap2 = v.hwcap2) (sy : v'.sysinfoDso = v.sysinfoDso) (fp : v'.fpuControl = v.fpuControl)
    (se : v'.secure = v.secure) (ra : v'.random = v.random) (de : v'.decided = v.decided) : RF K v' V :=
  ⟨by rw [pl]; exact h.platform, by rw [hw]; exact h.hwcap, by rw [h2]; exact h.hwcap2, by rw [sy]; exact h.sysinfo,
    by rw [fp]; exact h.fpu, by rw [se]; exact h.secure, by rw [ra]; exact h.random, by rw [de]; exact h.decided,
    by rw [h2]; exact h.fHwcap2, by rw [fp]; exact h.fFpu, by rw [hw]; exact h.fHwcap, by rw [sy]; exact h.fSysinfo,
    by rw [se, de]; exact h.fSecure, by rw [ra]; exact h.fRandom, h.v0, h.v1, h.v2, h.v3, h.v4, h.v5⟩

theorem vc_704 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 16 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_704 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  have hv : K.vs (n + 1) = { K.vs n with hwcap := K.val n } := by rw [hK.hvs n hn, hty]; rfl
  have hp := keep hK (keep hK ⟨hO, hax⟩ 52 (toBytesLE (1#8) 1) (by ln)) 8 (toBytesLE (K.val n) 8) (by ln)
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  wpx [W_704, W_734, o36, e52, e8, add_k, a8, a16, s16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f8, hE.wr hK 52 1 (by decide), hE.wr hK 8 8 (by decide), f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by rw [hv]; exact hF.set_hwcap hK _, hp.1, hp.2, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_496 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 33 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_496 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  have hv : K.vs (n + 1) = { K.vs n with sysinfoDso := K.val n } := by rw [hK.hvs n hn, hty]; rfl
  have hp := keep hK (keep hK ⟨hO, hax⟩ 53 (toBytesLE (1#8) 1) (by ln)) 24 (toBytesLE (K.val n) 8) (by ln)
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  wpx [W_496, W_526, o31, e53, e24, add_k, a8, a16, s16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f8, hE.wr hK 53 1 (by decide), hE.wr hK 24 8 (by decide), f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by rw [hv]; exact hF.set_sysinfo hK _, hp.1, hp.2, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_536 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 26 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_536 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  have hv : K.vs (n + 1) = { K.vs n with hwcap2 := K.val n } := by rw [hK.hvs n hn, hty]; rfl
  have hp := keep hK (keep hK ⟨hO, hax⟩ 34 (toBytesLE (1#8) 1) (by ln)) 16 (toBytesLE (K.val n) 8) (by ln)
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  wpx [W_536, W_566, o32, e34, e16, add_k, a8, a16, s16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f8, hE.wr hK 34 1 (by decide), hE.wr hK 16 8 (by decide), f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by rw [hv]; exact hF.set_hwcap2 hK _, hp.1, hp.2, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_624 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 18 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_624 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  have hv : K.vs (n + 1) = { K.vs n with fpuControl := (K.val n).setWidth 16 } := by rw [hK.hvs n hn, hty]; rfl
  have hp := keep hK (keep hK ⟨hO, hax⟩ 35 (toBytesLE (1#8) 1) (by ln)) 32 (toBytesLE ((K.val n).setWidth 16) 2) (by ln)
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have a2 : rdw(V, K.av.add (16 * n + 8)) = (K.val n).setWidth 16 := by rw [rd16_lo, a8]
  wpx [W_624, W_654, o34, e35, e32, add_k, a2, a16, s16, sw16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun i hi => f8 i (by omega), hE.wr hK 35 1 (by decide), hE.wr hK 32 2 (by decide), f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by rw [hv]; exact hF.set_fpu hK _, hp.1, hp.2, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_576 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 23 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_576 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  have hv : K.vs (n + 1) = { K.vs n with secure := (K.val n).setWidth 32, decided := 1 } := by
    rw [hK.hvs n hn, hty]; rfl
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have a4 : rdd(V, K.av.add (16 * n + 8)) = (K.val n).setWidth 32 := by rw [rd32_lo, a8]
  have hp := keep hK (keep hK (keep hK ⟨hO, hax⟩ 54 (toBytesLE (1#8) 1) (by ln)) 48 (toBytesLE (1#32) 4) (by ln)) 36
    (toBytesLE ((K.val n).setWidth 32) 4) (by ln)
  wpx [W_576, W_617, o33, e54, e48, e36, add_k, a4, a16, s16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun i hi => f8 i (by omega), hE.wr hK 54 1 (by decide), hE.wr hK 48 4 (by decide),
    hE.wr hK 36 4 (by decide), f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by rw [hv]; exact hF.set_secure hK _, hp.1, hp.2, fun _ => ff32⟩

theorem vc_744 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 15 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_744 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  have hv : K.vs (n + 1) = { K.vs n with platform := K.val n } := by rw [hK.hvs n hn, hty]; rfl
  have hp := keep0 hK ⟨hO, hax⟩ (toBytesLE (K.val n) 8) (by ln)
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  wpx [W_744, W_775, o37, e0, add_k, a8, a16, s16', Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f8, hE.wr0 hK 8 (by decide), f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, hR.rbp, hR.f11, hR.r13, hR.fbx, hR.r15, hR.f12,
      fun h => absurd h one8⟩,
    by rw [hv]; exact hF.set_platform hK _, hp.1, hp.2, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_240 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 25 K m g V)
    (h256 : ∀ m' g' fl V', m' < m → I256 K m' g' V' → Q 256 g' fl V') :
    W_240 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  have hv : K.vs (n + 1) = { K.vs n with random := K.val n } := by rw [hK.hvs n hn, hty]; rfl
  have hp := keep hK (keep hK ⟨hO, hax⟩ 55 (toBytesLE (1#8) 1) (by ln)) 40 (toBytesLE (K.val n) 8) (by ln)
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  wpx [W_240, o4, e55, e40, add_k, a8, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f8, hE.wr hK 55 1 (by decide), hE.wr hK 40 8 (by decide), h256 _ _ _ _ (by omega) ⟨n, hn, ?_, rfl, rfl⟩⟩
  exact ⟨rfl, rfl, by rw [hv]; exact hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl,
    by rw [hv]; exact hF.set_random hK _, hp.1, hp.2, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_664 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 17 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_664 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = { K.vs n with clktck := (K.val n).setWidth 32 } := by rw [hK.hvs n hn, hty]; rfl
  have a4 : rdd(V, K.av.add (16 * n + 8)) = (K.val n).setWidth 32 := by rw [rd32_lo, a8]
  wpx [W_664, W_690, o35, add_k, a4, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun i hi => f8 i (by omega), f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, sw32 _, fun h => absurd h one8, hR.r13, hR.fbx, hR.r15, hR.f12,
      hR.f14⟩,
    by rw [hv]; exact hF.mv rfl rfl rfl rfl rfl rfl rfl rfl, hO, hax, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_960 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 5 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_960 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = { K.vs n with phnum := K.val n } := by rw [hK.hvs n hn, hty]; rfl
  wpx [W_960, W_987, o43, add_k, a8, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f8, f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, hR.rbp, hR.f11, hR.r13, hR.fbx, rfl, fun h => absurd h one8,
      hR.f14⟩,
    by rw [hv]; exact hF.mv rfl rfl rfl rfl rfl rfl rfl rfl, hO, hax, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_992 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 3 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_992 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = { K.vs n with phdr := K.val n } := by rw [hK.hvs n hn, hty]; rfl
  wpx [W_992, W_1018, o44, add_k, a8, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f8, f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, hR.rbp, hR.f11, rfl, fun h => absurd h one8, hR.r15, hR.f12,
      hR.f14⟩,
    by rw [hv]; exact hF.mv rfl rfl rfl rfl rfl rfl rfl rfl, hO, hax, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_912 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 6 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_912 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = if K.val n = 0 then K.vs n else { K.vs n with pagesize := K.val n } := by
    rw [hK.hvs n hn, hty]; rfl
  by_cases hz : K.val n = 0
  · have hc : (!(K.val n &&& K.val n == 0)) = false := by simp [hz]
    replace hv : K.vs (n + 1) = K.vs n := hv.trans (ite_pos' hz)
    wpx [W_912, W_949, o42, add_k, a8, a16, hc, Bool.false_eq_true, ite_false, Nat.reduceAdd, Nat.reduceLeDiff]
    refine ⟨f8, fun _ => ⟨f16, fun af => ?_⟩⟩
    refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
    exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, fun h => hR.f9 (by rw [← sw8]; exact h), hR.rbp, hR.f11, hR.r13,
        hR.fbx, hR.r15, hR.f12, hR.f14⟩,
      by rw [hv]; exact hF, hO, hax, sec_next hK hs (by rw [hty]; decide)⟩
  · have hc : (!(K.val n &&& K.val n == 0)) = true := by simpa using hz
    replace hv : K.vs (n + 1) = { K.vs n with pagesize := K.val n } := hv.trans (ite_neg' hz)
    wpx [W_912, W_949, o42, add_k, a8, a16, hc, ite_true, Nat.reduceAdd, Nat.reduceLeDiff]
    refine ⟨f8, fun _ => ⟨f16, fun af => ?_⟩⟩
    refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
    exact ⟨rfl, rfl, by rw [hv]; exact ⟨rfl, fun h => absurd h one8, hR.rbp, hR.f11, hR.r13, hR.fbx, hR.r15,
        hR.f12, hR.f14⟩,
      by rw [hv]; exact hF.mv rfl rfl rfl rfl rfl rfl rfl rfl, hO, hax, sec_next hK hs (by rw [hty]; decide)⟩

theorem vc_880 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 11 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_880 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = K.vs n := by rw [hK.hvs n hn, hty]; rfl
  wpx [W_880, W_904, o41, Op.xorm, add_k, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun i hi => f8 i (by omega), fun _ => ⟨f16, fun _ af => ?_⟩⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, hR.rbp, hR.f11, hR.r13, hR.fbx, hR.r15, hR.f12, hR.f14⟩,
    by rw [hv]; exact hF, hO, hax, fun h => or_ff _ _ (sec_next hK hs (by rw [hty]; decide) h)⟩

theorem vc_848 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 12 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_848 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = K.vs n := by rw [hK.hvs n hn, hty]; rfl
  wpx [W_848, W_872, o40, Op.xorm, add_k, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun i hi => f8 i (by omega), fun _ => ⟨f16, fun _ af => ?_⟩⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, hR.rbp, hR.f11, hR.r13, hR.fbx, hR.r15, hR.f12, hR.f14⟩,
    by rw [hv]; exact hF, hO, hax, fun h => or_ff _ _ (sec_next hK hs (by rw [hty]; decide) h)⟩

theorem vc_816 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 13 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_816 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = K.vs n := by rw [hK.hvs n hn, hty]; rfl
  wpx [W_816, W_839, o39, Op.xorm, add_k, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun i hi => f8 i (by omega), fun _ => ⟨f16, fun _ af => ?_⟩⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, hR.rbp, hR.f11, hR.r13, hR.fbx, hR.r15, hR.f12, hR.f14⟩,
    by rw [hv]; exact hF, hO, hax, fun h => or_ff _ _ (sec_next hK hs (by rw [hty]; decide) h)⟩

theorem vc_784 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Ic 14 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_784 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨rfl, rfl, hR, hF, hO, hax, hs⟩, rfl, hty, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  have hv : K.vs (n + 1) = K.vs n := by rw [hK.hvs n hn, hty]; rfl
  wpx [W_784, W_807, o38, Op.xorm, add_k, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun i hi => f8 i (by omega), fun _ => ⟨f16, fun _ af => ?_⟩⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨rfl, rfl, by rw [hv]; exact ⟨hR.r10, hR.f9, hR.rbp, hR.f11, hR.r13, hR.fbx, hR.r15, hR.f12, hR.f14⟩,
    by rw [hv]; exact hF, hO, hax, fun h => or_ff _ _ (sec_next hK hs (by rw [hty]; decide) h)⟩

theorem vc_256 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I256 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V')
    (h272 : ∀ m' g' fl V', m' < m → E 272 (fun v0 _ => v0) K m' g' V' → Q 272 g' fl V') :
    W_256 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, ⟨h1, h2, hR, hF, hO, hax, hs⟩, rfl, rfl⟩ := h
  obtain ⟨a8, f8, f16, a16, s16, s16'⟩ := vecAt hK hE hO hn
  wpx [W_256, W_269, o5, o6, add_k, a16, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨f16, fun af => ?_⟩
  refine next hK hn rfl ?_ rfl rfl (by omega) h216 h272 _ _
  exact ⟨h1, h2, hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hF, hO, hax, hs⟩

/-- A type the `switch` has no case for. -/
theorem step_other (v : Vars) (t x : BitVec 64) (h : 30#64 < t - 3#64) : AuxInit.step v (t, x) = v := by
  simp only [AuxInit.step]
  repeat (rw [ite_neg' (by intro e; rw [e] at h; exact absurd h (by decide))])

/-- Where the table's entries lead. -/
theorem jt_case : ∀ k : Fin 31, (jt k.1).signExtend 64 + 0x6f3660#64 = Addr.add aux_at (aux_cases.getD k.1 0) := by
  decide +kernel

theorem jt_lt : ∀ k : Fin 31, aux_cases.getD k.1 0 < aux.length := by decide +kernel

/-- An entry that changes nothing. -/
theorem Lp.skip (hL : Lp K n g V) (hK : K.Ok) (hn : n < K.N) (hst : AuxInit.step (K.vs n) (K.ty n, K.val n) = K.vs n)
    (h23 : K.ty n ≠ 23) : Lp K (n + 1) g V := by
  obtain ⟨h1, h2, hR, hF, hO, hax, hs⟩ := hL
  have hv : K.vs (n + 1) = K.vs n := by rw [hK.hvs n hn, hst]
  exact ⟨h1, h2, by rw [hv]; exact hR, by rw [hv]; exact hF, hO, hax, sec_next hK hs h23⟩

/-- At the `switch`: the invariant where the table leads for the entry's type. -/
theorem disp (hK : K.Ok) (hn : n < K.N) (hL : Lp K n g V) (hdi : g.rdi = K.av.add (16 * n)) (k : Nat) (hk : k < 31)
    (hty : K.ty n = BitVec.ofNat 64 (k + 3)) :
    ∃ m', m' < 3 * (K.N - n) + 302 ∧ InvT K (aux_cases.getD k 0) m' g V := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 3 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 5 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 6 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 11 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 12 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 13 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 14 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 15 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 16 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 17 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 18 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 23 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 25 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 26 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 300, by omega, show I256 K _ g V from
      ⟨n, hn, hL.skip hK hn (by rw [hty]; rfl) (by rw [hty]; decide), hdi, rfl⟩⟩
  · exact ⟨3 * (K.N - n) + 301, by omega, show Ic 33 K _ g V from ⟨n, hn, hL, hdi, hty, rfl⟩⟩

theorem vc_216 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : I216 K m g V)
    (hq : ∀ ℓ m' g' fl V', m' < m → InvT K ℓ m' g' V' → Q ℓ g' fl V') :
    W_216 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨n, hn, hL, rfl, rfl, rfl⟩ := h
  obtain ⟨rfl, rfl, hR, hF, hO, hax, hs⟩ := hL
  wpx [W_216, W_226, o2, o3, Op.ldsx, Nat.reduceAdd, Nat.reduceLeDiff]
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    have h30 : 30#64 < K.ty n - 3#64 := by bv_omega
    refine hq 256 (3 * (K.N - n) + 300) _ _ _ (by omega) (show I256 K _ _ _ from ⟨n, hn, ?_, rfl, rfl⟩)
    exact Lp.skip ⟨rfl, rfl, hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hF, hO, hax, hs⟩ hK hn
      (step_other _ _ _ h30) (by intro e; rw [e] at h30; exact absurd h30 (by decide))
  · simp only [Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at hc
    have hk31 : (K.ty n - 3#64).toNat < 31 := by
      rcases hc with h | h
      · omega
      · rw [h]; decide
    generalize hk : (K.ty n - 3#64).toNat = k at hk31
    have hty : K.ty n = BitVec.ofNat 64 (k + 3) := by bv_omega
    have ea : 7288416#64 + (K.ty n - 3#64) * 4#64 = Addr.add 0x6f3660#64 (4 * k) := by
      simp only [Addr.add]; bv_omega
    have aJ := hK.aJt
    have et : (Addr.add 0x6f3660#64 (4 * k)).toNat = 0x6f3660 + 4 * k := by simp only [Addr.add]; bv_omega
    have rd : rdd(V, Addr.add 0x6f3660#64 (4 * k)) = jt k := by
      rw [hO.rd (by omega) (by simp only [Off] at aJ ⊢; omega) (by omega)]
      exact hK.hjt k hk31
    rw [ea, rd, jt_case ⟨k, hk31⟩]
    refine ⟨fun i hi => ?_, aux_cases.getD k 0, jt_lt ⟨k, hk31⟩, rfl, ?_⟩
    · have e' := toNat_add_of_fits (a := Addr.add 0x6f3660#64 (4 * k)) hi (by omega)
      exact hE.tab _ (by omega) (by omega)
    · have hL' : Lp K n ⟨aux_at.add (aux_cases.getD k 0), rcx, 7288416#64, rbx, K.sp + 56#64, rbp, rsi,
          K.av.add (16 * n), r8, r9, r10, r11, r12, r13, r14, r15⟩ V :=
        ⟨rfl, rfl, hR.mv rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl, hF, hO, hax, hs⟩
      obtain ⟨m', hm', hi⟩ := disp hK hn hL' rfl k hk31 hty
      exact hq _ _ _ _ _ hm' hi

/-! ## After the loop: the stores to the variables -/

/-- Where a store to a variable may store. -/
theorem Env.wg (hE : Env K F Wl) (a n : Nat) (hm : (⟨BitVec.ofNat 64 a, n⟩ : Rgn) ∈ globals) (ha : a + n ≤ 2 ^ 64) :
    ∀ i, i < n → Foot Wl (Addr.add (BitVec.ofNat 64 a) i) := by
  intro i hi
  have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have e' := toNat_add_of_fits (a := BitVec.ofNat 64 a) hi (by omega)
  exact hE.gl _ hm _ (by simp only [Rgn.Mem]; omega)

/-- A load from the frame after a store to a variable. -/
theorem rd_gf (hK : K.Ok) (V : Addr → Byte) (a : Nat) (bs : List Byte) (c n : Nat) (ha : a + bs.length ≤ 2 ^ 64)
    (hp : 0 < bs.length) (ho : Off K a bs.length) (hc : c + n ≤ 104) :
    List.map (Vst V (BitVec.ofNat 64 a) bs) (byteAddrs (K.sp + BitVec.ofNat 64 c) n) =
      List.map V (byteAddrs (K.sp + BitVec.ofNat 64 c) n) := by
  have := hK.hsp
  have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  simp only [Off] at ho
  exact rd_Vst _ _ _ _ _ (by omega) (by bv_omega) (by bv_omega)

theorem rd_gf0 (hK : K.Ok) (V : Addr → Byte) (a : Nat) (bs : List Byte) (n : Nat) (ha : a + bs.length ≤ 2 ^ 64)
    (hp : 0 < bs.length) (ho : Off K a bs.length) (hc : n ≤ 104) :
    List.map (Vst V (BitVec.ofNat 64 a) bs) (byteAddrs K.sp n) = List.map V (byteAddrs K.sp n) := by
  have := hK.hsp
  have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  simp only [Off] at ho
  exact rd_Vst _ _ _ _ _ (by omega) (by omega) (by omega)

/-- A store to a variable keeps the frame. -/
theorem RF.out (hF : RF K v V) (hK : K.Ok) (a : Nat) (bs : List Byte) (ha : a + bs.length ≤ 2 ^ 64)
    (hp : 0 < bs.length) (ho : Off K a bs.length) : RF K v (Vst V (BitVec.ofNat 64 a) bs) :=
  ⟨by rw [rd_gf0 hK V a bs 8 ha hp ho (by decide)]; exact hF.platform,
   by rw [rd_gf hK V a bs 8 8 ha hp ho (by decide)]; exact hF.hwcap,
   by rw [rd_gf hK V a bs 16 8 ha hp ho (by decide)]; exact hF.hwcap2,
   by rw [rd_gf hK V a bs 24 8 ha hp ho (by decide)]; exact hF.sysinfo,
   by rw [rd_gf hK V a bs 32 2 ha hp ho (by decide)]; exact hF.fpu,
   by rw [rd_gf hK V a bs 36 4 ha hp ho (by decide)]; exact hF.secure,
   by rw [rd_gf hK V a bs 40 8 ha hp ho (by decide)]; exact hF.random,
   by rw [rd_gf hK V a bs 48 4 ha hp ho (by decide)]; exact hF.decided,
   by rw [rd_gf hK V a bs 34 1 ha hp ho (by decide)]; exact hF.fHwcap2,
   by rw [rd_gf hK V a bs 35 1 ha hp ho (by decide)]; exact hF.fFpu,
   by rw [rd_gf hK V a bs 52 1 ha hp ho (by decide)]; exact hF.fHwcap,
   by rw [rd_gf hK V a bs 53 1 ha hp ho (by decide)]; exact hF.fSysinfo,
   by rw [rd_gf hK V a bs 54 1 ha hp ho (by decide)]; exact hF.fSecure,
   by rw [rd_gf hK V a bs 55 1 ha hp ho (by decide)]; exact hF.fRandom,
   by rw [rd_gf hK V a bs 56 8 ha hp ho (by decide)]; exact hF.v0,
   by rw [rd_gf hK V a bs 64 8 ha hp ho (by decide)]; exact hF.v1,
   by rw [rd_gf hK V a bs 72 8 ha hp ho (by decide)]; exact hF.v2,
   by rw [rd_gf hK V a bs 80 8 ha hp ho (by decide)]; exact hF.v3,
   by rw [rd_gf hK V a bs 88 8 ha hp ho (by decide)]; exact hF.v4,
   by rw [rd_gf hK V a bs 96 8 ha hp ho (by decide)]; exact hF.v5⟩

/-- A load at a fixed address after a store at another. -/
theorem rd_cc (V : Addr → Byte) (a b n : Nat) (bs : List Byte)
    (h : (a + bs.length ≤ b ∨ b + n ≤ a) ∧ a + bs.length ≤ 2 ^ 64 ∧ b + n ≤ 2 ^ 64 ∧ 0 < bs.length ∧ 0 < n) :
    List.map (Vst V (BitVec.ofNat 64 a) bs) (byteAddrs (BitVec.ofNat 64 b) n) =
      List.map V (byteAddrs (BitVec.ofNat 64 b) n) := by
  have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  have e' : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  exact rd_Vst _ _ _ _ _ (by omega) (by omega) (by omega)

theorem rd_cs (V : Addr → Byte) (a n : Nat) (bs : List Byte) (hn : bs.length = n) (h : a + n ≤ 2 ^ 64 ∧ 0 < n) :
    List.map (Vst V (BitVec.ofNat 64 a) bs) (byteAddrs (BitVec.ofNat 64 a) n) = bs := by
  have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  exact rd_Vst_self _ _ _ hn (by omega)

macro "ln1" : tactic => `(tactic| simp only [toBytesLE_length])

theorem Gl.set_pagesize {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 7943128#64 (toBytesLE x 8)) { w with pagesize := x } :=
  ⟨by rw [rd_cs V 7943128 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 7943128 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 7943128 8029568 8 (toBytesLE x 8) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 7943128 8029592 8 (toBytesLE x 8) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 7943128 8029512 8 (toBytesLE x 8) (by ln)]; exact hG.platform,
   by rw [rd_cc V 7943128 8014536 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 7943128 8014528 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 7943128 8029448 8 (toBytesLE x 8) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 7943128 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 7943128 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 7943128 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cc V 7943128 7937184 8 (toBytesLE x 8) (by ln)]; exact hG.random⟩

theorem Gl.set_clktck {w : Vars} (hG : Gl V w) (x : BitVec 32) :
    Gl (Vst V 8029632#64 (toBytesLE x 4)) { w with clktck := x } :=
  ⟨by rw [rd_cc V 8029632 7943128 8 (toBytesLE x 4) (by ln)]; exact hG.pagesize,
   by rw [rd_cs V 8029632 4 (toBytesLE x 4) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8029632 8029568 8 (toBytesLE x 4) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 8029632 8029592 8 (toBytesLE x 4) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 8029632 8029512 8 (toBytesLE x 4) (by ln)]; exact hG.platform,
   by rw [rd_cc V 8029632 8014536 8 (toBytesLE x 4) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 8029632 8014528 8 (toBytesLE x 4) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 8029632 8029448 8 (toBytesLE x 4) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 8029632 7943116 2 (toBytesLE x 4) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8029632 7937248 4 (toBytesLE x 4) (by ln)]; exact hG.secure,
   by rw [rd_cc V 8029632 8029636 4 (toBytesLE x 4) (by ln)]; exact hG.decided,
   by rw [rd_cc V 8029632 7937184 8 (toBytesLE x 4) (by ln)]; exact hG.random⟩

theorem Gl.set_phdr {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 8029568#64 (toBytesLE x 8)) { w with phdr := x } :=
  ⟨by rw [rd_cc V 8029568 7943128 8 (toBytesLE x 8) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 8029568 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cs V 8029568 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8029568 8029592 8 (toBytesLE x 8) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 8029568 8029512 8 (toBytesLE x 8) (by ln)]; exact hG.platform,
   by rw [rd_cc V 8029568 8014536 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 8029568 8014528 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 8029568 8029448 8 (toBytesLE x 8) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 8029568 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8029568 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 8029568 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cc V 8029568 7937184 8 (toBytesLE x 8) (by ln)]; exact hG.random⟩

theorem Gl.set_phnum {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 8029592#64 (toBytesLE x 8)) { w with phnum := x } :=
  ⟨by rw [rd_cc V 8029592 7943128 8 (toBytesLE x 8) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 8029592 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 8029592 8029568 8 (toBytesLE x 8) (by ln)]; exact hG.phdr,
   by rw [rd_cs V 8029592 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8029592 8029512 8 (toBytesLE x 8) (by ln)]; exact hG.platform,
   by rw [rd_cc V 8029592 8014536 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 8029592 8014528 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 8029592 8029448 8 (toBytesLE x 8) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 8029592 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8029592 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 8029592 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cc V 8029592 7937184 8 (toBytesLE x 8) (by ln)]; exact hG.random⟩

theorem Gl.set_platform {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 8029512#64 (toBytesLE x 8)) { w with platform := x } :=
  ⟨by rw [rd_cc V 8029512 7943128 8 (toBytesLE x 8) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 8029512 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 8029512 8029568 8 (toBytesLE x 8) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 8029512 8029592 8 (toBytesLE x 8) (by ln)]; exact hG.phnum,
   by rw [rd_cs V 8029512 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8029512 8014536 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 8029512 8014528 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 8029512 8029448 8 (toBytesLE x 8) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 8029512 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8029512 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 8029512 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cc V 8029512 7937184 8 (toBytesLE x 8) (by ln)]; exact hG.random⟩

theorem Gl.set_hwcap {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 8014536#64 (toBytesLE x 8)) { w with hwcap := x } :=
  ⟨by rw [rd_cc V 8014536 7943128 8 (toBytesLE x 8) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 8014536 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 8014536 8029568 8 (toBytesLE x 8) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 8014536 8029592 8 (toBytesLE x 8) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 8014536 8029512 8 (toBytesLE x 8) (by ln)]; exact hG.platform,
   by rw [rd_cs V 8014536 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8014536 8014528 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 8014536 8029448 8 (toBytesLE x 8) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 8014536 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8014536 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 8014536 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cc V 8014536 7937184 8 (toBytesLE x 8) (by ln)]; exact hG.random⟩

theorem Gl.set_hwcap2 {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 8014528#64 (toBytesLE x 8)) { w with hwcap2 := x } :=
  ⟨by rw [rd_cc V 8014528 7943128 8 (toBytesLE x 8) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 8014528 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 8014528 8029568 8 (toBytesLE x 8) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 8014528 8029592 8 (toBytesLE x 8) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 8014528 8029512 8 (toBytesLE x 8) (by ln)]; exact hG.platform,
   by rw [rd_cc V 8014528 8014536 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap,
   by rw [rd_cs V 8014528 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8014528 8029448 8 (toBytesLE x 8) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 8014528 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8014528 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 8014528 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cc V 8014528 7937184 8 (toBytesLE x 8) (by ln)]; exact hG.random⟩

theorem Gl.set_sysinfoDso {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 8029448#64 (toBytesLE x 8)) { w with sysinfoDso := x } :=
  ⟨by rw [rd_cc V 8029448 7943128 8 (toBytesLE x 8) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 8029448 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 8029448 8029568 8 (toBytesLE x 8) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 8029448 8029592 8 (toBytesLE x 8) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 8029448 8029512 8 (toBytesLE x 8) (by ln)]; exact hG.platform,
   by rw [rd_cc V 8029448 8014536 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 8029448 8014528 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap2,
   by rw [rd_cs V 8029448 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8029448 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8029448 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 8029448 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cc V 8029448 7937184 8 (toBytesLE x 8) (by ln)]; exact hG.random⟩

theorem Gl.set_fpuControl {w : Vars} (hG : Gl V w) (x : BitVec 16) :
    Gl (Vst V 7943116#64 (toBytesLE x 2)) { w with fpuControl := x } :=
  ⟨by rw [rd_cc V 7943116 7943128 8 (toBytesLE x 2) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 7943116 8029632 4 (toBytesLE x 2) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 7943116 8029568 8 (toBytesLE x 2) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 7943116 8029592 8 (toBytesLE x 2) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 7943116 8029512 8 (toBytesLE x 2) (by ln)]; exact hG.platform,
   by rw [rd_cc V 7943116 8014536 8 (toBytesLE x 2) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 7943116 8014528 8 (toBytesLE x 2) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 7943116 8029448 8 (toBytesLE x 2) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cs V 7943116 2 (toBytesLE x 2) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 7943116 7937248 4 (toBytesLE x 2) (by ln)]; exact hG.secure,
   by rw [rd_cc V 7943116 8029636 4 (toBytesLE x 2) (by ln)]; exact hG.decided,
   by rw [rd_cc V 7943116 7937184 8 (toBytesLE x 2) (by ln)]; exact hG.random⟩

theorem Gl.set_secure {w : Vars} (hG : Gl V w) (x : BitVec 32) :
    Gl (Vst V 7937248#64 (toBytesLE x 4)) { w with secure := x } :=
  ⟨by rw [rd_cc V 7937248 7943128 8 (toBytesLE x 4) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 7937248 8029632 4 (toBytesLE x 4) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 7937248 8029568 8 (toBytesLE x 4) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 7937248 8029592 8 (toBytesLE x 4) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 7937248 8029512 8 (toBytesLE x 4) (by ln)]; exact hG.platform,
   by rw [rd_cc V 7937248 8014536 8 (toBytesLE x 4) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 7937248 8014528 8 (toBytesLE x 4) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 7937248 8029448 8 (toBytesLE x 4) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 7937248 7943116 2 (toBytesLE x 4) (by ln)]; exact hG.fpuControl,
   by rw [rd_cs V 7937248 4 (toBytesLE x 4) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 7937248 8029636 4 (toBytesLE x 4) (by ln)]; exact hG.decided,
   by rw [rd_cc V 7937248 7937184 8 (toBytesLE x 4) (by ln)]; exact hG.random⟩

theorem Gl.set_decided {w : Vars} (hG : Gl V w) (x : BitVec 32) :
    Gl (Vst V 8029636#64 (toBytesLE x 4)) { w with decided := x } :=
  ⟨by rw [rd_cc V 8029636 7943128 8 (toBytesLE x 4) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 8029636 8029632 4 (toBytesLE x 4) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 8029636 8029568 8 (toBytesLE x 4) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 8029636 8029592 8 (toBytesLE x 4) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 8029636 8029512 8 (toBytesLE x 4) (by ln)]; exact hG.platform,
   by rw [rd_cc V 8029636 8014536 8 (toBytesLE x 4) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 8029636 8014528 8 (toBytesLE x 4) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 8029636 8029448 8 (toBytesLE x 4) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 8029636 7943116 2 (toBytesLE x 4) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 8029636 7937248 4 (toBytesLE x 4) (by ln)]; exact hG.secure,
   by rw [rd_cs V 8029636 4 (toBytesLE x 4) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x,
   by rw [rd_cc V 8029636 7937184 8 (toBytesLE x 4) (by ln)]; exact hG.random⟩

theorem Gl.set_random {w : Vars} (hG : Gl V w) (x : BitVec 64) :
    Gl (Vst V 7937184#64 (toBytesLE x 8)) { w with random := x } :=
  ⟨by rw [rd_cc V 7937184 7943128 8 (toBytesLE x 8) (by ln)]; exact hG.pagesize,
   by rw [rd_cc V 7937184 8029632 4 (toBytesLE x 8) (by ln)]; exact hG.clktck,
   by rw [rd_cc V 7937184 8029568 8 (toBytesLE x 8) (by ln)]; exact hG.phdr,
   by rw [rd_cc V 7937184 8029592 8 (toBytesLE x 8) (by ln)]; exact hG.phnum,
   by rw [rd_cc V 7937184 8029512 8 (toBytesLE x 8) (by ln)]; exact hG.platform,
   by rw [rd_cc V 7937184 8014536 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap,
   by rw [rd_cc V 7937184 8014528 8 (toBytesLE x 8) (by ln)]; exact hG.hwcap2,
   by rw [rd_cc V 7937184 8029448 8 (toBytesLE x 8) (by ln)]; exact hG.sysinfoDso,
   by rw [rd_cc V 7937184 7943116 2 (toBytesLE x 8) (by ln)]; exact hG.fpuControl,
   by rw [rd_cc V 7937184 7937248 4 (toBytesLE x 8) (by ln)]; exact hG.secure,
   by rw [rd_cc V 7937184 8029636 4 (toBytesLE x 8) (by ln)]; exact hG.decided,
   by rw [rd_cs V 7937184 8 (toBytesLE x 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) x⟩

/-- After the loop, a variable stored. -/
theorem Ex.st {w w' : Vars} {g g' : Gprs} (h : Ex K w g V) (hK : K.Ok) (a n : Nat) (bs : List Byte)
    (hn : bs.length = n) (hb : a + n ≤ 2 ^ 64 ∧ 0 < n ∧ (a + n ≤ 0x7a8540 ∨ 0x7a8548 ≤ a)) (ho : Off K a n)
    (hG : Gl V w → Gl (Vst V (BitVec.ofNat 64 a) bs) w')
    (hsp : g'.rsp = g.rsp) (e10 : g'.r10 = g.r10) (e9 : g'.r9 = g.r9)
    (ebp : g'.rbp = g.rbp) (e11 : g'.r11 = g.r11) (e13 : g'.r13 = g.r13) (ebx : g'.rbx = g.rbx)
    (e15 : g'.r15 = g.r15) (e12 : g'.r12 = g.r12) (e14 : g'.r14 = g.r14) (ecx : g'.rcx = g.rcx)
    (hm : (⟨BitVec.ofNat 64 a, n⟩ : Rgn) ∈ globals := by simp [globals]) :
    Ex K w' g' (Vst V (BitVec.ofNat 64 a) bs) := by
  subst hn
  obtain ⟨h1, hR, hF, hGl, hax, hcx⟩ := h
  have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; omega
  exact ⟨hsp.trans h1, hR.mv e10 e9 ebp e11 e13 ebx e15 e12 e14 rfl rfl rfl rfl rfl, hF.out hK a bs hb.1 hb.2.1 ho,
    hG hGl, ⟨by rw [rd_cc V a 0x7a8540 8 bs ⟨by omega, hb.1, by decide, hb.2.1, by decide⟩]; exact hax.1,
      fun x hf hg => by
        have hx : ¬ (⟨BitVec.ofNat 64 a, bs.length⟩ : Rgn).Mem x := fun hx => hg ⟨_, hm, hx⟩
        simp only [Rgn.Mem, e] at hx
        rw [Vst_out V _ bs x (by rw [e]; exact hb.1) (by rw [e]; omega)]
        exact hax.2 x hf hg⟩,
    ecx ▸ hcx⟩

theorem W1_z {v0 v : Vars} (h : v.pagesize = v0.pagesize) : W1 v0 v = v0 := by
  unfold W1; rw [h]
theorem W1_s (v0 v : Vars) : W1 v0 v = { v0 with pagesize := v.pagesize } := rfl
theorem W2_z {v0 v : Vars} (h : v.clktck = v0.clktck) : W2 v0 v = W1 v0 v := by
  unfold W2 W1; rw [h]
theorem W2_s (v0 v : Vars) : W2 v0 v = { W1 v0 v with clktck := v.clktck } := rfl
theorem W3_z {v0 v : Vars} (h : v.phdr = v0.phdr) : W3 v0 v = W2 v0 v := by
  unfold W3 W2; rw [h]
theorem W3_s (v0 v : Vars) : W3 v0 v = { W2 v0 v with phdr := v.phdr } := rfl
theorem W4_z {v0 v : Vars} (h : v.phnum = v0.phnum) : W4 v0 v = W3 v0 v := by
  unfold W4 W3; rw [h]
theorem W4_s (v0 v : Vars) : W4 v0 v = { W3 v0 v with phnum := v.phnum } := rfl
theorem W5_z {v0 v : Vars} (h : v.platform = v0.platform) : W5 v0 v = W4 v0 v := by
  unfold W5 W4; rw [h]
theorem W5_s (v0 v : Vars) : W5 v0 v = { W4 v0 v with platform := v.platform } := rfl
theorem W6_z {v0 v : Vars} (h : v.hwcap = v0.hwcap) : W6 v0 v = W5 v0 v := by
  unfold W6 W5; rw [h]
theorem W6_s (v0 v : Vars) : W6 v0 v = { W5 v0 v with hwcap := v.hwcap } := rfl
theorem W7_z {v0 v : Vars} (h : v.hwcap2 = v0.hwcap2) : W7 v0 v = W6 v0 v := by
  unfold W7 W6; rw [h]
theorem W7_s (v0 v : Vars) : W7 v0 v = { W6 v0 v with hwcap2 := v.hwcap2 } := rfl
theorem W8_z {v0 v : Vars} (h : v.fpuControl = v0.fpuControl) : W8 v0 v = W7 v0 v := by
  unfold W8 W7; rw [h]
theorem W8_s (v0 v : Vars) : W8 v0 v = { W7 v0 v with fpuControl := v.fpuControl } := rfl
theorem W9_z {v0 v : Vars} (h : v.sysinfoDso = v0.sysinfoDso) : W9 v0 v = W8 v0 v := by
  unfold W9 W8; rw [h]
theorem W9_s (v0 v : Vars) : W9 v0 v = { W8 v0 v with sysinfoDso := v.sysinfoDso } := rfl
theorem W10_z {v0 v : Vars} (h : v.secure = v0.secure ∧ v.decided = v0.decided) : W10 v0 v = W9 v0 v := by
  unfold W10 W9; rw [h.1, h.2]
theorem W10_s (v0 v : Vars) : W10 v0 v = { W9 v0 v with secure := v.secure, decided := v.decided } := rfl
theorem W11_z {v0 v : Vars} (h : v.random = v0.random) : W11 v0 v = W10 v0 v := by
  unfold W11 W10; rw [← h]
theorem W11_s (v0 v : Vars) : W11 v0 v = { W10 v0 v with random := v.random } := rfl

theorem vc_272 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 272 (fun v0 _ => v0) K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 281 W1 K m' g' V' → Q 281 g' fl V') : W_272 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  have hv : r10 = (K.vs K.N).pagesize := hR.r10
  wpx [W_272, W_1024, o7, o45, Op.sta]
  refine fun af => ⟨fun _ => ⟨hE.wg 7943128 8 (by simp [globals]) (by decide), ?_⟩, fun hc => ?_⟩
  ·
    refine hq (500 - 281) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 7943128 8 _ (by ln1) (by decide) hK.oPs
      (fun hG => by rw [W1_s, ← hv]; exact hG.set_pagesize _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  · have hz : BitVec.setWidth 8 r9 = 0#8 := by simpa using hc
    refine hq (500 - 281) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W1_z (hR.f9 hz)]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩

theorem vc_281 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 281 W1 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 292 W2 K m' g' V' → Q 292 g' fl V') : W_281 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  have hv : BitVec.setWidth 32 rbp = (K.vs K.N).clktck := hR.rbp
  wpx [W_281, W_286, o8, o9, Op.sta]
  refine fun af => ⟨fun hc => ?_, fun _ => ⟨hE.wg 8029632 4 (by simp [globals]) (by decide), ?_⟩⟩
  · have hz : BitVec.setWidth 8 r11 = 0#8 := by simpa using hc
    refine hq (500 - 292) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W2_z (hR.f11 hz)]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  ·
    refine hq (500 - 292) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 8029632 4 _ (by ln1) (by decide) hK.oCk
      (fun hG => by rw [W2_s, ← hv]; exact hG.set_clktck _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_292 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 292 W2 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 303 W3 K m' g' V' → Q 303 g' fl V') : W_292 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  have hv : r13 = (K.vs K.N).phdr := hR.r13
  wpx [W_292, W_296, o10, o11, Op.sta]
  refine fun af => ⟨fun hc => ?_, fun _ => ⟨hE.wg 8029568 8 (by simp [globals]) (by decide), ?_⟩⟩
  · have hz : BitVec.setWidth 8 rbx = 0#8 := by simpa using hc
    refine hq (500 - 303) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W3_z (hR.fbx hz)]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  ·
    refine hq (500 - 303) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 8029568 8 _ (by ln1) (by decide) hK.oPh
      (fun hG => by rw [W3_s, ← hv]; exact hG.set_phdr _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_303 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 303 W3 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 315 W4 K m' g' V' → Q 315 g' fl V') : W_303 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  have hv : r15 = (K.vs K.N).phnum := hR.r15
  wpx [W_303, W_308, o12, o13, Op.sta]
  refine fun af => ⟨fun hc => ?_, fun _ => ⟨hE.wg 8029592 8 (by simp [globals]) (by decide), ?_⟩⟩
  · have hz : BitVec.setWidth 8 r12 = 0#8 := by simpa using hc
    refine hq (500 - 315) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W4_z (hR.f12 hz)]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  ·
    refine hq (500 - 315) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 8029592 8 _ (by ln1) (by decide) hK.oPn
      (fun hG => by rw [W4_s, ← hv]; exact hG.set_phnum _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_315 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 315 W4 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 332 W5 K m' g' V' → Q 332 g' fl V') : W_315 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  wpx [W_315, W_320, o14, o15, Op.sta, e0, hF.platform]
  refine fun af => ⟨fun hc => ?_, fun _ => ⟨fun i hi => hE.ws _ (hE.wr0 hK 8 (by decide) i hi),
    hE.wg 8029512 8 (by simp [globals]) (by decide), ?_⟩⟩
  · have hz : BitVec.setWidth 8 r14 = 0#8 := by simpa using hc
    refine hq (500 - 332) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W5_z (hR.f14 hz)]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  · refine hq (500 - 332) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 8029512 8 _ (by ln1) (by decide) hK.oPl
      (fun hG => by rw [W5_s]; exact hG.set_platform _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_332 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 332 W5 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 351 W6 K m' g' V' → Q 351 g' fl V') : W_332 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  wpx [W_332, W_339, o16, o17, Op.sta, Op.cmpmi, e52, e8, hF.hwcap]
  refine ⟨fun i hi => hE.ws _ (hE.wr hK 52 1 (by decide) i hi), fun hc => ?_, fun _ =>
    ⟨fun i hi => hE.ws _ (hE.wr hK 8 8 (by decide) i hi), hE.wg 8014536 8 (by simp [globals]) (by decide), ?_⟩⟩
  · refine hq (500 - 351) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W6_z (hF.fHwcap (of_decide_eq_true hc))]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  · refine hq (500 - 351) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 8014536 8 _ (by ln1) (by decide) hK.oHw
      (fun hG => by rw [W6_s]; exact hG.set_hwcap _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_351 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 351 W6 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 370 W7 K m' g' V' → Q 370 g' fl V') : W_351 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  wpx [W_351, W_358, o18, o19, Op.sta, Op.cmpmi, e34, e16, hF.hwcap2]
  refine ⟨fun i hi => hE.ws _ (hE.wr hK 34 1 (by decide) i hi), fun hc => ?_, fun _ =>
    ⟨fun i hi => hE.ws _ (hE.wr hK 16 8 (by decide) i hi), hE.wg 8014528 8 (by simp [globals]) (by decide), ?_⟩⟩
  · refine hq (500 - 370) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W7_z (hF.fHwcap2 (of_decide_eq_true hc))]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  · refine hq (500 - 370) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 8014528 8 _ (by ln1) (by decide) hK.oH2
      (fun hG => by rw [W7_s]; exact hG.set_hwcap2 _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_389 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 389 W8 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 408 W9 K m' g' V' → Q 408 g' fl V') : W_389 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  wpx [W_389, W_396, o22, o23, Op.sta, Op.cmpmi, e53, e24, hF.sysinfo]
  refine ⟨fun i hi => hE.ws _ (hE.wr hK 53 1 (by decide) i hi), fun hc => ?_, fun _ =>
    ⟨fun i hi => hE.ws _ (hE.wr hK 24 8 (by decide) i hi), hE.wg 8029448 8 (by simp [globals]) (by decide), ?_⟩⟩
  · refine hq (500 - 408) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W9_z (hF.fSysinfo (of_decide_eq_true hc))]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  · refine hq (500 - 408) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 8029448 8 _ (by ln1) (by decide) hK.oSy
      (fun hG => by rw [W9_s]; exact hG.set_sysinfoDso _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_435 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 435 W10 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 454 W11 K m' g' V' → Q 454 g' fl V') : W_435 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  wpx [W_435, W_442, o26, o27, Op.sta, Op.cmpmi, e55, e40, hF.random]
  refine ⟨fun i hi => hE.ws _ (hE.wr hK 55 1 (by decide) i hi), fun hc => ?_, fun _ =>
    ⟨fun i hi => hE.ws _ (hE.wr hK 40 8 (by decide) i hi), hE.wg 7937184 8 (by simp [globals]) (by decide), ?_⟩⟩
  · refine hq (500 - 454) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W11_z (hF.fRandom (of_decide_eq_true hc))]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  · refine hq (500 - 454) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 7937184 8 _ (by ln1) (by decide) hK.oRa
      (fun hG => by rw [W11_s]; exact hG.set_random _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_370 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 370 W7 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 389 W8 K m' g' V' → Q 389 g' fl V') : W_370 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  wpx [W_370, W_377, o20, o21, Op.sta, Op.cmpmi, e35, e32, hF.fpu, sw16b]
  refine ⟨fun i hi => hE.ws _ (hE.wr hK 35 1 (by decide) i hi), fun hc => ?_, fun _ =>
    ⟨fun i hi => hE.ws _ (hE.wr hK 32 2 (by decide) i hi), hE.wg 7943116 2 (by simp [globals]) (by decide), ?_⟩⟩
  · refine hq (500 - 389) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W8_z (hF.fFpu (of_decide_eq_true hc))]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  · refine hq (500 - 389) _ _ _ (by omega) ⟨?_, rfl⟩
    exact Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 7943116 2 _ (by ln1) (by decide) hK.oFp
      (fun hG => by rw [W8_s]; exact hG.set_fpuControl _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_408 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E 408 W9 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E 435 W10 K m' g' V' → Q 435 g' fl V') : W_408 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  wpx [W_408, W_415, o24, o25, Op.sta, Op.cmpmi, e54, e36, e48, hF.secure,
    rd_gf hK V 7937248 (toBytesLE (K.vs K.N).secure 4) 48 4 (by ln) (by ln) (by simp only [toBytesLE_length]; exact hK.oSe)
      (by decide), hF.decided]
  refine ⟨fun i hi => hE.ws _ (hE.wr hK 54 1 (by decide) i hi), fun hc => ?_, fun _ =>
    ⟨fun i hi => hE.ws _ (hE.wr hK 36 4 (by decide) i hi), hE.wg 7937248 4 (by simp [globals]) (by decide),
      fun i hi => hE.ws _ (hE.wr hK 48 4 (by decide) i hi), hE.wg 8029636 4 (by simp [globals]) (by decide), ?_⟩⟩
  · refine hq (500 - 435) _ _ _ (by omega) ⟨?_, rfl⟩
    rw [W10_z (hF.fSecure (of_decide_eq_true hc))]
    exact ⟨rfl, hR, hF, hG, hax, hcx⟩
  · refine hq (500 - 435) _ _ _ (by omega) ⟨?_, rfl⟩
    have h1 : Ex K { W9 (K.vs 0) (K.vs K.N) with secure := (K.vs K.N).secure } ⟨rax, rcx, rdx, rbx, K.sp + 56#64, rbp,
        rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ (Vst V 7937248#64 (toBytesLE (K.vs K.N).secure 4)) :=
      Ex.st ⟨rfl, hR, hF, hG, hax, hcx⟩ hK 7937248 4 _ (by ln1) (by decide) hK.oSe
        (fun hG => hG.set_secure _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    exact Ex.st h1 hK 8029636 4 _ (by ln1) (by decide) hK.oDe
      (fun hG => by rw [W10_s]; exact hG.set_decided _) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem vc_454 {Q : Post} (h : E 454 W11 K m g V)
    (hq : ∀ m' g' fl V', m' < m → E483 K m' g' V' → Q 483 g' fl V') : W_454 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨⟨rfl, hR, hF, hG, hax, hcx⟩, rfl⟩ := h
  have hcx' : BitVec.setWidth 32 rcx = 4294967295#32 := hcx
  wpx [W_454, W_459, o28, o29, hcx']
  exact ⟨fun _ => hq 17 _ _ _ (by omega) ⟨rfl, hF, hG, hax, rfl⟩, fun hc => absurd hc (by decide)⟩

theorem vc_483 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : E483 K m g V)
    (h493 : ∀ g' fl V', Ret K g' V' → Q 493 g' fl V') : W_483 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, hF, hG, hax, rfl⟩ := h
  have e1 : K.sp + 56#64 + 8 = K.sp + 64#64 := by bv_omega
  have e2 : K.sp + 64#64 + 8 = K.sp + 72#64 := by bv_omega
  have e3 : K.sp + 72#64 + 8 = K.sp + 80#64 := by bv_omega
  have e4 : K.sp + 80#64 + 8 = K.sp + 88#64 := by bv_omega
  have e5 : K.sp + 88#64 + 8 = K.sp + 96#64 := by bv_omega
  have e6 : K.sp + 96#64 + 8 = K.sp + 104#64 := by bv_omega
  wpx [W_483, o30, e1, e2, e3, e4, e5, e6, hF.v0, hF.v1, hF.v2, hF.v3, hF.v4, hF.v5]
  exact ⟨fun i hi => hE.ws _ (hE.wr hK 56 8 (by decide) i hi), fun i hi => hE.ws _ (hE.wr hK 64 8 (by decide) i hi),
    fun i hi => hE.ws _ (hE.wr hK 72 8 (by decide) i hi), fun i hi => hE.ws _ (hE.wr hK 80 8 (by decide) i hi),
    fun i hi => hE.ws _ (hE.wr hK 88 8 (by decide) i hi), fun i hi => hE.ws _ (hE.wr hK 96 8 (by decide) i hi),
    h493 _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hG, hax.1, hax.2⟩⟩

/-! ## The entry -/

/-- A load at a fixed address after a store into the frame. -/
theorem rd_gp (hK : K.Ok) (V : Addr → Byte) (b n c' : Nat) (bs : List Byte) (ho : Off K b n)
    (hb : b + n ≤ 2 ^ 64 ∧ 0 < n) (h1 : c' + bs.length ≤ 104) :
    List.map (Vst V (K.sp + BitVec.ofNat 64 c') bs) (byteAddrs (BitVec.ofNat 64 b) n) =
      List.map V (byteAddrs (BitVec.ofNat 64 b) n) := by
  have e : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  exact rd_fo hK (by omega) (by rw [e]; exact ho) V c' bs h1

theorem rd_gp0 (hK : K.Ok) (V : Addr → Byte) (b n : Nat) (bs : List Byte) (ho : Off K b n)
    (hb : b + n ≤ 2 ^ 64 ∧ 0 < n) (h1 : bs.length ≤ 104) :
    List.map (Vst V K.sp bs) (byteAddrs (BitVec.ofNat 64 b) n) = List.map V (byteAddrs (BitVec.ofNat 64 b) n) := by
  have e : (BitVec.ofNat 64 b).toNat = b := by rw [BitVec.toNat_ofNat]; omega
  exact rd_f0o hK (by omega) (by rw [e]; exact ho) V bs h1

theorem vc_0 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : P0 K m g V)
    (h216 : ∀ m' g' fl V', m' < m → I216 K m' g' V' → Q 216 g' fl V') :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  have e1 : K.sp + 104#64 - 8 = K.sp + 96#64 := by bv_omega
  have e2 : K.sp + 96#64 - 8 = K.sp + 88#64 := by bv_omega
  have e3 : K.sp + 88#64 - 8 = K.sp + 80#64 := by bv_omega
  have e4 : K.sp + 80#64 - 8 = K.sp + 72#64 := by bv_omega
  have e5 : K.sp + 72#64 - 8 = K.sp + 64#64 := by bv_omega
  have e6 : K.sp + 64#64 - 8 = K.sp + 56#64 := by bv_omega
  have hN : 0 < K.N := Nat.lt_of_le_of_lt (Nat.zero_le _) hK.hsn
  have ht0 : rdq(K.V0, K.av) = K.ty 0 := by
    have := hK.hty 0 hN
    rwa [show K.av.add (16 * 0) = K.av from by simp [Addr.add]] at this
  have k0 : Out K (Vst K.V0 8029504#64 (toBytesLE K.av 8)) ∧ rdq(Vst K.V0 8029504#64 (toBytesLE K.av 8), 8029504#64) = K.av := by
    refine ⟨fun a ha hx => ?_, ?_⟩
    · rw [Vst_out _ _ _ _ (by simp only [toBytesLE_length]; decide)
        (by simp only [toBytesLE_length, BitVec.toNat_ofNat]; exact hx)]
    · rw [rd_cs _ 8029504 8 (toBytesLE K.av 8) (by ln1) (by decide)]; exact ofBytesLE_toBytesLE (by decide) _
  wpx [W_0, W_23, o0, o1, Op.sta, Op.lda, Op.ldzxa, e1, e2, e3, e4, e5, e6, e0, e8, e16, e24, e32, e34, e35, e36, e40,
    e48, e52, e53, e54, e55, ht0, rd_gp hK, rd_gp0 hK, rd_cc, hK.oPs, hK.oCk, hK.oPh, hK.oPn, hK.oPl, hK.oHw, hK.oH2,
    hK.oSy, hK.oFp, hK.oSe, hK.oDe, hK.oRa, Nat.reduceAdd, Nat.reduceLeDiff, Nat.reduceLT, and_self, or_true, true_or,
    hK.hgl.pagesize, hK.hgl.clktck, hK.hgl.phdr, hK.hgl.phnum, hK.hgl.platform, hK.hgl.hwcap, hK.hgl.hwcap2,
    hK.hgl.sysinfoDso, hK.hgl.fpuControl, hK.hgl.secure, hK.hgl.decided, hK.hgl.random, sw16b]
  refine ⟨fun i hi => ?_, hE.wg _ _ (by simp [globals]) (by decide), fun af => ⟨fun hc => ?_, fun _ => ?_⟩⟩
  · have h1 := hK.hfit
    have e := toNat_add_of_fits (a := K.av) hi (by omega)
    exact hE.vec _ (by omega) (by omega)
  · exact absurd (by simpa using hc) (hK.hnz 0 hN)
  · repeat' (first
      | exact hE.wr hK _ _ (by decide)
      | exact hE.wr0 hK _ (by decide)
      | exact fun i hi => hE.ws _ (hE.wg _ _ (by simp [globals]) (by decide) i hi)
      | refine ⟨?_, ?_⟩
      | intro (_ : Bool))
    refine h216 (3 * (K.N - 0) + 302) _ _ _ (by omega) ⟨0, hN, ⟨rfl, rfl, ?_, ?_, ?_, ?_,
      fun h => absurd h (Nat.not_lt_zero _)⟩, by simp [Addr.add], rfl, rfl⟩
    · exact ⟨rfl, fun _ => rfl, sw32 _, fun _ => rfl, rfl, fun _ => rfl, rfl, fun _ => rfl, fun _ => rfl⟩
    · constructor <;>
        (try simp only [rd_ff hK, rd_f0f hK, rd_fself hK, rd_f0self hK, toBytesLE_length, Nat.reduceAdd,
          Nat.reduceMul, Nat.reduceLeDiff, true_or, or_true, ofBytesLE_toBytesLE, and_self]) <;>
        first | done | exact fun _ => trivial | exact fun _ => rfl | exact fun _ => ⟨rfl, rfl⟩
    · exact (keep0 hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (k0) 96 _ (by ln)) 88 _ (by ln)) 80 _ (by ln)) 72 _ (by ln)) 64 _ (by ln)) 56 _ (by ln)) 16 _ (by ln)) 24 _ (by ln)) 36 _ (by ln)) 40 _ (by ln)) 48 _ (by ln)) 55 _ (by ln)) 54 _ (by ln)) 53 _ (by ln)) 35 _ (by ln)) 34 _ (by ln)) 52 _ (by ln)) 32 _ (by ln)) 8 _ (by ln)) _ (by ln)).1
    · exact (keep0 hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (keep hK (k0) 96 _ (by ln)) 88 _ (by ln)) 80 _ (by ln)) 72 _ (by ln)) 64 _ (by ln)) 56 _ (by ln)) 16 _ (by ln)) 24 _ (by ln)) 36 _ (by ln)) 40 _ (by ln)) 48 _ (by ln)) 55 _ (by ln)) 54 _ (by ln)) 53 _ (by ln)) 35 _ (by ln)) 34 _ (by ln)) 52 _ (by ln)) 32 _ (by ln)) 8 _ (by ln)) _ (by ln)).2

/-! ## The conditions together -/

/-- One more cut point of the table. -/
theorem vcT {ℓ k : Nat} {I I' : Nat → Gprs → (Addr → Byte) → Prop} {W W' : Wpt}
    (h : ∀ n g f V, I n g V → W F Wl (Nx K n) g f V) (h' : ∀ n g f V, I' n g V → W' F Wl (Nx K n) g f V) :
    ∀ n g f V, (if ℓ = k then I else I') n g V → (if ℓ = k then W else W') F Wl (Nx K n) g f V := by
  split
  · exact h
  · exact h'

/-- The conditions of all the cut points: from the invariant at `ℓ`, the condition `Wt ℓ` of the code from `ℓ`, with
at each exit the invariant there and a smaller measure, or `Ret` at the `ret`. The stop (1040) is not reached. -/
theorem vcAll (hK : K.Ok) (hE : Env K F Wl) (ℓ : Nat) :
    ∀ n g f V, InvT K ℓ n g V → Wt ℓ F Wl (Nx K n) g f V :=
  vcT (k := 0) (fun _ _ _ _ h => vc_0 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 216) (fun _ _ _ _ h => vc_216 hK hE h (fun _ _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 240) (fun _ _ _ _ h => vc_240 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 256) (fun _ _ _ _ h => vc_256 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 272) (fun _ _ _ _ h => vc_272 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 281) (fun _ _ _ _ h => vc_281 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 292) (fun _ _ _ _ h => vc_292 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 303) (fun _ _ _ _ h => vc_303 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 315) (fun _ _ _ _ h => vc_315 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 332) (fun _ _ _ _ h => vc_332 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 351) (fun _ _ _ _ h => vc_351 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 370) (fun _ _ _ _ h => vc_370 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 389) (fun _ _ _ _ h => vc_389 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 408) (fun _ _ _ _ h => vc_408 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 435) (fun _ _ _ _ h => vc_435 hK hE h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 454) (fun _ _ _ _ h => vc_454 h (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 483) (fun _ _ _ _ h => vc_483 hK hE h (fun _ _ _ h' => Or.inr ⟨rfl, h'⟩)) <|
  vcT (k := 496) (fun _ _ _ _ h => vc_496 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 536) (fun _ _ _ _ h => vc_536 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 576) (fun _ _ _ _ h => vc_576 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 624) (fun _ _ _ _ h => vc_624 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 664) (fun _ _ _ _ h => vc_664 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 704) (fun _ _ _ _ h => vc_704 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 744) (fun _ _ _ _ h => vc_744 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 784) (fun _ _ _ _ h => vc_784 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 816) (fun _ _ _ _ h => vc_816 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 848) (fun _ _ _ _ h => vc_848 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 880) (fun _ _ _ _ h => vc_880 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 912) (fun _ _ _ _ h => vc_912 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 960) (fun _ _ _ _ h => vc_960 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  vcT (k := 992) (fun _ _ _ _ h => vc_992 hK hE h (fun _ _ _ _ hn h' => nx hn h') (fun _ _ _ _ hn h' => nx hn h')) <|
  fun _ _ _ _ h => h.elim

end FV7z.Auxv
