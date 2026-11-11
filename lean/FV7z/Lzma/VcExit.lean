import FV7z.Lzma.VcCopy
/-!
# The verification conditions of the way out (PLAN.md G2.2)

4611: no error, the normalization before the epilogue. 4632: the epilogue writes `dicPos`, `buf`, the range, the
code, the state, `processedPos`, `remainLen` and the four `reps` into the `CLzmaDec`, takes the saved registers back
and leaves `rsp` at the return address. `Ret`: what holds at `ret`, for the caller.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

/-- At `ret` (4718): the saved registers and `rsp` as at the call, 0 or 1 in `eax`; the probabilities in
`[31, 2017]`; in the `CLzmaDec`, `dicPos` up to `limit`, `processedPos` within its bound, `buf` within 20 bytes of
`bufLimit`, a range of at least `2^24`, a state below 12, `reps` no larger than the dictionary's buffer unless
`eax = 1`, and then a `remainLen` of at least 514. -/
def Ret (K : Ctx) (g : Gprs) (V : Addr → Byte) : Prop :=
  g.rsp = K.sq + 48#64 ∧ g.r15 = K.sv 0 ∧ g.r14 = K.sv 1 ∧ g.r13 = K.sv 2 ∧ g.r12 = K.sv 3 ∧ g.rbp = K.sv 4 ∧
    g.rbx = K.sv 5 ∧ (g.rax = 0#64 ∨ g.rax = 1#64) ∧ (∀ a, InPr K a → Pv ((rdw(V, a)).setWidth 32)) ∧
    (∃ dq, rdq(V, K.p + 40#64) = BitVec.ofNat 64 dq ∧ K.dp0 ≤ dq ∧ dq ≤ K.lim ∧
      (K.ckd.toNat = 0 → (rdd(V, K.p + 64#64)).toNat + (K.lim - dq) ≤ K.ppb)) ∧
    K.b0 ≤ (rdq(V, K.p + 48#64)).toNat ∧ (rdq(V, K.p + 48#64)).toNat ≤ K.bl.toNat + 20 ∧
    2 ^ 24 ≤ (rdd(V, K.p + 56#64)).toNat ∧ (rdd(V, K.p + 88#64)).toNat < 12 ∧
    (g.rax = 0#64 → (rdd(V, K.p + 72#64)).toNat ≤ K.dbs ∧ (rdd(V, K.p + 76#64)).toNat ≤ K.dbs ∧
      (rdd(V, K.p + 80#64)).toNat ≤ K.dbs ∧ (rdd(V, K.p + 84#64)).toNat ≤ K.dbs) ∧
    (g.rax = 1#64 → 514 ≤ (rdd(V, K.p + 92#64)).toNat)

/-- `V'` is `V` but for the `CLzmaDec`'s bytes. -/
def SameP (K : Ctx) (V V' : Addr → Byte) : Prop :=
  ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 → x.toNat + n ≤ K.p.toNat ∨ K.p.toNat + 0x60 ≤ x.toNat →
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n)

theorem SameP.st (hK : K.Ok) {V V' V'' : Addr → Byte} (h : SameP K V V') {a : Addr} {bs : List Byte}
    (hV : Vst V' a bs = V'') (ha : K.p.toNat ≤ a.toNat ∧ a.toNat + bs.length ≤ K.p.toNat + 0x60) :
    SameP K V V'' := by
  subst hV
  intro x n hx hd
  have := hK.hp
  rw [rd_Vst _ _ _ _ _ (by omega) hx (by omega)]
  exact h x n hx hd

theorem SameP.mem0 (hK : K.Ok) {V V' : Addr → Byte} (h : SameP K V V') (hM : Mem0 K V) : Mem0 K V' := by
  have := hK.hsq; have := hK.hsp1; have := hK.hsp2; have := hK.hp; have := hK.hnp; have := hK.aFp; have := hK.aPp
  refine hM.of_same hK (fun x n hx => h x n (by unfold FrC at hx; omega) (by unfold FrC at hx; omega)) fun a ha => ?_
  obtain ⟨i, hi, hai⟩ := ha
  rw [h a 2 (by omega) (by omega)]
  exact hM.pr a ⟨i, hi, hai⟩

theorem vc_4611 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Out4611 K n g V)
    (hq : ∀ n' g' fl, n' < n → Out4632 K n' g' V → Q 4632 g' fl V) :
    W_4611 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Out4611] at h
  obtain ⟨dq, k, d, pp, rfl, hMem, rfl, hd0, hdq, hB, hU, hS, rfl, hpp, rfl⟩ := h
  wpx [W_4611, o80, BitVec.reduceSetWidth, BitVec.xor_self]
  exact fun _ => wnorm_of hE hK hB hU fun R' rbp' r15' hN' fl => hq 100 _ _ (by omega)
    ⟨dq, k, d, pp, R', rfl, hMem.toMem0, .inl rfl, fun _ => hMem,
      fun h => absurd (show (0#64 : BitVec 64) = 1#64 from h) (by decide), rfl, hd0, hdq, rfl, hN', hS, rfl, hpp, rfl⟩

macro "rdv" : tactic => `(tactic| rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (by bv_omega)
  (by rw [toBytesLE_length]; bv_omega)])

macro "stp" : tactic => `(tactic| (rw [toBytesLE_length]; constructor <;> bv_omega))

theorem vc_4632 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Out4632 K n g V)
    (hq : ∀ g' fl V', Ret K g' V' → Q 4718 g' fl V') :
    W_4632 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Out4632] at h
  obtain ⟨dq, k, d, pp, R, rfl, hM0, hb, hb0, hb1, rfl, hd0, hdq, rfl, hN, hS, rfl, hpp, rfl⟩ := h
  wpx [W_4632, o81, BitVec.reduceSetWidth]
  simp only [hM0.s8, hM0.s38]
  have hp := hK.hp; have := hK.hsq; have := hK.hsp2; have hA := hK.aFp; have := hK.hsp1
  have hdic := hK.hdic; have hlim := hK.hlim
  have ed : K.dic + BitVec.ofNat 64 dq - K.dic = BitVec.ofNat 64 dq := by bv_omega
  simp only [ed]
  generalize hV1 : Vst V (K.p + 40#64) _ = V1
  have s1 : SameP K V V1 := SameP.st hK (fun _ _ _ _ => rfl) hV1 (by stp)
  generalize hV2 : Vst V1 (K.p + 48#64) _ = V2
  have s2 := s1.st hK hV2 (by stp)
  generalize hV3 : Vst V2 (K.p + 56#64) _ = V3
  have s3 := s2.st hK hV3 (by stp)
  generalize hV4 : Vst V3 (K.p + 60#64) _ = V4
  have s4 := s3.st hK hV4 (by stp)
  generalize hV5 : Vst V4 (K.p + 88#64) _ = V5
  have s5 := s4.st hK hV5 (by stp)
  generalize hV6 : Vst V5 (K.p + 64#64) _ = V6
  have s6 := s5.st hK hV6 (by stp)
  simp only [s6 (K.sp + 100#64) 4 (by bv_omega) (by bv_omega)]
  generalize hV7 : Vst V6 (K.p + 92#64) _ = V7
  have s7 := s6.st hK hV7 (by stp)
  simp only [s7 (K.sp + 112#64) 4 (by bv_omega) (by bv_omega)]
  generalize hV8 : Vst V7 (K.p + 72#64) _ = V8
  have s8 := s7.st hK hV8 (by stp)
  simp only [s8 (K.sp + 116#64) 4 (by bv_omega) (by bv_omega)]
  generalize hV9 : Vst V8 (K.p + 76#64) _ = V9
  have s9 := s8.st hK hV9 (by stp)
  simp only [s9 (K.sp + 120#64) 4 (by bv_omega) (by bv_omega)]
  generalize hV10 : Vst V9 (K.p + 80#64) _ = V10
  have s10 := s9.st hK hV10 (by stp)
  simp only [s10 (K.sp + 124#64) 4 (by bv_omega) (by bv_omega)]
  generalize hV11 : Vst V10 (K.p + 84#64) _ = V11
  have s11 := s10.st hK hV11 (by stp)
  have hM11 := s11.mem0 hK hM0
  simp only [hM11.s0, hM11.v0, hM11.v1, hM11.v2, hM11.v3, hM11.v4, hM11.v5]
  have v1 : rdq(V11, K.sq + 8) = K.sv 1 := hM11.v1
  have v2 : rdq(V11, K.sq + 8 + 8) = K.sv 2 := hM11.v2
  have v3 : rdq(V11, K.sq + 8 + 8 + 8) = K.sv 3 := hM11.v3
  have v4 : rdq(V11, K.sq + 8 + 8 + 8 + 8) = K.sv 4 := hM11.v4
  have v5 : rdq(V11, K.sq + 8 + 8 + 8 + 8 + 8) = K.sv 5 := hM11.v5
  have erax : BitVec.setWidth 64 (BitVec.setWidth 32 rbx) = rbx := by rcases hb with rfl | rfl <;> rfl
  simp only [v1, v2, v3, v4, v5, erax]
  have rq : ∀ a : Addr, K.sq.toNat ≤ a.toNat → a.toNat + 8 ≤ K.sq.toNat + 48 → ∀ i, i < 8 → Foot F.data (a.add i) :=
    fun a h1 h2 i hi => by
      have e := toNat_add_of_fits (a := a) hi (by omega)
      exact hE.ws _ (hE.fr _ (by omega) (by omega))
  have pw : ∀ c n, 0x28 ≤ c → c + n ≤ 0x60 → ∀ i, i < n → Foot Wl ((K.p + BitVec.ofNat 64 c).add i) :=
    fun c n h1 h2 i hi => by
      have e0 : (K.p + BitVec.ofNat 64 c).toNat = K.p.toNat + c := by bv_omega
      have e := toNat_add_of_fits (a := K.p + BitVec.ofNat 64 c) hi (by omega)
      exact hE.pw _ (by omega) (by omega)
  have f40 : rdq(V11, K.p + 40#64) = BitVec.ofNat 64 dq := by
    rw [← hV11, ← hV10, ← hV9, ← hV8, ← hV7, ← hV6, ← hV5, ← hV4, ← hV3, ← hV2, ← hV1]
    iterate 10 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f48 : rdq(V11, K.p + 48#64) = r15 := by
    rw [← hV11, ← hV10, ← hV9, ← hV8, ← hV7, ← hV6, ← hV5, ← hV4, ← hV3, ← hV2]
    iterate 9 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f56 : rdd(V11, K.p + 56#64) = R := by
    rw [← hV11, ← hV10, ← hV9, ← hV8, ← hV7, ← hV6, ← hV5, ← hV4, ← hV3]
    iterate 8 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f88 : rdd(V11, K.p + 88#64) = BitVec.setWidth 32 r8 >>> 1 := by
    rw [← hV11, ← hV10, ← hV9, ← hV8, ← hV7, ← hV6, ← hV5]
    iterate 6 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f64 : rdd(V11, K.p + 64#64) = pp := by
    rw [← hV11, ← hV10, ← hV9, ← hV8, ← hV7, ← hV6]
    iterate 5 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f92 : rdd(V11, K.p + 92#64) = rdd(V, K.sp + 100#64) := by
    rw [← hV11, ← hV10, ← hV9, ← hV8, ← hV7]
    iterate 4 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f72 : rdd(V11, K.p + 72#64) = rdd(V, K.sp + 112#64) := by
    rw [← hV11, ← hV10, ← hV9, ← hV8]
    iterate 3 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f76 : rdd(V11, K.p + 76#64) = rdd(V, K.sp + 116#64) := by
    rw [← hV11, ← hV10, ← hV9]
    iterate 2 rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f80 : rdd(V11, K.p + 80#64) = rdd(V, K.sp + 120#64) := by
    rw [← hV11, ← hV10]
    rdv
    rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have f84 : rdd(V11, K.p + 84#64) = rdd(V, K.sp + 124#64) := by
    rw [← hV11, rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
  have hr := hN.2.r15
  have hst : (BitVec.setWidth 32 r8 >>> 1).toNat < 12 := by
    obtain ⟨s, rfl, h2, h3, h4⟩ := hS
    bv_omega
  refine ⟨hE.rd_fr hK 8 (by bv_omega) (by omega), hE.rd_fr hK 56 (by bv_omega) (by omega),
    pw 40 8 (by omega) (by omega), pw 48 8 (by omega) (by omega), pw 56 4 (by omega) (by omega),
    pw 60 4 (by omega) (by omega), fun fl => ⟨pw 88 4 (by omega) (by omega), pw 64 4 (by omega) (by omega),
      hE.rd_fr hK 100 (by bv_omega) (by omega), pw 92 4 (by omega) (by omega),
      hE.rd_fr hK 112 (by bv_omega) (by omega), pw 72 4 (by omega) (by omega),
      hE.rd_fr hK 116 (by bv_omega) (by omega), pw 76 4 (by omega) (by omega),
      hE.rd_fr hK 120 (by bv_omega) (by omega), pw 80 4 (by omega) (by omega),
      hE.rd_fr hK 124 (by bv_omega) (by omega), pw 84 4 (by omega) (by omega),
      hE.rd_fr hK 0 (by omega) (by omega), rq _ (by omega) (by omega), rq _ (by bv_omega) (by bv_omega),
      rq _ (by bv_omega) (by bv_omega), rq _ (by bv_omega) (by bv_omega), rq _ (by bv_omega) (by bv_omega),
      rq _ (by bv_omega) (by bv_omega), hq _ _ _ ?_⟩⟩
  exact ⟨by bv_omega, rfl, rfl, rfl, rfl, rfl, rfl, hb, hM11.pr, ⟨dq, f40, hd0, hdq, by rw [f64]; exact hpp⟩,
    by rw [f48]; exact hr.1, by rw [f48]; exact hr.2, by rw [f56]; exact hN.1, by rw [f88]; exact hst,
    fun h0 => ⟨by rw [f72]; exact (hb0 h0).r0, by rw [f76]; exact (hb0 h0).r1, by rw [f80]; exact (hb0 h0).r2,
      by rw [f84]; exact (hb0 h0).r3⟩, fun h1 => by rw [f92]; exact hb1 h1⟩
end FV7z.Lzma
