import FV7z.Lzma.VcDist
/-!
# The verification conditions of a match's end and of its copy (PLAN.md G2.2)

2594: the distance against the dictionary's size and what was checked of it, the end marker, the repeats' store;
2664: the bytes to copy now, the source's place, whether it wraps around the dictionary's end; 2736, 2748, 2784,
2797: the copy within the dictionary, byte by byte, the last byte and the next symbol; 4505: the copy from the
dictionary's end up to the wrap.

The exit of a distance beyond the dictionary (4632 with `ebx = 1`) stores the distance as it is: there only `Mem0`
holds, with a remaining length of at least 514.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

/-- The state after a match: 7 or 10, doubled. -/
theorem st_mat (s : BitVec 32) :
    St (BitVec.setWidth 64 (if (!decide (s.toNat < 38)) = true then 20#32 else 14#32)) 14 24 := by
  split
  · exact ⟨20#32, rfl, by decide, by decide, by decide⟩
  · exact ⟨14#32, rfl, by decide, by decide, by decide⟩

/-! ## The source's place when it wraps -/

theorem wrap_lt (dp : Nat) (r0 : BitVec 32) (hd : dp < 2 ^ 64)
    (h : (BitVec.ofNat 64 dp).toNat < (BitVec.setWidth 64 r0).toNat) : dp < r0.toNat := by
  have e1 : (BitVec.ofNat 64 dp).toNat = dp := by rw [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.setWidth 64 r0).toNat = r0.toNat := by
    rw [BitVec.toNat_setWidth]; have := r0.isLt; omega
  rw [e1, e2] at h; omega
theorem wrap_src (dbs dp : Nat) (r0 : BitVec 32) (h1 : dp < r0.toNat) (h2 : r0.toNat ≤ dbs) (h3 : dbs < 2 ^ 64) :
    BitVec.ofNat 64 dp - BitVec.setWidth 64 r0 + BitVec.ofNat 64 dbs = BitVec.ofNat 64 (dp + dbs - r0.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have := r0.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega
theorem wrap_sub (dbs dp : Nat) (r0 : BitVec 32) (h1 : dp < r0.toNat) (h2 : r0.toNat ≤ dbs) (h3 : dbs < 2 ^ 64) :
    (BitVec.ofNat 64 dbs - (BitVec.ofNat 64 dp - BitVec.setWidth 64 r0 + BitVec.ofNat 64 dbs)).toNat =
      r0.toNat - dp := by
  rw [wrap_src dbs dp r0 h1 h2 h3]
  have := r0.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem neg_nat (c : BitVec 32) (h : 1 ≤ c.toNat) :
    0 - BitVec.setWidth 64 c = BitVec.ofNat 64 (18446744073709551616 - c.toNat) := by
  bv_omega
theorem sw_nat (c : BitVec 32) : BitVec.setWidth 64 c = BitVec.ofNat 64 c.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := c.isLt
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
theorem sw_toNat (c : BitVec 32) : (BitVec.setWidth 64 c).toNat = c.toNat := by
  have := c.isLt
  rw [BitVec.toNat_setWidth]; omega
theorem vc_2594 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Fin2594 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Cp2664 K n' g' V' → Q 2664 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Out4611 K n' g' V' → Q 4611 g' fl V')
    (hq3 : ∀ n' g' fl V', n' < n → Out4632 K n' g' V' → Q 4632 g' fl V') :
    W_2594 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Fin2594, PosC, LenC, Bd] at h
  obtain ⟨dp, k, d, ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, hB, hU, rfl⟩ := h
  wpx [W_2594, o39, W_4595, o78, W_4541, o77, W_4599, o79, W_2624, o40, BitVec.reduceSetWidth]
  simp only [hMem.s5c]
  have := hK.hsq; have := hK.hsp2
  have hlm : (if (K.ckd &&& K.ckd == 0) = true then pp else K.ckd).toNat ≤ K.dbs := by
    by_cases hc : K.ckd = 0
    · have h0 : K.ckd.toNat = 0 := by rw [hc]; rfl
      have := hpp h0; have := hK.hppb
      simp only [hc, BitVec.and_self, beq_self_eq_true, ↓reduceIte]; omega
    · have := hK.hckd
      simp only [BitVec.and_self, beq_iff_eq, hc, ↓reduceIte]; omega
  generalize (if (K.ckd &&& K.ckd == 0) = true then pp else K.ckd) = lm at hlm ⊢
  have fr : ∀ c, c + 4 ≤ 0x80 → ∀ i, i < 4 → Foot Wl ((K.sp + BitVec.ofNat 64 c).add i) :=
    fun c hc => hE.wr_fr hK c (by bv_omega) hc
  have hpp' : K.ckd.toNat = 0 → pp.toNat + (K.lim - dp) ≤ K.ppb := fun h => by have := hpp h; omega
  refine ⟨hE.rd_fr hK 112 (by bv_omega) (by omega), hE.rd_fr hK 116 (by bv_omega) (by omega),
    hE.rd_fr hK 120 (by bv_omega) (by omega), hE.rd_fr hK 92 (by bv_omega) (by omega), fun _ =>
    ⟨fun h1 => ⟨fun h2 => ⟨fr 100 (by omega), fr 112 (by omega), fr 116 (by omega), fr 120 (by omega),
      fr 124 (by omega), ?_⟩, fun h2 => ⟨fr 100 (by omega), ?_⟩⟩,
     fun h1 => ⟨fr 112 (by omega), fr 116 (by omega), fr 120 (by omega), fr 124 (by omega), ?_⟩⟩⟩
  · have hM1 := hMem.toMem0.st_free hK (a := K.sp + 100#64) (bs := toBytesLE (L + 512#32) 4)
      (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
    have hM2 := hM1.st_free hK (a := K.sp + 112#64) (bs := toBytesLE (BitVec.setWidth 32 rbx + 1) 4)
      (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
    have hM3 := hM2.st_free hK (a := K.sp + 116#64) (bs := toBytesLE rdd(V, K.sp + 112#64) 4)
      (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
    have hM4 := hM3.st_free hK (a := K.sp + 120#64) (bs := toBytesLE rdd(V, K.sp + 116#64) 4)
      (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
    have hM5 := hM4.st_free hK (a := K.sp + 124#64) (bs := toBytesLE rdd(V, K.sp + 120#64) 4)
      (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
    have e100 : rdd(Vst (Vst (Vst (Vst (Vst V (K.sp + 100#64) (toBytesLE (L + 512#32) 4)) (K.sp + 112#64)
        (toBytesLE (BitVec.setWidth 32 rbx + 1) 4)) (K.sp + 116#64) (toBytesLE rdd(V, K.sp + 112#64) 4))
        (K.sp + 120#64) (toBytesLE rdd(V, K.sp + 116#64) 4)) (K.sp + 124#64) (toBytesLE rdd(V, K.sp + 120#64) 4),
        K.sp + 100#64) = L + 512#32 := by
      rw [rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (by bv_omega) (by rw [toBytesLE_length]; bv_omega),
        rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (by bv_omega) (by rw [toBytesLE_length]; bv_omega),
        rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (by bv_omega) (by rw [toBytesLE_length]; bv_omega),
        rd_Vst _ _ _ _ _ (by rw [toBytesLE_length]; bv_omega) (by bv_omega) (by rw [toBytesLE_length]; bv_omega),
        rd_Vst_self _ _ _ (toBytesLE_length _ _) (by bv_omega), ofBytesLE_toBytesLE (by rfl)]
    refine wnorm_of hE hK hB hU fun R' rbp' r15' hN' fl => hq3 100 _ _ _ (by omega) ?_
    exact ⟨dp, k, d, pp, R', rfl, hM5, .inr rfl, fun h => absurd (show (1#64 : BitVec 64) = 0#64 from h) (by decide),
      fun _ => by rw [e100]; bv_omega, rfl, hd0, by omega, rfl, hN', (st_mat s).mono (by omega) (by omega), rfl, hpp', rfl⟩
  · have hM1 := hMem.st_free hK (a := K.sp + 100#64) (bs := toBytesLE 274#32 4)
      (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
    exact hq2 200 _ _ _ (by omega) ⟨dp, k, d, pp, rfl, hM1, rfl, hd0, by omega, hB, hU,
      ⟨s - 24#32, rfl, by bv_omega, by bv_omega, by bv_omega⟩, rfl, hpp', rfl⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not] at h1
    have hM1 := hMem.st_rep hK (v := BitVec.setWidth 32 rbx + 1) (by bv_omega) 112 (by simp) rfl
    have hM2 := hM1.st_rep hK (v := rdd(V, K.sp + 112#64)) hMem.r0 116 (by simp) rfl
    have hM3 := hM2.st_rep hK (v := rdd(V, K.sp + 116#64)) hMem.r1 120 (by simp) rfl
    have hM4 := hM3.st_rep hK (v := rdd(V, K.sp + 120#64)) hMem.r2 124 (by simp) rfl
    exact hq1 (2 ^ 20 * (K.lim - dp) + 4400) _ _ _ (by omega)
      ⟨dp, k, d, L, ⟨rfl, rfl, hM4, hd0, hdp, pp, rfl, hpp⟩, rfl, st_mat s, rfl, hB, hU, rfl, by omega, hL2, rfl⟩

theorem vc_2664 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Cp2664 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Cp2736 K n' g' V' → Q 2736 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Cp4505 K n' g' V' → Q 4505 g' fl V')
    (hq3 : ∀ n' g' fl V', n' < n → Out4611 K n' g' V' → Q 4611 g' fl V') :
    W_2664 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cp2664, Bd] at h
  obtain ⟨dp, k, d, L, ⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, hB, hU, rfl, hL1, hL2, rfl⟩ := h
  wpx [W_2664, o41, W_4535, o76, W_2678, o42, W_2716, o43, W_4491, o73, BitVec.reduceSetWidth]
  have := hK.hsq; have := hK.hsp2; have hdic := hK.hdic; have hlim := hK.hlim
  have hdb : K.dbs < 2 ^ 64 := by have := hK.aFD; bv_omega
  have hd64 : dp < 2 ^ 64 := by omega
  simp only [hMem.s40]
  have er : K.dic + BitVec.ofNat 64 K.lim - (K.dic + BitVec.ofNat 64 dp) = BitVec.ofNat 64 (K.lim - dp) := by bv_omega
  simp only [er]
  obtain ⟨c, ec, hc1, hc2, hc3⟩ : ∃ c : BitVec 32, (if (!decide ((BitVec.ofNat 64 (K.lim - dp)).toNat <
      (BitVec.setWidth 64 L).toNat)) = true then L else BitVec.setWidth 32 (BitVec.ofNat 64 (K.lim - dp))) = c ∧
      1 ≤ c.toNat ∧ c.toNat ≤ L.toNat ∧ c.toNat ≤ K.lim - dp := by
    by_cases hh : (BitVec.ofNat 64 (K.lim - dp)).toNat < (BitVec.setWidth 64 L).toNat
    · exact ⟨BitVec.setWidth 32 (BitVec.ofNat 64 (K.lim - dp)),
        by simp only [hh, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte], by bv_omega, by bv_omega,
        by bv_omega⟩
    · exact ⟨L, by simp only [hh, decide_false, Bool.not_false, ↓reduceIte], hL1, Nat.le_refl _, by bv_omega⟩
  simp only [ec]
  have hMem' := hMem.st_free hK (a := K.sp + 100#64) (bs := toBytesLE (L - c) 4)
    (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
  have hr0 := hMem.r0
  have ed : K.dic + BitVec.ofNat 64 dp - K.dic = BitVec.ofNat 64 dp := by bv_omega
  simp only [hMem.s38, hMem'.s28, ed]
  generalize rdd(V, K.sp + 112#64) = r0 at hr0 ⊢
  generalize Vst V (K.sp + 100#64) _ = V' at hMem' ⊢
  have hBd : ∀ x0 x1 x2 x3 x5 x6 x7 x9 x12 x15 : BitVec 64, Bd K ⟨x0, x1, x2, x3, K.sp, x5, x6, x7, r8, x9, 2048#64,
      K.P, x12, BitVec.setWidth 64 (pp + c), K.dic + BitVec.ofNat 64 dp + BitVec.setWidth 64 c, x15⟩ V'
      (dp + c.toNat - 1) 1 := fun _ _ _ _ _ _ _ _ _ _ =>
    ⟨rfl, rfl, hMem', by omega, by omega, pp + c, rfl, fun h => by have := hpp h; bv_omega⟩
  have e14 : K.dic + BitVec.ofNat 64 dp + BitVec.setWidth 64 c = K.dic + BitVec.ofNat 64 (dp + c.toNat - 1 + 1) := by
    bv_omega
  refine ⟨hE.rd_fr hK 64 (by bv_omega) (by omega), fun h1 => absurd (of_decide_eq_true h1) (by bv_omega),
    fun _ => ⟨hE.rd_fr hK 56 (by bv_omega) (by omega), hE.rd_fr hK 112 (by bv_omega) (by omega),
      hE.wr_fr hK 100 (by bv_omega) (by omega), fun h1 => ?_, fun h1 => ⟨hE.rd_fr hK 40 (by bv_omega) (by omega),
        fun h2 => ⟨hE.rd_fr hK 40 (by bv_omega) (by omega), ?_⟩, fun h2 => ?_⟩⟩⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
    have g1 : r0.toNat ≤ dp := by bv_omega
    exact hq1 (2 ^ 20 * (K.lim - (dp + c.toNat - 1)) + 4300) _ _ _ (by omega)
      ⟨dp + c.toNat - 1, c.toNat, dp - r0.toNat, k, d, hBd _ _ _ _ _ _ _ _ _ _, e14, hS, rfl, rfl, by bv_omega,
        by bv_omega, hc1, by omega, by omega, by omega, hB, hU, rfl⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at h1
    have g1 : dp < r0.toNat := wrap_lt dp r0 (by omega) h1
    have eX := wrap_sub K.dbs dp r0 g1 hr0 hdb
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h2
    have h21 := h2.1
    have h22 : (BitVec.setWidth 64 c).toNat ≠ _ := fun e => h2.2 (BitVec.eq_of_toNat_eq e)
    rw [eX, sw_toNat] at h21 h22
    clear h2 h1 eX
    rw [wrap_src K.dbs dp r0 g1 hr0 hdb, neg_nat c hc1]
    exact hq2 (2 ^ 20 * (K.lim - (dp + c.toNat - 1)) + 3000 + (K.dbs - (dp + K.dbs - r0.toNat))) _ _ _ (by omega)
      ⟨dp + c.toNat - 1, c.toNat, dp + K.dbs - r0.toNat, k, d, hBd _ _ _ _ _ _ _ _ _ _, e14, hS, rfl, rfl, rfl,
        rfl, rfl, rfl, by omega, by omega, by omega, by omega, hB, hU, rfl⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at h1
    have g1 : dp < r0.toNat := wrap_lt dp r0 (by omega) h1
    have eX := wrap_sub K.dbs dp r0 g1 hr0 hdb
    have g2 : c.toNat ≤ r0.toNat - dp := by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_false, Bool.or_eq_true, decide_eq_true_eq] at h2
      rcases h2 with h2 | h2
      · rw [eX, sw_toNat] at h2; exact Nat.le_of_lt h2
      · have h3 := congrArg BitVec.toNat h2; rw [eX, sw_toNat] at h3; exact Nat.le_of_eq h3
    clear h2 h1 eX
    rw [wrap_src K.dbs dp r0 g1 hr0 hdb]
    exact hq1 (2 ^ 20 * (K.lim - (dp + c.toNat - 1)) + 4300) _ _ _ (by omega)
      ⟨dp + c.toNat - 1, c.toNat, dp + K.dbs - r0.toNat, k, d, hBd _ _ _ _ _ _ _ _ _ _, e14, hS, rfl, rfl, rfl,
        sw_nat c, hc1, by omega, by omega, by omega, hB, hU, rfl⟩

theorem vc_2736 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Cp2736 K n g V)
    (hq : ∀ n' g' fl, n' < n → Cp2748 K n' g' V → Q 2748 g' fl V) :
    W_2736 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cp2736, Bd] at h
  obtain ⟨dq, cur, pos, k, d, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hS, rfl, rfl, rfl, rfl, hc1, hc2, hc3, hc4, hB, hU,
    rfl⟩ := h
  wpx [W_2736, o44, BitVec.reduceSetWidth]
  have hdic := hK.hdic; have hlim := hK.hlim
  have hdb : K.dbs < 2 ^ 64 := by have := hK.aFD; have := hK.hsq; have := hK.hsp2; omega
  exact ⟨hE.rd_dic hK pos (by bv_omega) (by omega), hq (2 ^ 20 * (K.lim - dq) + 2000) _ _ (by omega)
    ⟨dq, cur, pos + cur, k, d, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hS, rfl, rfl, by bv_omega, by bv_omega, hc1, hc2,
      hc3, by omega, hc4, hB, hU, rfl⟩⟩

theorem vc_2748 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Cp2748 K n g V)
    (hq1 : ∀ n' g' fl, n' < n → Cp2797 K n' g' V → Q 2797 g' fl V)
    (hq2 : ∀ n' g' fl, n' < n → Cp2784 K n' g' V → Q 2784 g' fl V) :
    W_2748 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cp2748, Bd] at h
  obtain ⟨dq, m, se, k, d, ⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, rfl, rfl, hm1, hm2, hm3, hm4,
    hm5, hB, hU, rfl⟩ := h
  wpx [W_2748, o45, W_2770, o46, BitVec.reduceSetWidth]
  simp only [hMem.s58]
  have hdic := hK.hdic; have hlim := hK.hlim; have := hK.hsq; have := hK.hsp2
  have e14 : K.dic + BitVec.ofNat 64 (dq + 1) - 1 = K.dic + BitVec.ofNat 64 dq := by bv_omega
  refine ⟨hE.rd_fr hK 88 (by bv_omega) (by omega), fun _ => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · exact hq1 (2 ^ 20 * (K.lim - dq) + 500) _ _ (by omega)
      ⟨dq, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, e14, hS, rfl, rfl, px_of _ _ hK.hpbm, rfl, k, d, hB, hU⟩, rfl⟩
  · simp only [beq_eq_false_iff_ne, ne_eq] at h1
    have hj : 2 ≤ m := by bv_omega
    exact hq2 (2 ^ 20 * (K.lim - dq) + 1000 + (m - 1)) _ _ (by omega)
      ⟨dq, m - 1, se, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, e14, hS, rfl, rfl, px_of _ _ hK.hpbm, rfl, k, d, hB,
        hU⟩, rfl, by bv_omega, by omega, by omega, by omega, by omega, hm5, rfl⟩

theorem vc_2784 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Cp2784 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Cp2784 K n' g' V' → Q 2784 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Cp2797 K n' g' V' → Q 2797 g' fl V') :
    W_2784 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cp2784, CpC, Bd] at h
  obtain ⟨dq, j, se, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, hX, rfl, hR⟩, rfl, rfl, hj1, hj2,
    hj3, hj4, hj5, rfl⟩ := h
  wpx [W_2784, o47, BitVec.reduceSetWidth]
  have hdic := hK.hdic; have hlim := hK.hlim
  have hMem' := hMem.st_free hK (a := K.dic + BitVec.ofNat 64 dq + BitVec.ofNat 64 (18446744073709551616 - j))
    (bs := toBytesLE (BitVec.setWidth 8 rbx) 1) (by rw [toBytesLE_length]; left; constructor <;> bv_omega)
  generalize Vst V _ _ = V' at hMem' ⊢
  refine ⟨hE.wr_dic hK (dq - j) (by bv_omega) (by omega) (by omega), hE.rd_dic hK (se - j) (by bv_omega) (by omega),
    fun h1 => ?_, fun h1 => ?_⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at h1
    have hj : 2 ≤ j := by bv_omega
    exact hq1 (2 ^ 20 * (K.lim - dq) + 1000 + (j - 1)) _ _ _ (by omega)
      ⟨dq, j - 1, se, ⟨⟨rfl, rfl, hMem', hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, hX, rfl, hR⟩, rfl, by bv_omega,
        by omega, by omega, by omega, by omega, hj5, rfl⟩
  · exact hq2 (2 ^ 20 * (K.lim - dq) + 500) _ _ _ (by omega)
      ⟨dq, ⟨⟨rfl, rfl, hMem', hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, hX, rfl, hR⟩, rfl⟩

theorem vc_4505 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Cp4505 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Cp4505 K n' g' V' → Q 4505 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Cp2748 K n' g' V' → Q 2748 g' fl V') :
    W_4505 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cp4505, Bd] at h
  obtain ⟨dq, m, ps, k, d, ⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, rfl, rfl, rfl, rfl, hp1, hp2,
    hm2, hm3, hB, hU, rfl⟩ := h
  wpx [W_4505, o74, W_4524, o75, BitVec.reduceSetWidth]
  have hdic := hK.hdic; have hlim := hK.hlim
  have hdb : K.dbs < 2 ^ 64 := by have := hK.aFD; have := hK.hsq; have := hK.hsp2; omega
  have hMem' := hMem.st_free hK
    (a := K.dic + BitVec.ofNat 64 (dq + 1) + BitVec.ofNat 64 (18446744073709551616 - m))
    (bs := toBytesLE (BitVec.setWidth 8 (BitVec.setWidth 32 (ofBytesLE 8 (List.map V
      (byteAddrs (K.dic + BitVec.ofNat 64 ps) 1))))) 1)
    (by rw [toBytesLE_length]; left; constructor <;> bv_omega)
  generalize Vst V _ _ = V' at hMem' ⊢
  refine ⟨hE.rd_dic hK ps (by bv_omega) (by omega), hE.wr_dic hK (dq + 1 - m) (by bv_omega) (by omega) (by omega),
    fun h1 => ?_, fun h1 => ?_⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
    have hj : ps + 1 < K.dbs := by bv_omega
    exact hq1 (2 ^ 20 * (K.lim - dq) + 3000 + (K.dbs - (ps + 1))) _ _ _ (by omega)
      ⟨dq, m - 1, ps + 1, k, d, ⟨rfl, rfl, hMem', hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, rfl, by bv_omega, rfl,
        by bv_omega, hj, by omega, by omega, by omega, hB, hU, rfl⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at h1
    have hj : ps + 1 = K.dbs := by bv_omega
    exact ⟨hE.rd_dic hK 0 (by omega) (by omega), hq2 (2 ^ 20 * (K.lim - dq) + 2000) _ _ _ (by omega)
      ⟨dq, m - 1, m - 1, k, d, ⟨rfl, rfl, hMem', hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, by bv_omega, by bv_omega,
        by omega, by omega, by omega, Nat.le_refl _, by omega, hB, hU, rfl⟩⟩

theorem vc_2797 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Cp2797 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Sym K n' g' V' 14 24 (g'.r12 = K.dic) → Q 2825 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Out4611 K n' g' V' → Q 4611 g' fl V') :
    W_2797 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cp2797, CpC, Bd] at h
  obtain ⟨dq, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, hS, rfl, rfl, hX, rfl, k, d, hB, hU⟩, rfl⟩ := h
  wpx [W_2797, o48, W_2814, o13, BitVec.reduceSetWidth]
  have hdic := hK.hdic; have hlim := hK.hlim; have := hK.hsq; have := hK.hsp2
  have hMem' := hMem.st_free hK (a := K.dic + BitVec.ofNat 64 dq) (bs := toBytesLE (BitVec.setWidth 8 rbx) 1)
    (by rw [toBytesLE_length]; left; constructor <;> bv_omega)
  simp only [hMem'.s48, hMem'.s40]
  generalize Vst V _ _ = V' at hMem' ⊢
  have e14 : K.dic + BitVec.ofNat 64 dq + 1 = K.dic + BitVec.ofNat 64 (dq + 1) := by bv_omega
  have hpp' : K.ckd.toNat = 0 → pp.toNat + (K.lim - (dq + 1)) ≤ K.ppb := fun h => by have := hpp h; omega
  have hout : ∀ fl, Q 4611 ⟨rax, rcx, rdx, rbx, K.sp, rbp, K.P + r8, rdi, r8, r9, 2048#64, K.P, K.dic,
      BitVec.setWidth 64 pp, K.dic + BitVec.ofNat 64 dq + 1, r15⟩ fl V' := fun fl =>
    hq2 200 _ fl _ (by omega) ⟨dq + 1, k, d, pp, rfl, hMem', e14, by omega, by omega, hB, hU,
      hS.mono (by omega) (by omega), rfl, hpp', rfl⟩
  refine ⟨hE.wr_dic hK dq (by bv_omega) hd0 (by omega), hE.rd_fr hK 72 (by bv_omega) (by omega),
      fun _ => hout _, fun h1 => ⟨hE.rd_fr hK 64 (by bv_omega) (by omega), fun _ => hout _, fun h2 => ?_⟩⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at h1 h2
  exact hq1 (2 ^ 20 * (K.lim - (dq + 1)) + 9000) _ _ _ (by omega) ⟨dq + 1, ⟨⟨rfl, rfl, hMem', by omega, by bv_omega,
    pp, rfl, hpp'⟩, e14, hS, rfl, rfl, hX⟩, hU.reset h1, rfl, rfl⟩
end FV7z.Lzma
