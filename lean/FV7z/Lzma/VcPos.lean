import FV7z.Lzma.VcLen
/-!
# The verification conditions of the distance's slot (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

The six bits of the slot (1695 to 2099), a tree of 64 probabilities. From the slot: a distance below 4 as it is
(2594), one below 128 with its bits from `SpecPos` (4384), a longer one with direct bits (2226).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

theorem and3_cases (Z : BitVec 32) :
    Z &&& 3#32 = 0#32 ∨ Z &&& 3#32 = 1#32 ∨ Z &&& 3#32 = 2#32 ∨ Z &&& 3#32 = 3#32 := by
  have h : (Z &&& 3#32).toNat = Z.toNat % 4 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 2
  rcases (by omega : Z.toNat % 4 = 0 ∨ Z.toNat % 4 = 1 ∨ Z.toNat % 4 = 2 ∨ Z.toNat % 4 = 3) with e | e | e | e
  · exact .inl (BitVec.eq_of_toNat_eq (h.trans e))
  · exact .inr (.inl (BitVec.eq_of_toNat_eq (h.trans e)))
  · exact .inr (.inr (.inl (BitVec.eq_of_toNat_eq (h.trans e))))
  · exact .inr (.inr (.inr (BitVec.eq_of_toNat_eq (h.trans e))))

/-- The first of the probabilities of a distance below 128, and the reach of its bits: within `SpecPos`. -/
theorem spec_base (Z X : BitVec 32) (h1 : 34 ≤ X.toNat) (h2 : X.toNat ≤ 38) :
    ((Z &&& 3#32 ||| 2#32) <<< ((BitVec.setWidth 8 (X - 33#32)).toNat % 32)).toNat + 2 ^ (X - 33#32).toNat ≤ 128 := by
  have hX : X = 34#32 ∨ X = 35#32 ∨ X = 36#32 ∨ X = 37#32 ∨ X = 38#32 := by
    rcases (by omega : X.toNat = 34 ∨ X.toNat = 35 ∨ X.toNat = 36 ∨ X.toNat = 37 ∨ X.toNat = 38) with e | e | e | e | e
    · exact .inl (BitVec.eq_of_toNat_eq e)
    · exact .inr (.inl (BitVec.eq_of_toNat_eq e))
    · exact .inr (.inr (.inl (BitVec.eq_of_toNat_eq e)))
    · exact .inr (.inr (.inr (.inl (BitVec.eq_of_toNat_eq e))))
    · exact .inr (.inr (.inr (.inr (BitVec.eq_of_toNat_eq e))))
  rcases hX with rfl | rfl | rfl | rfl | rfl <;> rcases and3_cases Z with e | e | e | e <;> rw [e] <;> decide

theorem vc_1695 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Pos1695 K n g V)
    (hq : ∀ n' g' fl V', n' < n → PosI K n' g' V' 13 4 6300 g'.rdx g'.rcx → Q 1778 g' fl V') :
    W_1695 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Pos1695, PosC, LenC, Bd] at h
  obtain ⟨dp, R, P1, P2, ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, hN, rfl, hP1, rfl, hP2, hT, rfl⟩ := h
  wpx [W_1695, o8, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨c, hc, ec⟩ := sbb_c 2#32 b (by decide)
  generalize 2#32 - 4294967295#32 - BitVec.setWidth 32 (BitVec.ofBool b) = X at ec ⊢
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + 6#64) := hT.at 3 (by omega) (by bv_omega)
  have a2 : InPr K (r11 + 2#64) := hT.at 1 (by omega) (by bv_omega)
  have a3 : InPr K (r11 + BitVec.setWidth 64 X * 4#64) := hT.at (2 * (2 + c)) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, hE.rd_pr hK a3, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 6300) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, _, rfl, hN', rfl, (hMem.rd_pr a1).ite _ hP2, rfl, hMem'.rd_pr a3, rfl,
    by bv_omega, by bv_omega, by bv_omega,
    ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩

theorem vc_pos9 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} {k lo rk e : Nat} (hk : k ≤ 20) (hlo : lo ≤ 16)
    (hrk : 100 ≤ rk) (h : PosI K n g V k lo rk g.rdx g.rcx)
    (hq : ∀ n' g' fl V', n' < n → PosI K n' g' V' (k + 1) (2 * lo) (rk - 100) g'.rcx g'.rdx → Q e g' fl V') :
    wp F Wl o9 (Wnorm e F Wl Q) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [PosI, PosC, LenC, Bd] at h
  obtain ⟨dp, R, P1, P2, M, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh,
    ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩ := h
  wpx [o9, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 2#64 + 2#64) := hT.at (M.toNat + 1) (by omega) (by bv_omega)
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have a3 : InPr K (r11 + BitVec.setWidth 64 (M - 4294967295#32 - BitVec.setWidth 32 (BitVec.ofBool b)) * 4#64) :=
    hT.at (2 * (M.toNat + c)) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, hE.rd_pr hK a3, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + (rk - 100)) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, _, rfl, hN', rfl, (hMem.rd_pr a1).ite _ hP2, rfl, hMem'.rd_pr a3, rfl,
    by bv_omega, by bv_omega, by bv_omega,
    ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩

theorem vc_pos10 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} {k lo rk e : Nat} (hk : k ≤ 20) (hlo : lo ≤ 16)
    (hrk : 100 ≤ rk) (h : PosI K n g V k lo rk g.rcx g.rdx)
    (hq : ∀ n' g' fl V', n' < n → PosI K n' g' V' (k + 1) (2 * lo) (rk - 100) g'.rdx g'.rcx → Q e g' fl V') :
    wp F Wl o10 (Wnorm e F Wl Q) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [PosI, PosC, LenC, Bd] at h
  obtain ⟨dp, R, P1, P2, M, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh,
    ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩ := h
  wpx [o10, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 2#64 + 2#64) := hT.at (M.toNat + 1) (by omega) (by bv_omega)
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have a3 : InPr K (r11 + BitVec.setWidth 64 (M - 4294967295#32 - BitVec.setWidth 32 (BitVec.ofBool b)) * 4#64) :=
    hT.at (2 * (M.toNat + c)) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, hE.rd_pr hK a3, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + (rk - 100)) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, _, rfl, hN', rfl, (hMem.rd_pr a1).ite _ hP2, rfl, hMem'.rd_pr a3, rfl,
    by bv_omega, by bv_omega, by bv_omega,
    ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩

theorem vc_2021 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : PosI K n g V 16 32 6000 g.rcx g.rdx)
    (hq : ∀ n' g' fl V', n' < n → Pos2099 K n' g' V' → Q 2099 g' fl V') :
    W_2021 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [PosI, PosC, LenC, Bd] at h
  obtain ⟨dp, R, P1, P2, M, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh,
    ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩ := h
  wpx [W_2021, o28, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 2#64 + 2#64) := hT.at (M.toNat + 1) (by omega) (by bv_omega)
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 5900) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, rfl, hN', rfl, (hMem.rd_pr a1).ite _ hP2, rfl, rfl, by bv_omega, by bv_omega,
    ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩

theorem vc_2099 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Pos2099 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Fin2594 K n' g' V' → Q 2594 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Spec4384 K n' g' V' → Q 4384 g' fl V')
    (hq3 : ∀ n' g' fl V', n' < n → Dir2226 K n' g' V' → Q 2226 g' fl V') :
    W_2099 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Pos2099, PosC, LenC, Bd] at h
  obtain ⟨dp, R, P, X, rfl, hN, rfl, hP, rfl, rfl, hX1, hX2,
    ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, hT, rfl⟩ := h
  wpx [W_2099, o29, W_4352, o68, W_4361, o69, W_2162, o30, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P).toNat) = b
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp; have := hK.hsq; have := hK.hsp2; have := hK.hP; have := hK.hnp0
  have a2 : InPr K (r11 + BitVec.setWidth 64 (X + X)) := hT.at X.toNat (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP.upc b)
  generalize Vst V (r11 + BitVec.setWidth 64 (X + X)) _ = V' at hMem' ⊢
  simp only [hMem'.s30]
  have hC : ∀ x0 x1 x2 x3 x5 x6 x7 x9 x11 x15, PosC K ⟨x0, x1, x2, x3, K.sp, x5, x6, x7,
      BitVec.setWidth 64 s, x9, 2048#64, x11, BitVec.setWidth 64 L, r13, K.dic + BitVec.ofNat 64 dp, x15⟩ V' dp :=
    fun _ _ _ _ _ _ _ _ _ _ =>
      ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩
  refine fun _ _ _ _ => ⟨hE.wr_pr hK a2, fun _ => ⟨hE.rd_fr hK 48 (by bv_omega) (by omega),
    fun h1 => ⟨fun h2 => ?_, fun h2 _ => ?_⟩, fun h1 => ?_⟩⟩
  · exact hq1 (2 ^ 20 * (K.lim - dp) + 4500) _ _ _ (by omega)
      ⟨dp, 18, 0, hC _ _ _ _ _ _ _ _ _ _, rfl, .inl ⟨by omega, by omega⟩, hN.bit hP _, rfl⟩
  · simp only [decide_eq_true_eq] at h1
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h2
    have h33 : X.toNat ≠ 33 := fun e => h2.2 (BitVec.eq_of_toNat_eq e)
    have hW := spec_base (X + X - 63#32 - BitVec.setWidth 32 (BitVec.ofBool b)) X (by omega) (by omega)
    have hc : (X - 33#32).toNat = X.toNat - 33 := by bv_omega
    have hT5 : 2 ^ (X - 33#32).toNat ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
    generalize (X + X - 63#32 - BitVec.setWidth 32 (BitVec.ofBool b) &&& 3#32 ||| 2#32) <<<
      ((BitVec.setWidth 8 (X - 33#32)).toNat % 32) = W at hW ⊢
    generalize hTe : 2 ^ (X - 33#32).toNat = T at hW hT5
    exact hq2 (2 ^ 20 * (K.lim - dp) + 5000 + 20 * (X - 33#32).toNat + 10) _ _ _ (by omega)
      ⟨dp, 1, W.toNat + 1, T, X - 33#32, hC _ _ _ _ _ _ _ _ _ _, rfl, by omega, by omega, rfl, by omega,
        by rw [Nat.one_mul]; exact hTe, by omega, by bv_omega, by omega,
        (hN.bit hP _).mono (by omega) (Nat.le_refl _), rfl⟩
  · simp only [decide_eq_false_iff_not] at h1
    have a5 : InPr K (K.P + 2#64) := ⟨1665, by omega, by bv_omega⟩
    refine ⟨hE.rd_pr hK a5, fun _ => ?_⟩
    exact hq3 (2 ^ 20 * (K.lim - dp) + 5000 + 20 * (X - 37#32).toNat + 10) _ _ _ (by bv_omega)
      ⟨dp, 0, X - 37#32, ⟨hC _ _ _ _ _ _ _ _ _ _, rfl, rfl, _, rfl, hMem'.rd_pr a5⟩, rfl, by bv_omega, by bv_omega,
        hN.bit hP _, rfl⟩
end FV7z.Lzma
