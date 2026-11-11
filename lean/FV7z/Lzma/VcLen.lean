import FV7z.Lzma.VcMatch
/-!
# The verification conditions of the length (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

From the start of a length (1129): its two choices (1158, 1224), the tree of 8 for a low or a middle length (1376,
1422), the first six bits of the tree of 256 (the loop 1280, 1306), and the last two bits of either tree (1479,
1505, 1581). The exits are the copy (2664) for a repeat and the distance's slot (1695) for a match; the length is
from 2 to 273.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

theorem InPrR.mono {a : Addr} {m k : Nat} (h : InPrR K a m) (hk : k ≤ m) : InPrR K a k := by
  obtain ⟨i, hi, hn⟩ := h
  exact ⟨i, hi, by omega⟩

theorem InPrR.add {a : Addr} {m : Nat} (h : InPrR K a m) (j : Nat) (hj : j ≤ m) {b : Addr}
    (hb : b.toNat = a.toNat + 2 * j) : InPrR K b (m - j) := by
  obtain ⟨i, hi, hn⟩ := h
  exact ⟨i + j, by omega, by omega⟩

/-- The length from the tree's last step: 2 to 9, 10 to 17, 18 to 273. -/
theorem len_fin (lo : Nat) (r12 : BitVec 64) (M : BitVec 32) (b : Bool) (hT : LenT lo r12) (hM2 : M.toNat % 2 = 0)
    (hMl : 4 * lo ≤ M.toNat) (hMh : M.toNat < 8 * lo) :
    2 ≤ (M - BitVec.setWidth 32 r12 - BitVec.setWidth 32 (BitVec.ofBool b)).toNat ∧
      (M - BitVec.setWidth 32 r12 - BitVec.setWidth 32 (BitVec.ofBool b)).toNat ≤ 273 := by
  rcases hT with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;> cases b <;> simp <;> bv_omega

theorem vc_1129 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1129 K n g V)
    (hq : ∀ n' g' fl, n' < n → LenB K n' g' V 0 512 8100 5#64 → Q 1158 g' fl V) :
    W_1129 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1129, LenC, Bd, Px] at h
  obtain ⟨dp, s, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hU, hT, ⟨x, rfl, hx1, hx2⟩, rfl⟩ := h
  wpx [W_1129, o18, BitVec.reduceSetWidth]
  have a1 : InPr K r11 := hT.at 0 (by omega) (by omega)
  refine ⟨hE.rd_pr hK a1, wnorm_of hE hK (kl_bg s (by omega)) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 8100) _ _ (by omega) ?_⟩
  exact ⟨dp, s, R', _, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN', rfl, hMem.rd_pr a1, hT,
    ⟨x, rfl, hx1, hx2⟩, rfl, rfl⟩

theorem vc_1158 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : LenB K n g V 0 512 8100 5#64)
    (hq1 : ∀ n' g' fl V', n' < n → Len1376 K n' g' V' → Q 1376 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → LenB K n' g' V' 1 504 8000 4294967293#64 → Q 1224 g' fl V') :
    W_1158 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [LenB, LenC, Bd, Px] at h
  obtain ⟨dp, s, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN, rfl, hP, hT, ⟨x, rfl, hx1, hx2⟩, rfl, rfl⟩ := h
  wpx [W_1158, o15, W_1174, o19, BitVec.reduceSetWidth]
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K r11 := hT.at 0 (by omega) (by omega)
  have a2 : InPr K (r11 + 16#64) := hT.at 8 (by omega) (by bv_omega)
  refine fun _ _ => ⟨fun _ => hq1 (2 ^ 20 * (K.lim - dp) + 6900) _ _ _ (by omega)
    ⟨dp, s, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩,
      (hN.bit0 hP).mono (by rw [kl_succ]; exact kl_le s (by omega)) (Nat.le_refl _), rfl, hP, hT.mono (by omega),
      ⟨x, rfl, hx1, hx2⟩, .inl rfl, rfl⟩, fun _ _ => ?_⟩
  have hMem' := hMem.st_pr hK a1 hP.up1
  refine ⟨hE.wr_pr hK a1, hE.rd_pr hK a2, wnorm_of hE hK (kl_bg s (by omega))
    ((hN.bit1 hP).mono (Nat.le_of_eq (kl_succ s 0)) (Nat.le_refl _)) fun R' rbp' r15' hN' fl =>
    hq2 (2 ^ 20 * (K.lim - dp) + 8000) _ _ _ (by omega) ?_⟩
  exact ⟨dp, s, R', _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN', rfl, hMem'.rd_pr a2,
    hT.add 8 (by omega) (by bv_omega), ⟨x, rfl, hx1, hx2⟩, rfl, rfl⟩

theorem vc_1224 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : LenB K n g V 1 504 8000 4294967293#64)
    (hq1 : ∀ n' g' fl V', n' < n → Len1376 K n' g' V' → Q 1376 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Len1280 K n' g' V' → Q 1280 g' fl V') :
    W_1224 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [LenB, LenC, Bd, Px] at h
  obtain ⟨dp, s, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN, rfl, hP, hT, ⟨x, rfl, hx1, hx2⟩, rfl, rfl⟩ := h
  wpx [W_1224, o15, W_1240, o20, BitVec.reduceSetWidth]
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K r11 := hT.at 0 (by omega) (by omega)
  have a2 : InPr K (r11 + 496#64 + 2#64) := hT.at 249 (by omega) (by bv_omega)
  refine fun _ _ => ⟨fun _ => hq1 (2 ^ 20 * (K.lim - dp) + 6900) _ _ _ (by omega)
    ⟨dp, s, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩,
      (hN.bit0 hP).mono (Nat.le_of_eq (kl_succ s 1)) (Nat.le_refl _), rfl, hP, hT.mono (by omega),
      ⟨x, rfl, hx1, hx2⟩, .inr rfl, rfl⟩, fun _ _ => ?_⟩
  have hMem' := hMem.st_pr hK a1 hP.up1
  exact ⟨hE.wr_pr hK a1, hE.rd_pr hK a2, hq2 (2 ^ 20 * (K.lim - dp) + 7650 - 100 * 0) _ _ _ (by omega)
    ⟨dp, 0, s, _, 1#32, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, by omega,
      (hN.bit1 hP).mono (Nat.le_of_eq (kl_succ s 1)) (Nat.le_refl _), rfl, hMem'.rd_pr a2, rfl, by decide, by decide,
      hT.add 248 (by omega) (by bv_omega), rfl⟩⟩

theorem vc_1280 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1280 K n g V)
    (hq : ∀ n' g' fl, n' < n → Len1306 K n' g' V → Q 1306 g' fl V) :
    W_1280 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1280, LenC, Bd, Px] at h
  obtain ⟨dp, j, s, P1, M, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hj, hU, rfl, hP1, rfl, hMl, hMh, hT, rfl⟩ := h
  wpx [W_1280, o21, BitVec.reduceSetWidth]
  have hp : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 4#64) := hT.at (2 * M.toNat) (by omega) (by bv_omega)
  refine ⟨hE.rd_pr hK a1, wnorm_of hE hK (kl_bg s (by omega)) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 7600 - 100 * j) _ _ (by omega) ?_⟩
  exact ⟨dp, j, s, R', P1, _, M + M, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hj, rfl, hN', rfl, hP1,
    rfl, hMem.rd_pr a1, rfl, by bv_omega, by bv_omega, by bv_omega, hT, rfl⟩

theorem vc_1306 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1306 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Len1280 K n' g' V' → Q 1280 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Len1479 K n' g' V' → Q 1479 g' fl V') :
    W_1306 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1306, LenC, Bd, Px] at h
  obtain ⟨dp, j, s, R, P1, P2, M, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hj, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh, hT, rfl⟩ := h
  wpx [W_1306, o22, W_1368, o23, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have hp : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 2#64 + 2#64) := hT.at (M.toNat + 1) (by omega) (by bv_omega)
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, fun h1 => ?_, fun h1 => ?_⟩⟩
  · simp only [decide_eq_true_eq] at h1
    have hj' : j < 5 := by
      rcases Nat.lt_or_ge j 5 with h5 | h5
      · exact h5
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) h5
        omega
    exact hq1 (2 ^ 20 * (K.lim - dp) + 7650 - 100 * (j + 1)) _ _ _ (by omega)
      ⟨dp, j + 1, s, _, _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, by omega,
        (hN.bit hP1 _).mono (Nat.le_of_eq (kl_succ s (2 + j))) (Nat.le_refl _), rfl, (hMem.rd_pr a1).ite _ hP2, rfl,
        by omega, by omega, hT, rfl⟩
  · simp only [decide_eq_false_iff_not] at h1
    exact hq2 (2 ^ 20 * (K.lim - dp) + 6700) _ _ _ (by omega)
      ⟨dp, 64, s, _, _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩,
        (hN.bit hP1 _).mono (by rw [kl_succ]; exact kl_le s (by omega)) (Nat.le_refl _), rfl,
        (hMem.rd_pr a1).ite _ hP2, rfl, by omega, by omega, hT, .inr ⟨rfl, rfl⟩, rfl⟩

theorem vc_1376 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1376 K n g V)
    (hq : ∀ n' g' fl V', n' < n → Len1422 K n' g' V' → Q 1422 g' fl V') :
    W_1376 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1376, LenC, Bd, Px] at h
  obtain ⟨dp, s, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hU, rfl, hP, hT, ⟨x, rfl, hx1, hx2⟩, h12, rfl⟩ := h
  wpx [W_1376, o24, BitVec.reduceSetWidth]
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K r11 := hT.at 0 (by omega) (by omega)
  have a2 : InPr K (r11 + BitVec.setWidth 64 x + 2#64) := hT.at (x.toNat / 2 + 1) (by omega) (by bv_omega)
  have a3 : InPr K (r11 + BitVec.setWidth 64 x + 4#64) := hT.at (x.toNat / 2 + 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a1 hP.up0
  refine fun _ => ⟨hE.wr_pr hK a1, hE.rd_pr hK a2, hE.rd_pr hK a3, wnorm_of hE hK (kl_bg s (by omega)) hU
    fun R' rbp' r15' hN' fl => hq (2 ^ 20 * (K.lim - dp) + 6800) _ _ _ (by omega) ?_⟩
  exact ⟨dp, s, R', _, _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN', rfl, hMem'.rd_pr a2, rfl,
    hMem'.rd_pr a3, (hT.add (x.toNat / 2) (by omega) (by bv_omega)).mono (by omega), h12, rfl⟩

theorem vc_1422 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1422 K n g V)
    (hq : ∀ n' g' fl V', n' < n → Len1479 K n' g' V' → Q 1479 g' fl V') :
    W_1422 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1422, LenC, Bd, Px] at h
  obtain ⟨dp, s, R, P1, P2, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN, rfl, hP1, rfl, hP2, hT, h12, rfl⟩ := h
  wpx [W_1422, o25, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨c, hc, ec⟩ := sbb_c 2#32 b (by decide)
  have e2 : (2#32).toNat = 2 := rfl
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + 6#64) := hT.at 3 (by omega) (by bv_omega)
  have a2 : InPr K (r11 + 2#64) := hT.at 1 (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  exact fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, hq (2 ^ 20 * (K.lim - dp) + 6700) _ _ _ (by omega)
    ⟨dp, 2, s, _, _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩,
      (hN.bit hP1 _).mono (by rw [kl_succ]; exact kl_le s (by omega)) (Nat.le_refl _), rfl,
      (hMem.rd_pr a1).ite _ hP2, rfl, by omega, by omega, hT.mono (by omega), .inl ⟨rfl, h12⟩, rfl⟩⟩⟩

theorem vc_1479 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1479 K n g V)
    (hq : ∀ n' g' fl, n' < n → Len1505 K n' g' V → Q 1505 g' fl V) :
    W_1479 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1479, LenC, Bd, Px] at h
  obtain ⟨dp, lo, s, P1, M, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hU, rfl, hP1, rfl, hMl, hMh, hT, h12, rfl⟩ := h
  wpx [W_1479, o21, BitVec.reduceSetWidth]
  have hlo : lo ≤ 64 := by rcases h12 with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 4#64) := hT.at (2 * M.toNat) (by omega) (by bv_omega)
  refine ⟨hE.rd_pr hK a1, wnorm_of hE hK (kl_bg s (by omega)) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 6600) _ _ (by omega) ?_⟩
  exact ⟨dp, lo, s, R', P1, _, M + M, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN', rfl, hP1,
    rfl, hMem.rd_pr a1, rfl, by bv_omega, by bv_omega, by bv_omega, hT, h12, rfl⟩

theorem vc_1505 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1505 K n g V)
    (hq : ∀ n' g' fl V', n' < n → Len1581 K n' g' V' → Q 1581 g' fl V') :
    W_1505 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1505, LenC, Bd, Px] at h
  obtain ⟨dp, lo, s, R, P1, P2, M, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh, hT, h12, rfl⟩ := h
  wpx [W_1505, o11, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have hlo : lo ≤ 64 := by rcases h12 with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 2#64 + 2#64) := hT.at (M.toNat + 1) (by omega) (by bv_omega)
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, ?_⟩⟩
  refine wnorm_of hE hK (kl_bg s (by omega)) ((hN.bit hP1 _).mono (Nat.le_of_eq (kl_succ s 8)) (Nat.le_refl _))
    fun R' rbp' r15' hN' fl => hq (2 ^ 20 * (K.lim - dp) + 6500) _ _ _ (by omega) ?_
  exact ⟨dp, lo, s, R', _, _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN', rfl,
    (hMem.rd_pr a1).ite _ hP2, rfl, by bv_omega, by bv_omega, by bv_omega, hT, h12, rfl⟩

theorem vc_1581 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Len1581 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Cp2664 K n' g' V' → Q 2664 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Pos1695 K n' g' V' → Q 1695 g' fl V') :
    W_1581 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Len1581, LenC, Bd, Px] at h
  obtain ⟨dp, lo, s, R, P, M, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, rfl, hN, rfl, hP, rfl, hM2, hMl, hMh, hT, h12, rfl⟩ := h
  wpx [W_1581, o26, W_1642, o27, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P).toNat) = b
  have hlo : lo ≤ 64 := by rcases h12 with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  obtain ⟨hL1, hL2⟩ := len_fin lo r12 M b h12 hM2 hMl hMh
  generalize M - BitVec.setWidth 32 r12 - BitVec.setWidth 32 (BitVec.ofBool b) = L at hL1 hL2 ⊢
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp; have := hK.hsq; have := hK.hsp2; have := hK.hP; have := hK.hnp0
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP.upc b)
  simp only [hMem'.s30]
  refine fun _ _ _ _ => ⟨hE.wr_pr hK a2, hE.rd_fr hK 48 (by bv_omega) (by omega), fun h1 => ?_, fun h1 _ => ?_⟩
  · simp only [decide_eq_true_eq] at h1
    exact hq1 (2 ^ 20 * (K.lim - dp) + 4400) _ _ _ (by omega)
      ⟨dp, kl s 10, 0, L, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, by omega, h1⟩, rfl, kl_bg s (by omega),
        (hN.bit hP _).mono (Nat.le_of_eq (kl_succ s 9)) (Nat.le_refl _), rfl, by omega, hL2, rfl⟩
  · simp only [decide_eq_false_iff_not] at h1
    have he : ∃ e : BitVec 32, (if decide (L.toNat < 5) = true then L else 5#32) = e ∧ 2 ≤ e.toNat ∧ e.toNat ≤ 5 := by
      by_cases h5 : L.toNat < 5
      · exact ⟨L, by simp only [h5, decide_true, ↓reduceIte], hL1, by omega⟩
      · exact ⟨5#32, by simp only [h5, decide_false, Bool.false_eq_true, ↓reduceIte], by decide, by decide⟩
    obtain ⟨e, ee, he1, he2⟩ := he
    simp only [ee]
    have hT' : InPrR K (K.P + 18446744073709551488#64 + BitVec.setWidth 64 (e <<< 7)) 64 :=
      ⟨1600 + 64 * e.toNat, by bv_omega, by omega⟩
    have a3 := hT'.at 1 (by omega) (b := K.P + 18446744073709551488#64 + BitVec.setWidth 64 (e <<< 7) + 2#64) (by bv_omega)
    have a4 := hT'.at 2 (by omega) (b := K.P + 18446744073709551488#64 + BitVec.setWidth 64 (e <<< 7) + 4#64) (by bv_omega)
    refine ⟨hE.rd_pr hK a3, hE.rd_pr hK a4, wnorm_of hE hK (.inl ⟨by omega, by omega⟩)
      ((hN.bit hP _).mono (by rw [kl_ge _ (by omega)]; omega) (Nat.le_refl _)) (k := 12) fun R' rbp' r15' hN' fl =>
      hq2 (2 ^ 20 * (K.lim - dp) + 6400) _ _ _ (by omega) ?_⟩
    exact ⟨dp, R', _, _, ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, by omega, rfl, hL1, hL2⟩,
      rfl, hN', rfl, hMem'.rd_pr a3, rfl, hMem'.rd_pr a4, hT', rfl⟩
end FV7z.Lzma
