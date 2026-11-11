import FV7z.Lzma.VcLit
/-!
# The verification conditions of a literal after a match (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

The symbol's first bit after a match (2852) and after a literal that followed one (3797), the byte to match from
the dictionary (2960), the eight bits of the tree with `offs` (3023 to 3670), back to the start of a symbol, or out.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

theorem vc_2852 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : SymB K n g V 14 24 (g.r12 = K.dic))
    (hq1 : ∀ n' g' fl V', n' < n → MLit2960 K n' g' V' → Q 2960 g' fl V')
    (hq2 : ∀ n' g' fl, n' < n → Mat1044 K n' g' V → Q 1044 g' fl V) :
    W_2852 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [SymB, SymC, Bd, St, Px] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, rfl, rfl⟩ := h
  wpx [W_2852, o15, W_2868, o49, W_2955, o50, BitVec.reduceSetWidth]
  have := hK.hsq; have := hK.hsp2; have hdic := hK.hdic; have hlim := hK.hlim
  have a0 := inpr_im hK s x hs2 hsh hx1 hx2
  have hMem' := hMem.st_pr hK a0 hP.up0
  have hMem'' := hMem'.st_free hK (a := K.sp + 104#64) (bs := toBytesLE (K.dic + BitVec.ofNat 64 dp) 8)
    (by rw [toBytesLE_length]; right; left; constructor <;> bv_omega)
  have hr0 := hMem'.r0
  simp only [hMem.s54, hMem''.s28]
  generalize rdd(Vst V (K.P + BitVec.setWidth 64 s + BitVec.setWidth 64 x + 18446744073709551104#64)
    (toBytesLE (BitVec.setWidth 16 (P + (2048#32 - P) >>> 5)) 2), K.sp + 112#64) = r0 at hr0 ⊢
  have hT := lit_base hK (BitVec.setWidth 32 rbx + pp <<< 8 &&& K.lpm)
    (BitVec.setWidth 8 rdd(V, K.sp + 80#64)).toNat
    (by rw [BitVec.toNat_and]; exact Nat.and_le_right)
    (by have := hMem.s50; simp only [BitVec.toNat_setWidth]; omega)
  have hS := st_mlit s hs2 hsl hsh
  have hC : MLitC K ⟨0, 0, 0, rbx, K.sp, rbp, 0, rdi, BitVec.setWidth 64 (if (!decide ((s - 6#32).toNat < 14)) = true then
      BitVec.setWidth 32 (BitVec.setWidth 64 s + 18446744073709551604#64) else s - 6#32), r9, 2048#64,
      K.P + 640#64 + BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.setWidth 64 (BitVec.setWidth 32 rbx + pp <<< 8 &&& K.lpm) +
          BitVec.setWidth 64 (BitVec.setWidth 32 rbx + pp <<< 8 &&& K.lpm) * 2#64) <<<
            ((BitVec.setWidth 8 rdd(V, K.sp + 80#64)).toNat % 32)), 0, BitVec.setWidth 64 (pp + 1), 0, r15⟩
      (Vst (Vst V (K.P + BitVec.setWidth 64 s + BitVec.setWidth 64 x + 18446744073709551104#64)
        (toBytesLE (BitVec.setWidth 16 (P + (2048#32 - P) >>> 5)) 2))
        (K.sp + 104#64) (toBytesLE (K.dic + BitVec.ofNat 64 dp) 8)) dp :=
    ⟨hT, ⟨rfl, rfl, hMem'', hd0, hdp, _, rfl, fun h => by have := hpp h; bv_omega⟩, Spill.of_st hK _ _, hS⟩
  refine fun _ _ => ⟨fun _ => hq2 (2 ^ 20 * (K.lim - dp) + 8800) _ _ (by omega) ?_, fun _ _ =>
    ⟨hE.rd_fr hK 84 (by bv_omega) (by omega), hE.rd_fr hK 80 (by bv_omega) (by omega), fun _ _ =>
      ⟨hE.wr_pr hK a0, hE.rd_fr hK 112 (by bv_omega) (by omega), hE.wr_fr hK 104 (by bv_omega) (by omega),
        fun h1 => hq1 (2 ^ 20 * (K.lim - dp) + 8800) _ _ _ (by omega) ⟨dp, dp - r0.toNat, hC, hN.bit0 hP, rfl, ?_, ?_, rfl⟩,
        fun h1 => ⟨hE.rd_fr hK 40 (by bv_omega) (by omega),
          hq1 (2 ^ 20 * (K.lim - dp) + 8800) _ _ _ (by omega) ⟨dp, dp + K.dbs - r0.toNat, hC, hN.bit0 hP, rfl, ?_, ?_, rfl⟩⟩⟩⟩⟩
  · exact ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, ⟨s, rfl, hs2, by omega, by omega⟩, rfl, rfl, x, rfl, hx1, hx2⟩,
      rfl, hN, rfl, rfl, hP, fun _ => rfl, rfl⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not] at h1
    bv_omega
  · omega
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not] at h1
    bv_omega
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not] at h1
    bv_omega

theorem vc_2960 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : MLit2960 K n g V)
    (hq : ∀ n' g' fl, n' < n → MLit3023 K n' g' V → Q 3023 g' fl V) :
    W_2960 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [MLit2960, MLitC, Bd] at h
  obtain ⟨dp, o, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, hSp, hS⟩, hU, rfl, rfl, ho, rfl⟩ := h
  wpx [W_2960, o51, BitVec.reduceSetWidth]
  have hdic := hK.hdic; have hnp := hK.hnp
  generalize BitVec.setWidth 32 (ofBytesLE 8 (List.map V (byteAddrs (K.dic + BitVec.ofNat 64 o) 1))) <<< 2 = Y
  obtain ⟨A, B, hB, hA, hAB, hs⟩ := ofs_and Y 512#32 (.inr rfl)
  rw [BitVec.and_comm] at hB
  rw [hB, hA]
  obtain ⟨h1, h2, h3⟩ := hAB.nat
  obtain ⟨i, hTi, hTn⟩ := id hT
  have a1 : InPr K (r11 + BitVec.setWidth 64 B + 514#64) := hT.at (B.toNat / 2 + 257) (by omega) (by bv_omega)
  refine ⟨hE.rd_dic hK o (by bv_omega) (by omega), fun _ _ => ⟨hE.rd_pr hK a1, fun _ => ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 8700) _ _ (by omega) ?_
  exact ⟨dp, R', _, A, B, rfl, hN', rfl, hMem.rd_pr a1, a1, rfl, rfl, hAB, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, hSp, hS⟩, rfl⟩

theorem vc_3023 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : MLit3023 K n g V)
    (hq : ∀ n' g' fl V', n' < n → MLitI K n' g' V' 2 4 8600 (OfsR g') → Q 3118 g' fl V') :
    W_3023 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [MLit3023, MLitC, Bd] at h
  obtain ⟨dp, R, P1, A, B, rfl, hN, rfl, hP1, hdx, rfl, rfl, hAB, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, hSp, hS⟩, rfl⟩ := h
  wpx [W_3023, o52, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have hX := hAB.sel (!b)
  generalize (if (!b) = true then B else A) = X at hX ⊢
  obtain ⟨A', B', hB, hA, hAB', hs⟩ := ofs_and (BitVec.setWidth 32 r9) X hX
  rw [hB, hA]
  obtain ⟨h1, h2, h3⟩ := hAB'.nat
  obtain ⟨c, hc, ec⟩ := sbb_c3 b
  generalize 0#32 - 4294967293#32 - BitVec.setWidth 32 (BitVec.ofBool b) = X3 at ec ⊢
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have hD : InPrR K (r11 + BitVec.setWidth 64 X + BitVec.setWidth 64 B') 0x100 :=
    ⟨i + (X.toNat + B'.toNat) / 2, by bv_omega, by omega⟩
  have a3 : InPr K (r11 + BitVec.setWidth 64 X + BitVec.setWidth 64 B' + BitVec.setWidth 64 X3 * 2#64) :=
    hD.at (2 + c) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK hdx (hP1.upc b)
  refine fun _ _ _ _ => ⟨hE.wr_pr hK hdx, fun _ => ⟨hE.rd_pr hK a3, fun _ => ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 8600) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, rfl, hN', rfl, hMem'.rd_pr a3, rfl, by bv_omega, by bv_omega, by bv_omega, hD,
    ⟨A', B', rfl, rfl, hAB'⟩, ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, hSp.st_pr hK hdx _, hS⟩, rfl⟩

theorem vc_mlit53 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} {k lo rk e : Nat} (hk : k ≤ 20) (hlo : lo ≤ 64)
    (hrk : 100 ≤ rk) (h : MLitI K n g V k lo rk (OfsR g))
    (hq : ∀ n' g' fl V', n' < n → MLitI K n' g' V' (k + 1) (2 * lo) (rk - 100) (OfsR g') → Q e g' fl V') :
    wp F Wl o53 (Wnorm e F Wl Q) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [MLitI, MLitC, Bd, OfsR] at h
  obtain ⟨dp, R, P1, M, rfl, hN, rfl, hP1, rfl, hM2, hMl, hMh, hD, ⟨A, B, rfl, rfl, hAB⟩,
    ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, hSp, hS⟩, rfl⟩ := h
  wpx [o53, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have hX := hAB.sel (!b)
  generalize (if (!b) = true then B else A) = X at hX ⊢
  obtain ⟨A', B', hB, hA, hAB', hs⟩ := ofs_and (BitVec.setWidth 32 r9) X hX
  rw [hB, hA]
  obtain ⟨h1, h2, h3⟩ := hAB'.nat
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  generalize M - 4294967295#32 - BitVec.setWidth 32 (BitVec.ofBool b) = M' at ec ⊢
  obtain ⟨i, hTi, hTn⟩ := id hT
  obtain ⟨i', hDi, hDn⟩ := id hD
  have hnp := hK.hnp
  have hD' : InPrR K (r11 + BitVec.setWidth 64 X + BitVec.setWidth 64 B') 0x100 :=
    ⟨i + (X.toNat + B'.toNat) / 2, by bv_omega, by omega⟩
  have a2 : InPr K (rdx + BitVec.setWidth 64 M) := hD.at (M.toNat / 2) (by omega) (by bv_omega)
  have a3 : InPr K (r11 + BitVec.setWidth 64 X + BitVec.setWidth 64 B' + BitVec.setWidth 64 M' * 2#64) :=
    hD'.at (M.toNat + c) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ _ _ => ⟨hE.wr_pr hK a2, fun _ => ⟨hE.rd_pr hK a3, fun _ => ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + (rk - 100)) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, rfl, hN', rfl, hMem'.rd_pr a3, rfl, by bv_omega, by bv_omega, by bv_omega, hD',
    ⟨A', B', rfl, rfl, hAB'⟩, ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, hSp.st_pr hK a2 _, hS⟩, rfl⟩

theorem vc_3583 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : MLitI K n g V 7 128 8100 (OfsR g))
    (hq : ∀ n' g' fl V', n' < n → MLitI K n' g' V' 8 256 8000 True → Q 3670 g' fl V') :
    W_3583 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [MLitI, MLitC, Bd, OfsR] at h
  obtain ⟨dp, R, P1, M, rfl, hN, rfl, hP1, rfl, hM2, hMl, hMh, hD, ⟨A, B, rfl, rfl, hAB⟩,
    ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, hSp, hS⟩, rfl⟩ := h
  wpx [W_3583, o54, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have hX := hAB.sel (!b)
  generalize (if (!b) = true then B else A) = X at hX ⊢
  obtain ⟨A', B', hB, hA, hAB', hs⟩ := ofs_and (BitVec.setWidth 32 r9) X hX
  rw [hB]
  obtain ⟨h1, h2, h3⟩ := hAB'.nat
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  generalize M - 4294967295#32 - BitVec.setWidth 32 (BitVec.ofBool b) = M' at ec ⊢
  obtain ⟨i, hTi, hTn⟩ := id hT
  obtain ⟨i', hDi, hDn⟩ := id hD
  have hnp := hK.hnp
  have hD' : InPrR K (r11 + BitVec.setWidth 64 X + BitVec.setWidth 64 B') 0x100 :=
    ⟨i + (X.toNat + B'.toNat) / 2, by bv_omega, by omega⟩
  have a2 : InPr K (rdx + BitVec.setWidth 64 M) := hD.at (M.toNat / 2) (by omega) (by bv_omega)
  have a3 : InPr K (r11 + BitVec.setWidth 64 X + BitVec.setWidth 64 B' + BitVec.setWidth 64 M' * 2#64) :=
    hD'.at (M.toNat + c) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ _ _ => ⟨hE.wr_pr hK a2, fun _ => ⟨hE.rd_pr hK a3, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 8000) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, rfl, hN', rfl, hMem'.rd_pr a3, rfl, by bv_omega, by bv_omega, by bv_omega, hD',
    trivial, ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, hSp.st_pr hK a2 _, hS⟩, rfl⟩

theorem vc_3670 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : MLitI K n g V 8 256 8000 True)
    (hq1 : ∀ n' g' fl V', n' < n → Sym K n' g' V' 8 14 True → Q 3770 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Out4611 K n' g' V' → Q 4611 g' fl V') :
    W_3670 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [MLitI, MLitC, Bd] at h
  obtain ⟨dp, R, P1, M, rfl, hN, rfl, hP1, rfl, hM2, hMl, hMh, hD, -,
    ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, hSp, hS⟩, rfl⟩ := h
  wpx [W_3670, o55, W_3759, o13, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨i', hDi, hDn⟩ := id hD
  have hnp := hK.hnp; have := hK.hsq; have := hK.hsp2; have hdic := hK.hdic; have hlim := hK.hlim
  have a2 : InPr K (rdx + BitVec.setWidth 64 M) := hD.at (M.toNat / 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  have hSp' : Spill K _ dp := hSp.st_pr hK a2 (BitVec.setWidth 16 (((if b = true then 2048#32 else 31#32) - P1).sshiftRight 5 + P1))
  unfold Spill at hSp'
  have hMem'' := hMem'.st_free hK (a := K.dic + BitVec.ofNat 64 dp)
    (bs := toBytesLE (BitVec.setWidth 8 (M - 255#32 - BitVec.setWidth 32 (BitVec.ofBool b))) 1)
    (by rw [toBytesLE_length]; left; constructor <;> bv_omega)
  simp only [hMem'.s30, hMem'.s58, hSp', hMem''.s48, hMem''.s40]
  have e14 : K.dic + BitVec.ofNat 64 dp + 1 = K.dic + BitVec.ofNat 64 (dp + 1) := by bv_omega
  have hpp' : K.ckd.toNat = 0 → pp.toNat + (K.lim - (dp + 1)) ≤ K.ppb := fun h => by have := hpp h; omega
  have hout : ∀ fl, Q 4611 ⟨BitVec.setWidth 64 (if (!b) = true then R - R >>> 11 * P1 else R >>> 11 * P1),
      BitVec.setWidth 64 ((K.pbm &&& pp) <<< 5), rdx,
      BitVec.setWidth 64 (M - 255#32 - BitVec.setWidth 32 (BitVec.ofBool b)), K.sp,
      BitVec.setWidth 64 (if b = true then BitVec.setWidth 32 rbp else BitVec.setWidth 32 rbp - R >>> 11 * P1),
      K.P + r8, BitVec.setWidth 64 (((if b = true then 2048#32 else 31#32) - P1).sshiftRight 5 + P1), r8, r9,
      2048#64, K.P, r12, BitVec.setWidth 64 pp, K.dic + BitVec.ofNat 64 dp + 1, r15⟩ fl _ := fun fl =>
    hq2 200 _ fl _ (by omega) ⟨dp + 1, 9, 0, pp, rfl, hMem'', e14, by omega, by omega, .inl ⟨by omega, by omega⟩,
      hN.bit hP1 _, hS.mono (by omega) (by omega), rfl, hpp', rfl⟩
  refine fun _ _ _ _ => ⟨hE.wr_pr hK a2, hE.rd_fr hK 48 (by bv_omega) (by omega), hE.rd_fr hK 88 (by bv_omega) (by omega),
    fun _ => ⟨hE.rd_fr hK 104 (by bv_omega) (by omega), hE.wr_dic hK dp (by bv_omega) hd0 (by omega), hE.rd_fr hK 72 (by bv_omega) (by omega),
      fun _ => hout _, fun h1 => ⟨hE.rd_fr hK 64 (by bv_omega) (by omega), fun _ => hout _, fun h2 => ?_⟩⟩⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at h1 h2
  refine hq1 (2 ^ 20 * (K.lim - (dp + 1)) + 9000) _ _ _ (by omega) ⟨dp + 1, ⟨⟨rfl, rfl, hMem'', by omega, by bv_omega, pp, rfl, hpp'⟩,
    e14, hS, rfl, rfl, px_of _ _ hK.hpbm⟩, (hN.bit hP1 _).reset h1, trivial, rfl⟩

theorem vc_3797 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : SymB K n g V 8 14 True)
    (hq1 : ∀ n' g' fl, n' < n → Lit259 K n' g' V → Q 259 g' fl V)
    (hq2 : ∀ n' g' fl, n' < n → Mat1044 K n' g' V → Q 1044 g' fl V) :
    W_3797 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [SymB, SymC, Bd, St, Px] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, -, rfl⟩ := h
  wpx [W_3797, o15, W_3813, o56, BitVec.reduceSetWidth]
  have := hK.hsq; have := hK.hsp2
  simp only [hMem.s54]
  refine fun _ _ => ⟨fun _ => hq2 (2 ^ 20 * (K.lim - dp) + 8800) _ _ (by omega) ?_,
    fun _ => ⟨hE.rd_fr hK 84 (by bv_omega) (by omega), hq1 (2 ^ 20 * (K.lim - dp) + 8800) _ _ (by omega) ?_⟩⟩
  · exact ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, by omega, by omega⟩, rfl, rfl, x, rfl, hx1, hx2⟩,
      rfl, hN, rfl, rfl, hP, fun h => by exfalso; revert h; simp only [BitVec.toNat_setWidth]; omega, rfl⟩
  · exact ⟨dp, P, s, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hN.bit0 hP, rfl, hP, ⟨s - 6#32, rfl, by bv_omega, by bv_omega, by bv_omega⟩,
      rfl, rfl, hs2, by omega, ⟨x, rfl, hx1, hx2⟩, by simp only [sw_64_32], rfl⟩
end FV7z.Lzma
