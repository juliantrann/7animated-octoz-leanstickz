import FV7z.Lzma.VcLit
/-!
# The verification conditions of a match or a repeat, up to the length (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

After the bit 1 of `IsMatch` (1044): the bit of `IsRep` (1088), and for a repeat the bits that tell which one (4002,
4055, 4182, 4266) with the four `reps` put in their new order, or the repeat of one byte (3911). The exits are the
start of the length (1129) and the store of a byte (2797).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

theorem kl_ge (s : BitVec 32) (h : 24 ≤ s.toNat) (δ : Nat) : kl s δ = 2 + δ := by
  unfold kl; split <;> omega

theorem kl_lt (s : BitVec 32) (h : s.toNat < 24) (δ : Nat) : kl s δ = 5 + δ := by
  unfold kl; split <;> omega

/-- A slot at an even place from the array's middle. -/
theorem inpr_so (hK : K.Ok) (s : BitVec 32) (c : BitVec 64) (hs2 : s.toNat % 2 = 0) (hsh : s.toNat < 24)
    (hc2 : c.toNat % 2 = 0) (hc : c.toNat ≤ 0x400) : InPr K (K.P + BitVec.setWidth 64 s + c) := by
  have := hK.hP; have := hK.hnp; have := hK.hnp0
  exact ⟨(0xd00 + s.toNat + c.toNat) / 2, by omega, by bv_omega⟩

/-- A slot of `IsRep0Long`. -/
theorem inpr_r0l (hK : K.Ok) (s x : BitVec 32) (hs2 : s.toNat % 2 = 0) (hsh : s.toNat < 24) (hx1 : x.toNat ≤ 480)
    (hx2 : x.toNat % 32 = 0) :
    InPr K (K.P + BitVec.setWidth 64 s + BitVec.setWidth 64 x + 18446744073709548544#64) := by
  have := hK.hP; have := hK.hnp; have := hK.hnp0
  exact ⟨(0x100 + s.toNat + x.toNat) / 2, by omega, by bv_omega⟩

theorem st_rep (s : BitVec 32) :
    St (BitVec.setWidth 64 (if (!decide (s.toNat < 14)) = true then 22#32 else 16#32)) 16 24 := by
  by_cases h : s.toNat < 14
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, rfl, by decide, by decide, by decide⟩
  · simp only [h, decide_false, Bool.not_false, ↓reduceIte]
    exact ⟨_, rfl, by decide, by decide, by decide⟩

theorem vc_1044 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Mat1044 K n g V)
    (hq : ∀ n' g' fl V', n' < n → Mat1088 K n' g' V' → Q 1088 g' fl V') :
    W_1044 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Mat1044, SymC, Bd, St, Px] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩, rfl, hN, rfl, rfl, hP, -, rfl⟩ := h
  wpx [W_1044, o16, BitVec.reduceSetWidth]
  have a1 := inpr_im hK s x hs2 hsh hx1 hx2
  have a2 := inpr_so hK s 32#64 hs2 hsh (by decide) (by decide)
  have hMem' := hMem.st_pr hK a1 hP.up1
  refine fun _ => ⟨hE.wr_pr hK a1, hE.rd_pr hK a2, wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit1 hP)
    fun R' rbp' r15' hN' fl => hq (2 ^ 20 * (K.lim - dp) + 8700) _ _ _ (by omega) ?_⟩
  exact ⟨dp, R', _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩,
    rfl, hN', rfl, hMem'.rd_pr a2, rfl⟩

theorem vc_1088 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Mat1088 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → RepB K n' g' V' 2 8600 True → Q 4002 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Len1129 K n' g' V' → Q 1129 g' fl V') :
    W_1088 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Mat1088, SymC, Bd, St, Px] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, rfl⟩ := h
  wpx [W_1088, o15, W_3936, o60, W_1104, o17, BitVec.reduceSetWidth]
  have a1 := inpr_so hK s 32#64 hs2 hsh (by decide) (by decide)
  have a2 := inpr_so hK s 56#64 hs2 hsh (by decide) (by decide)
  have := hK.hP; have := hK.hnp; have := hK.hnp0
  refine fun _ _ => ⟨fun _ _ => ?_, fun _ _ => ?_⟩
  · have hMem' := hMem.st_pr hK a1 hP.up1
    refine ⟨hE.wr_pr hK a1, hE.rd_pr hK a2, wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit1 hP)
      fun R' rbp' r15' hN' fl => hq1 (2 ^ 20 * (K.lim - dp) + 8600) _ _ _ (by omega) ?_⟩
    exact ⟨dp, R', _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, st_rep s, rfl, ⟨s, rfl, hs2, hsh⟩, x, rfl, hx1, hx2⟩,
      rfl, hN', rfl, hMem'.rd_pr a2, trivial, rfl⟩
  · have hMem' := hMem.st_pr hK a1 hP.up0
    refine ⟨hE.wr_pr hK a1, hq2 (2 ^ 20 * (K.lim - dp) + 8200) _ _ _ (by omega)
      ⟨dp, s + 24#32, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, by bv_omega, by bv_omega, by bv_omega⟩,
        (hN.bit0 hP).mono (by rw [kl_ge _ (by bv_omega)]; omega) (Nat.le_refl _), ⟨896, by bv_omega, by omega⟩,
        ⟨x, rfl, hx1, hx2⟩, rfl⟩⟩

theorem vc_4002 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : RepB K n g V 2 8600 True)
    (hq1 : ∀ n' g' fl V', n' < n → RepB K n' g' V' 3 8400 (RepV K g'.r9 ∧ RepV K g'.rbx) → Q 4182 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → RepB K n' g' V' 3 8500 True → Q 4055 g' fl V') :
    W_4002 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [RepB, RepC, Bd, Px] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hS, rfl, ⟨so, rfl, ho2, hoh⟩, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, -, rfl⟩ := h
  wpx [W_4002, o15, W_4128, o63, W_4014, o61, BitVec.reduceSetWidth]
  have a1 := inpr_so hK so 56#64 ho2 hoh (by decide) (by decide)
  have a2 := inpr_so hK so 80#64 ho2 hoh (by decide) (by decide)
  have a3 := inpr_r0l hK so x ho2 hoh hx1 hx2
  have := hK.hsq; have := hK.hsp2
  refine fun _ _ => ⟨fun _ _ => ?_, fun _ _ => ?_⟩
  · have hMem' := hMem.st_pr hK a1 hP.up1
    have hMem'' := hMem'.st_rep hK hMem'.r0 116 (by simp) rfl
    refine ⟨hE.wr_pr hK a1, hE.rd_fr hK 112 (by bv_omega) (by omega), hE.rd_fr hK 116 (by bv_omega) (by omega),
      hE.wr_fr hK 116 (by bv_omega) (by omega), hE.rd_pr hK a2,
      wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit1 hP)
        fun R' rbp' r15' hN' fl => hq1 (2 ^ 20 * (K.lim - dp) + 8400) _ _ _ (by omega) ?_⟩
    exact ⟨dp, R', _, ⟨⟨rfl, rfl, hMem'', hd0, hdp, hpp⟩, rfl, hS, rfl, ⟨so, rfl, ho2, hoh⟩, x, rfl, hx1, hx2⟩,
      rfl, hN', rfl, hMem''.rd_pr a2, ⟨by simp only [RepV, sw_64_32]; exact hMem'.r0,
        by simp only [RepV, sw_64_32]; exact hMem'.r1⟩, rfl⟩
  · have hMem' := hMem.st_pr hK a1 hP.up0
    refine ⟨hE.wr_pr hK a1, hE.rd_pr hK a3, wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit0 hP)
        fun R' rbp' r15' hN' fl => hq2 (2 ^ 20 * (K.lim - dp) + 8500) _ _ _ (by omega) ?_⟩
    exact ⟨dp, R', _, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, hS, rfl, ⟨so, rfl, ho2, hoh⟩, x, rfl, hx1, hx2⟩,
      rfl, hN', rfl, hMem'.rd_pr a3, trivial, rfl⟩

theorem vc_4182 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : RepB K n g V 3 8400 (RepV K g.r9 ∧ RepV K g.rbx))
    (hq1 : ∀ n' g' fl V', n' < n → RepB K n' g' V' 4 8300 (RepV K g'.r9) → Q 4266 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Len1129 K n' g' V' → Q 1129 g' fl V') :
    W_4182 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [RepB, RepC, Bd, Px, St] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, ⟨so, rfl, ho2, hoh⟩, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, ⟨h9, hb⟩, rfl⟩ := h
  wpx [W_4182, o15, W_4217, o65, W_4194, o64, BitVec.reduceSetWidth]
  have a1 := inpr_so hK so 80#64 ho2 hoh (by decide) (by decide)
  have a2 := inpr_so hK so 104#64 ho2 hoh (by decide) (by decide)
  have := hK.hsq; have := hK.hsp2; have := hK.hP; have := hK.hnp; have := hK.hnp0
  refine fun _ _ => ⟨fun _ _ => ?_, fun _ _ => ?_⟩
  · have hMem' := hMem.st_pr hK a1 hP.up1
    have hMem'' := hMem'.st_rep hK (v := BitVec.setWidth 32 rbx) hb 120 (by simp) rfl
    refine ⟨hE.wr_pr hK a1, hE.rd_fr hK 120 (by bv_omega) (by omega),
      hE.wr_fr hK 120 (by bv_omega) (by omega), hE.rd_pr hK a2,
      wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit1 hP)
        fun R' rbp' r15' hN' fl => hq1 (2 ^ 20 * (K.lim - dp) + 8300) _ _ _ (by omega) ?_⟩
    exact ⟨dp, R', _, ⟨⟨rfl, rfl, hMem'', hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, ⟨so, rfl, ho2, hoh⟩, x, rfl, hx1, hx2⟩,
      rfl, hN', rfl, hMem''.rd_pr a2, by simp only [RepV, sw_64_32]; exact hMem'.r2, rfl⟩
  · have hMem' := hMem.st_pr hK a1 hP.up0
    have hMem'' := hMem'.st_rep hK (v := BitVec.setWidth 32 rbx) hb 112 (by simp) rfl
    exact ⟨hE.wr_pr hK a1, hE.wr_fr hK 112 (by bv_omega) (by omega), hq2 (2 ^ 20 * (K.lim - dp) + 8200) _ _ _ (by omega)
      ⟨dp, s, ⟨⟨rfl, rfl, hMem'', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, by omega⟩,
        (hN.bit0 hP).mono (by rw [kl_lt _ hsh]; omega) (Nat.le_refl _), ⟨384, by bv_omega, by omega⟩,
        ⟨x, rfl, hx1, hx2⟩, rfl⟩⟩

theorem vc_4266 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : RepB K n g V 4 8300 (RepV K g.r9))
    (hq : ∀ n' g' fl V', n' < n → Len1129 K n' g' V' → Q 1129 g' fl V') :
    W_4266 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [RepB, RepC, Bd, Px, St] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, ⟨so, rfl, ho2, hoh⟩, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, h9, rfl⟩ := h
  wpx [W_4266, o15, W_4302, o67, W_4278, o66, BitVec.reduceSetWidth]
  have a1 := inpr_so hK so 104#64 ho2 hoh (by decide) (by decide)
  have := hK.hsq; have := hK.hsp2; have := hK.hP; have := hK.hnp; have := hK.hnp0
  refine fun _ _ => ⟨fun _ _ => ?_, fun _ _ => ?_⟩
  · have hMem' := hMem.st_pr hK a1 hP.up1
    have hMem'' := hMem'.st_rep hK (v := BitVec.setWidth 32 r9) h9 124 (by simp) rfl
    have hMem3 := hMem''.st_rep hK hMem'.r3 112 (by simp) rfl
    exact ⟨hE.wr_pr hK a1, hE.rd_fr hK 124 (by bv_omega) (by omega), hE.wr_fr hK 124 (by bv_omega) (by omega),
      hE.wr_fr hK 112 (by bv_omega) (by omega), hq (2 ^ 20 * (K.lim - dp) + 8200) _ _ _ (by omega)
      ⟨dp, s, ⟨⟨rfl, rfl, hMem3, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, by omega⟩,
        (hN.bit1 hP).mono (by rw [kl_lt _ hsh]; omega) (Nat.le_refl _), ⟨384, by bv_omega, by omega⟩,
        ⟨x, rfl, hx1, hx2⟩, rfl⟩⟩
  · have hMem' := hMem.st_pr hK a1 hP.up0
    have hMem'' := hMem'.st_rep hK (v := BitVec.setWidth 32 r9) h9 112 (by simp) rfl
    exact ⟨hE.wr_pr hK a1, hE.wr_fr hK 112 (by bv_omega) (by omega), hq (2 ^ 20 * (K.lim - dp) + 8200) _ _ _ (by omega)
      ⟨dp, s, ⟨⟨rfl, rfl, hMem'', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, by omega⟩,
        (hN.bit0 hP).mono (by rw [kl_lt _ hsh]; omega) (Nat.le_refl _), ⟨384, by bv_omega, by omega⟩,
        ⟨x, rfl, hx1, hx2⟩, rfl⟩⟩

theorem st_or2 (s : BitVec 32) (hs2 : s.toNat % 2 = 0) (hsl : 16 ≤ s.toNat) (hsh : s.toNat < 24) :
    St (BitVec.setWidth 64 (s ||| 2#32)) 14 24 := by
  have : s = 16#32 ∨ s = 18#32 ∨ s = 20#32 ∨ s = 22#32 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl, by decide, by decide, by decide⟩

theorem vc_4055 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : RepB K n g V 3 8500 True)
    (hq1 : ∀ n' g' fl V', n' < n → Rep3911 K n' g' V' → Q 3911 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Len1129 K n' g' V' → Q 1129 g' fl V') :
    W_4055 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [RepB, RepC, Bd, Px, St] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, ⟨so, rfl, ho2, hoh⟩, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, -, rfl⟩ := h
  wpx [W_4055, o15, W_3840, o57, W_3906, o58, W_4071, o62, BitVec.reduceSetWidth]
  have a1 := inpr_r0l hK so x ho2 hoh hx1 hx2
  have := hK.hsq; have := hK.hsp2; have := hK.hP; have := hK.hnp; have := hK.hnp0
  have hdic := hK.hdic; have hlim := hK.hlim
  have e11 : K.P + 18446744073709549056#64 - 18446744073709549056#64 = K.P := by bv_omega
  have ed : K.dic + BitVec.ofNat 64 dp - K.dic = BitVec.ofNat 64 dp := by bv_omega
  simp only [e11]
  refine fun _ _ => ⟨fun _ _ => ?_, fun _ _ => ?_⟩
  · have hMem' := hMem.st_pr hK a1 hP.up0
    have hr0 := hMem'.r0
    simp only [hMem'.s38, hMem'.s58, hMem'.s28, ed]
    refine ⟨hE.wr_pr hK a1, hE.rd_fr hK 56 (by bv_omega) (by omega), hE.rd_fr hK 112 (by bv_omega) (by omega),
      hE.rd_fr hK 88 (by bv_omega) (by omega), ?_⟩
    generalize Vst V _ _ = V' at hMem' hr0 ⊢
    generalize rdd(V', K.sp + 112#64) = r0 at hr0 ⊢
    have hC : CpC K ⟨BitVec.setWidth 64 (R >>> 11 * P), BitVec.setWidth 64 ((K.pbm &&& pp + 1) <<< 5), 0, 0, K.sp, 0,
        K.P + BitVec.setWidth 64 (s ||| 2#32), 0, BitVec.setWidth 64 (s ||| 2#32), 0, 2048#64, K.P, K.dic,
        BitVec.setWidth 64 (pp + 1), K.dic + BitVec.ofNat 64 dp, r15⟩ V' dp :=
      ⟨⟨rfl, rfl, hMem', hd0, hdp, pp + 1, rfl, fun h => by have := hpp h; bv_omega⟩, rfl, st_or2 s hs2 hsl hsh, rfl, rfl,
        px_of _ _ hK.hpbm, rfl, 4, 0, .inl ⟨by omega, by omega⟩, hN.bit0 hP⟩
    refine fun _ => ⟨fun h1 => ?_, fun h1 => ⟨hE.rd_fr hK 40 (by bv_omega) (by omega), ?_⟩⟩
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not] at h1
      exact hq1 (2 ^ 20 * (K.lim - dp) + 8400) _ _ _ (by omega) ⟨dp, dp - r0.toNat, hC, by bv_omega, by bv_omega, rfl⟩
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not] at h1
      exact hq1 (2 ^ 20 * (K.lim - dp) + 8400) _ _ _ (by omega)
        ⟨dp, dp + K.dbs - r0.toNat, hC, by bv_omega, by bv_omega, rfl⟩
  · have hMem' := hMem.st_pr hK a1 hP.up1
    exact ⟨hE.wr_pr hK a1, hq2 (2 ^ 20 * (K.lim - dp) + 8200) _ _ _ (by omega)
      ⟨dp, s, ⟨⟨rfl, rfl, hMem', hd0, hdp, pp, rfl, hpp⟩, rfl, rfl, hs2, hsl, by omega⟩,
        (hN.bit1 hP).mono (by rw [kl_lt _ hsh]; omega) (Nat.le_refl _), ⟨384, by bv_omega, by omega⟩,
        ⟨x, rfl, hx1, hx2⟩, rfl⟩⟩

theorem vc_3911 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Rep3911 K n g V)
    (hq : ∀ n' g' fl, n' < n → Cp2797 K n' g' V → Q 2797 g' fl V) :
    W_3911 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Rep3911, CpC, Bd, Px] at h
  obtain ⟨dq, o, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hS, rfl, rfl, hX, rfl, hR⟩, rfl, ho, rfl⟩ := h
  wpx [W_3911, o59, BitVec.reduceSetWidth]
  have hdic := hK.hdic; have hlim := hK.hlim
  exact ⟨hE.rd_dic hK o (by bv_omega) (by omega), hq (2 ^ 20 * (K.lim - dq) + 500) _ _ (by omega)
    ⟨dq, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hS, rfl, rfl, hX, rfl, hR⟩, rfl⟩⟩
end FV7z.Lzma
