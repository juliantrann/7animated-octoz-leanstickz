import FV7z.Lzma.Inv
/-!
# The verification conditions of a literal (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

From the start of a symbol (1001) through its first bit (1028), the literal's start (259) and the eight bits of its
tree (341 to 905) back to the start of a symbol, or out (4611): at each cut point, the condition of `Cuts.lean` from
the invariant of `Inv.lean`, with the invariants of the next cut points at the exits.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

/-- The slot of a symbol's first bit. -/
theorem inpr_im (hK : K.Ok) (s x : BitVec 32) (hs2 : s.toNat % 2 = 0) (hsh : s.toNat < 24) (hx1 : x.toNat ≤ 480)
    (hx2 : x.toNat % 32 = 0) :
    InPr K (K.P + BitVec.setWidth 64 s + BitVec.setWidth 64 x + 18446744073709551104#64) := by
  have := hK.hP; have := hK.hnp; have := hK.hnp0
  exact ⟨(0xb00 + s.toNat + x.toNat) / 2, by omega, by bv_omega⟩

theorem vc_sym (hK : K.Ok) (hE : Env K F Wl) {Q : Post} {lo hi e : Nat} {X : BitVec 64 → BitVec 64 → Prop}
    (hhi : hi ≤ 24) (h : Sym K n g V lo hi (X g.r9 g.r12))
    (hq : ∀ n' g' fl, n' < n → SymB K n' g' V lo hi (X g'.r9 g'.r12) → Q e g' fl V) :
    wp F Wl o14 (Wnorm e F Wl Q) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Sym, SymC, Bd, St, Px] at h
  obtain ⟨dp, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩, hU, hXg, rfl⟩ := h
  wpx [o14]
  have a1 := inpr_im hK s x hs2 (by omega) hx1 hx2
  refine ⟨hE.rd_pr hK a1, wnorm_of hE hK (.inl ⟨by omega, by omega⟩) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 8900) _ _ (by omega) ?_⟩
  exact ⟨dp, R', _, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩,
    rfl, hN', rfl, hMem.rd_pr a1, hXg, rfl⟩

theorem vc_1028 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : SymB K n g V 0 8 (g.r9.setWidth 32 = K.lpm))
    (hq1 : ∀ n' g' fl, n' < n → Lit259 K n' g' V → Q 259 g' fl V)
    (hq2 : ∀ n' g' fl, n' < n → Mat1044 K n' g' V → Q 1044 g' fl V) :
    W_1028 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [SymB, SymC, Bd, St, Px] at h
  obtain ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, hsl, hsh⟩, rfl, rfl, x, rfl, hx1, hx2⟩, rfl, hN, rfl, hP, h9, rfl⟩ := h
  wpx [W_1028, o15, W_256, o4, BitVec.xor_self, BitVec.reduceSetWidth]
  refine fun _ _ => ⟨fun _ _ => hq1 (2 ^ 20 * (K.lim - dp) + 8800) _ _ (by omega) ?_,
    fun _ => hq2 (2 ^ 20 * (K.lim - dp) + 8800) _ _ (by omega) ?_⟩
  · exact ⟨dp, P, s, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hN.bit0 hP, rfl, hP, ⟨0#32, rfl, by decide, by decide, by decide⟩,
      rfl, rfl, hs2, by omega, ⟨x, rfl, hx1, hx2⟩, h9, rfl⟩
  · exact ⟨dp, R, P, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, ⟨s, rfl, hs2, by omega, by omega⟩, rfl, rfl, x, rfl, hx1, hx2⟩,
      rfl, hN, rfl, rfl, hP, fun h => by exfalso; revert h; simp only [BitVec.toNat_setWidth]; omega, rfl⟩

theorem vc_259 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : Lit259 K n g V)
    (hq : ∀ n' g' fl V', n' < n → Lit341 K n' g' V' → Q 341 g' fl V') :
    W_259 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lit259, Bd, Px] at h
  obtain ⟨dp, P, so, ⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩, rfl, hU, rfl, hP, hS, rfl, rfl, hso2, hso, ⟨x, rfl, hx1, hx2⟩, h9, rfl⟩ := h
  wpx [W_259, o5, BitVec.reduceSetWidth]
  have := hK.hsq; have := hK.hsp2
  have hT := lit_base hK (BitVec.setWidth 32 rbx + pp <<< 8 &&& BitVec.setWidth 32 r9)
    (BitVec.setWidth 8 rdd(V, K.sp + 80#64)).toNat
    (by rw [h9, BitVec.toNat_and]; exact Nat.and_le_right)
    (by have := hMem.s50; simp only [BitVec.toNat_setWidth]; omega)
  generalize K.P + 640#64 + BitVec.setWidth 64 (BitVec.setWidth 32
    (BitVec.setWidth 64 (BitVec.setWidth 32 rbx + pp <<< 8 &&& BitVec.setWidth 32 r9) +
      BitVec.setWidth 64 (BitVec.setWidth 32 rbx + pp <<< 8 &&& BitVec.setWidth 32 r9) * 2#64) <<<
        ((BitVec.setWidth 8 rdd(V, K.sp + 80#64)).toNat % 32)) = T at hT ⊢
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a0 := inpr_im hK so x hso2 hso hx1 hx2
  have a1 : InPr K (T + 2#64) := hT.at 1 (by omega) (by bv_omega)
  have a2 : InPr K (T + 4#64) := hT.at 2 (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a0 hP.up0
  refine fun _ => ⟨hE.rd_fr hK 80 (by bv_omega) (by omega), fun _ _ => ⟨hE.wr_pr hK a0, hE.rd_pr hK a1, hE.rd_pr hK a2, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 8700) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, rfl, hN', rfl, hMem'.rd_pr a1, rfl, hMem'.rd_pr a2,
    ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, _, rfl, fun h => by have := hpp h; bv_omega⟩, rfl, hS, h9⟩, rfl⟩


theorem vc_341 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Lit341 K n g V)
    (hq : ∀ n' g' fl V', n' < n → LitI K n' g' V' 2 4 8600 g'.rdx g'.rcx → Q 424 g' fl V') :
    W_341 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lit341, LitC, Bd] at h
  obtain ⟨dp, R, P1, P2, rfl, hN, rfl, hP1, rfl, hP2, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, hS, h9⟩, rfl⟩ := h
  wpx [W_341, o8, BitVec.reduceSetWidth]
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
    hq (2 ^ 20 * (K.lim - dp) + 8600) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, _, rfl, hN', rfl, (hMem.rd_pr a1).ite _ hP2, rfl, hMem'.rd_pr a3, rfl,
    by bv_omega, by bv_omega, by bv_omega, ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, hS, h9⟩, rfl⟩

theorem vc_lit9 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} {k lo rk e : Nat} (hk : k ≤ 20) (hlo : lo ≤ 128)
    (hrk : 100 ≤ rk) (h : LitI K n g V k lo rk g.rdx g.rcx)
    (hq : ∀ n' g' fl V', n' < n → LitI K n' g' V' (k + 1) (2 * lo) (rk - 100) g'.rcx g'.rdx → Q e g' fl V') :
    wp F Wl o9 (Wnorm e F Wl Q) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [LitI, LitC, Bd] at h
  obtain ⟨dp, R, P1, P2, M, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩,
    rfl, hS, h9⟩, rfl⟩ := h
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
    by bv_omega, by bv_omega, by bv_omega, ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, hS, h9⟩, rfl⟩

theorem vc_lit10 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} {k lo rk e : Nat} (hk : k ≤ 20) (hlo : lo ≤ 128)
    (hrk : 100 ≤ rk) (h : LitI K n g V k lo rk g.rcx g.rdx)
    (hq : ∀ n' g' fl V', n' < n → LitI K n' g' V' (k + 1) (2 * lo) (rk - 100) g'.rdx g'.rcx → Q e g' fl V') :
    wp F Wl o10 (Wnorm e F Wl Q) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [LitI, LitC, Bd] at h
  obtain ⟨dp, R, P1, P2, M, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩,
    rfl, hS, h9⟩, rfl⟩ := h
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
    by bv_omega, by bv_omega, by bv_omega, ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, hS, h9⟩, rfl⟩

theorem vc_829 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : LitI K n g V 7 128 8100 g.rcx g.rdx)
    (hq : ∀ n' g' fl V', n' < n → LitI K n' g' V' 8 256 8000 g'.rdx g'.rdx → Q 905 g' fl V') :
    W_829 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [LitI, LitC, Bd] at h
  obtain ⟨dp, R, P1, P2, M, rfl, hN, rfl, hP1, rfl, hP2, rfl, hM2, hMl, hMh, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, hpp⟩,
    rfl, hS, h9⟩, rfl⟩ := h
  wpx [W_829, o11, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨c, hc, ec⟩ := sbb_c M b (by omega)
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp
  have a1 : InPr K (r11 + BitVec.setWidth 64 M * 2#64 + 2#64) := hT.at (M.toNat + 1) (by omega) (by bv_omega)
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ _ => ⟨hE.wr_pr hK a2, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 8000) _ _ _ (by omega) ?_
  exact ⟨dp, R', _, _, _, rfl, hN', rfl, (hMem.rd_pr a1).ite _ hP2, rfl, (hMem.rd_pr a1).ite _ hP2, rfl,
    by bv_omega, by bv_omega, by bv_omega, ⟨hT, ⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, hS, h9⟩, rfl⟩

theorem vc_905 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : LitI K n g V 8 256 8000 g.rdx g.rdx)
    (hq1 : ∀ n' g' fl V', n' < n → Sym K n' g' V' 0 8 (g'.r9.setWidth 32 = K.lpm) → Q 1001 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Out4611 K n' g' V' → Q 4611 g' fl V') :
    W_905 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [LitI, LitC, Bd] at h
  obtain ⟨dp, R, P1, P2, M, rfl, hN, rfl, hP1, _, _, rfl, hM2, hMl, hMh, ⟨hT, ⟨rfl, rfl, hMem, hd0, hdp, pp, rfl, hpp⟩,
    rfl, hS, h9⟩, rfl⟩ := h
  wpx [W_905, o12, W_990, o13, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  obtain ⟨i, hTi, hTn⟩ := id hT
  have hnp := hK.hnp; have := hK.hsq; have := hK.hsp2; have hdic := hK.hdic; have hlim := hK.hlim
  have a2 : InPr K (r11 + BitVec.setWidth 64 M) := hT.at (M.toNat / 2) (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  have hMem'' := hMem'.st_free hK (a := K.dic + BitVec.ofNat 64 dp)
    (bs := toBytesLE (BitVec.setWidth 8 (M - 255#32 - BitVec.setWidth 32 (BitVec.ofBool b))) 1)
    (by rw [toBytesLE_length]; left; constructor <;> bv_omega)
  simp only [hMem'.s30, hMem'.s58, hMem''.s48, hMem''.s40]
  have e14 : K.dic + BitVec.ofNat 64 dp + 1 = K.dic + BitVec.ofNat 64 (dp + 1) := by bv_omega
  have hpp' : K.ckd.toNat = 0 → pp.toNat + (K.lim - (dp + 1)) ≤ K.ppb := fun h => by have := hpp h; omega
  have hout : ∀ fl, Q 4611 ⟨BitVec.setWidth 64 (if (!b) = true then R - R >>> 11 * P1 else R >>> 11 * P1),
      BitVec.setWidth 64 ((K.pbm &&& pp) <<< 5), BitVec.setWidth 64 P1,
      BitVec.setWidth 64 (M - 255#32 - BitVec.setWidth 32 (BitVec.ofBool b)), K.sp,
      BitVec.setWidth 64 (if b = true then BitVec.setWidth 32 rbp else BitVec.setWidth 32 rbp - R >>> 11 * P1),
      K.P + r8, BitVec.setWidth 64 (((if b = true then 2048#32 else 31#32) - P1).sshiftRight 5 + P1), r8, r9,
      2048#64, K.P, r12, BitVec.setWidth 64 pp, K.dic + BitVec.ofNat 64 dp + 1, r15⟩ fl _ := fun fl =>
    hq2 200 _ fl _ (by omega) ⟨dp + 1, 9, 0, pp, rfl, hMem'', e14, by omega, by omega, .inl ⟨by omega, by omega⟩,
      hN.bit hP1 _, hS.mono (by omega) (by omega), rfl, hpp', rfl⟩
  refine fun _ _ _ _ => ⟨hE.wr_pr hK a2, hE.rd_fr hK 48 (by bv_omega) (by omega), hE.rd_fr hK 88 (by bv_omega) (by omega),
    fun _ => ⟨hE.wr_dic hK dp (by bv_omega) hd0 (by omega), hE.rd_fr hK 72 (by bv_omega) (by omega),
      fun _ => hout _, fun h1 => ⟨hE.rd_fr hK 64 (by bv_omega) (by omega), fun _ => hout _, fun h2 => ?_⟩⟩⟩
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at h1 h2
  refine hq1 (2 ^ 20 * (K.lim - (dp + 1)) + 9000) _ _ _ (by omega) ⟨dp + 1, ⟨⟨rfl, rfl, hMem'', by omega, by bv_omega, pp, rfl, hpp'⟩,
    e14, hS, rfl, rfl, px_of _ _ hK.hpbm⟩, (hN.bit hP1 _).reset h1, h9, rfl⟩
end FV7z.Lzma
