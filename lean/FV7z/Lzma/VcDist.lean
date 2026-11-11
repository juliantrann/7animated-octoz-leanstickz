import FV7z.Lzma.VcPos
/-!
# The verification conditions of the distance's bits (PLAN.md G2, pilot `LzmaDec_DecodeReal_3`)

After the slot: the direct bits of a long distance (the loop 2226, 2208), then the four bits of `Align` (2295 to
2546); the bits of a distance below 128 from `SpecPos` (the loop 4384, 4412). All end at 2594 with the distance in
`rbx`, of which nothing is known here: 2594 checks it.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Lzma
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace FV7z.Lzma
variable {K : Ctx} {F : Footprint} {Wl : List Rgn} {V : Addr → Byte} {n : Nat} {g : Gprs} {f : Rflags}

/-- A `cmov` of 64 bits to `r9`, or to `rbx`: the choice is of that register alone. -/
theorem ite_mk9 (c : Prop) [Decidable c] (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (if c then Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 v a10 a11 a12 a13 a14 a15
      else Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) =
    Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 (if c then v else a9) a10 a11 a12 a13 a14 a15 := by
  split <;> rfl

theorem ite_mk3 (c : Prop) [Decidable c] (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (if c then Gprs.mk a0 a1 a2 v a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      else Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) =
    Gprs.mk a0 a1 a2 (if c then v else a3) a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := by
  split <;> rfl

theorem PosC.gpr {g g' : Gprs} {dp : Nat} (h : PosC K g V dp) (h1 : g'.rsp = g.rsp) (h2 : g'.r10 = g.r10)
    (h3 : g'.r13 = g.r13) (h4 : g'.r14 = g.r14) (h5 : g'.r8 = g.r8) (h6 : g'.r12 = g.r12) : PosC K g' V dp := by
  simp only [PosC, LenC, Bd, h1, h2, h3, h4, h5, h6]
  exact h

theorem PosC.mem {g : Gprs} {dp : Nat} (h : PosC K g V dp) : Mem K V := by
  obtain ⟨s, L, ⟨⟨-, -, hMem, -⟩, -⟩, -⟩ := h
  exact hMem

theorem vc_2226 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Dir2226 K n g V)
    (hq : ∀ n' g' fl V', n' < n → Dir2208 K n' g' V' → Q 2208 g' fl V') :
    W_2226 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Dir2226, DirC] at h
  obtain ⟨dp, d, c, ⟨hC, rfl, rfl, Pa, rfl, hPa⟩, rfl, hc1, hc2, hU, rfl⟩ := h
  wpx [W_2226, o33, BitVec.reduceSetWidth]
  exact wnorm_of hE hK (.inl ⟨by omega, by omega⟩) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 5000 + 20 * c.toNat) _ _ _ (by omega)
      ⟨dp, d, c, R', ⟨hC.gpr rfl rfl rfl rfl rfl rfl, rfl, rfl, Pa, rfl, hPa⟩, rfl, hc1, hc2, rfl, hN', rfl⟩

theorem vc_2208 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Dir2208 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → AlnI K n' g' V' 18 4900 g'.rdx g'.rcx (g'.r9 = K.P + 4#64) → Q 2295 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Dir2226 K n' g' V' → Q 2226 g' fl V') :
    W_2208 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Dir2208, DirC] at h
  obtain ⟨dp, d, c, R, ⟨hC, rfl, rfl, Pa, rfl, hPa⟩, rfl, hc1, hc2, rfl, hN, rfl⟩ := h
  wpx [W_2208, o31, W_2272, o34, W_2224, o32, BitVec.reduceSetWidth]
  have := hK.hP; have := hK.hnp; have := hK.hnp0
  have a : InPr K (K.P + 4#64) := ⟨1666, by omega, by bv_omega⟩
  refine fun _ => ⟨fun h1 => ⟨hE.rd_pr hK a, ?_⟩, fun h1 => ?_⟩
  · exact wnorm_of hE hK (.inl ⟨by omega, by omega⟩) hN.dir fun R' rbp' r15' hN' fl =>
      hq1 (2 ^ 20 * (K.lim - dp) + 4900) _ _ _ (by omega)
        ⟨dp, d + 1, R', Pa, _, hC.gpr rfl rfl rfl rfl rfl rfl, rfl, rfl, hN', by omega, rfl, hPa, rfl,
          hC.mem.rd_pr a, rfl, rfl⟩
  · simp only [decide_eq_false_iff_not] at h1
    have h1' : c.toNat ≠ 1 := fun e => h1 (BitVec.eq_of_toNat_eq e)
    exact hq2 (2 ^ 20 * (K.lim - dp) + 5000 + 20 * (c - 1#32).toNat + 10) _ _ _ (by bv_omega)
      ⟨dp, d + 1, c - 1#32, ⟨hC.gpr rfl rfl rfl rfl rfl rfl, rfl, rfl, Pa, rfl, hPa⟩, rfl, by bv_omega, by bv_omega,
        hN.dir, rfl⟩

theorem vc_2295 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : AlnI K n g V 18 4900 g.rdx g.rcx (g.r9 = K.P + 4#64))
    (hq : ∀ n' g' fl V', n' < n → AlnI K n' g' V' 19 4800 g'.rcx g'.rdx (AlnA K g'.r9 4 6) → Q 2379 g' fl V') :
    W_2295 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [AlnI, PosC, LenC, Bd] at h
  obtain ⟨dp, d, R, P1, P2, ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, rfl, hN, hd, rfl, hP1, rfl, hP2, rfl, rfl⟩ := h
  wpx [W_2295, o35, ite_mk9, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have := hK.hP; have hnp := hK.hnp; have := hK.hnp0
  have ip : ∀ (x : Addr) (j : Nat), j < 16 → x.toNat = K.P.toNat + 2 * j → InPr K x :=
    fun x j hj hx => ⟨1664 + j, by omega, by omega⟩
  have a1 : InPr K (K.P + 6#64) := ip _ 3 (by omega) (by bv_omega)
  have a2 : InPr K (K.P + 2#64) := ip _ 1 (by omega) (by bv_omega)
  obtain ⟨a, ha1, ha2, e9⟩ : ∃ a, 4 ≤ a ∧ a < 6 ∧
      (if (!b) = true then K.P + 6#64 else K.P + 4#64) + 4#64 = K.P + BitVec.ofNat 64 (2 * a) := by
    cases b
    · exact ⟨5, by omega, by omega, by simp only [Bool.not_false, ↓reduceIte]; bv_omega⟩
    · exact ⟨4, by omega, by omega, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; bv_omega⟩
  simp only [e9]
  have a3 : InPr K (K.P + BitVec.ofNat 64 (2 * a)) := ip _ a (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ => ⟨hE.wr_pr hK a2, hE.rd_pr hK a3, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 4800) _ _ _ (by omega) ?_
  exact ⟨dp, d, R', _, _, ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, rfl, hN', hd, rfl, (hMem.rd_pr a1).ite _ hP2, rfl, hMem'.rd_pr a3, ⟨a, rfl, ha1, ha2⟩, rfl⟩

theorem vc_2379 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : AlnI K n g V 19 4800 g.rcx g.rdx (AlnA K g.r9 4 6))
    (hq : ∀ n' g' fl V', n' < n → AlnI K n' g' V' 20 4700 g'.rdx g'.rcx (AlnA K g'.r9 8 12) → Q 2462 g' fl V') :
    W_2379 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [AlnI, AlnA, PosC, LenC, Bd] at h
  obtain ⟨dp, d, R, P1, P2, ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, rfl, hN, hd, rfl, hP1, rfl, hP2, ⟨a, rfl, ha1, ha2⟩, rfl⟩ := h
  wpx [W_2379, o36, ite_mk9, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have := hK.hP; have hnp := hK.hnp; have := hK.hnp0
  have ip : ∀ (x : Addr) (j : Nat), j < 16 → x.toNat = K.P.toNat + 2 * j → InPr K x :=
    fun x j hj hx => ⟨1664 + j, by omega, by omega⟩
  have a1 : InPr K (K.P + BitVec.ofNat 64 (2 * a) + 4#64) := ip _ (a + 2) (by omega) (by bv_omega)
  have a2 : InPr K (K.P + BitVec.ofNat 64 (2 * a) + 4#64 + 18446744073709551608#64) :=
    ip _ (a - 2) (by omega) (by bv_omega)
  obtain ⟨a', ha1', ha2', e9⟩ : ∃ a', 8 ≤ a' ∧ a' < 12 ∧
      (if (!b) = true then K.P + BitVec.ofNat 64 (2 * a) + 4#64 else K.P + BitVec.ofNat 64 (2 * a)) + 8#64 =
        K.P + BitVec.ofNat 64 (2 * a') := by
    cases b
    · exact ⟨a + 6, by omega, by omega, by simp only [Bool.not_false, ↓reduceIte]; bv_omega⟩
    · exact ⟨a + 4, by omega, by omega, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; bv_omega⟩
  simp only [e9]
  have a3 : InPr K (K.P + BitVec.ofNat 64 (2 * a')) := ip _ a' (by omega) (by bv_omega)
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ => ⟨hE.wr_pr hK a2, hE.rd_pr hK a3, ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 4700) _ _ _ (by omega) ?_
  exact ⟨dp, d, R', _, _, ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, rfl, hN', hd, rfl, (hMem.rd_pr a1).ite _ hP2, rfl, hMem'.rd_pr a3, ⟨a', rfl, ha1', ha2'⟩, rfl⟩

theorem vc_2462 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : AlnI K n g V 20 4700 g.rdx g.rcx (AlnA K g.r9 8 12))
    (hq : ∀ n' g' fl V', n' < n → AlnI K n' g' V' 21 4600 g'.rcx g'.rcx
      (∃ a, g'.r9 = BitVec.ofNat 64 a ∧ 8 ≤ a ∧ a < 16) → Q 2546 g' fl V') :
    W_2462 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [AlnI, AlnA, PosC, LenC, Bd] at h
  obtain ⟨dp, d, R, P1, P2, ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, rfl, hN, hd, rfl, hP1, rfl, hP2, ⟨a, rfl, ha1, ha2⟩, rfl⟩ := h
  wpx [W_2462, o37, ite_mk9, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have := hK.hP; have hnp := hK.hnp; have := hK.hnp0
  have ip : ∀ (x : Addr) (j : Nat), j < 16 → x.toNat = K.P.toNat + 2 * j → InPr K x :=
    fun x j hj hx => ⟨1664 + j, by omega, by omega⟩
  have a1 : InPr K (K.P + BitVec.ofNat 64 (2 * a) + 8#64) := ip _ (a + 4) (by omega) (by bv_omega)
  have a2 : InPr K (K.P + BitVec.ofNat 64 (2 * a) + 8#64 + 18446744073709551600#64) :=
    ip _ (a - 4) (by omega) (by bv_omega)
  obtain ⟨a', ha1', ha2', e9⟩ : ∃ a', 8 ≤ a' ∧ a' < 16 ∧
      BitVec.setWidth 64 (BitVec.setWidth 32
        ((if (!b) = true then K.P + BitVec.ofNat 64 (2 * a) + 8#64 else K.P + BitVec.ofNat 64 (2 * a)) - K.P) >>> 1) =
        BitVec.ofNat 64 a' := by
    cases b
    · exact ⟨a + 4, by omega, by omega, by simp only [Bool.not_false, ↓reduceIte]; bv_omega⟩
    · exact ⟨a, by omega, by omega, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; bv_omega⟩
  simp only [e9]
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ => ⟨hE.rd_pr hK a1, fun _ => ⟨hE.wr_pr hK a2, fun _ _ => ?_⟩⟩
  refine wnorm_of hE hK (.inl ⟨by omega, by omega⟩) (hN.bit hP1 _) fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 4600) _ _ _ (by omega) ?_
  exact ⟨dp, d, R', _, _, ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, rfl, hN', hd, rfl, (hMem.rd_pr a1).ite _ hP2, rfl, (hMem.rd_pr a1).ite _ hP2, ⟨a', rfl, ha1', ha2'⟩, rfl⟩

theorem vc_2546 (hK : K.Ok) (hE : Env K F Wl) {Q : Post}
    (h : AlnI K n g V 21 4600 g.rcx g.rcx (∃ a, g.r9 = BitVec.ofNat 64 a ∧ 8 ≤ a ∧ a < 16))
    (hq : ∀ n' g' fl V', n' < n → Fin2594 K n' g' V' → Q 2594 g' fl V') :
    W_2546 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [AlnI, PosC, LenC, Bd] at h
  obtain ⟨dp, d, R, P1, P2, ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, rfl, hN, hd, rfl, hP1, -, -, ⟨a, rfl, ha1, ha2⟩, rfl⟩ := h
  wpx [W_2546, o38, ite_mk9, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P1).toNat) = b
  have := hK.hP; have hnp := hK.hnp; have := hK.hnp0
  have a2 : InPr K (K.P + BitVec.ofNat 64 a * 2#64) := ⟨1664 + a, by omega, by bv_omega⟩
  have hMem' := hMem.st_pr hK a2 (hP1.upc b)
  refine fun _ _ _ => ⟨hE.wr_pr hK a2, ?_⟩
  exact hq (2 ^ 20 * (K.lim - dp) + 4500) _ _ _ (by omega)
    ⟨dp, 22, d, ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩, rfl,
      .inl ⟨by omega, hd⟩, hN.bit hP1 _, rfl⟩

theorem vc_4384 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Spec4384 K n g V)
    (hq : ∀ n' g' fl V', n' < n → Spec4412 K n' g' V' → Q 4412 g' fl V') :
    W_4384 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Spec4384] at h
  obtain ⟨dp, u, q, T, c, hC, rfl, hc1, hc2, rfl, hu, hT, hT32, hq0, hqT, hU, rfl⟩ := h
  wpx [W_4384, o70, BitVec.reduceSetWidth]
  have hnp := hK.hnp; have := hK.hP; have := hK.hnp0
  have hu2 : u * 2 ≤ T := hT ▸ Nat.mul_le_mul_left u (Nat.pow_le_pow_right (by decide : 0 < 2) hc1)
  have a1 : InPr K rbx := ⟨q, by omega, hq0⟩
  refine ⟨hE.rd_pr hK a1, ?_⟩
  refine wnorm_of hE hK (.inr ⟨by omega, rfl⟩) hU fun R' rbp' r15' hN' fl =>
    hq (2 ^ 20 * (K.lim - dp) + 5000 + 20 * c.toNat) _ _ _ (by omega) ?_
  exact ⟨dp, u, q + u, T, c, R', _, hC.gpr rfl rfl rfl rfl rfl rfl, rfl, hc1, hc2, rfl, hu, hT, hT32, by bv_omega,
    by omega, a1, rfl, hN', rfl, hC.mem.rd_pr a1, rfl⟩

theorem vc_4412 (hK : K.Ok) (hE : Env K F Wl) {Q : Post} (h : Spec4412 K n g V)
    (hq1 : ∀ n' g' fl V', n' < n → Spec4384 K n' g' V' → Q 4384 g' fl V')
    (hq2 : ∀ n' g' fl V', n' < n → Fin2594 K n' g' V' → Q 2594 g' fl V') :
    W_4412 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Spec4412, PosC, LenC, Bd] at h
  obtain ⟨dp, u, q, T, c, R, P, ⟨s, L, ⟨⟨rfl, rfl, hMem, hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩,
    rfl, hc1, hc2, rfl, hu, hT, hT32, hq0, hqT, h11, rfl, hN, rfl, hP, rfl⟩ := h
  wpx [W_4412, o71, W_4467, o72, ite_mk3, BitVec.reduceSetWidth]
  generalize decide ((BitVec.setWidth 32 rbp).toNat < (R >>> 11 * P).toNat) = b
  have hnp := hK.hnp; have := hK.hP; have := hK.hnp0; have := hK.hsq; have := hK.hsp2
  have hu2 : u * 2 ≤ T := hT ▸ Nat.mul_le_mul_left u (Nat.pow_le_pow_right (by decide : 0 < 2) hc1)
  have hMem' := hMem.st_pr hK h11 (hP.upc b)
  generalize Vst V r11 _ = V' at hMem' ⊢
  simp only [hMem'.s30]
  have hx : ∃ q', (if (!b) = true then rbx + BitVec.ofNat 64 (2 * u) else rbx).toNat = K.pbn + 2 * q' ∧
      q' ≤ q + u := by
    cases b
    · exact ⟨q + u, by simp only [Bool.not_false, ↓reduceIte]; bv_omega, by omega⟩
    · exact ⟨q, by simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hq0, by omega⟩
  obtain ⟨q', hq', hqq⟩ := hx
  generalize (if (!b) = true then rbx + BitVec.ofNat 64 (2 * u) else rbx) = rbx' at hq' ⊢
  have hC : ∀ x0 x1 x2 x3 x5 x6 x7 x9 x11 x15, PosC K ⟨x0, x1, x2, x3, K.sp, x5, x6, x7,
      BitVec.setWidth 64 s, x9, 2048#64, x11, BitVec.setWidth 64 L, r13, K.dic + BitVec.ofNat 64 dp, x15⟩ V' dp :=
    fun _ _ _ _ _ _ _ _ _ _ =>
      ⟨s, L, ⟨⟨rfl, rfl, hMem', hd0, hdp, hpp⟩, rfl, rfl, hs2, hsl, hsh⟩, hs24, rfl, hL1, hL2⟩
  refine fun _ _ _ => ⟨hE.wr_pr hK h11, fun h1 => ?_, fun h1 => ⟨hE.rd_fr hK 48 (by bv_omega) (by omega), fun _ => ?_⟩⟩
  · simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h1
    have h1' : c.toNat ≠ 1 := fun e => h1 (BitVec.eq_of_toNat_eq e)
    have hc' : (c - 1#32).toNat = c.toNat - 1 := by bv_omega
    obtain ⟨m, hm⟩ : ∃ m, c.toNat = m + 1 := ⟨c.toNat - 1, by omega⟩
    have hT' : 2 * u * 2 ^ (c - 1#32).toNat = T := by
      rw [hc', ← hT, hm, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm 2 u, Nat.mul_assoc, Nat.mul_comm 2]
    have hu4 : u * 4 ≤ T := by
      obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have h4 : 2 ^ 2 ≤ 2 ^ c.toNat := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
      exact hT ▸ Nat.mul_le_mul_left u h4
    exact hq1 (2 ^ 20 * (K.lim - dp) + 5000 + 20 * (c - 1#32).toNat + 10) _ _ _ (by omega)
      ⟨dp, 2 * u, q', T, c - 1#32, hC _ _ _ _ _ _ _ _ _ _, rfl, by omega, by omega, by bv_omega, by omega, hT', hT32,
        hq', by omega, (hN.bit hP _).mono (by omega) (Nat.le_refl _), rfl⟩
  · exact hq2 (2 ^ 20 * (K.lim - dp) + 4500) _ _ _ (by omega)
      ⟨dp, 23, 0, hC _ _ _ _ _ _ _ _ _ _, rfl, .inr ⟨by omega, rfl⟩, (hN.bit hP _).mono (by omega) (Nat.le_refl _), rfl⟩
end FV7z.Lzma
