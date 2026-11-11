import FV7z.Memcmp.Avx2Movbe.Loop
/-!
# `__memcmp_avx2_movbe` of `7zzs`: 32 bytes and more (PLAN.md G2.1)

From `14`, with `n ≥ 32`: the first window, then by `n`: the last window (`n ≤ 64`, `at241`), two windows and the
last two (`n < 128`, `at743`), four windows at 0 and four at `n - 128` (`n ≤ 256`), or the first window, the pointers
aligned (`rdi` to 32 bytes) and the loop (`n > 256`, `at592`).
-/
namespace FV7z.MemcmpAvx2
open ZellicX86 Decode Memcmp MemcmpCall Order

attribute [-simp] BitVec.getLsbD_eq_getElem

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {e : Addr}

theorem and31 (v : BitVec 64) : ((v.setWidth 32 &&& BitVec.ofNat 32 31).setWidth 64).toNat = v.toNat % 32 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [show (31 % 2 ^ 32 : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 5 ∣ 2 ^ 32)]
  exact Nat.mod_eq_of_lt (by omega)

theorem add_zero' (b : Addr) : b.add 0 = b := by simp [Addr.add]

theorem rdx_ofNat (s₀ : State) : s₀.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - 0) := by simp [nn]

/-- At `592`, more than 256 bytes: the first window; `rdi` up to the next multiple of 32, `rsi` and `rdx` with it;
the loop. -/
theorem at592 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 592) (hdi : X.cpu.gpr.rdi = p₁ s₀) (hsi : X.cpu.gpr.rsi = p₂ s₀)
    (hdx : X.cpu.gpr.rdx = s₀.cpu.gpr.rdx) (hn : 256 < nn s₀)
    (hz0 : X.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512) : Go prof L s₀ ra o X t :=
  win x hK hC (Or.inl rfl) (a := 0) (d592 _ x.f) (d596 _ x.f) (d600 _ x.f) (d604 _ x.f) (d607 _ x.f) (by decide)
    (by decide) hrip (by rw [hdi, add_zero']) (by rw [hsi, add_zero']) (by omega) (fun i hi => absurd hi (by omega))
    fun hall Y1 _ hK1 hr1 ⟨hC1, hdi1, hsi1, hdx1, _, hz1⟩ =>
  x.c.s_mov_rr hK1 (by simp [avx2Movbe_length]) hr1 (d613 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, z2⟩ =>
  x.c.s_and_ri hK2 (by simp [avx2Movbe_length]) hr2 (d616 _ x.f) fun Y3 _ hK3 hr3 ⟨g3, z3⟩ =>
  x.c.s_sub_ri hK3 (by simp [avx2Movbe_length]) hr3 (Or.inr rfl) (d619 _ x.f) fun Y4 _ hK4 hr4 ⟨g4, z4, _⟩ =>
  x.c.s_sub_rr hK4 (by simp [avx2Movbe_length]) hr4 (Or.inr rfl) (d623 _ x.f) fun Y5 _ hK5 hr5 ⟨g5, z5, _⟩ =>
  x.c.s_sub_rr hK5 (by simp [avx2Movbe_length]) hr5 (Or.inr rfl) (d626 _ x.f) fun Y6 _ hK6 hr6 ⟨g6, z6, _⟩ =>
  x.c.s_add_rr hK6 (by simp [avx2Movbe_length]) hr6 (d629 _ x.f) fun Y7 t7 hK7 hr7 ⟨g7, z7⟩ => by
    have hc : Y4.cpu.gpr.rcx.toNat = (p₁ s₀).toNat % 32 + 2 ^ 64 - 32 := by
      have h31 := and31 (p₁ s₀)
      simp only [g4, g3, g2, set_regOf_1, rv, get_1, get_7, hdi1, hdi, BitVec.setWidth_eq] at h31 ⊢
      rw [BitVec.toNat_sub, h31, BitVec.toNat_ofNat]
      have : (p₁ s₀).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
      omega
    have h4di : Y4.cpu.gpr.rdi = p₁ s₀ := by simp only [g4, g3, g2, set_regOf_1]; rw [hdi1, hdi]
    have h4si : Y4.cpu.gpr.rsi = p₂ s₀ := by simp only [g4, g3, g2, set_regOf_1]; rw [hsi1, hsi]
    have h4dx : Y4.cpu.gpr.rdx = s₀.cpu.gpr.rdx := by simp only [g4, g3, g2, set_regOf_1]; rw [hdx1, hdx]
    have hR : (p₁ s₀).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
    have hp1 := (p₁ s₀).isLt
    have hp2 := (p₂ s₀).isLt
    have hdi7 : Y7.cpu.gpr.rdi = (p₁ s₀).add (32 - (p₁ s₀).toNat % 32) := by
      simp only [g7, g6, g5, set_regOf_2, set_regOf_6, set_regOf_7, rv, get_7, get_1, BitVec.setWidth_eq, h4di]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, hc, Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hsi7 : Y7.cpu.gpr.rsi = (p₂ s₀).add (32 - (p₁ s₀).toNat % 32) := by
      simp only [g7, g6, g5, set_regOf_2, set_regOf_6, set_regOf_7, rv, get_6, get_1, BitVec.setWidth_eq, h4si]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, hc, Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hdx7 : Y7.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - (32 - (p₁ s₀).toNat % 32)) := by
      simp only [g7, g6, g5, set_regOf_2, set_regOf_6, set_regOf_7, rv, get_2, get_1, BitVec.setWidth_eq, h4dx]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, hc, BitVec.toNat_ofNat]
      have := nn_lt s₀
      simp only [nn] at hn this ⊢
      omega
    exact loop x _ rfl hK7 (hC1.of_gpr (by simp [g7, g6, g5, g4, g3, g2])) hr7 hdi7 hsi7 hdx7 (by omega)
      (by rw [z7, z6, z5, z4, z3, z2, hz1, hz0]) (fun i hi => hall i (by omega))

/-- At `75`, 128 to 256 bytes: four windows at 0 (`ymm1` to `ymm4`, their `AND` in `ymm5`), `VPTEST`, `JAE 864`. -/
theorem at75 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 75) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hz0 : X.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512) (hn : 128 ≤ nn s₀)
    (k' : (∀ i < 128, Ag s₀ i) → Then prof L s₀ ra o e 136 fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm (xmmOf 0) = X.cpu.vec.zmm (xmmOf 0)) :
    Go prof L s₀ ra o X t :=
  pair x hK (a := 0) (d75 _ x.f) (d79 _ x.f) (by decide) hrip hdi hsi (by omega) fun Y1 _ hK1 hr1 ⟨g1, z1⟩ =>
  pair x hK1 (a := 0) (d83 _ x.f) (d88 _ x.f) (by decide) hr1 (by rw [g1]; exact hdi) (by rw [g1]; exact hsi)
    (by omega) fun Y2 _ hK2 hr2 ⟨g2, z2⟩ =>
  pair x hK2 (a := 0) (d93 _ x.f) (d98 _ x.f) (by decide) hr2 (by rw [g2, g1]; exact hdi) (by rw [g2, g1]; exact hsi)
    (by omega) fun Y3 _ hK3 hr3 ⟨g3, z3⟩ =>
  pair x hK3 (a := 0) (d103 _ x.f) (d108 _ x.f) (by decide) hr3 (by rw [g3, g2, g1]; exact hdi)
    (by rw [g3, g2, g1]; exact hsi) (by omega) fun Y4 _ hK4 hr4 ⟨g4, z4⟩ =>
  x.c.s_vpand hK4 (by simp [avx2Movbe_length]) hr4 (d113 _ x.f) fun Y5 _ hK5 hr5 ⟨g5, z5⟩ =>
  x.c.s_vpand hK5 (by simp [avx2Movbe_length]) hr5 (d117 _ x.f) fun Y6 _ hK6 hr6 ⟨g6, z6⟩ =>
  x.c.s_vpand hK6 (by simp [avx2Movbe_length]) hr6 (d121 _ x.f) fun Y7 _ hK7 hr7 ⟨g7, z7⟩ =>
  x.c.s_vptest hK7 (by simp [avx2Movbe_length]) hr7 (d125 _ x.f) fun Y8 _ hK8 hr8 ⟨g8, z8, f8⟩ => by
    have gX : Y8.cpu.gpr = X.cpu.gpr := by rw [g8, g7, g6, g5, g4, g3, g2, g1]
    have zz : ∀ q, Y8.cpu.vec.zmm q = Y7.cpu.vec.zmm q := fun q => by rw [z8]
    have e0 : Y7.cpu.vec.zmm (xmmOf 0) = X.cpu.vec.zmm (xmmOf 0) := by
      simp only [z7, z6, z5, z4, z3, z2, z1, withZmm, xmmOf]; simp
    have e1 : Y7.cpu.vec.zmm (xmmOf 1) = EqW s₀ 0 := by
      simp only [z7, z6, z5, z4, z3, z2, z1, withZmm, xmmOf]; simp
    have e2 : Y7.cpu.vec.zmm (xmmOf 2) = EqW s₀ (0 + 32) := by
      simp only [z7, z6, z5, z4, z3, z2, withZmm, xmmOf]; simp
    have e3 : Y7.cpu.vec.zmm (xmmOf 3) = EqW s₀ (0 + 64) := by
      simp only [z7, z6, z5, z4, z3, withZmm, xmmOf]; simp
    have e4 : Y7.cpu.vec.zmm (xmmOf 4) = EqW s₀ (0 + 96) := by
      simp only [z7, z6, z5, z4, withZmm, xmmOf]; simp
    have hall : Y8.cpu.rflags.cf = true ↔ ∀ j < 128, Ag s₀ (0 + j) := by
      rw [f8, e0, hz0, cf_all]
      refine all4 0 fun i hi => ?_
      simp only [z7, z6, z5, z4, z3, z2, z1, withZmm, xmmOf]
      simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, getLsbD_EqW', hi, and_assoc, and_comm, and_left_comm]
    refine x.c.s_jcc hK8 (by simp [avx2Movbe_length]) hr8 (d130 _ x.f) (tgt := 864) (by decide)
      (by simp [avx2Movbe_length]) (fun hc => ?_) (fun hc => ?_)
    · intro Y9 t9 hK9 hr9 ⟨g9, z9⟩
      rw [cond3, Bool.not_eq_true'] at hc
      refine h864 x hK9 (hC.of_gpr (by simp [g9, gX])) hr9 (by rw [g9, gX]; exact hdi) (by rw [g9, gX]; exact hsi)
        (by rw [z9, zz, e1]) (by rw [z9, zz, e2]) (by rw [z9, zz, e3]) (by rw [z9, zz, e4]) (by omega)
        (fun i hi => absurd hi (by omega)) ?_
      intro h; rw [← hall] at h; rw [h] at hc; exact Bool.noConfusion hc
    · intro Y9 t9 hK9 hr9 ⟨g9, z9⟩
      rw [cond3, Bool.not_eq_false'] at hc
      exact k' (fun i hi => by simpa using (hall.1 hc) i hi) Y9 t9 hK9 hr9 ⟨by rw [g9, gX], by rw [z9, zz, e0]⟩

/-- At `136`, 128 to 256 bytes, the first 128 equal: four windows at `n - 128`; equal, so 0. -/
theorem at136 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 136) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀))
    (hz0 : X.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512) (hn : 128 ≤ nn s₀) (hn2 : nn s₀ ≤ 256)
    (hall : ∀ i < 128, Ag s₀ i) : Go prof L s₀ ra o X t :=
  have hv := nn_lt s₀
  x.c.s_lea hK (by simp [avx2Movbe_length]) hrip (d136 _ x.f) fun Y10 _ hK10 hr10 ⟨g10, z10⟩ =>
  x.c.s_lea hK10 (by simp [avx2Movbe_length]) hr10 (d141 _ x.f) fun Y11 _ hK11 hr11 ⟨g11, z11⟩ => by
    refine quadB x hK11 (hC.of_gpr (by simp [g11, g10])) (a := nn s₀ - 128) (d146 _ x.f) (d150 _ x.f)
      (d154 _ x.f) (d159 _ x.f) (d164 _ x.f) (d168 _ x.f) (d173 _ x.f) (d178 _ x.f) (d182 _ x.f) (d187 _ x.f)
      (d192 _ x.f) (d196 _ x.f) (d201 _ x.f) (by decide) (by decide) hr11
      (by simp only [g11, g10, set_regOf_6, set_regOf_7, eaI, get_7, get_2, hdi, hdx, add_addr]
          exact add_mod _ (by omega))
      (by simp only [g11, g10, set_regOf_6, set_regOf_7, eaI, get_6, get_2, hsi, hdx, add_addr]
          exact add_mod _ (by omega))
      (by rw [z11, z10, hz0]) (by omega) (fun i hi => hall i (by omega)) ?_
    intro hall' Y12 _ hK12 hr12 ⟨g12, _⟩
    refine x.c.s_xor_rr hK12 (by simp [avx2Movbe_length]) hr12 (d207 _ x.f) fun Y13 _ hK13 hr13 ⟨g13, _⟩ => ?_
    refine x.c.s_vzeroupper hK13 (by simp [avx2Movbe_length]) hr13 (d209 _ x.f) fun Y14 _ hK14 hr14 g14 => ?_
    exact x.c.ret hK14 (hC.of_gpr (by simp [g14, g13, g12, g11, g10])) (by simp [avx2Movbe_length]) hr14
      (d212 _ x.f) (post_eq (by simp [g14, g13]) fun i hi => hall' i (by omega))

/-- At `62`, 65 to 256 bytes, the first 32 equal: `n < 128` to `743`, else `75` and `136`. -/
theorem at62 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 62) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add 0) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add 0)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀))
    (hz0 : X.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512) (hn : 64 < nn s₀) (hn2 : nn s₀ ≤ 256)
    (hall : ∀ i < 32, Ag s₀ i) : Go prof L s₀ ra o X t :=
  have hv := nn_lt s₀
  x.c.s_cmp_ri hK (by simp [avx2Movbe_length]) hrip (d62 _ x.f) fun Y7 _ hK7 hr7 ⟨g7, z7, f7⟩ => by
    have hf7 : Y7.cpu.rflags = subF (rf0 X) (BitVec.ofNat 64 (nn s₀)) (BitVec.ofNat 64 128) := by
      rw [f7]; simp only [rv, get_2, hdx, BitVec.setWidth_eq]
    refine x.c.s_jcc hK7 (by simp [avx2Movbe_length]) hr7 (d69 _ x.f) (tgt := 743) (by omega)
      (by simp [avx2Movbe_length]) (fun hc => ?_) (fun hc => ?_)
    · rw [cond2, hf7, cf64 _ hv (by decide), decide_eq_true_iff] at hc
      intro Y8 _ hK8 hr8 ⟨g8, _⟩
      have gY : Y8.cpu.gpr = X.cpu.gpr := by rw [g8, g7]
      exact at743 x hK8 (hC.of_gpr (by simp [gY])) hr8 (a := 0) (by rw [gY, hdi])
        (by rw [gY, hsi]) (by rw [gY, hdx, Nat.sub_zero]) (by omega) (by omega) (fun i hi => absurd hi (by omega))
    · rw [cond2, hf7, cf64 _ hv (by decide), decide_eq_false_iff_not] at hc
      intro Y8 _ hK8 hr8 ⟨g8, z8⟩
      have gY8 : Y8.cpu.gpr = X.cpu.gpr := by rw [g8, g7]
      refine at75 x hK8 (hC.of_gpr (by simp [gY8])) hr8 (by rw [gY8, hdi])
        (by rw [gY8, hsi]) (by rw [z8, z7, hz0]) (by omega) ?_
      intro hall128 Y9 _ hK9 hr9 ⟨g9, z9⟩
      have gY9 : Y9.cpu.gpr = X.cpu.gpr := by rw [g9, gY8]
      exact at136 x hK9 (hC.of_gpr (by simp [gY9])) hr9 (by rw [gY9, hdi]) (by rw [gY9, hsi]) (by rw [gY9, hdx])
        (by rw [z9, z8, z7, hz0]) (by omega) hn2 hall128

/-- At `14`, 32 bytes or more. -/
theorem at14 (x : Ctx prof L s₀ ra o e) {X : State} {t : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 14) (hdi : X.cpu.gpr.rdi = p₁ s₀) (hsi : X.cpu.gpr.rsi = p₂ s₀)
    (hdx : X.cpu.gpr.rdx = s₀.cpu.gpr.rdx) (hn : 32 ≤ nn s₀) : Go prof L s₀ ra o X t :=
  have hv := nn_lt s₀
  have hdx' : s₀.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀) := by simp [nn]
  win x hK hC (Or.inl rfl) (a := 0) (d14 _ x.f) (d18 _ x.f) (d22 _ x.f) (d26 _ x.f) (d29 _ x.f) (by decide)
    (by decide) hrip (by rw [hdi, add_zero']) (by rw [hsi, add_zero']) (by omega) (fun i hi => absurd hi (by omega))
    fun hall Y1 _ hK1 hr1 ⟨hC1, hdi1, hsi1, hdx1, _, _⟩ =>
  have hdx1' : Y1.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀) := by rw [hdx1, hdx, hdx']
  x.c.s_cmp_ri hK1 (by simp [avx2Movbe_length]) hr1 (d35 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, z2, f2⟩ => by
    have hf2 : Y2.cpu.rflags = subF (rf0 Y1) (BitVec.ofNat 64 (nn s₀)) (BitVec.ofNat 64 64) := by
      rw [f2]; simp only [rv, get_2, hdx1', BitVec.setWidth_eq]
    refine x.c.s_jcc hK2 (by simp [avx2Movbe_length]) hr2 (d39 _ x.f) (tgt := 241) (by omega)
      (by simp [avx2Movbe_length]) (fun hc => ?_) (fun hc => ?_)
    · rw [cond6, hf2, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      intro Y3 _ hK3 hr3 ⟨g3, _⟩
      have gY : Y3.cpu.gpr = Y1.cpu.gpr := by rw [g3, g2]
      exact at241 x hK3 (hC1.of_gpr (by simp [gY])) hr3 (a := 0) (b := 32)
        (by rw [gY, hdi1, hdi, add_zero']) (by rw [gY, hsi1, hsi, add_zero']) (by rw [gY, hdx1', Nat.sub_zero]) (by omega)
        hn (by omega) hall
    · rw [cond6, hf2, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
      intro Y3 _ hK3 hr3 ⟨g3, z3⟩
      have gY3 : Y3.cpu.gpr = Y1.cpu.gpr := by rw [g3, g2]
      refine x.c.s_vpcmpeqb_r hK3 (by simp [avx2Movbe_length]) hr3 (d45 _ x.f) fun Y4 _ hK4 hr4 ⟨g4, z4⟩ => ?_
      have hz4 : Y4.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512 := by
        rw [z4, withZmm_same, eqb_self (by decide)]
      have gY4 : Y4.cpu.gpr = Y1.cpu.gpr := by rw [g4, gY3]
      refine x.c.s_cmp_ri hK4 (by simp [avx2Movbe_length]) hr4 (d49 _ x.f) fun Y5 _ hK5 hr5 ⟨g5, z5, f5⟩ => ?_
      have hf5 : Y5.cpu.rflags = subF (rf0 Y4) (BitVec.ofNat 64 (nn s₀)) (BitVec.ofNat 64 256) := by
        rw [f5]; simp only [rv, get_2, gY4, hdx1', BitVec.setWidth_eq]
      refine x.c.s_jcc hK5 (by simp [avx2Movbe_length]) hr5 (d56 _ x.f) (tgt := 592) (by omega)
        (by simp [avx2Movbe_length]) (fun hc' => ?_) (fun hc' => ?_)
      · rw [cond7, hf5, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc'
        simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc'
        intro Y6 _ hK6 hr6 ⟨g6, z6⟩
        have gY : Y6.cpu.gpr = Y1.cpu.gpr := by rw [g6, g5, gY4]
        exact at592 x hK6 (hC1.of_gpr (by simp [gY])) hr6 (by rw [gY, hdi1, hdi]) (by rw [gY, hsi1, hsi])
          (by rw [gY, hdx1, hdx]) (by omega) (by rw [z6, z5, hz4])
      · rw [cond7, hf5, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc'
        simp only [Bool.not_eq_false', Bool.or_eq_true, decide_eq_true_eq] at hc'
        intro Y6 _ hK6 hr6 ⟨g6, z6⟩
        have gY : Y6.cpu.gpr = Y1.cpu.gpr := by rw [g6, g5, gY4]
        exact at62 x hK6 (hC1.of_gpr (by simp [gY])) hr6 (by rw [gY, hdi1, hdi, add_zero'])
          (by rw [gY, hsi1, hsi, add_zero']) (by rw [gY, hdx1']) (by rw [z6, z5, hz4]) (by omega) (by omega) hall

end FV7z.MemcmpAvx2
