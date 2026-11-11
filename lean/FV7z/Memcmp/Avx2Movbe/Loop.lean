import FV7z.Memcmp.Avx2Movbe.Tail
/-!
# `__memcmp_avx2_movbe` of `7zzs`: the loop (PLAN.md G2.1)

The loop at `632` for more than 256 bytes: four windows at `a` (`quadB`), then `a + 128`, while 128 bytes or more are
left; then the last windows (`at241`, `at224`, `at743`), by what is left. By strong induction on `n - a`.
-/
namespace FV7z.MemcmpAvx2
open ZellicX86 Decode Memcmp MemcmpCall Order

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {e : Addr}

theorem sub_ofNat {m d : Nat} (h : d ≤ m) (hm : m < 2 ^ 64) :
    BitVec.ofNat 64 m - BitVec.ofNat 64 d = BitVec.ofNat 64 (m - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64), Nat.mod_eq_of_lt (by omega : m - d < 2 ^ 64)]
  omega

theorem cf64 (f : Rflags) {v imm : Nat} (hv : v < 2 ^ 64) (hi : imm < 2 ^ 64) :
    (subF f (BitVec.ofNat 64 v) (BitVec.ofNat 64 imm)).cf = decide (v < imm) := by
  rw [subF_cf]; simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hi]

theorem zf64 (f : Rflags) {v imm : Nat} (hv : v < 2 ^ 64) (hi : imm < 2 ^ 64) :
    (subF f (BitVec.ofNat 64 v) (BitVec.ofNat 64 imm)).zf = decide (v = imm) := by
  rw [subF_zf]
  exact decide_eq_decide.2 ⟨fun h => by
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hi] at this
    exact this, fun h => h ▸ rfl⟩

theorem cond2 (f : Rflags) : f.cond 2 = f.cf := rfl
theorem cond6 (f : Rflags) : f.cond 6 = (f.cf || f.zf) := rfl
theorem cond7 (f : Rflags) : f.cond 7 = !(f.cf || f.zf) := rfl

/-- The loop at `632`, from `a` with at least 128 bytes left. -/
theorem loop (x : Ctx prof L s₀ ra o e) : ∀ m {X : State} {t a : Nat}, nn s₀ - a = m → Kept s₀ X → Callee s₀ X →
    X.cpu.rip = e.add 632 → X.cpu.gpr.rdi = (p₁ s₀).add a → X.cpu.gpr.rsi = (p₂ s₀).add a →
    X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - a) → a + 128 ≤ nn s₀ →
    X.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512 → (∀ i < a, Ag s₀ i) → Go prof L s₀ ra o X t := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
  intro X t a hm hK hC hrip hdi hsi hdx hn hz0 hpre
  refine quadB x hK hC (d632 _ x.f) (d636 _ x.f) (d640 _ x.f) (d645 _ x.f) (d650 _ x.f) (d654 _ x.f) (d659 _ x.f)
    (d664 _ x.f) (d668 _ x.f) (d673 _ x.f) (d678 _ x.f) (d682 _ x.f) (d687 _ x.f) (by decide) (by decide) hrip hdi hsi
    hz0 hn hpre ?_
  intro hall Y1 _ hK1 hr1 ⟨g1, z1⟩
  refine x.c.s_add_ri hK1 (by simp [avx2Movbe_length]) hr1 (d693 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, z2⟩ => ?_
  refine x.c.s_add_ri hK2 (by simp [avx2Movbe_length]) hr2 (d700 _ x.f) fun Y3 _ hK3 hr3 ⟨g3, z3⟩ => ?_
  refine x.c.s_sub_ri hK3 (by simp [avx2Movbe_length]) hr3 (Or.inr rfl) (d707 _ x.f)
    fun Y4 _ hK4 hr4 ⟨g4, z4, _⟩ => ?_
  have hv : nn s₀ - (a + 128) < 2 ^ 64 := by have := nn_lt s₀; omega
  have hdx4 : Y4.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - (a + 128)) := by
    simp only [g4, g3, g2, g1, set_regOf_2, set_regOf_6, set_regOf_7, rv, get_2, hdx, BitVec.setWidth_eq]
    rw [sub_ofNat (by omega) (by have := nn_lt s₀; omega)]; congr 1
  have hdi4 : Y4.cpu.gpr.rdi = (p₁ s₀).add (a + 128) := by
    simp only [g4, g3, g2, g1, set_regOf_2, set_regOf_6, set_regOf_7, rv, get_7, hdi, BitVec.setWidth_eq, add_addr]
  have hsi4 : Y4.cpu.gpr.rsi = (p₂ s₀).add (a + 128) := by
    simp only [g4, g3, g2, g1, set_regOf_2, set_regOf_6, set_regOf_7, rv, get_6, hsi, BitVec.setWidth_eq, add_addr]
  have hC4 : Callee s₀ Y4 := hC.of_gpr (by simp [g4, g3, g2, g1])
  have hz4 : Y4.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512 := by rw [z4, z3, z2, z1, hz0]
  have hall4 : ∀ i < a + 128, Ag s₀ i := hall
  refine x.c.s_cmp_ri hK4 (by simp [avx2Movbe_length]) hr4 (d714 _ x.f) fun Y5 _ hK5 hr5 ⟨g5, z5, f5⟩ => ?_
  have hf5 : Y5.cpu.rflags = subF (rf0 Y4) (BitVec.ofNat 64 (nn s₀ - (a + 128))) (BitVec.ofNat 64 128) := by
    rw [f5]; simp only [rv, get_2, hdx4, BitVec.setWidth_eq]
  refine x.c.s_jcc hK5 (by simp [avx2Movbe_length]) hr5 (d721 _ x.f) (tgt := 632) (by omega) (by simp [avx2Movbe_length]) (fun hc => ?_)
    (fun hc => ?_)
  · rw [cond3, hf5, cf64 _ hv (by decide), Bool.not_eq_true', decide_eq_false_iff_not] at hc
    intro Y6 t6 hK6 hr6 ⟨g6, z6⟩
    have gY : Y6.cpu.gpr = Y4.cpu.gpr := by rw [g6, g5]
    exact ih (nn s₀ - (a + 128)) (by omega) rfl hK6 (hC4.of_gpr (by simp [gY])) hr6 (by rw [gY, hdi4])
      (by rw [gY, hsi4]) (by rw [gY, hdx4]) (by omega) (by rw [z6, z5, hz4]) hall4
  · rw [cond3, hf5, cf64 _ hv (by decide), Bool.not_eq_false', decide_eq_true_iff] at hc
    intro Y6 _ hK6 hr6 ⟨g6, z6⟩
    refine x.c.s_cmp_ri hK6 (by simp [avx2Movbe_length]) hr6 (d723 _ x.f) fun Y7 _ hK7 hr7 ⟨g7, z7, f7⟩ => ?_
    have g7' : Y7.cpu.gpr = Y4.cpu.gpr := by rw [g7, g6, g5]
    have hf7 : Y7.cpu.rflags = subF (rf0 Y6) (BitVec.ofNat 64 (nn s₀ - (a + 128))) (BitVec.ofNat 64 32) := by
      rw [f7]; simp only [rv, get_2, g6, g5, hdx4, BitVec.setWidth_eq]
    refine x.c.s_jcc hK7 (by simp [avx2Movbe_length]) hr7 (d727 _ x.f) (tgt := 241) (by omega) (by simp [avx2Movbe_length]) (fun hc' => ?_)
      (fun hc' => ?_)
    · rw [cond6, hf7, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc'
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc'
      intro Y8 _ hK8 hr8 ⟨g8, _⟩
      have gY : Y8.cpu.gpr = Y4.cpu.gpr := by rw [g8, g7']
      exact at241 x hK8 (hC4.of_gpr (by simp [gY])) hr8 (by rw [gY, hdi4]) (by rw [gY, hsi4]) (by rw [gY, hdx4])
        (by omega) (by omega) (b := a + 128) (by omega) hall4
    · rw [cond6, hf7, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc'
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc'
      intro Y8 _ hK8 hr8 ⟨g8, z8⟩
      refine x.c.s_cmp_ri hK8 (by simp [avx2Movbe_length]) hr8 (d733 _ x.f) fun Y9 _ hK9 hr9 ⟨g9, z9, f9⟩ => ?_
      have g9' : Y9.cpu.gpr = Y4.cpu.gpr := by rw [g9, g8, g7']
      have hf9 : Y9.cpu.rflags = subF (rf0 Y8) (BitVec.ofNat 64 (nn s₀ - (a + 128))) (BitVec.ofNat 64 64) := by
        rw [f9]; simp only [rv, get_2, g8, g7', hdx4, BitVec.setWidth_eq]
      refine x.c.s_jcc hK9 (by simp [avx2Movbe_length]) hr9 (d737 _ x.f) (tgt := 224) (by omega) (by simp [avx2Movbe_length]) (fun hc'' => ?_)
        (fun hc'' => ?_)
      · rw [cond6, hf9, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc''
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hc''
        intro Y10 _ hK10 hr10 ⟨g10, _⟩
        have gY : Y10.cpu.gpr = Y4.cpu.gpr := by rw [g10, g9']
        exact at224 x hK10 (hC4.of_gpr (by simp [gY])) hr10 (by rw [gY, hdi4]) (by rw [gY, hsi4])
          (by rw [gY, hdx4]) (by omega) (by omega) hall4
      · rw [cond6, hf9, cf64 _ hv (by decide), zf64 _ hv (by decide)] at hc''
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc''
        intro Y10 _ hK10 hr10 ⟨g10, _⟩
        have gY : Y10.cpu.gpr = Y4.cpu.gpr := by rw [g10, g9']
        exact at743 x hK10 (hC4.of_gpr (by simp [gY])) hr10 (by rw [gY, hdi4]) (by rw [gY, hsi4])
          (by rw [gY, hdx4]) (by omega) (by omega) hall4

end FV7z.MemcmpAvx2
