import FV7z.Memcmp.Avx2Movbe.Blocks
/-!
# `__memcmp_avx2_movbe` of `7zzs`: the last windows (PLAN.md G2.1)

The ends of the paths for 32 bytes and more: the last window, at `n - 32` (`at241`), after one more window
(`at224`), after two windows and the two last ones (`at743`), each returning 0 when their bytes all agree.
-/
namespace FV7z.MemcmpAvx2
open ZellicX86 Decode Memcmp MemcmpCall Order

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {e : Addr}

/-- `rax`'s low half 0 when the strings agree: the result `memcmp`'s contract asks. -/
theorem post_eq {Y : State} (hz : Y.cpu.gpr.rax.setWidth 32 = 0) (hall : ∀ i < nn s₀, Ag s₀ i) :
    contract.post s₀ Y := by
  show compare (Y.cpu.gpr.rax.setWidth 32).toInt 0 = _
  rw [hz, cmp_mem_all hall]
  decide

theorem lea_addr (b : Addr) {c m d D : Nat} (hD : D + d = 2 ^ 64) (hd : d ≤ c + m) (hm : m < 2 ^ 64) :
    b.add c + BitVec.ofNat 64 m + BitVec.ofNat 64 D = b.add (c + m - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_addr (b : Addr) (c d : Nat) : b.add c + BitVec.ofNat 64 d = b.add (c + d) := by
  rw [← addr_add_add]; rfl

theorem add_mod (b : Addr) {x y : Nat} (h : x % 2 ^ 64 = y % 2 ^ 64) : b.add x = b.add y := by
  simp only [Addr.add]; congr 1; exact BitVec.eq_of_toNat_eq (by simpa using h)

theorem nn_lt (s₀ : State) : nn s₀ < 2 ^ 64 := s₀.cpu.gpr.rdx.isLt

/-- At `241`: `LEA` both pointers to the last 32 bytes, the window there, `VZEROUPPER`, `RET` 0. -/
theorem at241 (x : Ctx prof L s₀ ra o e) {X : State} {t a b : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 241) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - a)) (ha : a ≤ nn s₀) (h32 : 32 ≤ nn s₀) (hb : nn s₀ ≤ b + 32)
    (hpre : ∀ i < b, Ag s₀ i) : Go prof L s₀ ra o X t :=
  x.c.s_lea hK (by simp [avx2Movbe_length]) hrip (d241 _ x.f) fun Y1 _ hK1 hr1 ⟨g1, _⟩ =>
  x.c.s_lea hK1 (by simp [avx2Movbe_length]) hr1 (d246 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, _⟩ =>
  win x hK2 (hC.of_gpr (by simp [g2, g1])) (Or.inl rfl) (a := nn s₀ - 32) (d251 _ x.f) (d255 _ x.f) (d259 _ x.f)
    (d263 _ x.f) (d266 _ x.f) (by decide) (by decide) hr2
    (by simp only [g2, g1, set_regOf_6, set_regOf_7, eaI, get_7, get_2, hdi, hdx, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by simp only [g2, g1, set_regOf_6, set_regOf_7, eaI, get_6, get_2, hsi, hdx, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by omega) (fun i hi => hpre i (by omega))
    fun hall Y3 _ hK3 hr3 ⟨hC3, _, _, _, hz3, _⟩ =>
  x.c.s_vzeroupper hK3 (by simp [avx2Movbe_length]) hr3 (d268 _ x.f) fun Y4 _ hK4 hr4 g4 =>
  x.c.ret hK4 (hC3.of_gpr (by simp [g4])) (by simp [avx2Movbe_length]) hr4 (d271 _ x.f)
    (post_eq (by rw [g4]; exact hz3) fun i hi => hall i (by omega))

/-- At `224`: a window at `a`, then the last 32 bytes. -/
theorem at224 (x : Ctx prof L s₀ ra o e) {X : State} {t a : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 224) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - a)) (ha : a + 32 ≤ nn s₀) (h64 : nn s₀ ≤ a + 64)
    (hpre : ∀ i < a, Ag s₀ i) : Go prof L s₀ ra o X t :=
  win x hK hC (Or.inl rfl) (a := a) (d224 _ x.f) (d228 _ x.f) (d232 _ x.f) (d236 _ x.f) (d239 _ x.f) (by decide)
    (by decide) hrip hdi hsi (by omega) hpre
    fun hall Y1 _ hK1 hr1 ⟨hC1, hdi1, hsi1, hdx1, _, _⟩ =>
  at241 x hK1 hC1 hr1 (hdi1.trans hdi) (hsi1.trans hsi) (hdx1.trans hdx) (by omega) (by omega) (b := a + 32)
    (by omega) hall

/-- At `743`: windows at `a` and `a + 32`, then the last 64 bytes in two windows. -/
theorem at743 (x : Ctx prof L s₀ ra o e) {X : State} {t a : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 743) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - a)) (ha : a + 64 ≤ nn s₀) (h128 : nn s₀ ≤ a + 128)
    (hpre : ∀ i < a, Ag s₀ i) : Go prof L s₀ ra o X t :=
  win x hK hC (Or.inl rfl) (a := a) (d743 _ x.f) (d747 _ x.f) (d751 _ x.f) (d755 _ x.f) (d758 _ x.f) (by decide)
    (by decide) hrip hdi hsi (by omega) hpre
    fun hall1 Y1 _ hK1 hr1 ⟨hC1, hdi1, hsi1, hdx1, _, _⟩ =>
  x.c.s_add_ri hK1 (by simp [avx2Movbe_length]) hr1 (d764 _ x.f) fun Y2 _ hK2 hr2 ⟨g2, _⟩ =>
  x.c.s_add_ri hK2 (by simp [avx2Movbe_length]) hr2 (d768 _ x.f) fun Y3 _ hK3 hr3 ⟨g3, _⟩ =>
  win x hK3 (hC1.of_gpr (by simp [g3, g2])) (Or.inl rfl) (a := a + 32) (d772 _ x.f) (d776 _ x.f) (d780 _ x.f)
    (d784 _ x.f) (d787 _ x.f) (by decide) (by decide) hr3
    (by simp only [g3, g2, set_regOf_6, set_regOf_7, rv, get_7, hdi1, hdi, BitVec.setWidth_eq]; exact add_addr _ _ _)
    (by simp only [g3, g2, set_regOf_6, set_regOf_7, rv, get_6, hsi1, hsi, BitVec.setWidth_eq]; exact add_addr _ _ _)
    (by omega) hall1
    fun hall2 Y4 _ hK4 hr4 ⟨hC4, hdi4, hsi4, hdx4, _, _⟩ =>
  x.c.s_lea hK4 (by simp [avx2Movbe_length]) hr4 (d793 _ x.f) fun Y5 _ hK5 hr5 ⟨g5, _⟩ =>
  x.c.s_lea hK5 (by simp [avx2Movbe_length]) hr5 (d798 _ x.f) fun Y6 _ hK6 hr6 ⟨g6, _⟩ =>
  have hdx3 : Y3.cpu.gpr.rdx = BitVec.ofNat 64 (nn s₀ - a) := by simp only [g3, g2, set_regOf_6, set_regOf_7]; exact hdx1.trans hdx
  win x hK6 (hC4.of_gpr (by simp [g6, g5])) (Or.inl rfl) (a := nn s₀ - 64) (d803 _ x.f) (d807 _ x.f) (d811 _ x.f)
    (d815 _ x.f) (d818 _ x.f) (by decide) (by decide) hr6
    (by simp only [g6, g5, set_regOf_6, set_regOf_7, eaI, get_7, get_2, hdi4, hdx4, hdx3, g3, g2, hdx1, hdx, rv, hdi1, hdi, BitVec.setWidth_eq, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by simp only [g6, g5, set_regOf_6, set_regOf_7, eaI, get_6, get_2, hsi4, hdx4, hdx3, g3, g2, hdx1, hdx, rv, hsi1, hsi, BitVec.setWidth_eq, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by omega) (fun i hi => hall2 i (by omega))
    fun hall3 Y7 _ hK7 hr7 ⟨hC7, hdi7, hsi7, _, _, _⟩ =>
  x.c.s_add_ri hK7 (by simp [avx2Movbe_length]) hr7 (d824 _ x.f) fun Y8 _ hK8 hr8 ⟨g8, _⟩ =>
  x.c.s_add_ri hK8 (by simp [avx2Movbe_length]) hr8 (d828 _ x.f) fun Y9 _ hK9 hr9 ⟨g9, _⟩ =>
  win x hK9 (hC7.of_gpr (by simp [g9, g8])) (Or.inl rfl) (a := nn s₀ - 64 + 32) (d832 _ x.f) (d836 _ x.f)
    (d840 _ x.f) (d844 _ x.f) (d847 _ x.f) (by decide) (by decide) hr9
    (by simp only [g9, g8, set_regOf_6, set_regOf_7, rv, get_7, hdi7, g6, g5, eaI, get_2, hdi4, hdx4, hdx3, g3, g2, hdx1, hdx,
          hdi1, hdi, BitVec.setWidth_eq, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by simp only [g9, g8, set_regOf_6, set_regOf_7, rv, get_6, hsi7, g6, g5, eaI, get_2, hsi4, hdx4, hdx3, g3, g2, hdx1, hdx,
          hsi1, hsi, BitVec.setWidth_eq, add_addr]
        exact add_mod _ (by have := nn_lt s₀; omega))
    (by omega) hall3
    fun hall4 Y10 _ hK10 hr10 ⟨hC10, _, _, _, hz10, _⟩ =>
  x.c.s_vzeroupper hK10 (by simp [avx2Movbe_length]) hr10 (d853 _ x.f) fun Y11 _ hK11 hr11 g11 =>
  x.c.ret hK11 (hC10.of_gpr (by simp [g11])) (by simp [avx2Movbe_length]) hr11 (d856 _ x.f)
    (post_eq (by rw [g11]; exact hz10) fun i hi => hall4 i (by omega))

end FV7z.MemcmpAvx2
