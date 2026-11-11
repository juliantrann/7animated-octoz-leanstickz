import FV7z.Memcmp.Avx2Movbe.Decode
import FV7z.Memcmp.Steps
import FV7z.Memcmp.Words
import FV7z.Lemmas.Mask
/-!
# `__memcmp_avx2_movbe` of `7zzs`: blocks (PLAN.md G2.1)

The blocks the paths of `__memcmp_avx2_movbe` share: the exit on the first byte that differs in a window of 32 bytes
(`diff`: `TZCNT`, two `MOVZX`, `SUB`), and the window itself (`win`: `VMOVDQU`, `VPCMPEQB`, `VPMOVMSKB`, `SUB`,
`JNE`), which either exits there or goes on knowing the window's bytes agree.
-/
namespace FV7z.MemcmpAvx2
open ZellicX86 Decode Memcmp MemcmpCall Order

attribute [-simp] BitVec.getLsbD_eq_getElem

@[simp] theorem get_0 (g : Gprs) : g.get (regOf 0) = g.rax := rfl
@[simp] theorem get_1 (g : Gprs) : g.get (regOf 1) = g.rcx := rfl
@[simp] theorem get_2 (g : Gprs) : g.get (regOf 2) = g.rdx := rfl
@[simp] theorem get_6 (g : Gprs) : g.get (regOf 6) = g.rsi := rfl
@[simp] theorem get_7 (g : Gprs) : g.get (regOf 7) = g.rdi := rfl

/-- A call of the code, on a processor it runs on. -/
structure Ctx (prof : Profile) (L : List (Addr × List Byte)) (s₀ : State) (ra : Addr) (o : Oracle) (e : Addr) :
    Prop where
  c : Call prof avx2Movbe e L s₀ ra o
  f : Feat prof.feat

/-- The first string. -/
abbrev p₁ (s₀ : State) : Addr := s₀.cpu.gpr.rdi
/-- The second string. -/
abbrev p₂ (s₀ : State) : Addr := s₀.cpu.gpr.rsi
/-- Their length. -/
abbrev nn (s₀ : State) : Nat := s₀.cpu.gpr.rdx.toNat
/-- The strings agree at index `i`. -/
abbrev Ag (s₀ : State) (i : Nat) : Prop := Agree s₀.proc.mm.mem (p₁ s₀) (p₂ s₀) i

theorem mem₁ {s₀ : State} : (⟨p₁ s₀, nn s₀⟩ : Rgn) ∈ strings s₀ := Call.mem₁
theorem mem₂ {s₀ : State} : (⟨p₂ s₀, nn s₀⟩ : Rgn) ∈ strings s₀ := Call.mem₂

theorem addr_idx (b : Addr) {a p d : Nat} (hp : p < 2 ^ 32) :
    b.add a + (BitVec.ofNat 32 p).setWidth 64 + BitVec.ofNat 64 d = b.add (a + d + p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := p) hp, Nat.mod_eq_of_lt (a := p) (by omega)]
  omega

theorem setWidth_byte (x : Byte) : (((x.setWidth 32).setWidth 64).setWidth 32 : BitVec 32) = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide : 256 < 2 ^ 32))]

theorem toNat_byte (x : Byte) : (x.setWidth 32 : BitVec 32).toNat = x.toNat := by
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide : 256 < 2 ^ 32))]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle} {e : Addr}

/-- The result of two bytes that differ, the first difference. -/
theorem post_diff {Y : State} {x y : Byte} {q : Nat} (hq : q < nn s₀) (hpre : ∀ i < q, Ag s₀ i) (hne : ¬ Ag s₀ q)
    (hx : x = s₀.proc.mm.mem.readByte ((p₁ s₀).add q)) (hy : y = s₀.proc.mm.mem.readByte ((p₂ s₀).add q))
    (hY : Y.cpu.gpr.rax.setWidth 32 = x.setWidth 32 - y.setWidth 32) : contract.post s₀ Y := by
  show compare (Y.cpu.gpr.rax.setWidth 32).toInt 0 = _
  rw [hY, compare_sub (by rw [toNat_byte]; have := x.isLt; omega) (by rw [toNat_byte]; have := y.isLt; omega),
    toNat_byte, toNat_byte, cmp_mem_first hq hpre hne, hx, hy]

/-- The exit on the first difference: `TZCNT ecx, eax` finds the window's first byte that differs, at `d + rcx` from
`rdi` and `rsi`; `MOVZX`, `MOVZX`, `SUB`, `VZEROUPPER`, `RET` return their difference. -/
theorem diff (x : Ctx prof L s₀ ra o e) {X : State} {t k d l a p : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (h0 : Dec prof.feat avx2Movbe k (FV7z.mk (.bit .tzcnt) 32 [gr 32 1, gr 32 0] 4) ∨
      Dec prof.feat avx2Movbe k (FV7z.mk (.bit .bsf) 32 [gr 32 1, gr 32 0] 4))
    (h1 : Dec prof.feat avx2Movbe (k + 4) (FV7z.mk .movzx 32 [gr 32 0, .mem (mbi 7 1 d 8)] l))
    (h2 : Dec prof.feat avx2Movbe (k + 4 + l) (FV7z.mk .movzx 32 [gr 32 2, .mem (mbi 6 1 d 8)] l))
    (h3 : Dec prof.feat avx2Movbe (k + 4 + l + l) (FV7z.mk .sub 32 [gr 32 0, gr 32 2] 2))
    (h4 : Dec prof.feat avx2Movbe (k + 4 + l + l + 2) (FV7z.mk (.avx .vzeroupper) 32 [] 3))
    (h5 : Dec prof.feat avx2Movbe (k + 4 + l + l + 2 + 3) (FV7z.mk .ret 64 [] 1))
    (hlen : k + 4 + l + l + 2 + 3 < 980)
    (hrip : X.cpu.rip = e.add k) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hx : rv X 32 0 ≠ 0) (hp : lowestSetBit (rv X 32 0) = p) (hp32 : p < 32)
    (hn : a + d + p < nn s₀) (hpre : ∀ i < a + d + p, Ag s₀ i) (hne : ¬ Ag s₀ (a + d + p)) :
    Go prof L s₀ ra o X t :=
  x.c.s_tzcnt hK (by simp [avx2Movbe_length]; omega) hrip h0 hx fun Y1 _ hK1 hr1 ⟨g1, _⟩ =>
  x.c.s_movzx8_i hK1 (by simp [avx2Movbe_length]; omega) hr1 h1 mem₁ (a := a + d + p)
    (by simp only [eaI, g1, set_regOf_1, get_7, get_1, hdi, hp]; exact addr_idx _ (by omega)) (show _ ≤ nn s₀ by omega)
    fun Y2 _ hK2 hr2 g2 =>
  x.c.s_movzx8_i hK2 (by simp [avx2Movbe_length]; omega) hr2 h2 mem₂ (a := a + d + p)
    (by simp only [eaI, g2, g1, set_regOf_0, set_regOf_1, get_6, get_1, hsi, hp]; exact addr_idx _ (by omega))
    (show _ ≤ nn s₀ by omega)
    fun Y3 _ hK3 hr3 g3 =>
  x.c.s_sub_rr hK3 (by simp [avx2Movbe_length]; omega) hr3 (Or.inl rfl) h3 fun Y4 _ hK4 hr4 ⟨g4, _, _⟩ =>
  x.c.s_vzeroupper hK4 (by simp [avx2Movbe_length]; omega) hr4 h4 fun Y5 _ hK5 hr5 g5 =>
  x.c.ret hK5
    (hC.of_gpr (by simp only [g5, g4, g3, g2, g1, set_regOf_0, set_regOf_1, set_regOf_2]; simp))
    (by simp [avx2Movbe_length]; omega) hr5 h5
    (post_diff hn hpre hne rfl rfl (by
      simp only [g5, g4, g3, g2, set_regOf_0, set_regOf_2, rv, get_0, get_2]
      rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, setWidth_byte, setWidth_byte]))

/-- The exits on the first difference, at `272`, `902`, `928`, `960`. -/
theorem diff272 (x : Ctx prof L s₀ ra o e) {X : State} {t a p : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 272) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hx : rv X 32 0 ≠ 0) (hp : lowestSetBit (rv X 32 0) = p) (hp32 : p < 32)
    (hn : a + 0 + p < nn s₀) (hpre : ∀ i < a + 0 + p, Ag s₀ i) (hne : ¬ Ag s₀ (a + 0 + p)) :
    Go prof L s₀ ra o X t :=
  diff x hK hC (d272 _ x.f) (d276 _ x.f) (d280 _ x.f) (d284 _ x.f) (d286 _ x.f) (d289 _ x.f) (by decide) hrip hdi hsi
    hx hp hp32 hn hpre hne

theorem diff902 (x : Ctx prof L s₀ ra o e) {X : State} {t a p : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 902) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hx : rv X 32 0 ≠ 0) (hp : lowestSetBit (rv X 32 0) = p) (hp32 : p < 32)
    (hn : a + 96 + p < nn s₀) (hpre : ∀ i < a + 96 + p, Ag s₀ i) (hne : ¬ Ag s₀ (a + 96 + p)) :
    Go prof L s₀ ra o X t :=
  diff x hK hC (d902 _ x.f) (d906 _ x.f) (d911 _ x.f) (d916 _ x.f) (d918 _ x.f) (d921 _ x.f) (by decide) hrip hdi hsi
    hx hp hp32 hn hpre hne

theorem diff928 (x : Ctx prof L s₀ ra o e) {X : State} {t a p : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 928) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hx : rv X 32 0 ≠ 0) (hp : lowestSetBit (rv X 32 0) = p) (hp32 : p < 32)
    (hn : a + 32 + p < nn s₀) (hpre : ∀ i < a + 32 + p, Ag s₀ i) (hne : ¬ Ag s₀ (a + 32 + p)) :
    Go prof L s₀ ra o X t :=
  diff x hK hC (d928 _ x.f) (d932 _ x.f) (d937 _ x.f) (d942 _ x.f) (d944 _ x.f) (d947 _ x.f) (by decide) hrip hdi hsi
    hx hp hp32 hn hpre hne

theorem diff960 (x : Ctx prof L s₀ ra o e) {X : State} {t a p : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 960) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hx : rv X 32 0 ≠ 0) (hp : lowestSetBit (rv X 32 0) = p) (hp32 : p < 32)
    (hn : a + 64 + p < nn s₀) (hpre : ∀ i < a + 64 + p, Ag s₀ i) (hne : ¬ Ag s₀ (a + 64 + p)) :
    Go prof L s₀ ra o X t :=
  diff x hK hC (d960 _ x.f) (d964 _ x.f) (d969 _ x.f) (d974 _ x.f) (d976 _ x.f) (d979 _ x.f) (by decide) hrip hdi hsi
    hx hp hp32 hn hpre hne

/-! ## A window -/

theorem withZmm_same (z : Fin 32 → BitVec 512) (n : Fin 32) (v : BitVec 512) : withZmm z n v n = v := by
  simp [withZmm]

theorem withZmm_ne (z : Fin 32 → BitVec 512) {n m : Fin 32} (v : BitVec 512) (h : m ≠ n) : withZmm z n v m = z m := by
  simp [withZmm, h]

/-- Lane `j` of the comparison of a window of the strings at `a`: whether the strings agree at `a + j`. -/
theorem win_bit {w a j : Nat} (hw : w = 256 ∨ w = 128) (hj : j < w / 8) :
    decide (elem 8 (ofBytesLE w (readBytes s₀.proc.mm.mem ((p₂ s₀).add a) (w / 8))) j =
      elem 8 (ofBytesLE w (readBytes s₀.proc.mm.mem ((p₁ s₀).add a) (w / 8))) j) = decide (Ag s₀ (a + j)) := by
  have hl : ∀ q : Addr, (readBytes s₀.proc.mm.mem q (w / 8)).length = w / 8 := fun q => readBytes_length _ _ _
  rw [elem_ofBytesLE (by rw [hl]; exact hj) (by rw [hl]; omega), elem_ofBytesLE (by rw [hl]; exact hj)
    (by rw [hl]; omega), readBytes_getElem, readBytes_getElem, addr_add_add, addr_add_add]
  exact decide_eq_decide.2 eq_comm

/-- The mask of a window, after `VMOVDQU`, `VPCMPEQB`, `VPMOVMSKB`. -/
theorem win_mask {w : Nat} (hw : w = 256 ∨ w = 128) (z : Fin 32 → BitVec 512) (B2 B1 : BitVec w) :
    (ofBits 32 fun j => decide (j < w / 8) && (elem 8 ((withZmm (withZmm z (xmmOf 2) (B2.setWidth 512)) (xmmOf 2)
      ((eqb ((withZmm z (xmmOf 2) (B2.setWidth 512) (xmmOf 2)).setWidth w) B1).setWidth 512) (xmmOf 2)).setWidth w)
        j).msb) =
      ofBits 32 fun j => decide (j < w / 8) && decide (elem 8 B2 j = elem 8 B1 j) := by
  rw [withZmm_same, withZmm_same, movmsk_eqb (by omega), BitVec.setWidth_setWidth_of_le _ (by omega),
    BitVec.setWidth_eq]

theorem cond5 {w : Nat} (f : Rflags) (x y : BitVec w) : (subF f x y).cond 5 = !decide (x = y) := by
  simp [Rflags.cond]

theorem rv_set0 (X : State) {g : Gprs} {v : BitVec 32} (hg : X.cpu.gpr = { g with rax := (v : BitVec 32).setWidth 64 }) :
    rv X 32 0 = v := by
  simp only [rv, get_0, hg]
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

/-- A window of `w / 8` bytes at `a` (`VMOVDQU`, `VPCMPEQB`, `VPMOVMSKB`, `SUB`, `JNE` to `272`): its first difference
returns, or the run goes on knowing the strings agree to `a + w / 8`, with `eax` 0. -/
theorem win (x : Ctx prof L s₀ ra o e) {X : State} {t k w ls lj rel a : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hw : w = 256 ∨ w = 128)
    (h0 : Dec prof.feat avx2Movbe k (FV7z.mk (.avx .vmovdqu) 32 [.vreg 2 w, .mem (mbd 6 0 w)] 4))
    (h1 : Dec prof.feat avx2Movbe (k + 4)
      (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 w, .vreg 2 w, .mem (mbd 7 0 w)] 4))
    (h2 : Dec prof.feat avx2Movbe (k + 4 + 4) (FV7z.mk (.avx .vpmovmskb) 32 [gr 32 0, .vreg 2 w] 4))
    (h3 : Dec prof.feat avx2Movbe (k + 4 + 4 + 4) (FV7z.mk .sub 32 [gr 32 0, .imm 32 (2 ^ (w / 8) - 1)] ls))
    (h4 : Dec prof.feat avx2Movbe (k + 4 + 4 + 4 + ls) (FV7z.mk (.jcc 5) 64 [.rel rel] lj))
    (htgt : (k + 4 + 4 + 4 + ls + lj + rel) % 2 ^ 64 = 272 % 2 ^ 64) (hlen : k + 4 + 4 + 4 + ls + lj < 980)
    (hrip : X.cpu.rip = e.add k) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hn : a + w / 8 ≤ nn s₀) (hpre : ∀ i < a, Ag s₀ i)
    (k' : (∀ i < a + w / 8, Ag s₀ i) → Then prof L s₀ ra o e (k + 4 + 4 + 4 + ls + lj) fun Y => Callee s₀ Y ∧
      Y.cpu.gpr.rdi = X.cpu.gpr.rdi ∧ Y.cpu.gpr.rsi = X.cpu.gpr.rsi ∧ Y.cpu.gpr.rdx = X.cpu.gpr.rdx ∧
      Y.cpu.gpr.rax.setWidth 32 = 0 ∧ Y.cpu.vec.zmm (xmmOf 0) = X.cpu.vec.zmm (xmmOf 0)) :
    Go prof L s₀ ra o X t :=
  x.c.s_vmovdqu hK (by simp [avx2Movbe_length]; omega) hrip h0 mem₂ (a := a) (by simp [hsi]) hn
    fun Y1 _ hK1 hr1 ⟨g1, z1⟩ =>
  x.c.s_vpcmpeqb_m hK1 (by simp [avx2Movbe_length]; omega) hr1 h1 mem₁ (a := a) (by simp [g1, hdi]) hn
    fun Y2 _ hK2 hr2 ⟨g2, z2⟩ =>
  x.c.s_vpmovmskb hK2 (by simp [avx2Movbe_length]; omega) hr2 h2 fun Y3 _ hK3 hr3 ⟨g3, z3⟩ =>
  x.c.s_sub_ri hK3 (by simp [avx2Movbe_length]; omega) hr3 (Or.inl rfl) h3 fun Y4 _ hK4 hr4 ⟨g4, z4, f4⟩ => by
    have hk : w / 8 ≤ 32 := by omega
    have hm : rv Y3 32 0 = ofBits 32 fun j => decide (j < w / 8) && decide (Ag s₀ (a + j)) := by
      rw [rv_set0 Y3 (by rw [g3, set_regOf_0]), z2, z1, win_mask hw]
      apply ofBits_congr
      intro j _
      by_cases hj : j < w / 8
      · simp only [hj, decide_true, Bool.true_and]; exact win_bit hw hj
      · simp [hj]
    have hr4' : rv Y4 32 0 = rv Y3 32 0 - BitVec.ofNat 32 (2 ^ (w / 8) - 1) :=
      rv_set0 Y4 (by rw [g4, set_regOf_0])
    refine x.c.s_jcc hK4 (by simp [avx2Movbe_length]; omega) hr4 h4 htgt (by simp [avx2Movbe_length])
      (fun hc => ?_) (fun hc => ?_)
    · rw [f4, cond5, Bool.not_eq_true', decide_eq_false_iff_not, ← sub_eq_zero_iff, hm, mask_sub_eq_zero hk] at hc
      have hex : ∃ j < w / 8, decide (Ag s₀ (a + j)) = false := by
        refine Classical.byContradiction fun hno => hc fun j hj => ?_
        exact by
          cases hb : decide (Ag s₀ (a + j))
          · exact absurd ⟨j, hj, hb⟩ hno
          · rfl
      obtain ⟨p, hp, hf, ht⟩ := exists_first _ hex
      intro Y5 _ hK5 hr5 ⟨g5, _⟩
      have hY5 : rv Y5 32 0 = rv Y3 32 0 - BitVec.ofNat 32 (2 ^ (w / 8) - 1) := by
        rw [← hr4']; simp only [rv, g5]
      refine diff272 x hK5 (hC.of_gpr (by simp [g5, g4, g3, g2, g1])) hr5 (a := a) (p := p)
        (by simp [g5, g4, g3, g2, g1, hdi]) (by simp [g5, g4, g3, g2, g1, hsi]) ?_ ?_ (by omega) (by omega)
        ?_ (by simpa using hf)
      · rw [hY5, hm, Ne, sub_eq_zero_iff, ← sub_eq_zero_iff, mask_sub_eq_zero hk]
        intro h; have := h p hp; rw [hf] at this; exact Bool.false_ne_true this
      · rw [hY5, hm]; exact mask_sub_lowest hk _ hp hf ht
      · intro i hi
        by_cases hia : i < a
        · exact hpre i hia
        · have := ht (i - a) (by omega)
          rw [show a + (i - a) = i by omega] at this
          simpa using this
    · rw [f4, cond5, Bool.not_eq_false', decide_eq_true_iff, ← sub_eq_zero_iff] at hc
      have hz : rv Y4 32 0 = 0 := hr4' ▸ hc
      rw [hm, mask_sub_eq_zero hk] at hc
      have hall : ∀ i < a + w / 8, Ag s₀ i := fun i hi => by
        by_cases hia : i < a
        · exact hpre i hia
        · have := hc (i - a) (by omega)
          rw [show a + (i - a) = i by omega] at this
          simpa using this
      intro Y5 t5 hK5 hr5 ⟨g5, z5⟩
      refine k' hall Y5 t5 hK5 hr5 ⟨hC.of_gpr (by simp [g5, g4, g3, g2, g1]), by simp [g5, g4, g3, g2, g1],
        by simp [g5, g4, g3, g2, g1], by simp [g5, g4, g3, g2, g1], ?_, ?_⟩
      · simpa [rv, g5] using hz
      · rw [z5, z4, z3, z2, z1, withZmm_ne _ _ (by decide), withZmm_ne _ _ (by decide)]

/-! ## Masks of windows held in registers -/

/-- The masks of the 32 bytes of a window of both strings at `b`, as `VPCMPEQB` leaves them. -/
def EqW (s₀ : State) (b : Nat) : BitVec 512 :=
  (eqb (ofBytesLE 256 (readBytes s₀.proc.mm.mem ((p₂ s₀).add b) (256 / 8)))
    (ofBytesLE 256 (readBytes s₀.proc.mm.mem ((p₁ s₀).add b) (256 / 8)))).setWidth 512

theorem getLsbD_EqW (b : Nat) {i : Nat} (hi : i < 256) :
    ((EqW s₀ b).setWidth 256).getLsbD i = decide (Ag s₀ (b + i / 8)) := by
  rw [EqW, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq, getLsbD_eqb (by decide)]
  simp only [hi, decide_true, Bool.true_and]
  exact win_bit (Or.inl rfl) (by omega)

theorem mask_EqW (b : Nat) :
    (ofBits 32 fun j => decide (j < 256 / 8) && (elem 8 ((EqW s₀ b).setWidth 256) j).msb) =
      ofBits 32 fun j => decide (j < 256 / 8) && decide (Ag s₀ (b + j)) := by
  rw [EqW, movmsk_eqb (by omega)]
  apply ofBits_congr
  intro j _
  by_cases hj : j < 256 / 8
  · simp only [hj, decide_true, Bool.true_and]; exact win_bit (Or.inl rfl) hj
  · simp [hj]

theorem mask_zero_iff {k : Nat} (hk : k ≤ 32) (Q : Nat → Prop) [DecidablePred Q] :
    ofBits 32 (fun j => decide (j < k) && decide (Q j)) - BitVec.ofNat 32 (2 ^ k - 1) = 0 ↔ ∀ j < k, Q j := by
  rw [mask_sub_eq_zero hk]; simp

theorem mask_first {k : Nat} (hk : k ≤ 32) (Q : Nat → Prop) [DecidablePred Q]
    (h : ofBits 32 (fun j => decide (j < k) && decide (Q j)) - BitVec.ofNat 32 (2 ^ k - 1) ≠ 0) :
    ∃ p < k, lowestSetBit (ofBits 32 (fun j => decide (j < k) && decide (Q j)) - BitVec.ofNat 32 (2 ^ k - 1)) = p ∧
      ¬ Q p ∧ ∀ i < p, Q i := by
  have hex : ∃ j < k, decide (Q j) = false := Classical.byContradiction fun hno =>
    h ((mask_zero_iff hk Q).2 fun j hj => by
      cases hb : decide (Q j)
      · exact absurd ⟨j, hj, hb⟩ hno
      · simpa using hb)
  obtain ⟨p, hp, hf, ht⟩ := exists_first _ hex
  exact ⟨p, hp, mask_sub_lowest hk _ hp hf ht, by simpa using hf, fun i hi => by simpa using ht i hi⟩

theorem withZmm_withZmm (z : Fin 32 → BitVec 512) (n : Fin 32) (v v' : BitVec 512) :
    withZmm (withZmm z n v) n v' = withZmm z n v' := by
  funext j; simp only [withZmm]; split <;> rfl

/-- `VMOVDQU ymmq, [rsi + d]; VPCMPEQB ymmq, ymmq, [rdi + d]`: the masks of the window at `a + d`. -/
theorem pair (x : Ctx prof L s₀ ra o e) {X : State} {t k q d l a : Nat} (hK : Kept s₀ X)
    (h0 : Dec prof.feat avx2Movbe k (FV7z.mk (.avx .vmovdqu) 32 [.vreg q 256, .mem (mbd 6 d 256)] l))
    (h1 : Dec prof.feat avx2Movbe (k + l)
      (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg q 256, .vreg q 256, .mem (mbd 7 d 256)] l))
    (hlen : k + l < 980)
    (hrip : X.cpu.rip = e.add k) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hn : a + d + 32 ≤ nn s₀)
    (k' : Then prof L s₀ ra o e (k + l + l) fun Y => Y.cpu.gpr = X.cpu.gpr ∧
      Y.cpu.vec.zmm = withZmm X.cpu.vec.zmm (xmmOf q) (EqW s₀ (a + d))) :
    Go prof L s₀ ra o X t :=
  x.c.s_vmovdqu hK (by simp [avx2Movbe_length]; omega) hrip h0 mem₂ (a := a + d)
    (by simp only [eaD, get_6, hsi]; exact addr_add_add _ _ _) (by show _ ≤ nn s₀; omega)
    fun Y1 _ hK1 hr1 ⟨g1, z1⟩ =>
  x.c.s_vpcmpeqb_m hK1 (by simp [avx2Movbe_length]; omega) hr1 h1 mem₁ (a := a + d)
    (by simp only [eaD, get_7, g1, hdi]; exact addr_add_add _ _ _) (by show _ ≤ nn s₀; omega)
    fun Y2 t2 hK2 hr2 ⟨g2, z2⟩ => k' Y2 t2 hK2 hr2 ⟨g2.trans g1, by
      rw [z2, z1, withZmm_withZmm, withZmm_same, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
      rfl⟩

/-- The mask of the window at `b`, less all ones. -/
abbrev Mk (s₀ : State) (b : Nat) : BitVec 32 :=
  ofBits 32 (fun j => decide (j < 32) && decide (Ag s₀ (b + j))) - BitVec.ofNat 32 (2 ^ 32 - 1)

/-- `VPMOVMSKB eax, ymmq; SUB eax, -1` of the masks of the window at `b`. -/
theorem msk (x : Ctx prof L s₀ ra o e) {X : State} {t k q b : Nat} (hK : Kept s₀ X)
    (h0 : Dec prof.feat avx2Movbe k (FV7z.mk (.avx .vpmovmskb) 32 [gr 32 0, .vreg q 256] 4))
    (h1 : Dec prof.feat avx2Movbe (k + 4) (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3))
    (hlen : k + 4 < 980) (hrip : X.cpu.rip = e.add k) (hz : X.cpu.vec.zmm (xmmOf q) = EqW s₀ b)
    (k' : Then prof L s₀ ra o e (k + 4 + 3) fun Y => Y.cpu.gpr = { X.cpu.gpr with rax := (Mk s₀ b).setWidth 64 } ∧
      Y.cpu.vec.zmm = X.cpu.vec.zmm ∧ rv Y 32 0 = Mk s₀ b ∧ Y.cpu.rflags.cond 5 = !decide (rv Y 32 0 = 0)) :
    Go prof L s₀ ra o X t :=
  x.c.s_vpmovmskb hK (by simp [avx2Movbe_length]; omega) hrip h0 fun Y1 _ hK1 hr1 ⟨g1, z1⟩ =>
  x.c.s_sub_ri hK1 (by simp [avx2Movbe_length]; omega) hr1 (Or.inl rfl) h1 fun Y2 t2 hK2 hr2 ⟨g2, z2, f2⟩ => by
    have hm : rv Y1 32 0 = ofBits 32 fun j => decide (j < 32) && decide (Ag s₀ (b + j)) := by
      rw [rv_set0 Y1 (by rw [g1, set_regOf_0]), hz, mask_EqW]
    have hr : rv Y2 32 0 = rv Y1 32 0 - BitVec.ofNat 32 4294967295 := rv_set0 Y2 (by rw [g2, set_regOf_0])
    refine k' Y2 t2 hK2 hr2 ⟨?_, z2.trans z1, hr.trans (by rw [hm]), ?_⟩
    · rw [g2, g1]; simp only [set_regOf_0, hm]
    · rw [f2, cond5, hr]
      congr 1
      exact decide_eq_decide.2 (sub_eq_zero_iff _ _).symm

/-- `VPMOVMSKB eax, ymmq; SUB eax, -1; JNE tgt` of the masks of the window at `b`: to `tgt` with the window's first
difference `p` the lowest set bit of `eax`, or on knowing the window's bytes agree. -/
theorem mskj (x : Ctx prof L s₀ ra o e) {X : State} {t k q b rel lj tgt : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (h0 : Dec prof.feat avx2Movbe k (FV7z.mk (.avx .vpmovmskb) 32 [gr 32 0, .vreg q 256] 4))
    (h1 : Dec prof.feat avx2Movbe (k + 4) (FV7z.mk .sub 32 [gr 32 0, .imm 32 4294967295] 3))
    (h2 : Dec prof.feat avx2Movbe (k + 4 + 3) (FV7z.mk (.jcc 5) 64 [.rel rel] lj))
    (htgt : (k + 4 + 3 + lj + rel) % 2 ^ 64 = tgt % 2 ^ 64) (ht : tgt < 980) (hlen : k + 4 + 3 < 980)
    (hrip : X.cpu.rip = e.add k) (hz : X.cpu.vec.zmm (xmmOf q) = EqW s₀ b)
    (taken : ∀ p < 32, ¬ Ag s₀ (b + p) → (∀ i < p, Ag s₀ (b + i)) → ∀ Y t', Kept s₀ Y → Y.cpu.rip = e.add tgt →
      Callee s₀ Y → Y.cpu.gpr.rdi = X.cpu.gpr.rdi → Y.cpu.gpr.rsi = X.cpu.gpr.rsi → rv Y 32 0 ≠ 0 →
      lowestSetBit (rv Y 32 0) = p → Go prof L s₀ ra o Y t')
    (fall : (∀ j < 32, Ag s₀ (b + j)) → ∀ Y t', Kept s₀ Y → Y.cpu.rip = e.add (k + 4 + 3 + lj) →
      Callee s₀ Y → Y.cpu.gpr.rdi = X.cpu.gpr.rdi → Y.cpu.gpr.rsi = X.cpu.gpr.rsi →
      Y.cpu.vec.zmm = X.cpu.vec.zmm → Go prof L s₀ ra o Y t') :
    Go prof L s₀ ra o X t :=
  msk x hK h0 h1 (by omega) hrip hz fun Y1 _ hK1 hr1 ⟨g1, z1, m1, c1⟩ => by
    refine x.c.s_jcc hK1 (by simp [avx2Movbe_length]; omega) hr1 h2 htgt (by simp [avx2Movbe_length]; omega)
      (fun hc => ?_) (fun hc => ?_)
    · rw [c1, Bool.not_eq_true', decide_eq_false_iff_not, m1] at hc
      obtain ⟨p, hp, hl, hne, hlt⟩ := mask_first (by omega) (fun j => Ag s₀ (b + j)) hc
      intro Y2 t2 hK2 hr2 ⟨g2, _⟩
      have hY : rv Y2 32 0 = rv Y1 32 0 := by simp only [rv, g2]
      refine taken p hp hne hlt Y2 t2 hK2 hr2 (hC.of_gpr (by simp [g2, g1])) (by simp [g2, g1])
        (by simp [g2, g1]) (by rw [hY, m1]; exact hc) (by rw [hY, m1]; exact hl)
    · rw [c1, Bool.not_eq_false', decide_eq_true_iff, m1, mask_zero_iff (by omega)] at hc
      intro Y2 t2 hK2 hr2 ⟨g2, z2⟩
      exact fall hc Y2 t2 hK2 hr2 (hC.of_gpr (by simp [g2, g1])) (by simp [g2, g1]) (by simp [g2, g1])
        (z2.trans z1)

theorem agree_join {s₀ : State} {a b c d : Nat} (hc : c = a) (hd : d = a + b) (h₁ : ∀ i < a, Ag s₀ i)
    (h₂ : ∀ j < b, Ag s₀ (c + j)) : ∀ i < d, Ag s₀ i := fun i hi => by
  by_cases hia : i < a
  · exact h₁ i hia
  · have := h₂ (i - a) (by omega)
    rwa [show c + (i - a) = i by omega] at this

/-- The handler at `864` of a block of four windows at `a` (`ymm1` to `ymm4`) whose bytes do not all agree: the first
window with a difference, and its first difference. -/
theorem h864 (x : Ctx prof L s₀ ra o e) {X : State} {t a : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (hrip : X.cpu.rip = e.add 864) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hz1 : X.cpu.vec.zmm (xmmOf 1) = EqW s₀ a) (hz2 : X.cpu.vec.zmm (xmmOf 2) = EqW s₀ (a + 32))
    (hz3 : X.cpu.vec.zmm (xmmOf 3) = EqW s₀ (a + 64)) (hz4 : X.cpu.vec.zmm (xmmOf 4) = EqW s₀ (a + 96))
    (hn : a + 128 ≤ nn s₀) (hpre : ∀ i < a, Ag s₀ i) (hne : ¬ ∀ j < 128, Ag s₀ (a + j)) :
    Go prof L s₀ ra o X t :=
  mskj x hK hC (b := a) (d864 _ x.f) (d868 _ x.f) (d871 _ x.f) (by decide) (by decide) (by decide) hrip hz1
    (fun p hp hne' hlt Y t' hK' hr' hC' hdi' hsi' hx hl =>
      diff272 x hK' hC' hr' (hdi'.trans hdi) (hsi'.trans hsi) hx hl hp (by omega)
        (agree_join rfl (by omega) hpre hlt) hne')
    fun h0 Y1 _ hK1 hr1 hC1 hdi1 hsi1 hz1' =>
  have hA : ∀ i < a + 32, Ag s₀ i := agree_join rfl rfl hpre h0
  mskj x hK1 hC1 (b := a + 32) (d877 _ x.f) (d881 _ x.f) (d884 _ x.f) (by decide) (by decide) (by decide) hr1
    (by rw [hz1']; exact hz2)
    (fun p hp hne' hlt Y t' hK' hr' hC' hdi' hsi' hx hl =>
      diff928 x hK' hC' hr' (hdi'.trans (hdi1.trans hdi)) (hsi'.trans (hsi1.trans hsi)) hx hl hp (by omega)
        (agree_join rfl rfl hA hlt) hne')
    fun h1 Y2 _ hK2 hr2 hC2 hdi2 hsi2 hz2' =>
  have hB : ∀ i < a + 64, Ag s₀ i := agree_join rfl (by omega) hA h1
  mskj x hK2 hC2 (b := a + 64) (d886 _ x.f) (d890 _ x.f) (d893 _ x.f) (by decide) (by decide) (by decide) hr2
    (by rw [hz2', hz1']; exact hz3)
    (fun p hp hne' hlt Y t' hK' hr' hC' hdi' hsi' hx hl =>
      diff960 x hK' hC' hr' (hdi'.trans (hdi2.trans (hdi1.trans hdi))) (hsi'.trans (hsi2.trans (hsi1.trans hsi)))
        hx hl hp (by omega) (agree_join rfl rfl hB hlt) hne')
    fun h2 Y3 _ hK3 hr3 hC3 hdi3 hsi3 hz3' =>
  have hD : ∀ i < a + 96, Ag s₀ i := agree_join rfl (by omega) hB h2
  msk x hK3 (b := a + 96) (d895 _ x.f) (d899 _ x.f) (by decide) hr3 (by rw [hz3', hz2', hz1']; exact hz4)
    fun Y4 _ hK4 hr4 ⟨g4, _, m4, _⟩ => by
      have hx : rv Y4 32 0 ≠ 0 := by
        rw [m4]
        intro h3
        rw [Mk, mask_zero_iff (by omega)] at h3
        exact hne fun j hj => agree_join rfl rfl hD h3 (a + j) (by omega)
      rw [m4, Mk] at hx
      obtain ⟨p, hp, hl, hne', hlt⟩ := mask_first (by omega) (fun j => Ag s₀ (a + 96 + j)) hx
      exact diff902 x hK4 (hC3.of_gpr (by simp [g4])) hr4 (p := p) (by simp [g4, hdi3, hdi2, hdi1, hdi])
        (by simp [g4, hsi3, hsi2, hsi1, hsi]) (by rw [m4]; exact hx) (by rw [m4]; exact hl) hp (by omega)
        (agree_join rfl rfl hD hlt) hne'

/-! ## Four windows -/

theorem getLsbD_EqW' (b i : Nat) : (EqW s₀ b).getLsbD i = (decide (i < 256) && decide (Ag s₀ (b + i / 8))) := by
  rw [EqW, BitVec.getLsbD_setWidth, getLsbD_eqb (by decide)]
  by_cases hi : i < 256
  · simp only [hi, show i < 512 by omega, decide_true, Bool.true_and]
    exact win_bit (Or.inl rfl) (by omega)
  · simp [hi]

/-- `VPTEST` of the `AND` of the masks of four windows at `a`: all set exactly when the 128 bytes agree. -/
theorem all4 {Y : BitVec 256} (a : Nat)
    (hY : ∀ i < 256, Y.getLsbD i = true ↔
      (Ag s₀ (a + i / 8) ∧ Ag s₀ (a + 32 + i / 8) ∧ Ag s₀ (a + 64 + i / 8) ∧ Ag s₀ (a + 96 + i / 8))) :
    (∀ i < 256, Y.getLsbD i = true) ↔ ∀ j < 128, Ag s₀ (a + j) := by
  constructor
  · intro h j hj
    have h4 := (hY (j % 32 * 8) (by omega)).1 (h _ (by omega))
    rw [show j % 32 * 8 / 8 = j % 32 by omega] at h4
    obtain ⟨e0, e1, e2, e3⟩ := h4
    by_cases c0 : j < 32
    · rwa [show a + j = a + j % 32 by omega]
    by_cases c1 : j < 64
    · rwa [show a + j = a + 32 + j % 32 by omega]
    by_cases c2 : j < 96
    · rwa [show a + j = a + 64 + j % 32 by omega]
    · rwa [show a + j = a + 96 + j % 32 by omega]
  · intro h i hi
    refine (hY i hi).2 ⟨?_, ?_, ?_, ?_⟩
    · exact h _ (by omega)
    · rw [show a + 32 + i / 8 = a + (32 + i / 8) by omega]; exact h _ (by omega)
    · rw [show a + 64 + i / 8 = a + (64 + i / 8) by omega]; exact h _ (by omega)
    · rw [show a + 96 + i / 8 = a + (96 + i / 8) by omega]; exact h _ (by omega)

theorem cf_all {Y : BitVec 256} : ((~~~Y &&& ((BitVec.allOnes 256).setWidth 512).setWidth 256) == 0) = true ↔
    ∀ i < 256, Y.getLsbD i = true := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
  exact vptest_cf Y

theorem cond3 (f : Rflags) : f.cond 3 = !f.cf := rfl

/-- Four windows at `a` (`ymm1` to `ymm4`, their `AND` in `ymm5` as they come), `VPTEST ymm5, ymm0`, `JAE 864`: the
handler at `864`, or on knowing the 128 bytes agree. The block at `146` and the loop's body at `632`. -/
theorem quadB (x : Ctx prof L s₀ ra o e) {X : State} {t k a rel : Nat} (hK : Kept s₀ X) (hC : Callee s₀ X)
    (h0 : Dec prof.feat avx2Movbe k (FV7z.mk (.avx .vmovdqu) 32 [.vreg 1 256, .mem (mbd 6 0 256)] 4))
    (h1 : Dec prof.feat avx2Movbe (k + 4)
      (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 1 256, .vreg 1 256, .mem (mbd 7 0 256)] 4))
    (h2 : Dec prof.feat avx2Movbe (k + 4 + 4) (FV7z.mk (.avx .vmovdqu) 32 [.vreg 2 256, .mem (mbd 6 32 256)] 5))
    (h3 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5)
      (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 2 256, .vreg 2 256, .mem (mbd 7 32 256)] 5))
    (h4 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5)
      (FV7z.mk (.avx .vpand) 32 [.vreg 5 256, .vreg 1 256, .vreg 2 256] 4))
    (h5 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4)
      (FV7z.mk (.avx .vmovdqu) 32 [.vreg 3 256, .mem (mbd 6 64 256)] 5))
    (h6 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4 + 5)
      (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 3 256, .vreg 3 256, .mem (mbd 7 64 256)] 5))
    (h7 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4 + 5 + 5)
      (FV7z.mk (.avx .vpand) 32 [.vreg 5 256, .vreg 5 256, .vreg 3 256] 4))
    (h8 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4 + 5 + 5 + 4)
      (FV7z.mk (.avx .vmovdqu) 32 [.vreg 4 256, .mem (mbd 6 96 256)] 5))
    (h9 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5)
      (FV7z.mk (.avx (.vpcmpeq 8)) 32 [.vreg 4 256, .vreg 4 256, .mem (mbd 7 96 256)] 5))
    (h10 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5 + 5)
      (FV7z.mk (.avx .vpand) 32 [.vreg 5 256, .vreg 5 256, .vreg 4 256] 4))
    (h11 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5 + 5 + 4)
      (FV7z.mk (.avx .vptest) 32 [.vreg 5 256, .vreg 0 256] 5))
    (h12 : Dec prof.feat avx2Movbe (k + 4 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5)
      (FV7z.mk (.jcc 3) 64 [.rel rel] 6))
    (htgt : (k + 4 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5 + 6 + rel) % 2 ^ 64 = 864 % 2 ^ 64)
    (hlen : k + 61 < 980)
    (hrip : X.cpu.rip = e.add k) (hdi : X.cpu.gpr.rdi = (p₁ s₀).add a) (hsi : X.cpu.gpr.rsi = (p₂ s₀).add a)
    (hz0 : X.cpu.vec.zmm (xmmOf 0) = (BitVec.allOnes 256).setWidth 512)
    (hn : a + 128 ≤ nn s₀) (hpre : ∀ i < a, Ag s₀ i)
    (k' : (∀ i < a + 128, Ag s₀ i) → Then prof L s₀ ra o e (k + 4 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5 + 5 + 4 + 5 + 6)
      fun Y => Y.cpu.gpr = X.cpu.gpr ∧ Y.cpu.vec.zmm (xmmOf 0) = X.cpu.vec.zmm (xmmOf 0)) :
    Go prof L s₀ ra o X t :=
  pair x hK (a := a) h0 h1 (by omega) hrip hdi hsi (by omega) fun Y1 _ hK1 hr1 ⟨g1, z1⟩ =>
  pair x hK1 (a := a) h2 h3 (by omega) hr1 (by rw [g1]; exact hdi) (by rw [g1]; exact hsi) (by omega)
    fun Y2 _ hK2 hr2 ⟨g2, z2⟩ =>
  x.c.s_vpand hK2 (by simp [avx2Movbe_length]; omega) hr2 h4 fun Y3 _ hK3 hr3 ⟨g3, z3⟩ =>
  pair x hK3 (a := a) h5 h6 (by omega) hr3 (by rw [g3, g2, g1]; exact hdi) (by rw [g3, g2, g1]; exact hsi) (by omega)
    fun Y4 _ hK4 hr4 ⟨g4, z4⟩ =>
  x.c.s_vpand hK4 (by simp [avx2Movbe_length]; omega) hr4 h7 fun Y5 _ hK5 hr5 ⟨g5, z5⟩ =>
  pair x hK5 (a := a) h8 h9 (by omega) hr5 (by rw [g5, g4, g3, g2, g1]; exact hdi) (by rw [g5, g4, g3, g2, g1]; exact hsi)
    (by omega) fun Y6 _ hK6 hr6 ⟨g6, z6⟩ =>
  x.c.s_vpand hK6 (by simp [avx2Movbe_length]; omega) hr6 h10 fun Y7 _ hK7 hr7 ⟨g7, z7⟩ =>
  x.c.s_vptest hK7 (by simp [avx2Movbe_length]; omega) hr7 h11 fun Y8 _ hK8 hr8 ⟨g8, z8, f8⟩ => by
    have gX : Y8.cpu.gpr = X.cpu.gpr := by rw [g8, g7, g6, g5, g4, g3, g2, g1]
    have zz : ∀ q, Y8.cpu.vec.zmm q = Y7.cpu.vec.zmm q := fun q => by rw [z8]
    have e0 : Y7.cpu.vec.zmm (xmmOf 0) = X.cpu.vec.zmm (xmmOf 0) := by
      simp only [z7, z6, z5, z4, z3, z2, z1, withZmm, xmmOf]; simp
    have e1 : Y7.cpu.vec.zmm (xmmOf 1) = EqW s₀ a := by
      simp only [z7, z6, z5, z4, z3, z2, z1, withZmm, xmmOf]; simp
    have e2 : Y7.cpu.vec.zmm (xmmOf 2) = EqW s₀ (a + 32) := by
      simp only [z7, z6, z5, z4, z3, z2, withZmm, xmmOf]; simp
    have e3 : Y7.cpu.vec.zmm (xmmOf 3) = EqW s₀ (a + 64) := by
      simp only [z7, z6, z5, z4, withZmm, xmmOf]; simp
    have e4 : Y7.cpu.vec.zmm (xmmOf 4) = EqW s₀ (a + 96) := by
      simp only [z7, z6, withZmm, xmmOf]; simp
    have hall : Y8.cpu.rflags.cf = true ↔ ∀ j < 128, Ag s₀ (a + j) := by
      rw [f8, e0, hz0, cf_all]
      refine all4 a fun i hi => ?_
      simp only [z7, z6, z5, z4, z3, z2, z1, withZmm, xmmOf]
      simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, getLsbD_EqW', hi, and_assoc]
    refine x.c.s_jcc hK8 (by simp [avx2Movbe_length]; omega) hr8 h12 htgt (by simp [avx2Movbe_length])
      (fun hc => ?_) (fun hc => ?_)
    · intro Y9 t9 hK9 hr9 ⟨g9, z9⟩
      rw [cond3, Bool.not_eq_true'] at hc
      refine h864 x hK9 (hC.of_gpr (by simp [g9, gX])) hr9 (by rw [g9, gX]; exact hdi) (by rw [g9, gX]; exact hsi)
        (by rw [z9, zz, e1]) (by rw [z9, zz, e2]) (by rw [z9, zz, e3]) (by rw [z9, zz, e4]) hn hpre ?_
      intro h; rw [← hall] at h; rw [h] at hc; exact Bool.noConfusion hc
    · intro Y9 t9 hK9 hr9 ⟨g9, z9⟩
      rw [cond3, Bool.not_eq_false'] at hc
      exact k' (agree_join rfl rfl hpre (hall.1 hc)) Y9 t9 hK9 hr9 ⟨by rw [g9, gX], by rw [z9, zz, e0]⟩

end FV7z.MemcmpAvx2
