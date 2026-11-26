import FV7z.Sen.Cuts
import FV7z.Rfw.Holds
import FV7z.Lemmas.SpCallK
import FV7z.Lemmas.Signed
/-!
# `StringsAreEqualNoCase` (PLAN.md §M, M1)

7-Zip 26.06's `StringsAreEqualNoCase (const wchar_t *s1, const wchar_t *s2)` at `0x44ba80` in `7zzs`
(`CPP/Common/MyString.cpp`; `objdump -d`): the 32-bit characters of `p` = `rdi` and `q` = `rsi` (`c1`, `c2`),
compared through `MyCharUpper` (`Up`: `c - 32` for `a`..`z`, `c` up to 127, `towupper` above), up to the first 0 of
`p`; 1 if all are equal (`Eqs`), else 0. `towupper` (glibc, `0x669660`) is a hypothesis `FnK` with `Rt`: it changes
`rax`, `rcx`, `rdx`, `rsi`, `rdi` alone (`setWidth 32 rax` = `U` of `edi`), no bytes (a leaf: no `push`, no stores).

Cut points: the entry (0), the loop's head (62, the characters `i` next), in the loop with the characters `i` loaded
(40 and 107: the calls, 45, 48, 53, 58, 87, 95, 112), the `return 0` (144); the `ret`s at 141 (1) and 154 (0).
The measure 20 (`N` - `i`) + a rank, `N` the index of a 0 of `p`. The bytes: as after the five `push`es (`Vp`) but
for the return address's slot of the calls (`Keep`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sen

/-! ## The `ret`s and the calls -/

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_141 : pret <+: sen.drop 141 := by decide +kernel
theorem w_154 : pret <+: sen.drop 154 := by decide +kernel
theorem ret_at (feat : Features) {j : Nat} (hj : j = 141 ∨ j = 154) :
    j < sen.length ∧ Dec feat sen j (FV7z.mk .ret 64 [] 1) := by
  rcases hj with rfl | rfl
  · exact ⟨lt_len (by decide), Dec.shift (j := 141) (k := 0) (pret_0 feat) w_141 (Nat.zero_le _)⟩
  · exact ⟨lt_len (by decide), Dec.shift (j := 154) (k := 0) (pret_0 feat) w_154 (Nat.zero_le _)⟩

def pc1 : List Byte := [0xe8, 0xb3, 0xdb, 0x21, 0x00]
def pc2 : List Byte := [0xe8, 0x70, 0xdb, 0x21, 0x00]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 2218931] 5) := by dec_rfl
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 2218864] 5) := by dec_rfl
theorem w_40 : pc1 <+: sen.drop 40 := by decide +kernel
theorem w_107 : pc2 <+: sen.drop 107 := by decide +kernel
theorem cl40 (feat : Features) : Dec feat sen 40 (FV7z.mk .call 64 [.rel 2218931] 5) :=
  Dec.shift (j := 40) (k := 0) (pc1_0 feat) w_40 (Nat.zero_le _)
theorem cl107 (feat : Features) : Dec feat sen 107 (FV7z.mk .call 64 [.rel 2218864] 5) :=
  Dec.shift (j := 107) (k := 0) (pc2_0 feat) w_107 (Nat.zero_le _)

/-- glibc's `towupper`. -/
abbrev tup_at : Addr := 0x669660
theorem tg40 : Addr.add sen_at (40 + 5) + BitVec.ofNat 64 2218931 = tup_at := by decide
theorem tg107 : Addr.add sen_at (107 + 5) + BitVec.ofNat 64 2218864 = tup_at := by decide

/-! ## Arithmetic -/

/-- `jle` after `cmp x, y` (32 bits): signed not greater. -/
theorem subF_le32 (f : Rflags) (x y : BitVec 32) : (subF f x y).cond 14 = decide (x.toInt ≤ y.toInt) := by
  have e : (subF f x y).cond 14 = !((subF f x y).cond 15) := by simp only [Rflags.cond, Bool.not_not]
  rw [e, subF_g32]
  by_cases h : x.toInt ≤ y.toInt
  · rw [decide_eq_true h, decide_eq_false (Int.not_lt.mpr h)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (Int.lt_of_not_ge h)]
    rfl

theorem i96 : (96#32 : BitVec 32).toInt = 96 := by decide
theorem i122 : (122#32 : BitVec 32).toInt = 122 := by decide
theorem i127 : (127#32 : BitVec 32).toInt = 127 := by decide

/-- `lea r14d, [rbx - 32]`. -/
theorem l32 (c : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 c + 18446744073709551584#64) = c - 32#32 := by
  bv_omega

/-- `add r13, 4`. -/
theorem ad4 (p : Addr) (i : Nat) : Addr.add p (4 * i) + 4#64 = Addr.add p (4 * (i + 1)) :=
  (FV7z.Rfw.add4 p i).symm

theorem s_1 (s : Addr) (h : 48 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem s_2 (s : Addr) (h : 48 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem s_3 (s : Addr) (h : 48 ≤ s.toNat) : (s - 8 - 8 - 8).toNat = s.toNat - 24 := by bv_omega
theorem s_4 (s : Addr) (h : 48 ≤ s.toNat) : (s - 8 - 8 - 8 - 8).toNat = s.toNat - 32 := by bv_omega
theorem s_5 (s : Addr) (h : 48 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8).toNat = s.toNat - 40 := by bv_omega
theorem s_6 (s : Addr) (h : 48 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8 - 8).toNat = s.toNat - 48 := by bv_omega

theorem set4 (g : Gprs) (v : BitVec 64) : g.set 4 v = { g with rsp := v } := rfl

/-! ## The specification -/

/-- 7-Zip's `MyCharUpper` of a character, `U` = `towupper`. -/
def Up (U : BitVec 32 → BitVec 32) (c : BitVec 32) : BitVec 32 :=
  if c.toInt ≤ 96 then c else if c.toInt ≤ 122 then c - 32#32 else if c.toInt ≤ 127 then c else U c

theorem up_le {U : BitVec 32 → BitVec 32} {c : BitVec 32} (h : c.toInt ≤ 96) : Up U c = c := by
  rw [Up, if_pos h]
theorem up_lo {U : BitVec 32 → BitVec 32} {c : BitVec 32} (h1 : ¬ c.toInt ≤ 96) (h2 : c.toInt ≤ 122) :
    Up U c = c - 32#32 := by
  rw [Up, if_neg h1, if_pos h2]
theorem up_mid {U : BitVec 32 → BitVec 32} {c : BitVec 32} (h2 : ¬ c.toInt ≤ 122) (h3 : c.toInt ≤ 127) :
    Up U c = c := by
  rw [Up, if_neg (by omega), if_neg h2, if_pos h3]
theorem up_hi {U : BitVec 32 → BitVec 32} {c : BitVec 32} (h3 : ¬ c.toInt ≤ 127) : Up U c = U c := by
  rw [Up, if_neg (by omega), if_neg (by omega), if_neg h3]

/-- The characters `i` of `p` = `rdi` and `q` = `rsi`. -/
def c1 (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) : BitVec 32 := rdd(V₀, Addr.add g₀.rdi (4 * i))
def c2 (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) : BitVec 32 := rdd(V₀, Addr.add g₀.rsi (4 * i))

/-- The first `i` characters: none of `p`'s 0, and equal through `Up`. -/
def Pre (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) : Prop :=
  ∀ k < i, c1 g₀ V₀ k ≠ 0 ∧ Up U (c1 g₀ V₀ k) = Up U (c2 g₀ V₀ k)

/-- The strings equal through `Up`, up to `p`'s first 0. -/
def Eqs (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) : Prop :=
  ∃ n, Pre U g₀ V₀ n ∧ c1 g₀ V₀ n = 0 ∧ Up U (c1 g₀ V₀ n) = Up U (c2 g₀ V₀ n)

variable {U : BitVec 32 → BitVec 32} {N : Nat} {g₀ : Gprs} {V₀ : Addr → Byte}

theorem pre0 : Pre U g₀ V₀ 0 := fun k hk => absurd hk (Nat.not_lt_zero k)

theorem pre_le {i : Nat} (hP : Pre U g₀ V₀ i) (hN : c1 g₀ V₀ N = 0) : i ≤ N := by
  apply Nat.le_of_not_lt
  intro h
  exact (hP N h).1 hN

theorem pre_succ {i : Nat} (hP : Pre U g₀ V₀ i) (hz : c1 g₀ V₀ i ≠ 0)
    (hu : Up U (c1 g₀ V₀ i) = Up U (c2 g₀ V₀ i)) : Pre U g₀ V₀ (i + 1) := fun k hk => by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
  · exact hP k h
  · exact ⟨hz, hu⟩

theorem neqs {i : Nat} (hP : Pre U g₀ V₀ i) (hne : Up U (c1 g₀ V₀ i) ≠ Up U (c2 g₀ V₀ i)) :
    ¬ Eqs U g₀ V₀ := by
  rintro ⟨n, hPn, hz, hu⟩
  rcases Nat.lt_trichotomy i n with h | rfl | h
  · exact hne (hPn i h).2
  · exact hne hu
  · exact (hP n h).1 hz

/-! ## The bytes -/

/-- After the five `push`es. -/
def Vp (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r14 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.r13 8))
    (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.r12 8)) (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbp 8))
    (g₀.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8)

/-- As after the `push`es but for the slot of the calls' return address. -/
def Keep (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  ∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat - 40 ≤ y.toNat → V y = Vp g₀ V₀ y

/-- A character's 4 bytes: not wrapping, apart from the frame. -/
def Ok (s x : Addr) : Prop := x.toNat + 4 ≤ 2 ^ 64 ∧ (x.toNat + 4 ≤ s.toNat - 48 ∨ s.toNat ≤ x.toNat)

/-- The frame below the return address at `s`: the `push`es' and the calls' slots, those of the `pop`s and the
`ret`. -/
structure Fr (F : Footprint) (Wl : List Rgn) (s : Addr) : Prop where
  lo : 48 ≤ s.toNat
  hi : s.toNat + 8 ≤ 2 ^ 64
  w1 : ∀ i < 8, Foot Wl (Addr.add (s - 8) i)
  w2 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8) i)
  w3 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8) i)
  w4 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8) i)
  w5 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8 - 8) i)
  w6 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8 - 8 - 8) i)
  d0 : ∀ i < 8, Foot F.data (Addr.add s i)
  d1 : ∀ i < 8, Foot F.data (Addr.add (s - 8) i)
  d2 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8) i)
  d3 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8) i)
  d4 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8 - 8) i)
  d5 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8 - 8 - 8) i)

theorem Vp_out (hlo : 48 ≤ g₀.rsp.toNat) (y : Addr)
    (h : y.toNat < g₀.rsp.toNat - 40 ∨ g₀.rsp.toNat ≤ y.toNat) : Vp g₀ V₀ y = V₀ y := by
  have := g₀.rsp.isLt
  have e1 := s_1 _ hlo
  have e2 := s_2 _ hlo
  have e3 := s_3 _ hlo
  have e4 := s_4 _ hlo
  have e5 := s_5 _ hlo
  dsimp only [Vp]
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e5]; omega) (by rw [toBytesLE_length, e5]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- A character apart from the frame reads as at the entry. -/
theorem keep_rd {V : Addr → Byte} {x : Addr} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V)
    (hx : Ok g₀.rsp x) : rdd(V, x) = rdd(V₀, x) := by
  obtain ⟨hx1, hx2⟩ := hx
  apply congrArg (ofBytesLE 32)
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have := toNat_add_of_fits hj hx1
  rw [hK (x.add j) (by omega), Vp_out hlo (x.add j) (by omega)]

/-- The store of a call's return address. -/
theorem keep_st {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V) (v : BitVec 64) :
    Keep g₀ V₀ (Vst V (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE v 8)) := fun y hy => by
  have := g₀.rsp.isLt
  have e6 := s_6 _ hlo
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega)]
  exact hK y hy

/-- Outside the frame, the bytes at a call are those at the entry. -/
theorem keep_tt {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V) (v : BitVec 64) :
    ∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat ≤ y.toNat →
      Vst V (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE v 8) y = V₀ y := fun y hy => by
  rw [keep_st hlo hK v y (by omega), Vp_out hlo y (by omega)]

theorem keep_out {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V) :
    ∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat ≤ y.toNat → V y = V₀ y := fun y hy => by
  rw [hK y (by omega), Vp_out hlo y (by omega)]

theorem rq_self (V : Addr → Byte) (a : Addr) (v : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst V a (toBytesLE v 8), a) = v := by
  rw [Tun.rd_Vst_self V a (toBytesLE v 8) (toBytesLE_length v 8) ha]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem rq_out (V : Addr → Byte) (a x : Addr) (v : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) :
    rdq(Vst V a (toBytesLE v 8), x) = rdq(V, x) := by
  rw [Tun.rd_Vst V a (toBytesLE v 8) x 8 (by rw [toBytesLE_length]; exact ha) hx
    (by rw [toBytesLE_length]; exact h)]

/-- 8 bytes in the frame or above read as after the `push`es. -/
theorem keep_q {V : Addr → Byte} (hK : Keep g₀ V₀ V) {x : Addr} (h1 : g₀.rsp.toNat - 40 ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ 2 ^ 64) : rdq(V, x) = rdq(Vp g₀ V₀, x) := by
  apply congrArg (ofBytesLE 64)
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have := toNat_add_of_fits hj h2
  exact hK _ (Or.inr (by omega))

/-- The `pop`s' loads. -/
theorem pops {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hhi : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hK : Keep g₀ V₀ V) :
    rdq(V, g₀.rsp - 8) = g₀.r14 ∧ rdq(V, g₀.rsp - 8 - 8) = g₀.r13 ∧ rdq(V, g₀.rsp - 8 - 8 - 8) = g₀.r12 ∧
      rdq(V, g₀.rsp - 8 - 8 - 8 - 8) = g₀.rbp ∧ rdq(V, g₀.rsp - 8 - 8 - 8 - 8 - 8) = g₀.rbx := by
  have e1 := s_1 _ hlo
  have e2 := s_2 _ hlo
  have e3 := s_3 _ hlo
  have e4 := s_4 _ hlo
  have e5 := s_5 _ hlo
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [keep_q hK (x := g₀.rsp - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8) _ (by omega)]
  · rw [keep_q hK (x := g₀.rsp - 8 - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8 - 8) _ (by omega)]
  · rw [keep_q hK (x := g₀.rsp - 8 - 8 - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8 - 8 - 8) _ (by omega)]
  · rw [keep_q hK (x := g₀.rsp - 8 - 8 - 8 - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8 - 8 - 8 - 8) _ (by omega)]
  · rw [keep_q hK (x := g₀.rsp - 8 - 8 - 8 - 8 - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_self _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) _ (by omega)]

/-- The return address. -/
theorem keep_ra {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hhi : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hK : Keep g₀ V₀ V) : rdq(V, g₀.rsp) = rdq(V₀, g₀.rsp) := by
  apply congrArg (ofBytesLE 64)
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have := toNat_add_of_fits hj hhi
  exact keep_out hlo hK _ (Or.inr (by omega))

/-! ## `towupper` -/

/-- `towupper` from its entry to the return address: `rax`, `rcx`, `rdx`, `rsi`, `rdi` changed, `eax` = `U edi`,
the bytes as they were. -/
def Rt (U : BitVec 32 → BitVec 32) : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop :=
  fun g W g' W' => W' = W ∧ ∃ a c d si di, g' = { g with
    rax := a, rcx := c, rdx := d, rsi := si, rdi := di,
    rsp := g.rsp + 8 } ∧ BitVec.setWidth 32 a = U (BitVec.setWidth 32 g.rdi)

/-- `towupper`'s condition at the calls: the return address 48 bytes below that at the entry, the bytes outside
the frame those at the entry. -/
def TtOk (g₀ : Gprs) (V₀ : Addr → Byte) (Tt : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ g W, g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 →
    (∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat ≤ y.toNat → W y = V₀ y) → Tt g W

/-! ## The invariant -/

/-- The registers in the loop: the strings' pointers at the characters `j`. -/
def Sh (g₀ : Gprs) (j : Nat) (a di b bp r : BitVec 64) (g : Gprs) : Prop :=
  ∃ c d si, g = { g₀ with
    rax := a, rcx := c, rdx := d, rbx := b, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := bp,
    rsi := si, rdi := di, r12 := Addr.add g₀.rsi (4 * j), r13 := Addr.add g₀.rdi (4 * j), r14 := r }

def I62 (g₀ : Gprs) (i : Nat) (g : Gprs) : Prop := ∃ a di b bp r, Sh g₀ i a di b bp r g
def I40 (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  127 < (c1 g₀ V₀ i).toInt ∧ ∃ a r, Sh g₀ (i + 1) a (BitVec.setWidth 64 (c1 g₀ V₀ i))
    (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c2 g₀ V₀ i)) r g
def I45 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  127 < (c1 g₀ V₀ i).toInt ∧ ∃ a di r, Sh g₀ (i + 1) a di (BitVec.setWidth 64 (c1 g₀ V₀ i))
    (BitVec.setWidth 64 (c2 g₀ V₀ i)) r g ∧ BitVec.setWidth 32 a = U (c1 g₀ V₀ i)
def I48 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ∃ a di r, Sh g₀ (i + 1) a di (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c2 g₀ V₀ i)) r g ∧
    BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i)
def I87 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ Up U (c1 g₀ V₀ i) = c1 g₀ V₀ i ∧
    ∃ a di r, Sh g₀ (i + 1) a di (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c2 g₀ V₀ i)) r g
def I95 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  96 < (c2 g₀ V₀ i).toInt ∧ ∃ a di r, Sh g₀ (i + 1) a di (BitVec.setWidth 64 (c1 g₀ V₀ i))
    (BitVec.setWidth 64 (c2 g₀ V₀ i)) r g ∧ BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i)
def I107 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  127 < (c2 g₀ V₀ i).toInt ∧ ∃ a r, Sh g₀ (i + 1) a (BitVec.setWidth 64 (c2 g₀ V₀ i))
    (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c2 g₀ V₀ i)) r g ∧
    BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i)
def I112 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  127 < (c2 g₀ V₀ i).toInt ∧ ∃ a di r, Sh g₀ (i + 1) a di (BitVec.setWidth 64 (c1 g₀ V₀ i))
    (BitVec.setWidth 64 (c2 g₀ V₀ i)) r g ∧ BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i) ∧
    BitVec.setWidth 32 a = U (c2 g₀ V₀ i)
def I53 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ∃ a di bp r, Sh g₀ (i + 1) a di (BitVec.setWidth 64 (c1 g₀ V₀ i)) bp r g ∧
    BitVec.setWidth 32 bp = Up U (c2 g₀ V₀ i) ∧ BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i)
def I58 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  Up U (c1 g₀ V₀ i) = Up U (c2 g₀ V₀ i) ∧
    ∃ a di bp r, Sh g₀ (i + 1) a di (BitVec.setWidth 64 (c1 g₀ V₀ i)) bp r g
def I144 (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) : Prop :=
  ¬ Eqs U g₀ V₀ ∧ ∃ j a di b bp r, Sh g₀ j a di b bp r g

/-- The invariant at the cut points, `n` the measure. -/
def Inv (U : BitVec 32 → BitVec 32) (N : Nat) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs)
    (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ n = 20 * N + 20 ∧ g = g₀ ∧ V = V₀) ∨
  (Keep g₀ V₀ V ∧ ((ℓ = 144 ∧ n = 2 ∧ I144 U g₀ V₀ g) ∨ ∃ i, Pre U g₀ V₀ i ∧ (
    (ℓ = 62 ∧ n = 20 * (N - i) + 13 ∧ I62 g₀ i g) ∨
    (ℓ = 40 ∧ n = 20 * (N - i) + 11 ∧ I40 g₀ V₀ i g) ∨
    (ℓ = 45 ∧ n = 20 * (N - i) + 10 ∧ I45 U g₀ V₀ i g) ∨
    (ℓ = 48 ∧ n = 20 * (N - i) + 9 ∧ I48 U g₀ V₀ i g) ∨
    (ℓ = 87 ∧ n = 20 * (N - i) + 8 ∧ I87 U g₀ V₀ i g) ∨
    (ℓ = 95 ∧ n = 20 * (N - i) + 7 ∧ I95 U g₀ V₀ i g) ∨
    (ℓ = 107 ∧ n = 20 * (N - i) + 6 ∧ I107 U g₀ V₀ i g) ∨
    (ℓ = 112 ∧ n = 20 * (N - i) + 5 ∧ I112 U g₀ V₀ i g) ∨
    (ℓ = 53 ∧ n = 20 * (N - i) + 4 ∧ I53 U g₀ V₀ i g) ∨
    (ℓ = 58 ∧ n = 20 * (N - i) + 3 ∧ I58 U g₀ V₀ i g))))

/-- At a `ret`: 1 (141) if the strings are equal, else 0 (154); the callee-saved registers restored. -/
def Fin (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) :
    Prop :=
  Keep g₀ V₀ V ∧ ∃ a c d si di, g = { g₀ with rax := a, rcx := c, rdx := d, rsi := si, rdi := di } ∧
    ((j = 141 ∧ a = 1#64 ∧ Eqs U g₀ V₀) ∨ (j = 154 ∧ a = 0#64 ∧ ¬ Eqs U g₀ V₀))

def Nx (U : BitVec 32 → BitVec 32) (N : Nat) (g₀ : Gprs) (V₀ : Addr → Byte) (m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv U N g₀ V₀ j m' g V) ∨ Fin U g₀ V₀ j g V

/-! ## The exits -/

section X
variable {m i : Nat} {V : Addr → Byte} {g : Gprs} {fl : Rflags} {a c d si di b bp r : BitVec 64}

theorem x62z (hm : 20 * N + 13 < m) (hK : Keep g₀ V₀ V)
    (hg : g = { g₀ with rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, r12 := g₀.rsi, r13 := g₀.rdi }) :
    Nx U N g₀ V₀ m 62 g fl V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨0, pre0, Or.inl ⟨rfl, by omega, g₀.rax, g₀.rdi, g₀.rbx, g₀.rbp,
    g₀.r14, g₀.rcx, g₀.rdx, g₀.rsi, ?_⟩⟩⟩⟩
  rw [hg]
  simp only [Nat.mul_zero, addr_add_zero]

theorem x62s (hN : c1 g₀ V₀ N = 0) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (hz : c1 g₀ V₀ i ≠ 0)
    (hu : Up U (c1 g₀ V₀ i) = Up U (c2 g₀ V₀ i)) (hm : 20 * (N - i) + 3 ≤ m)
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := b, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := bp,
      rsi := si, rdi := di, r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)),
      r14 := r }) :
    Nx U N g₀ V₀ m 62 g fl V := by
  have hle := pre_le hP hN
  have hne : i ≠ N := by
    rintro rfl
    exact hz hN
  exact Or.inl ⟨_, by omega, Or.inr ⟨hK, Or.inr ⟨i + 1, pre_succ hP hz hu, Or.inl ⟨rfl, rfl, a, di, b, bp, r,
    c, d, si, hg⟩⟩⟩⟩

theorem x40 (hm : 20 * (N - i) + 11 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (h : 127 < (c1 g₀ V₀ i).toInt)
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := BitVec.setWidth 64 (c2 g₀ V₀ i), rsi := si,
      rdi := BitVec.setWidth 64 (c1 g₀ V₀ i), r12 := Addr.add g₀.rsi (4 * (i + 1)),
      r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 40 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inl ⟨rfl, rfl, h, a, r, c, d, si, hg⟩)⟩⟩⟩

theorem x45 (hm : 20 * (N - i) + 10 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (h : 127 < (c1 g₀ V₀ i).toInt) (ha : BitVec.setWidth 32 a = U (c1 g₀ V₀ i))
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := BitVec.setWidth 64 (c2 g₀ V₀ i), rsi := si, rdi := di,
      r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 45 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h, a, di, r, ⟨c, d, si, hg⟩,
    ha⟩))⟩⟩⟩

theorem x48 (hm : 20 * (N - i) + 9 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (hr : BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i))
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := BitVec.setWidth 64 (c2 g₀ V₀ i), rsi := si, rdi := di,
      r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 48 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, a, di, r,
    ⟨c, d, si, hg⟩, hr⟩)))⟩⟩⟩

theorem x87 (hm : 20 * (N - i) + 8 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (hu : Up U (c1 g₀ V₀ i) = c1 g₀ V₀ i)
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := BitVec.setWidth 64 (c2 g₀ V₀ i), rsi := si, rdi := di,
      r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 87 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hne, hu, a, di,
    r, c, d, si, hg⟩))))⟩⟩⟩

theorem x95 (hm : 20 * (N - i) + 7 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (h : 96 < (c2 g₀ V₀ i).toInt) (hr : BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i))
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := BitVec.setWidth 64 (c2 g₀ V₀ i), rsi := si, rdi := di,
      r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 95 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h, a,
    di, r, ⟨c, d, si, hg⟩, hr⟩)))))⟩⟩⟩

theorem x107 (hm : 20 * (N - i) + 6 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (h : 127 < (c2 g₀ V₀ i).toInt) (hr : BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i))
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := BitVec.setWidth 64 (c2 g₀ V₀ i), rsi := si,
      rdi := BitVec.setWidth 64 (c2 g₀ V₀ i), r12 := Addr.add g₀.rsi (4 * (i + 1)),
      r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 107 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl,
    h, a, r, ⟨c, d, si, hg⟩, hr⟩))))))⟩⟩⟩

theorem x112 (hm : 20 * (N - i) + 5 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (h : 127 < (c2 g₀ V₀ i).toInt) (hr : BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i))
    (ha : BitVec.setWidth 32 a = U (c2 g₀ V₀ i))
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := BitVec.setWidth 64 (c2 g₀ V₀ i), rsi := si, rdi := di,
      r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 112 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, rfl, h, a, di, r, ⟨c, d, si, hg⟩, hr, ha⟩)))))))⟩⟩⟩

theorem x53 (hm : 20 * (N - i) + 4 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (hbp : BitVec.setWidth 32 bp = Up U (c2 g₀ V₀ i)) (hr : BitVec.setWidth 32 r = Up U (c1 g₀ V₀ i))
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := bp, rsi := si, rdi := di,
      r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 53 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, a, di, bp, r, ⟨c, d, si, hg⟩, hbp, hr⟩))))))))⟩⟩⟩

theorem x58 (hm : 20 * (N - i) + 3 < m) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (hu : Up U (c1 g₀ V₀ i) = Up U (c2 g₀ V₀ i))
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := BitVec.setWidth 64 (c1 g₀ V₀ i),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := bp, rsi := si, rdi := di,
      r12 := Addr.add g₀.rsi (4 * (i + 1)), r13 := Addr.add g₀.rdi (4 * (i + 1)), r14 := r }) :
    Nx U N g₀ V₀ m 58 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr ⟨rfl, rfl, hu, a, di, bp, r, c, d, si, hg⟩))))))))⟩⟩⟩

theorem x144 {j : Nat} (hm : 2 < m) (hK : Keep g₀ V₀ V) (hne : ¬ Eqs U g₀ V₀)
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := b, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8, rbp := bp,
      rsi := si, rdi := di, r12 := Addr.add g₀.rsi (4 * j), r13 := Addr.add g₀.rdi (4 * j), r14 := r }) :
    Nx U N g₀ V₀ m 144 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inl ⟨rfl, rfl, hne, j, a, di, b, bp, r, c, d, si, hg⟩⟩⟩

theorem xF1 (hK : Keep g₀ V₀ V) (ha : a = 1#64) (he : Eqs U g₀ V₀)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rsi := si, rdi := di }) : Nx U N g₀ V₀ m 141 g fl V :=
  Or.inr ⟨hK, a, c, d, si, di, hg, Or.inl ⟨rfl, ha, he⟩⟩

theorem xF0 (hK : Keep g₀ V₀ V) (ha : a = 0#64) (hne : ¬ Eqs U g₀ V₀)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rsi := si, rdi := di }) : Nx U N g₀ V₀ m 154 g fl V :=
  Or.inr ⟨hK, a, c, d, si, di, hg, Or.inr ⟨rfl, ha, hne⟩⟩

end X

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn} {i : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- The entry: the five `push`es, the loop's head with the characters 0 next. -/
theorem vc_0 (hF : Fr F Wl g₀.rsp) : W_0 F Wl (Nx U N g₀ V₀ (20 * N + 20)) g₀ f V₀ := by
  have hK : Keep g₀ V₀ (Vp g₀ V₀) := fun _ _ => rfl
  obtain ⟨-, -, w1, w2, w3, w4, w5, -, -, -, -, -, -, -⟩ := hF
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at w1 w2 w3 w4 w5
  wpx [W_0, o0]
  exact ⟨w1, w2, w3, w4, w5, x62z (by omega) hK rfl⟩

set_option maxHeartbeats 2000000 in
/-- The loop's head: the loads; equal, or by the case of `p`'s character. -/
theorem vc_62 (hF : Fr F Wl g₀.rsp)
    (hw : ∀ k, Pre U g₀ V₀ k → ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add g₀.rsi (4 * k)) j))
    (hd : ∀ k, Pre U g₀ V₀ k → Ok g₀.rsp (Addr.add g₀.rdi (4 * k)) ∧ Ok g₀.rsp (Addr.add g₀.rsi (4 * k)))
    (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I62 g₀ i g) :
    W_62 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 13)) g f V := by
  obtain ⟨a, di, b, bp, r, c, d, si, rfl⟩ := h
  have hr1 : rdd(V, Addr.add g₀.rdi (4 * i)) = c1 g₀ V₀ i := keep_rd hF.lo hK (hd i hP).1
  have hr2 : rdd(V, Addr.add g₀.rsi (4 * i)) = c2 g₀ V₀ i := keep_rd hF.lo hK (hd i hP).2
  have f1 : ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * i)) j) := fun j hj => (hw i hP j hj).1
  have f2 : ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rsi (4 * i)) j) := fun j hj => (hw i hP j hj).2
  wpx [W_62, W_82, W_24, W_33, W_38, o8, o9, o1, o2, o3, hr1, hr2, ad4, l32, subF_g32, subF_le32, i96, i122,
    i127, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible exact f1
    | with_reducible exact f2
    | apply And.intro
    | intro)
  all_goals first
    | exact x58 (by omega) hK hP (congrArg (Up U) (by assumption)) rfl
    | exact x48 (by omega) hK hP (by rw [sw_64_32]; exact (up_lo (by omega) (by omega)).symm) rfl
    | exact x87 (by omega) hK hP (by assumption) (up_mid (by omega) (by omega)) rfl
    | exact x40 (by omega) hK hP (by omega) rfl
    | exact x87 (by omega) hK hP (by assumption) (up_le (by omega)) rfl

set_option maxHeartbeats 1000000 in
/-- `test ebx, ebx`: the `return 1` at `p`'s 0, else the next characters. -/
theorem vc_58 (hF : Fr F Wl g₀.rsp) (hN : c1 g₀ V₀ N = 0) (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i)
    (h : I58 U g₀ V₀ i g) : W_58 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 3)) g f V := by
  obtain ⟨hu, a, di, bp, r, c, d, si, rfl⟩ := h
  obtain ⟨q1, q2, q3, q4, q5⟩ := pops hF.lo hF.hi hK
  have d1 := hF.d1
  have d2 := hF.d2
  have d3 := hF.d3
  have d4 := hF.d4
  have d5 := hF.d5
  wpx [W_58, W_128, o7, o16, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, BitVec.sub_add_cancel, q1, q2,
    q3, q4, q5]
  all_goals repeat' (first
    | with_reducible exact d1
    | with_reducible exact d2
    | with_reducible exact d3
    | with_reducible exact d4
    | with_reducible exact d5
    | apply And.intro
    | intro)
  all_goals first
    | exact xF1 hK (by decide) ⟨i, hP, by assumption, hu⟩ rfl
    | exact x62s hN hK hP (by assumption) hu (by omega) rfl

set_option maxHeartbeats 1000000 in
/-- `cmp ebp, r14d`: the `return 0` if the upper cases differ. -/
theorem vc_53 (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I53 U g₀ V₀ i g) :
    W_53 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 4)) g f V := by
  obtain ⟨a, di, bp, r, ⟨c, d, si, rfl⟩, hbp, hr⟩ := h
  wpx [W_53, o6, hbp, hr, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · exact x144 (by omega) hK (neqs hP fun e => h1 e.symm) rfl
  · exact x58 (by omega) hK hP h1.symm rfl

set_option maxHeartbeats 1000000 in
/-- `cmp ebp, 96`. -/
theorem vc_48 (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I48 U g₀ V₀ i g) :
    W_48 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 9)) g f V := by
  obtain ⟨a, di, r, ⟨c, d, si, rfl⟩, hr⟩ := h
  wpx [W_48, o5, subF_g32, i96, decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · exact x95 (by omega) hK hP (by omega) hr rfl
  · exact x53 (by omega) hK hP (by rw [sw_64_32]; exact (up_le (by omega)).symm) hr rfl

set_option maxHeartbeats 1000000 in
/-- After the first call: `mov r14d, eax`. -/
theorem vc_45 (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I45 U g₀ V₀ i g) :
    W_45 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 10)) g f V := by
  obtain ⟨h127, a, di, r, ⟨c, d, si, rfl⟩, ha⟩ := h
  wpx [W_45, o4]
  exact x48 (by omega) hK hP (by rw [sw_64_32, ha]; exact (up_hi (by omega)).symm) rfl

set_option maxHeartbeats 1000000 in
/-- `cmp ebp, 96` with `p`'s character its own upper case. -/
theorem vc_87 (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I87 U g₀ V₀ i g) :
    W_87 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 8)) g f V := by
  obtain ⟨hne, hu1, a, di, r, c, d, si, rfl⟩ := h
  wpx [W_87, W_92, o5, o10, subF_le32, i96, decide_eq_true_eq, decide_eq_false_iff_not]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have e2 : Up U (c2 g₀ V₀ i) = c2 g₀ V₀ i := up_le (by omega)
    exact x144 (by omega) hK (neqs hP (by rw [hu1, e2]; exact hne)) rfl
  · exact x95 (by omega) hK hP (by omega) (by rw [sw_64_32]; exact hu1.symm) rfl

set_option maxHeartbeats 1000000 in
/-- `q`'s character above 96: `a`..`z`, up to 127, or the call. -/
theorem vc_95 (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I95 U g₀ V₀ i g) :
    W_95 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 7)) g f V := by
  obtain ⟨h96, a, di, r, ⟨c, d, si, rfl⟩, hr⟩ := h
  wpx [W_95, W_120, W_100, W_105, o11, o15, o12, o13, subF_le32, i122, i127, decide_eq_true_eq,
    decide_eq_false_iff_not]
  refine ⟨fun h1 => ?_, fun h1 => ⟨fun h2 => ?_, fun h2 => ?_⟩⟩
  · exact x53 (by omega) hK hP (by rw [sw_64_32]; exact (up_lo (by omega) (by omega)).symm) hr rfl
  · exact x53 (by omega) hK hP (by rw [sw_64_32]; exact (up_mid (by omega) (by omega)).symm) hr rfl
  · exact x107 (by omega) hK hP (by omega) hr rfl

set_option maxHeartbeats 1000000 in
/-- After the second call: `mov ebp, eax`. -/
theorem vc_112 (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I112 U g₀ V₀ i g) :
    W_112 F Wl (Nx U N g₀ V₀ (20 * (N - i) + 5)) g f V := by
  obtain ⟨h127, a, di, r, ⟨c, d, si, rfl⟩, hr, ha⟩ := h
  wpx [W_112, o14]
  exact x53 (by omega) hK hP (by rw [sw_64_32, ha]; exact (up_hi (by omega)).symm) hr rfl

set_option maxHeartbeats 1000000 in
/-- The `return 0`. -/
theorem vc_144 (hF : Fr F Wl g₀.rsp) (hK : Keep g₀ V₀ V) (h : I144 U g₀ V₀ g) :
    W_144 F Wl (Nx U N g₀ V₀ 2) g f V := by
  obtain ⟨hne, j, a, di, b, bp, r, c, d, si, rfl⟩ := h
  obtain ⟨q1, q2, q3, q4, q5⟩ := pops hF.lo hF.hi hK
  have d1 := hF.d1
  have d2 := hF.d2
  have d3 := hF.d3
  have d4 := hF.d4
  have d5 := hF.d5
  wpx [W_144, o17, BitVec.xor_self, BitVec.sub_add_cancel, q1, q2, q3, q4, q5]
  all_goals repeat' (first
    | with_reducible exact d1
    | with_reducible exact d2
    | with_reducible exact d3
    | with_reducible exact d4
    | with_reducible exact d5
    | apply And.intro
    | intro)
  all_goals exact xF0 hK (by simp) hne rfl

/-- The first call of `towupper`, of `p`'s character. -/
theorem vc_40 {Tt : Gprs → (Addr → Byte) → Prop} (hF : Fr F Wl g₀.rsp) (hTt : TtOk g₀ V₀ Tt)
    (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I40 g₀ V₀ i g) :
    CallK Wl sen_at 45 Tt (Rt U) (Nx U N g₀ V₀ (20 * (N - i) + 11)) g f V := by
  obtain ⟨h127, a, r, c, d, si, rfl⟩ := h
  have := g₀.rsp.isLt
  have e6 := s_6 _ hF.lo
  dsimp only [CallK]
  refine ⟨hF.w6, by omega, hTt _ _ rfl (keep_tt hF.lo hK _), ?_⟩
  rintro g' V' ⟨rfl, a', c', d', si', di', rfl, ha⟩ fl
  simp only [set4, BitVec.sub_add_cancel] at ha ⊢
  rw [sw_64_32] at ha
  exact x45 (by omega) (keep_st hF.lo hK _) hP h127 ha rfl

/-- The second call of `towupper`, of `q`'s character. -/
theorem vc_107 {Tt : Gprs → (Addr → Byte) → Prop} (hF : Fr F Wl g₀.rsp) (hTt : TtOk g₀ V₀ Tt)
    (hK : Keep g₀ V₀ V) (hP : Pre U g₀ V₀ i) (h : I107 U g₀ V₀ i g) :
    CallK Wl sen_at 112 Tt (Rt U) (Nx U N g₀ V₀ (20 * (N - i) + 6)) g f V := by
  obtain ⟨h127, a, r, ⟨c, d, si, rfl⟩, hr⟩ := h
  have := g₀.rsp.isLt
  have e6 := s_6 _ hF.lo
  dsimp only [CallK]
  refine ⟨hF.w6, by omega, hTt _ _ rfl (keep_tt hF.lo hK _), ?_⟩
  rintro g' V' ⟨rfl, a', c', d', si', di', rfl, ha⟩ fl
  simp only [set4, BitVec.sub_add_cancel] at ha ⊢
  rw [sw_64_32] at ha
  exact x112 (by omega) (keep_st hF.lo hK _) hP h127 hr ha rfl

/-! ## The run -/

/-- The cut points' conditions, the calls' from `towupper`'s. -/
def WtC (F : Footprint) (Wl : List Rgn) (Tt : Gprs → (Addr → Byte) → Prop) (U : BitVec 32 → BitVec 32)
    (ℓ : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 40 then CallK Wl sen_at 45 Tt (Rt U) else
  if ℓ = 107 then CallK Wl sen_at 112 Tt (Rt U) else
  Wt ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}

theorem spC {Tt : Gprs → (Addr → Byte) → Prop} {tcode : List Byte} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L sen_at sen) (hinT : CodeIn L tup_at tcode) (hlT : 0 < tcode.length)
    (hT : FnK prof F Wl L s₀ o tup_at Tt (Rt U)) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o sen_at ℓ (WtC F Wl Tt U ℓ) := by
  by_cases e40 : ℓ = 40
  · subst e40
    exact SpAt.callK c hin (lt_len (by decide)) (cl40 _) hinT hlT tg40 hT
  by_cases e107 : ℓ = 107
  · subst e107
    exact SpAt.callK c hin (lt_len (by decide)) (cl107 _) hinT hlT tg107 hT
  have e : WtC F Wl Tt U ℓ = Wt ℓ F Wl := by simp only [WtC, e40, e107, ↓reduceIte]
  rw [e]
  exact (spAll prof ℓ).at c hin

theorem vcAll {Tt : Gprs → (Addr → Byte) → Prop} (hF : Fr F Wl g₀.rsp) (hN : c1 g₀ V₀ N = 0)
    (hw : ∀ k, Pre U g₀ V₀ k → ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add g₀.rsi (4 * k)) j))
    (hd : ∀ k, Pre U g₀ V₀ k → Ok g₀.rsp (Addr.add g₀.rdi (4 * k)) ∧ Ok g₀.rsp (Addr.add g₀.rsi (4 * k)))
    (hTt : TtOk g₀ V₀ Tt) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv U N g₀ V₀ ℓ n g V) : WtC F Wl Tt U ℓ (Nx U N g₀ V₀ n) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hK, ⟨rfl, rfl, h⟩ | ⟨i, hP, ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩⟩⟩
  · exact vc_0 hF
  · exact vc_144 hF hK h
  · exact vc_62 hF hw hd hK hP h
  · exact vc_40 (f := f) hF hTt hK hP h
  · exact vc_45 hK hP h
  · exact vc_48 hK hP h
  · exact vc_87 hK hP h
  · exact vc_95 hK hP h
  · exact vc_107 (f := f) hF hTt hK hP h
  · exact vc_112 hK hP h
  · exact vc_53 hK hP h
  · exact vc_58 hF hN hK hP h

variable {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- `StringsAreEqualNoCase (p, q)` from its entry to the return address, `towupper` (`U`) a hypothesis: `rax` 1
if the strings are equal through `Up` up to `p`'s 0 (at `N`), else 0; `rcx`, `rdx`, `rsi`, `rdi` changed; the bytes
outside the 48 below the return address as they were. -/
theorem sen_ok {Tt : Gprs → (Addr → Byte) → Prop} {tcode : List Byte} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L sen_at sen) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = sen_at) (hF : Fr F Wl X.cpu.gpr.rsp) (hN : c1 X.cpu.gpr V N = 0)
    (hw : ∀ k, Pre U X.cpu.gpr V k → ∀ j < 4, Foot F.data (Addr.add (Addr.add X.cpu.gpr.rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add X.cpu.gpr.rsi (4 * k)) j))
    (hd : ∀ k, Pre U X.cpu.gpr V k → Ok X.cpu.gpr.rsp (Addr.add X.cpu.gpr.rdi (4 * k)) ∧
      Ok X.cpu.gpr.rsp (Addr.add X.cpu.gpr.rsi (4 * k)))
    (hinT : CodeIn L tup_at tcode) (hlT : 0 < tcode.length) (hT : FnK prof F Wl L s₀ o tup_at Tt (Rt U))
    (hTt : TtOk X.cpu.gpr V Tt)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte) (a : BitVec 64), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      (∀ y : Addr, y.toNat < X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ y.toNat → V' y = V y) →
      (a = 1#64 ∧ Eqs U X.cpu.gpr V ∨ a = 0#64 ∧ ¬ Eqs U X.cpu.gpr V) →
      (∃ c d si di, Z.cpu.gpr = { X.cpu.gpr with
                                                 rax := a, rcx := c, rdx := d, rsi := si,
                                                 rdi := di }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine cfgAt (spC c hin hinT hlT hT) (fun ℓ n g _ V' => Inv U N X.cpu.gpr V ℓ n g V')
    (fun j g _ V' => Fin U X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hF hN hw hd hTt ℓ n g f V' h) ?_
    (20 * N + 20) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨hK', a, c', d', si, di, rfl, hres⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hra' : rdq(V', Y.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [hsY, keep_ra hF.lo hF.hi hK']
    exact hra
  have hres' : a = 1#64 ∧ Eqs U X.cpu.gpr V ∨ a = 0#64 ∧ ¬ Eqs U X.cpu.gpr V := by
    rcases hres with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  have hj : j = 141 ∨ j = 154 := by
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨hjl, hdj⟩ := ret_at prof.feat hj
  refine c.s_ret hKY hAY hin hjl hrY hdj (by rw [hsY]; exact hF.d0) hin₂ h₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' a hKZ hAZ hrZ (keep_out hF.lo hK') hres' ⟨c', d', si, di, by rw [hgZ, hsY, hgY]⟩

end FV7z.Sen
