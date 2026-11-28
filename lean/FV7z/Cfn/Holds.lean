import FV7z.Cfn.Cuts
import FV7z.Sen.Holds
/-!
# `CompareFileNames` (PLAN.md §M, M1)

7-Zip 26.06's `CompareFileNames (const wchar_t *s1, const wchar_t *s2)` at `0x4522b0` in `7zzs`
(`CPP/Common/Wildcard.cpp`; `objdump -d`): the 32-bit characters `c1`, `c2` of `p` = `rdi` and `q` = `rsi`, up to
the first index `n` where they do not go on (`Go`: `c1` not 0, and equal, or `c2` not 0 and equal through `Mp`);
the result (`Res`) 0 for equal characters (both 0), -1 for `c1` 0, 1 for `c2` 0, else the signed order of `Mp c2`
and `Mp c1` (`Ans`). `Mp` maps `'/'` to 0, and with the byte `g_CaseSensitive` (at `0x792180`) 0 (`Ci`) upper-cases
as `Sen.Up` (7-Zip's `MyCharUpper`: `c - 32` for `a`..`z`, `c` up to 127, `towupper` above). `towupper` (glibc,
`0x669660`, the calls at 200, 233, 356) is the hypothesis `FnK` with `Sen.Rt` (`StringsAreEqualNoCase`'s).

Cut points: the entry (0); the case-sensitive loop's head (34, the characters `i` next) and its compare (86); the
case-insensitive loop's head (125), its upper-casing of `c1` (175, the call 200, 205), of `c2` (208, the call 233,
238), its compare (241), the `c2 = '/'` way (328, the call 356, 361); `return 1` (97), `return -1` (400), the exit
(103); the `ret` at 116. The loop that runs is fixed by `ci` = `Ci V₀` (`ci = false` in the states of the first, `true`
in those of the second). The measure 20 (`N` - `i`) + a rank, `N` the index of a 0 of `p`. The bytes: as after the
four `push`es (`Vp`) but for the return address's slot of the calls (`Keep`; the `sub rsp, 8` slot is not written).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sen (c1 c2)
namespace FV7z.Cfn

/-! ## The `ret` and the calls -/

theorem wr116 : Sen.pret <+: cfn.drop 116 := by decide +kernel
theorem ret_at (feat : Features) : 116 < cfn.length ∧ Dec feat cfn 116 (FV7z.mk .ret 64 [] 1) :=
  ⟨lt_len (by decide), Dec.shift (j := 116) (k := 0) (Sen.pret_0 feat) wr116 (Nat.zero_le _)⟩

def pc1 : List Byte := [0xe8, 0xe3, 0x72, 0x21, 0x00]
def pc2 : List Byte := [0xe8, 0xc2, 0x72, 0x21, 0x00]
def pc3 : List Byte := [0xe8, 0x47, 0x72, 0x21, 0x00]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 2192099] 5) := by dec_rfl
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 2192066] 5) := by dec_rfl
theorem pc3_0 : ∀ feat, Dec feat pc3 0 (FV7z.mk .call 64 [.rel 2191943] 5) := by dec_rfl
theorem wc200 : pc1 <+: cfn.drop 200 := by decide +kernel
theorem wc233 : pc2 <+: cfn.drop 233 := by decide +kernel
theorem wc356 : pc3 <+: cfn.drop 356 := by decide +kernel
theorem cl200 (feat : Features) : Dec feat cfn 200 (FV7z.mk .call 64 [.rel 2192099] 5) :=
  Dec.shift (j := 200) (k := 0) (pc1_0 feat) wc200 (Nat.zero_le _)
theorem cl233 (feat : Features) : Dec feat cfn 233 (FV7z.mk .call 64 [.rel 2192066] 5) :=
  Dec.shift (j := 233) (k := 0) (pc2_0 feat) wc233 (Nat.zero_le _)
theorem cl356 (feat : Features) : Dec feat cfn 356 (FV7z.mk .call 64 [.rel 2191943] 5) :=
  Dec.shift (j := 356) (k := 0) (pc3_0 feat) wc356 (Nat.zero_le _)
theorem tg200 : Addr.add cfn_at (200 + 5) + BitVec.ofNat 64 2192099 = Sen.tup_at := by decide
theorem tg233 : Addr.add cfn_at (233 + 5) + BitVec.ofNat 64 2192066 = Sen.tup_at := by decide
theorem tg356 : Addr.add cfn_at (356 + 5) + BitVec.ofNat 64 2191943 = Sen.tup_at := by decide

/-! ## Arithmetic -/

/-- `jl` after `cmp x, y` (32 bits): signed less. -/
theorem subF_l32 (f : Rflags) (x y : BitVec 32) : (subF f x y).cond 12 = decide (x.toInt < y.toInt) := by
  by_cases h : x = y
  · subst h
    have e : (subF f x x).cond 12 = ((subF f x x).sf != (subF f x x).of) := rfl
    rw [e, subF_sf, subF_of, overflowSub, BitVec.sub_self]
    simp
  · have e : (subF f x y).cond 12 = (subF f x y).cond 14 := by
      have hz : (subF f x y).zf = false := by rw [subF_zf]; exact decide_eq_false h
      simp only [Rflags.cond, hz, Bool.false_or]
    rw [e, Sen.subF_le32]
    have hne : x.toInt ≠ y.toInt := fun e => h (BitVec.eq_of_toInt_eq e)
    by_cases h2 : x.toInt < y.toInt
    · rw [decide_eq_true h2, decide_eq_true (Int.le_of_lt h2)]
    · rw [decide_eq_false h2, decide_eq_false (by omega)]

/-- `jge` after `cmp x, y` (32 bits): signed not less. -/
theorem subF_ge32 (f : Rflags) (x y : BitVec 32) : (subF f x y).cond 13 = decide (y.toInt ≤ x.toInt) := by
  have e : (subF f x y).cond 13 = !((subF f x y).cond 12) := by simp only [Rflags.cond, bne, Bool.not_not]
  rw [e, subF_l32]
  by_cases h : x.toInt < y.toInt
  · rw [decide_eq_true h, decide_eq_false (Int.not_le.mpr h)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (Int.not_lt.mp h)]
    rfl

theorem eq_of_nlt {a b : BitVec 32} (h1 : ¬ a.toInt < b.toInt) (h2 : ¬ b.toInt < a.toInt) : a = b :=
  BitVec.eq_of_toInt_eq (by omega)

/-- `a`..`z` upper-cased: above 0. -/
theorem lo_pos {x : BitVec 32} (h1 : ¬ x.toInt ≤ 96) (h2 : x.toInt ≤ 122) :
    (0#32 : BitVec 32).toInt < (x - 32#32).toInt := by
  have hx : x.toNat < 4294967296 := x.isLt
  have e1 := BitVec.toInt_eq_toNat_cond x
  have e2 := BitVec.toInt_eq_toNat_cond (x - 32#32)
  have hs : (x - 32#32).toNat = (4294967264 + x.toNat) % 4294967296 := by bv_omega
  have e0 : (0#32 : BitVec 32).toInt = 0 := by decide
  simp only [Nat.reducePow] at e1 e2
  rw [hs] at e2
  rw [e0]
  split at e1 <;> split at e2 <;> omega

theorem s_6c (s : Addr) (h : 48 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8#64 - 8).toNat = s.toNat - 48 := by bv_omega

theorem e79 : (7938432#64 : Addr).toNat = 7938432 := by decide

theorem nope {P : Prop} {x y : BitVec 32} (hne : ¬ x = y) (h1 : x = 47#32) (h2 : y = 47#32) : P :=
  absurd (h1.trans h2.symm) hne

theorem hy0_47 {y : BitVec 32} (h : y = 47#32) : ¬ y = 0#32 := by
  rw [h]
  decide

/-! ## The specification -/

/-- `g_CaseSensitive` 0: the case-insensitive loop. -/
def Ci (V₀ : Addr → Byte) : Bool := decide (V₀ 7938432#64 = 0#8)

/-- A character as compared: `'/'` as 0, upper-cased (`Sen.Up`, `U` = `towupper`) if `ci`. -/
def Mp (ci : Bool) (U : BitVec 32 → BitVec 32) (c : BitVec 32) : BitVec 32 :=
  if c = 47#32 then 0#32 else if ci = true then Sen.Up U c else c

/-- The characters `x` of `p` and `y` of `q`: the loop goes on. -/
def Go (ci : Bool) (U : BitVec 32 → BitVec 32) (x y : BitVec 32) : Prop :=
  ¬ x = 0#32 ∧ (x = y ∨ (¬ y = 0#32 ∧ Mp ci U x = Mp ci U y))

/-- The result at characters that do not go on. -/
def Res (ci : Bool) (U : BitVec 32 → BitVec 32) (x y : BitVec 32) : BitVec 32 :=
  if x = y then 0#32 else if x = 0#32 then 4294967295#32 else if y = 0#32 then 1#32 else
    if (Mp ci U y).toInt < (Mp ci U x).toInt then 1#32 else 4294967295#32

/-- The first `i` characters go on. -/
def Pre (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) : Prop :=
  ∀ k < i, Go ci U (c1 g₀ V₀ k) (c2 g₀ V₀ k)

/-- `r` the result: that at the first characters that do not go on. -/
def Ans (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (r : BitVec 32) : Prop :=
  ∃ n, Pre ci U g₀ V₀ n ∧ ¬ Go ci U (c1 g₀ V₀ n) (c2 g₀ V₀ n) ∧ r = Res ci U (c1 g₀ V₀ n) (c2 g₀ V₀ n)

variable {U : BitVec 32 → BitVec 32} {N : Nat} {g₀ : Gprs} {V₀ : Addr → Byte} {ci : Bool} {i : Nat}

theorem ci_t {b : Byte} (hb : b = V₀ 7938432#64) (h : b = 0#8) : Ci V₀ = true := by
  rw [Ci, ← hb]
  exact decide_eq_true h
theorem ci_f {b : Byte} (hb : b = V₀ 7938432#64) (h : ¬ b = 0#8) : Ci V₀ = false := by
  rw [Ci, ← hb]
  exact decide_eq_false h

theorem mp_47 {c : BitVec 32} (h : c = 47#32) : Mp ci U c = 0#32 := by rw [Mp, if_pos h]
theorem mp_cs {c : BitVec 32} (h : ¬ c = 47#32) : Mp false U c = c := by
  simp only [Mp, if_neg h, Bool.false_eq_true, ↓reduceIte]
theorem mp_ci {c : BitVec 32} (h : ¬ c = 47#32) : Mp true U c = Sen.Up U c := by
  simp only [Mp, if_neg h, ↓reduceIte]

/-- The `cmove` of `'/'` to 0. -/
theorem cmv {y : BitVec 32} : (if y = 47#32 then 0#32 else y) = Mp false U y := by
  by_cases h : y = 47#32
  · rw [if_pos h, mp_47 h]
  · rw [if_neg h, mp_cs h]

theorem hp_47 {x : BitVec 32} (h : x = 47#32) : BitVec.setWidth 32 (0#64) = Mp ci U x := by
  rw [mp_47 h]
  decide
theorem hp_id {x : BitVec 32} (h : ¬ x = 47#32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = Mp false U x := by
  rw [sw_64_32, mp_cs h]
theorem hp_le {x : BitVec 32} (h47 : ¬ x = 47#32) (h : x.toInt ≤ 96) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x) = Mp true U x := by
  rw [sw_64_32, mp_ci h47, Sen.up_le h]
theorem hp_lo {x : BitVec 32} (h47 : ¬ x = 47#32) (h1 : ¬ x.toInt ≤ 96) (h2 : x.toInt ≤ 122) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (x - 32#32)) = Mp true U x := by
  rw [sw_64_32, mp_ci h47, Sen.up_lo h1 h2]
theorem hp_mid {x : BitVec 32} (h47 : ¬ x = 47#32) (h2 : ¬ x.toInt ≤ 122) (h3 : x.toInt ≤ 127) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x) = Mp true U x := by
  rw [sw_64_32, mp_ci h47, Sen.up_mid h2 h3]
theorem hp_hi {x : BitVec 32} {a : BitVec 64} (h47 : ¬ x = 47#32) (h3 : ¬ x.toInt ≤ 127)
    (ha : BitVec.setWidth 32 a = U x) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 a)) = Mp true U x := by
  rw [sw_64_32, ha, mp_ci h47, Sen.up_hi h3]

section G
variable {x y : BitVec 32}
theorem go_eq (h0 : ¬ x = 0#32) (h : x = y) : Go ci U x y := ⟨h0, Or.inl h⟩
theorem go_mp (h0 : ¬ x = 0#32) (hy : ¬ y = 0#32) (h : Mp ci U x = Mp ci U y) : Go ci U x y :=
  ⟨h0, Or.inr ⟨hy, h⟩⟩
theorem ngo_z (h0 : x = 0#32) : ¬ Go ci U x y := fun g => g.1 h0
theorem ngo_y (hne : ¬ x = y) (hy : y = 0#32) : ¬ Go ci U x y := fun g => g.2.elim hne fun h => h.1 hy
theorem ngo_mp (hne : ¬ x = y) (h : ¬ Mp ci U x = Mp ci U y) : ¬ Go ci U x y :=
  fun g => g.2.elim hne fun h' => h h'.2
end G

theorem pre0 : Pre ci U g₀ V₀ 0 := fun k hk => absurd hk (Nat.not_lt_zero k)

theorem pre_le (hP : Pre ci U g₀ V₀ i) (hN : c1 g₀ V₀ N = 0#32) : i ≤ N :=
  Nat.le_of_not_lt fun h => (hP N h).1 hN

theorem pre_succ (hP : Pre ci U g₀ V₀ i) (hg : Go ci U (c1 g₀ V₀ i) (c2 g₀ V₀ i)) : Pre ci U g₀ V₀ (i + 1) :=
  fun k hk => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | rfl
    · exact hP k h
    · exact hg

theorem ans_z (hP : Pre ci U g₀ V₀ i) (h : c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : c1 g₀ V₀ i = 0#32) :
    Ans ci U g₀ V₀ (c1 g₀ V₀ i) :=
  ⟨i, hP, ngo_z h0, by rw [Res, if_pos h]; exact h0⟩

theorem ans_m1a (hP : Pre ci U g₀ V₀ i) (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : c1 g₀ V₀ i = 0#32) :
    Ans ci U g₀ V₀ 4294967295#32 :=
  ⟨i, hP, ngo_z h0, by rw [Res, if_neg hne, if_pos h0]⟩

theorem ans_1a (hP : Pre ci U g₀ V₀ i) (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32)
    (hy : c2 g₀ V₀ i = 0#32) : Ans ci U g₀ V₀ 1#32 :=
  ⟨i, hP, ngo_y hne hy, by rw [Res, if_neg hne, if_neg h0, if_pos hy]⟩

theorem ans_m1b (hP : Pre ci U g₀ V₀ i) (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32)
    (hy0 : ¬ c2 g₀ V₀ i = 0#32) (hlt : (Mp ci U (c1 g₀ V₀ i)).toInt < (Mp ci U (c2 g₀ V₀ i)).toInt) :
    Ans ci U g₀ V₀ 4294967295#32 := by
  have h' : ¬ (Mp ci U (c2 g₀ V₀ i)).toInt < (Mp ci U (c1 g₀ V₀ i)).toInt := by omega
  exact ⟨i, hP, ngo_mp hne (fun e => by rw [e] at hlt; exact Int.lt_irrefl _ hlt),
    by rw [Res, if_neg hne, if_neg h0, if_neg hy0, if_neg h']⟩

theorem ans_1b (hP : Pre ci U g₀ V₀ i) (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32)
    (hy0 : ¬ c2 g₀ V₀ i = 0#32) (hlt : (Mp ci U (c2 g₀ V₀ i)).toInt < (Mp ci U (c1 g₀ V₀ i)).toInt) :
    Ans ci U g₀ V₀ 1#32 :=
  ⟨i, hP, ngo_mp hne (fun e => by rw [e] at hlt; exact Int.lt_irrefl _ hlt),
    by rw [Res, if_neg hne, if_neg h0, if_neg hy0, if_pos hlt]⟩

/-- `c2` `'/'`, `c1` in `a`..`z`: `return 1` without `towupper`. -/
theorem ans_1s (hP : Pre true U g₀ V₀ i) (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32)
    (h47 : ¬ c1 g₀ V₀ i = 47#32) (hy : c2 g₀ V₀ i = 47#32) (h1 : ¬ (c1 g₀ V₀ i).toInt ≤ 96)
    (h2 : (c1 g₀ V₀ i).toInt ≤ 122) : Ans true U g₀ V₀ 1#32 :=
  ans_1b hP hne h0 (hy0_47 hy) (by rw [mp_47 hy, mp_ci h47, Sen.up_lo h1 h2]; exact lo_pos h1 h2)

/-! ## The bytes -/

/-- After the four `push`es. -/
def Vp (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r13 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.r12 8))
    (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbp 8)) (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8)

/-- As after the `push`es but for the slot of the calls' return address. -/
def Keep (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  ∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat - 40 ≤ y.toNat → V y = Vp g₀ V₀ y

/-- The frame below the return address at `s`: the `push`es' and the calls' slots, those of the `pop`s and the
`ret`; the byte `g_CaseSensitive`, apart from the `push`es. -/
structure Fr (F : Footprint) (Wl : List Rgn) (s : Addr) : Prop where
  lo : 48 ≤ s.toNat
  hi : s.toNat + 8 ≤ 2 ^ 64
  w1 : ∀ i < 8, Foot Wl (Addr.add (s - 8) i)
  w2 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8) i)
  w3 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8) i)
  w4 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8) i)
  w6 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8 - 8#64 - 8) i)
  d0 : ∀ i < 8, Foot F.data (Addr.add s i)
  d1 : ∀ i < 8, Foot F.data (Addr.add (s - 8) i)
  d2 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8) i)
  d3 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8) i)
  d4 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8 - 8) i)
  fd : ∀ i < 1, Foot F.data (Addr.add 7938432#64 i)
  fo : 7938432 < s.toNat - 32 ∨ s.toNat ≤ 7938432

theorem Vp_out (hlo : 48 ≤ g₀.rsp.toNat) (y : Addr)
    (h : y.toNat < g₀.rsp.toNat - 32 ∨ g₀.rsp.toNat ≤ y.toNat) : Vp g₀ V₀ y = V₀ y := by
  have := g₀.rsp.isLt
  have e1 := Sen.s_1 _ hlo
  have e2 := Sen.s_2 _ hlo
  have e3 := Sen.s_3 _ hlo
  have e4 := Sen.s_4 _ hlo
  dsimp only [Vp]
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- A character apart from the frame reads as at the entry. -/
theorem keep_rd {V : Addr → Byte} {x : Addr} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V)
    (hx : Sen.Ok g₀.rsp x) : rdd(V, x) = rdd(V₀, x) := by
  obtain ⟨hx1, hx2⟩ := hx
  apply congrArg (ofBytesLE 32)
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have := toNat_add_of_fits hj hx1
  rw [hK (x.add j) (by omega), Vp_out hlo (x.add j) (by omega)]

/-- The store of a call's return address. -/
theorem keep_st {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V) (v : BitVec 64) :
    Keep g₀ V₀ (Vst V (g₀.rsp - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE v 8)) := fun y hy => by
  have := g₀.rsp.isLt
  have e6 := s_6c _ hlo
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega)]
  exact hK y hy

/-- Outside the frame, the bytes at a call are those at the entry. -/
theorem keep_tt {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V) (v : BitVec 64) :
    ∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat ≤ y.toNat →
      Vst V (g₀.rsp - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE v 8) y = V₀ y := fun y hy => by
  rw [keep_st hlo hK v y (by omega), Vp_out hlo y (by omega)]

theorem keep_out {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hK : Keep g₀ V₀ V) :
    ∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat ≤ y.toNat → V y = V₀ y := fun y hy => by
  rw [hK y (by omega), Vp_out hlo y (by omega)]

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
    rdq(V, g₀.rsp - 8) = g₀.r13 ∧ rdq(V, g₀.rsp - 8 - 8) = g₀.r12 ∧ rdq(V, g₀.rsp - 8 - 8 - 8) = g₀.rbp ∧
      rdq(V, g₀.rsp - 8 - 8 - 8 - 8) = g₀.rbx := by
  have e1 := Sen.s_1 _ hlo
  have e2 := Sen.s_2 _ hlo
  have e3 := Sen.s_3 _ hlo
  have e4 := Sen.s_4 _ hlo
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [keep_q hK (x := g₀.rsp - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [Sen.rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      Sen.rq_out _ (g₀.rsp - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      Sen.rq_out _ (g₀.rsp - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      Sen.rq_self _ (g₀.rsp - 8) _ (by omega)]
  · rw [keep_q hK (x := g₀.rsp - 8 - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [Sen.rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      Sen.rq_out _ (g₀.rsp - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      Sen.rq_self _ (g₀.rsp - 8 - 8) _ (by omega)]
  · rw [keep_q hK (x := g₀.rsp - 8 - 8 - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [Sen.rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      Sen.rq_self _ (g₀.rsp - 8 - 8 - 8) _ (by omega)]
  · rw [keep_q hK (x := g₀.rsp - 8 - 8 - 8 - 8) (by omega) (by omega)]
    dsimp only [Vp]
    rw [Sen.rq_self _ (g₀.rsp - 8 - 8 - 8 - 8) _ (by omega)]

/-- The return address. -/
theorem keep_ra {V : Addr → Byte} (hlo : 48 ≤ g₀.rsp.toNat) (hhi : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hK : Keep g₀ V₀ V) : rdq(V, g₀.rsp) = rdq(V₀, g₀.rsp) := by
  apply congrArg (ofBytesLE 64)
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have := toNat_add_of_fits hj hhi
  exact keep_out hlo hK _ (Or.inr (by omega))

/-- `towupper`'s condition at the calls: the return address 48 bytes below that at the entry, the bytes outside
the frame those at the entry. -/
def TtOk (g₀ : Gprs) (V₀ : Addr → Byte) (Tt : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ g W, g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8#64 - 8 →
    (∀ y : Addr, y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat ≤ y.toNat → W y = V₀ y) → Tt g W

/-! ## The invariant -/

/-- The registers in the loops: the strings' pointers at the characters `j`, `r12`, `r13` the characters. -/
def Sh (g₀ : Gprs) (j : Nat) (a c d si di p q : BitVec 64) (g : Gprs) : Prop :=
  g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * j),
    rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * j), rsi := si, rdi := di, r12 := p, r13 := q }

def I34 (ci : Bool) (g₀ : Gprs) (i : Nat) (g : Gprs) : Prop :=
  ci = false ∧ ∃ a c si di p q, Sh g₀ i a c 0#64 si di p q g
def I86 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = false ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ∃ a c si di p q, Sh g₀ (i + 1) a c 0#64 si di p q g ∧ BitVec.setWidth 32 p = Mp false U (c1 g₀ V₀ i) ∧
      BitVec.setWidth 32 a = Mp false U (c2 g₀ V₀ i)
def I125 (ci : Bool) (g₀ : Gprs) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ∃ a c d si di p q, Sh g₀ i a c d si di p q g
def I175 (ci : Bool) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ¬ c1 g₀ V₀ i = 47#32 ∧ ¬ c2 g₀ V₀ i = 47#32 ∧ ∃ a c d si di,
      Sh g₀ (i + 1) a c d si di (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c2 g₀ V₀ i)) g
def I200 (ci : Bool) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ¬ c1 g₀ V₀ i = 47#32 ∧ ¬ c2 g₀ V₀ i = 47#32 ∧ 127 < (c1 g₀ V₀ i).toInt ∧ ∃ a c d si,
      Sh g₀ (i + 1) a c d si (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c1 g₀ V₀ i))
        (BitVec.setWidth 64 (c2 g₀ V₀ i)) g
def I205 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ¬ c1 g₀ V₀ i = 47#32 ∧ ¬ c2 g₀ V₀ i = 47#32 ∧ 127 < (c1 g₀ V₀ i).toInt ∧ ∃ a c d si di,
      Sh g₀ (i + 1) a c d si di (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c2 g₀ V₀ i)) g ∧
      BitVec.setWidth 32 a = U (c1 g₀ V₀ i)
def I208 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ¬ c2 g₀ V₀ i = 47#32 ∧ ∃ a c d si di p, Sh g₀ (i + 1) a c d si di p (BitVec.setWidth 64 (c2 g₀ V₀ i)) g ∧
      BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i)
def I233 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ¬ c2 g₀ V₀ i = 47#32 ∧ 127 < (c2 g₀ V₀ i).toInt ∧ ∃ a c d si p,
      Sh g₀ (i + 1) a c d si (BitVec.setWidth 64 (c2 g₀ V₀ i)) p (BitVec.setWidth 64 (c2 g₀ V₀ i)) g ∧
      BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i)
def I238 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ¬ c2 g₀ V₀ i = 47#32 ∧ 127 < (c2 g₀ V₀ i).toInt ∧ ∃ a c d si di p,
      Sh g₀ (i + 1) a c d si di p (BitVec.setWidth 64 (c2 g₀ V₀ i)) g ∧
      BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i) ∧ BitVec.setWidth 32 a = U (c2 g₀ V₀ i)
def I241 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c2 g₀ V₀ i = 0#32 ∧
    ∃ a c d si di p q, Sh g₀ (i + 1) a c d si di p q g ∧ BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i) ∧
      BitVec.setWidth 32 q = Mp true U (c2 g₀ V₀ i)
def I328 (ci : Bool) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c1 g₀ V₀ i = 47#32 ∧ c2 g₀ V₀ i = 47#32 ∧
    ∃ a c d si di,
      Sh g₀ (i + 1) a c d si di (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c2 g₀ V₀ i)) g
def I356 (ci : Bool) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c1 g₀ V₀ i = 47#32 ∧ c2 g₀ V₀ i = 47#32 ∧
    127 < (c1 g₀ V₀ i).toInt ∧ ∃ a c d si,
      Sh g₀ (i + 1) a c d si (BitVec.setWidth 64 (c1 g₀ V₀ i)) (BitVec.setWidth 64 (c1 g₀ V₀ i)) 0#64 g
def I361 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (g : Gprs) : Prop :=
  ci = true ∧ ¬ c1 g₀ V₀ i = c2 g₀ V₀ i ∧ ¬ c1 g₀ V₀ i = 0#32 ∧ ¬ c1 g₀ V₀ i = 47#32 ∧ c2 g₀ V₀ i = 47#32 ∧
    127 < (c1 g₀ V₀ i).toInt ∧ ∃ a c d si di,
      Sh g₀ (i + 1) a c d si di (BitVec.setWidth 64 (c1 g₀ V₀ i)) 0#64 g ∧ BitVec.setWidth 32 a = U (c1 g₀ V₀ i)
/-- Before `mov r12d, v`: `v` the result. -/
def Ix (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (v : BitVec 32) (g : Gprs) : Prop :=
  Ans ci U g₀ V₀ v ∧ ∃ j a c d si di p q, Sh g₀ j a c d si di p q g
/-- The exit: `r12d` the result. -/
def I103 (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) : Prop :=
  ∃ r, Ans ci U g₀ V₀ r ∧ ∃ j a c d si di q, Sh g₀ j a c d si di (BitVec.setWidth 64 r) q g

/-- The invariant at the cut points, `n` the measure. -/
def Inv (ci : Bool) (U : BitVec 32 → BitVec 32) (N : Nat) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs)
    (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ n = 20 * N + 20 ∧ g = g₀ ∧ V = V₀) ∨
  (Keep g₀ V₀ V ∧ ((ℓ = 97 ∧ n = 3 ∧ Ix ci U g₀ V₀ 1#32 g) ∨
    (ℓ = 400 ∧ n = 3 ∧ Ix ci U g₀ V₀ 4294967295#32 g) ∨
    (ℓ = 103 ∧ n = 2 ∧ I103 ci U g₀ V₀ g) ∨ ∃ i, Pre ci U g₀ V₀ i ∧ (
    (ℓ = 34 ∧ n = 20 * (N - i) + 19 ∧ I34 ci g₀ i g) ∨
    (ℓ = 86 ∧ n = 20 * (N - i) + 18 ∧ I86 ci U g₀ V₀ i g) ∨
    (ℓ = 125 ∧ n = 20 * (N - i) + 19 ∧ I125 ci g₀ i g) ∨
    (ℓ = 175 ∧ n = 20 * (N - i) + 18 ∧ I175 ci g₀ V₀ i g) ∨
    (ℓ = 200 ∧ n = 20 * (N - i) + 17 ∧ I200 ci g₀ V₀ i g) ∨
    (ℓ = 205 ∧ n = 20 * (N - i) + 16 ∧ I205 ci U g₀ V₀ i g) ∨
    (ℓ = 208 ∧ n = 20 * (N - i) + 15 ∧ I208 ci U g₀ V₀ i g) ∨
    (ℓ = 233 ∧ n = 20 * (N - i) + 14 ∧ I233 ci U g₀ V₀ i g) ∨
    (ℓ = 238 ∧ n = 20 * (N - i) + 13 ∧ I238 ci U g₀ V₀ i g) ∨
    (ℓ = 241 ∧ n = 20 * (N - i) + 12 ∧ I241 ci U g₀ V₀ i g) ∨
    (ℓ = 328 ∧ n = 20 * (N - i) + 18 ∧ I328 ci g₀ V₀ i g) ∨
    (ℓ = 356 ∧ n = 20 * (N - i) + 17 ∧ I356 ci g₀ V₀ i g) ∨
    (ℓ = 361 ∧ n = 20 * (N - i) + 16 ∧ I361 ci U g₀ V₀ i g))))

/-- At the `ret`: `eax` the result, the callee-saved registers restored. -/
def Fin (ci : Bool) (U : BitVec 32 → BitVec 32) (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs)
    (V : Addr → Byte) : Prop :=
  Keep g₀ V₀ V ∧ j = 116 ∧ ∃ r c d si di,
    g = { g₀ with rax := BitVec.setWidth 64 r, rcx := c, rdx := d, rsi := si, rdi := di } ∧ Ans ci U g₀ V₀ r

def Nx (ci : Bool) (U : BitVec 32 → BitVec 32) (N : Nat) (g₀ : Gprs) (V₀ : Addr → Byte) (m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv ci U N g₀ V₀ j m' g V) ∨ Fin ci U g₀ V₀ j g V

/-! ## The exits -/

section X
variable {m : Nat} {V : Addr → Byte} {g : Gprs} {fl : Rflags} {a c d si di p q : BitVec 64}

theorem x34z (hm : 20 * N + 19 < m) (hK : Keep g₀ V₀ V) (hci : ci = false)
    (hg : g = { g₀ with rax := a, rdx := 0#64, rbx := g₀.rdi, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64,
      rbp := g₀.rsi }) :
    Nx ci U N g₀ V₀ m 34 g fl V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨0, pre0, Or.inl ⟨rfl, by omega, hci, a, g₀.rcx,
    g₀.rsi, g₀.rdi, g₀.r12, g₀.r13, ?_⟩⟩))⟩⟩
  rw [hg]
  simp only [Sh, Nat.mul_zero, addr_add_zero]

theorem x125z (hm : 20 * N + 19 < m) (hK : Keep g₀ V₀ V) (hci : ci = true)
    (hg : g = { g₀ with rax := a, rbx := g₀.rdi, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := g₀.rsi }) :
    Nx ci U N g₀ V₀ m 125 g fl V := by
  refine Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨0, pre0, Or.inr (Or.inr (Or.inl ⟨rfl, by omega,
    hci, a, g₀.rcx, g₀.rdx, g₀.rsi, g₀.rdi, g₀.r12, g₀.r13, ?_⟩))⟩))⟩⟩
  rw [hg]
  simp only [Sh, Nat.mul_zero, addr_add_zero]

theorem x34s (hN : c1 g₀ V₀ N = 0#32) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = false)
    (hgo : Go ci U (c1 g₀ V₀ i) (c2 g₀ V₀ i)) (hm : 20 * (N - i) ≤ m)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := 0#64, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := p, r13 := q }) :
    Nx ci U N g₀ V₀ m 34 g fl V := by
  have hle := pre_le hP hN
  have hne : i ≠ N := by
    rintro rfl
    exact hgo.1 hN
  exact Or.inl ⟨_, by omega, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i + 1, pre_succ hP hgo, Or.inl ⟨rfl, rfl, hci,
    a, c, si, di, p, q, hg⟩⟩))⟩⟩

theorem x125s (hN : c1 g₀ V₀ N = 0#32) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hgo : Go ci U (c1 g₀ V₀ i) (c2 g₀ V₀ i)) (hm : 20 * (N - i) ≤ m)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := p, r13 := q }) :
    Nx ci U N g₀ V₀ m 125 g fl V := by
  have hle := pre_le hP hN
  have hne : i ≠ N := by
    rintro rfl
    exact hgo.1 hN
  exact Or.inl ⟨_, by omega, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i + 1, pre_succ hP hgo,
    Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hci, a, c, d, si, di, p, q, hg⟩))⟩))⟩⟩

theorem x86 (hm : 20 * (N - i) + 18 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = false)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (hp : BitVec.setWidth 32 p = Mp false U (c1 g₀ V₀ i)) (ha : BitVec.setWidth 32 a = Mp false U (c2 g₀ V₀ i))
    (hg : g = { g₀ with rax := a, rcx := c, rdx := 0#64, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := p, r13 := q }) :
    Nx ci U N g₀ V₀ m 86 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inl ⟨rfl, rfl, hci, hne, h0, hy0, a, c,
    si, di, p, q, hg, hp, ha⟩)⟩))⟩⟩

theorem x175 (hm : 20 * (N - i) + 18 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (h47 : ¬ c1 g₀ V₀ i = 47#32) (hy47 : ¬ c2 g₀ V₀ i = 47#32)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := BitVec.setWidth 64 (c1 g₀ V₀ i), r13 := BitVec.setWidth 64 (c2 g₀ V₀ i) }) :
    Nx ci U N g₀ V₀ m 175 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hci, hne,
    h0, hy0, h47, hy47, a, c, d, si, di, hg⟩)))⟩))⟩⟩

theorem x200 (hm : 20 * (N - i) + 17 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (h47 : ¬ c1 g₀ V₀ i = 47#32) (hy47 : ¬ c2 g₀ V₀ i = 47#32) (h127 : 127 < (c1 g₀ V₀ i).toInt)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si,
      rdi := BitVec.setWidth 64 (c1 g₀ V₀ i), r12 := BitVec.setWidth 64 (c1 g₀ V₀ i),
      r13 := BitVec.setWidth 64 (c2 g₀ V₀ i) }) :
    Nx ci U N g₀ V₀ m 200 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl,
    hci, hne, h0, hy0, h47, hy47, h127, a, c, d, si, hg⟩))))⟩))⟩⟩

theorem x205 (hm : 20 * (N - i) + 16 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (h47 : ¬ c1 g₀ V₀ i = 47#32) (hy47 : ¬ c2 g₀ V₀ i = 47#32) (h127 : 127 < (c1 g₀ V₀ i).toInt)
    (ha : BitVec.setWidth 32 a = U (c1 g₀ V₀ i))
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := BitVec.setWidth 64 (c1 g₀ V₀ i), r13 := BitVec.setWidth 64 (c2 g₀ V₀ i) }) :
    Nx ci U N g₀ V₀ m 205 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, rfl, hci, hne, h0, hy0, h47, hy47, h127, a, c, d, si, di, hg, ha⟩)))))⟩))⟩⟩

theorem x208 (hm : 20 * (N - i) + 15 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (hy47 : ¬ c2 g₀ V₀ i = 47#32) (hp : BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i))
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := p, r13 := BitVec.setWidth 64 (c2 g₀ V₀ i) }) :
    Nx ci U N g₀ V₀ m 208 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, hci, hne, h0, hy0, hy47, a, c, d, si, di, p, hg, hp⟩))))))⟩))⟩⟩

theorem x233 (hm : 20 * (N - i) + 14 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (hy47 : ¬ c2 g₀ V₀ i = 47#32) (h127 : 127 < (c2 g₀ V₀ i).toInt)
    (hp : BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i))
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si,
      rdi := BitVec.setWidth 64 (c2 g₀ V₀ i), r12 := p, r13 := BitVec.setWidth 64 (c2 g₀ V₀ i) }) :
    Nx ci U N g₀ V₀ m 233 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨rfl, rfl, hci, hne, h0, hy0, hy47, h127, a, c, d, si, p, hg, hp⟩)))))))⟩))⟩⟩

theorem x238 (hm : 20 * (N - i) + 13 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (hy47 : ¬ c2 g₀ V₀ i = 47#32) (h127 : 127 < (c2 g₀ V₀ i).toInt)
    (hp : BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i)) (ha : BitVec.setWidth 32 a = U (c2 g₀ V₀ i))
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := p, r13 := BitVec.setWidth 64 (c2 g₀ V₀ i) }) :
    Nx ci U N g₀ V₀ m 238 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hci, hne, h0, hy0, hy47, h127, a, c, d, si, di, p, hg, hp,
    ha⟩))))))))⟩))⟩⟩

theorem x241 (hm : 20 * (N - i) + 12 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (hy0 : ¬ c2 g₀ V₀ i = 0#32)
    (hp : BitVec.setWidth 32 p = Mp true U (c1 g₀ V₀ i)) (hq : BitVec.setWidth 32 q = Mp true U (c2 g₀ V₀ i))
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := p, r13 := q }) :
    Nx ci U N g₀ V₀ m 241 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hci, hne, h0, hy0, a, c, d, si, di, p, q, hg, hp,
    hq⟩)))))))))⟩))⟩⟩

theorem x328 (hm : 20 * (N - i) + 18 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (h47 : ¬ c1 g₀ V₀ i = 47#32)
    (hy : c2 g₀ V₀ i = 47#32)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := BitVec.setWidth 64 (c1 g₀ V₀ i), r13 := BitVec.setWidth 64 (c2 g₀ V₀ i) }) :
    Nx ci U N g₀ V₀ m 328 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hci, hne, h0, h47, hy, a, c, d, si, di,
    hg⟩))))))))))⟩))⟩⟩

theorem x356 (hm : 20 * (N - i) + 17 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (h47 : ¬ c1 g₀ V₀ i = 47#32)
    (hy : c2 g₀ V₀ i = 47#32) (h127 : 127 < (c1 g₀ V₀ i).toInt)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si,
      rdi := BitVec.setWidth 64 (c1 g₀ V₀ i), r12 := BitVec.setWidth 64 (c1 g₀ V₀ i), r13 := 0#64 }) :
    Nx ci U N g₀ V₀ m 356 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hci, hne, h0, h47, hy, h127, a, c, d, si,
    hg⟩)))))))))))⟩))⟩⟩

theorem x361 (hm : 20 * (N - i) + 16 < m) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (hci : ci = true)
    (hne : ¬ c1 g₀ V₀ i = c2 g₀ V₀ i) (h0 : ¬ c1 g₀ V₀ i = 0#32) (h47 : ¬ c1 g₀ V₀ i = 47#32)
    (hy : c2 g₀ V₀ i = 47#32) (h127 : 127 < (c1 g₀ V₀ i).toInt) (ha : BitVec.setWidth 32 a = U (c1 g₀ V₀ i))
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * (i + 1)),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * (i + 1)), rsi := si, rdi := di,
      r12 := BitVec.setWidth 64 (c1 g₀ V₀ i), r13 := 0#64 }) :
    Nx ci U N g₀ V₀ m 361 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inr ⟨i, hP, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hci, hne, h0, h47, hy, h127, a, c, d, si, di,
    hg, ha⟩)))))))))))⟩))⟩⟩

theorem x97 {j : Nat} (hm : 3 < m) (hK : Keep g₀ V₀ V) (hA : Ans ci U g₀ V₀ 1#32)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * j),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * j), rsi := si, rdi := di,
      r12 := p, r13 := q }) :
    Nx ci U N g₀ V₀ m 97 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inl ⟨rfl, rfl, hA, j, a, c, d, si, di, p, q, hg⟩⟩⟩

theorem x400 {j : Nat} (hm : 3 < m) (hK : Keep g₀ V₀ V) (hA : Ans ci U g₀ V₀ 4294967295#32)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * j),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * j), rsi := si, rdi := di,
      r12 := p, r13 := q }) :
    Nx ci U N g₀ V₀ m 400 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inl ⟨rfl, rfl, hA, j, a, c, d, si, di, p, q, hg⟩)⟩⟩

theorem x103 {j : Nat} (hm : 2 < m) (hK : Keep g₀ V₀ V) (r : BitVec 32) (hA : Ans ci U g₀ V₀ r)
    (hp : p = BitVec.setWidth 64 r)
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rbx := Addr.add g₀.rdi (4 * j),
      rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8#64, rbp := Addr.add g₀.rsi (4 * j), rsi := si, rdi := di,
      r12 := p, r13 := q }) :
    Nx ci U N g₀ V₀ m 103 g fl V := by
  subst hp
  exact Or.inl ⟨_, hm, Or.inr ⟨hK, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, r, hA, j, a, c, d, si, di, q, hg⟩))⟩⟩

theorem xF {r : BitVec 32} (hK : Keep g₀ V₀ V) (hA : Ans ci U g₀ V₀ r)
    (hg : g = { g₀ with rax := BitVec.setWidth 64 r, rcx := c, rdx := d, rsi := si, rdi := di }) :
    Nx ci U N g₀ V₀ m 116 g fl V :=
  Or.inr ⟨hK, rfl, r, c, d, si, di, hg, hA⟩

end X

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn} {g : Gprs} {f : Rflags} {V : Addr → Byte}

set_option maxHeartbeats 1000000 in
/-- The entry: the four `push`es, the flag; the loop's head with the characters 0 next. -/
theorem vc_0 (hF : Fr F Wl g₀.rsp) (hci0 : ci = Ci V₀) :
    W_0 F Wl (Nx ci U N g₀ V₀ (20 * N + 20)) g₀ f V₀ := by
  have hK : Keep g₀ V₀ (Vp g₀ V₀) := fun _ _ => rfl
  have hb : Vp g₀ V₀ 7938432#64 = V₀ 7938432#64 := Vp_out hF.lo _ (by rw [e79]; exact hF.fo)
  obtain ⟨-, -, w1, w2, w3, w4, -, -, -, -, -, -, fd, -⟩ := hF
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at w1 w2 w3 w4
  wpx [W_0, W_32, o0, o1, Op.cmpmi, Tun.rd1, BitVec.xor_self, BitVec.setWidth_zero, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible exact w1
    | with_reducible exact w2
    | with_reducible exact w3
    | with_reducible exact w4
    | with_reducible exact fd
    | apply And.intro
    | intro)
  all_goals first
    | exact x125z (by omega) hK (hci0.trans (ci_t hb (by assumption))) rfl
    | exact x34z (by omega) hK (hci0.trans (ci_f hb (by assumption))) rfl

set_option maxHeartbeats 2000000 in
/-- The case-sensitive loop's head: the loads; equal, 0s, `'/'`. -/
theorem vc_34 (hF : Fr F Wl g₀.rsp) (hN : c1 g₀ V₀ N = 0#32)
    (hw : ∀ k, Pre ci U g₀ V₀ k → ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add g₀.rsi (4 * k)) j))
    (hd : ∀ k, Pre ci U g₀ V₀ k → Sen.Ok g₀.rsp (Addr.add g₀.rdi (4 * k)) ∧ Sen.Ok g₀.rsp (Addr.add g₀.rsi (4 * k)))
    (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I34 ci g₀ i g) :
    W_34 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 19)) g f V := by
  obtain ⟨rfl, a, c, si, di, p, q, rfl⟩ := h
  have hr1 : rdd(V, Addr.add g₀.rdi (4 * i)) = c1 g₀ V₀ i := keep_rd hF.lo hK (hd i hP).1
  have hr2 : rdd(V, Addr.add g₀.rsi (4 * i)) = c2 g₀ V₀ i := keep_rd hF.lo hK (hd i hP).2
  have f1 : ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * i)) j) := fun j hj => (hw i hP j hj).1
  have f2 : ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rsi (4 * i)) j) := fun j hj => (hw i hP j hj).2
  wpx [W_34, W_264, W_273, W_57, W_66, W_70, W_304, W_316, W_80, o2, o3, o4, o5, o6, o25, hr1, hr2, Sen.ad4,
    BitVec.and_self, BitVec.xor_self, BitVec.setWidth_zero, beq_iff_eq, beq_eq_false_iff_ne, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible exact f1
    | with_reducible exact f2
    | apply And.intro
    | intro)
  all_goals first
    | exact x34s hN hK hP rfl (go_eq (by assumption) (by assumption)) (by omega) rfl
    | exact x103 (by omega) hK _ (ans_z hP (by assumption) (by assumption)) rfl rfl
    | exact x400 (by omega) hK (ans_m1a hP (by assumption) (by assumption)) rfl
    | exact x97 (by omega) hK (ans_1a hP (by assumption) (by assumption) (by assumption)) rfl
    | exact x86 (by omega) hK hP rfl (by assumption) (by assumption) (by assumption) (hp_47 (by assumption))
        (hp_id (by assumption)) rfl
    | exact x86 (by omega) hK hP rfl (by assumption) (by assumption) (by assumption) (hp_id (by assumption))
        (by rw [sw_64_32]; exact cmv) rfl
    | exact nope (x := c1 g₀ V₀ i) (y := c2 g₀ V₀ i) (by assumption) (by assumption) (by assumption)

set_option maxHeartbeats 1000000 in
/-- `cmp eax, r12d`: `jg` `return -1`, `jge` the next characters, else `return 1`. -/
theorem vc_86 (hN : c1 g₀ V₀ N = 0#32) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I86 ci U g₀ V₀ i g) :
    W_86 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 18)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, a, c, si, di, p, q, rfl, hp, ha⟩ := h
  wpx [W_86, W_95, o7, hp, ha, subF_g32, subF_ge32, rfz_cond, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | apply And.intro
    | intro)
  all_goals first
    | exact x400 (by omega) hK (ans_m1b hP hne h0 hy0 (by assumption)) rfl
    | exact x34s hN hK hP rfl (go_mp h0 hy0 (eq_of_nlt (by assumption) (by omega))) (by omega) rfl
    | exact x97 (by omega) hK (ans_1b hP hne h0 hy0 (by omega)) rfl

set_option maxHeartbeats 1000000 in
/-- `mov r12d, 1`. -/
theorem vc_97 (hK : Keep g₀ V₀ V) (h : Ix ci U g₀ V₀ 1#32 g) : W_97 F Wl (Nx ci U N g₀ V₀ 3) g f V := by
  obtain ⟨hA, j, a, c, d, si, di, p, q, rfl⟩ := h
  wpx [W_97, o8]
  exact x103 (by omega) hK 1#32 hA (by first | rfl | decide) rfl

set_option maxHeartbeats 1000000 in
/-- `mov r12d, -1`. -/
theorem vc_400 (hK : Keep g₀ V₀ V) (h : Ix ci U g₀ V₀ 4294967295#32 g) :
    W_400 F Wl (Nx ci U N g₀ V₀ 3) g f V := by
  obtain ⟨hA, j, a, c, d, si, di, p, q, rfl⟩ := h
  wpx [W_400, o29]
  exact x103 (by omega) hK 4294967295#32 hA (by first | rfl | decide) rfl

set_option maxHeartbeats 1000000 in
/-- The exit: `eax` = `r12d`, the `pop`s. -/
theorem vc_103 (hF : Fr F Wl g₀.rsp) (hK : Keep g₀ V₀ V) (h : I103 ci U g₀ V₀ g) :
    W_103 F Wl (Nx ci U N g₀ V₀ 2) g f V := by
  obtain ⟨r, hA, j, a, c, d, si, di, q, rfl⟩ := h
  obtain ⟨q1, q2, q3, q4⟩ := pops hF.lo hF.hi hK
  have d1 := hF.d1
  have d2 := hF.d2
  have d3 := hF.d3
  have d4 := hF.d4
  wpx [W_103, o9, BitVec.sub_add_cancel, q1, q2, q3, q4]
  all_goals repeat' (first
    | with_reducible exact d1
    | with_reducible exact d2
    | with_reducible exact d3
    | with_reducible exact d4
    | apply And.intro
    | intro)
  all_goals exact xF hK hA rfl

set_option maxHeartbeats 2000000 in
/-- The case-insensitive loop's head: the loads; equal, 0s, `'/'`. -/
theorem vc_125 (hF : Fr F Wl g₀.rsp) (hN : c1 g₀ V₀ N = 0#32)
    (hw : ∀ k, Pre ci U g₀ V₀ k → ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add g₀.rsi (4 * k)) j))
    (hd : ∀ k, Pre ci U g₀ V₀ k → Sen.Ok g₀.rsp (Addr.add g₀.rdi (4 * k)) ∧ Sen.Ok g₀.rsp (Addr.add g₀.rsi (4 * k)))
    (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I125 ci g₀ i g) :
    W_125 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 19)) g f V := by
  obtain ⟨rfl, a, c, d, si, di, p, q, rfl⟩ := h
  have hr1 : rdd(V, Addr.add g₀.rdi (4 * i)) = c1 g₀ V₀ i := keep_rd hF.lo hK (hd i hP).1
  have hr2 : rdd(V, Addr.add g₀.rsi (4 * i)) = c2 g₀ V₀ i := keep_rd hF.lo hK (hd i hP).2
  have f1 : ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * i)) j) := fun j hj => (hw i hP j hj).1
  have f2 : ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rsi (4 * i)) j) := fun j hj => (hw i hP j hj).2
  wpx [W_125, W_120, W_145, W_154, W_159, W_288, W_297, W_165, o10, o3, o11, o5, o24, o12, hr1, hr2, Sen.ad4,
    BitVec.and_self, BitVec.xor_self, BitVec.setWidth_zero, beq_iff_eq, beq_eq_false_iff_ne, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | with_reducible exact f1
    | with_reducible exact f2
    | apply And.intro
    | intro)
  all_goals first
    | exact x125s hN hK hP rfl (go_eq (by assumption) (by assumption)) (by omega) rfl
    | exact x103 (by omega) hK _ (ans_z hP (by assumption) (by assumption)) rfl rfl
    | exact x400 (by omega) hK (ans_m1a hP (by assumption) (by assumption)) rfl
    | exact x97 (by omega) hK (ans_1a hP (by assumption) (by assumption) (by assumption)) rfl
    | exact x208 (by omega) hK hP rfl (by assumption) (by assumption) (by assumption) (by assumption)
        (hp_47 (by assumption)) rfl
    | exact x328 (by omega) hK hP rfl (by assumption) (by assumption) (by assumption) (by assumption) rfl
    | exact x175 (by omega) hK hP rfl (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) rfl
    | exact nope (x := c1 g₀ V₀ i) (y := c2 g₀ V₀ i) (by assumption) (by assumption) (by assumption)

set_option maxHeartbeats 1000000 in
/-- `c1` upper-cased: `a`..`z`, up to 127, or the call. -/
theorem vc_175 (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I175 ci g₀ V₀ i g) :
    W_175 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 18)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, h47, hy47, a, c, d, si, di, rfl⟩ := h
  wpx [W_175, W_181, W_191, W_197, W_384, o13, o14, o15, o16, o28, Sen.subF_le32, Sen.i96, Sen.i122, Sen.i127,
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | apply And.intro
    | intro)
  all_goals first
    | exact x208 (by omega) hK hP rfl hne h0 hy0 hy47 (hp_le h47 (by omega)) rfl
    | exact x208 (by omega) hK hP rfl hne h0 hy0 hy47 (hp_lo h47 (by omega) (by omega)) rfl
    | exact x208 (by omega) hK hP rfl hne h0 hy0 hy47 (hp_mid h47 (by omega) (by omega)) rfl
    | exact x200 (by omega) hK hP rfl hne h0 hy0 h47 hy47 (by omega) rfl

set_option maxHeartbeats 1000000 in
/-- After the call of `c1`: `mov r12d, eax`. -/
theorem vc_205 (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I205 ci U g₀ V₀ i g) :
    W_205 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 16)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, h47, hy47, h127, a, c, d, si, di, rfl, ha⟩ := h
  wpx [W_205, o17]
  exact x208 (by omega) hK hP rfl hne h0 hy0 hy47 (hp_hi h47 (by omega) ha) rfl

set_option maxHeartbeats 1000000 in
/-- `c2` upper-cased: `a`..`z`, up to 127, or the call. -/
theorem vc_208 (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I208 ci U g₀ V₀ i g) :
    W_208 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 15)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, hy47, a, c, d, si, di, p, rfl, hp⟩ := h
  wpx [W_208, W_214, W_224, W_230, W_368, o18, o19, o20, o21, o27, Sen.subF_le32, Sen.i96, Sen.i122, Sen.i127,
    decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | apply And.intro
    | intro)
  all_goals first
    | exact x241 (by omega) hK hP rfl hne h0 hy0 hp (hp_le hy47 (by omega)) rfl
    | exact x241 (by omega) hK hP rfl hne h0 hy0 hp (hp_lo hy47 (by omega) (by omega)) rfl
    | exact x241 (by omega) hK hP rfl hne h0 hy0 hp (hp_mid hy47 (by omega) (by omega)) rfl
    | exact x233 (by omega) hK hP rfl hne h0 hy0 hy47 (by omega) hp rfl

set_option maxHeartbeats 1000000 in
/-- After the call of `c2`: `mov r13d, eax`. -/
theorem vc_238 (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I238 ci U g₀ V₀ i g) :
    W_238 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 13)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, hy47, h127, a, c, d, si, di, p, rfl, hp, ha⟩ := h
  wpx [W_238, o22]
  exact x241 (by omega) hK hP rfl hne h0 hy0 hp (hp_hi hy47 (by omega) ha) rfl

set_option maxHeartbeats 1000000 in
/-- `cmp r13d, r12d`: `jg` `return -1`, `jl` `return 1`, else the next characters. -/
theorem vc_241 (hN : c1 g₀ V₀ N = 0#32) (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I241 ci U g₀ V₀ i g) :
    W_241 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 12)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, a, c, d, si, di, p, q, rfl, hp, hq⟩ := h
  wpx [W_241, W_250, W_256, o23, hp, hq, subF_g32, subF_l32, rfz_cond, decide_eq_true_eq,
    decide_eq_false_iff_not]
  all_goals repeat' (first
    | apply And.intro
    | intro)
  all_goals first
    | exact x400 (by omega) hK (ans_m1b hP hne h0 hy0 (by assumption)) rfl
    | exact x97 (by omega) hK (ans_1b hP hne h0 hy0 (by assumption)) rfl
    | exact x125s hN hK hP rfl (go_mp h0 hy0 (eq_of_nlt (by assumption) (by assumption))) (by omega) rfl

set_option maxHeartbeats 1000000 in
/-- `c2` `'/'`: `c1` as is up to 96, `return 1` for `a`..`z`, as is up to 127, or the call. -/
theorem vc_328 (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I328 ci g₀ V₀ i g) :
    W_328 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 18)) g f V := by
  obtain ⟨rfl, hne, h0, h47, hy, a, c, d, si, di, rfl⟩ := h
  wpx [W_328, W_416, W_334, W_344, W_353, o13, o30, o14, o26, o16, BitVec.xor_self, BitVec.setWidth_zero,
    Sen.subF_le32, Sen.i96, Sen.i122, Sen.i127, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | apply And.intro
    | intro)
  all_goals first
    | exact x241 (by omega) hK hP rfl hne h0 (hy0_47 hy) (hp_le h47 (by omega)) (hp_47 hy) rfl
    | exact x97 (by omega) hK (ans_1s hP hne h0 h47 hy (by omega) (by omega)) rfl
    | exact x241 (by omega) hK hP rfl hne h0 (hy0_47 hy) (hp_mid h47 (by omega) (by omega)) (hp_47 hy) rfl
    | exact x356 (by omega) hK hP rfl hne h0 h47 hy (by omega) rfl

set_option maxHeartbeats 1000000 in
/-- After the call of `c1` with `c2` `'/'`: `mov r12d, eax`. -/
theorem vc_361 (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I361 ci U g₀ V₀ i g) :
    W_361 F Wl (Nx ci U N g₀ V₀ (20 * (N - i) + 16)) g f V := by
  obtain ⟨rfl, hne, h0, h47, hy, h127, a, c, d, si, di, rfl, ha⟩ := h
  wpx [W_361, o17]
  exact x241 (by omega) hK hP rfl hne h0 (hy0_47 hy) (hp_hi h47 (by omega) ha) (hp_47 hy) rfl

/-- The call of `towupper` of `c1`. -/
theorem vc_200 {Tt : Gprs → (Addr → Byte) → Prop} (hF : Fr F Wl g₀.rsp) (hTt : TtOk g₀ V₀ Tt)
    (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I200 ci g₀ V₀ i g) :
    CallK Wl cfn_at 205 Tt (Sen.Rt U) (Nx ci U N g₀ V₀ (20 * (N - i) + 17)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, h47, hy47, h127, a, c, d, si, rfl⟩ := h
  have := g₀.rsp.isLt
  have e6 := s_6c _ hF.lo
  dsimp only [CallK]
  refine ⟨hF.w6, by omega, hTt _ _ rfl (keep_tt hF.lo hK _), ?_⟩
  rintro g' V' ⟨rfl, a', c', d', si', di', rfl, ha⟩ fl
  simp only [Sen.set4, BitVec.sub_add_cancel] at ha ⊢
  rw [sw_64_32] at ha
  exact x205 (by omega) (keep_st hF.lo hK _) hP rfl hne h0 hy0 h47 hy47 h127 ha rfl

/-- The call of `towupper` of `c2`. -/
theorem vc_233 {Tt : Gprs → (Addr → Byte) → Prop} (hF : Fr F Wl g₀.rsp) (hTt : TtOk g₀ V₀ Tt)
    (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I233 ci U g₀ V₀ i g) :
    CallK Wl cfn_at 238 Tt (Sen.Rt U) (Nx ci U N g₀ V₀ (20 * (N - i) + 14)) g f V := by
  obtain ⟨rfl, hne, h0, hy0, hy47, h127, a, c, d, si, p, rfl, hp⟩ := h
  have := g₀.rsp.isLt
  have e6 := s_6c _ hF.lo
  dsimp only [CallK]
  refine ⟨hF.w6, by omega, hTt _ _ rfl (keep_tt hF.lo hK _), ?_⟩
  rintro g' V' ⟨rfl, a', c', d', si', di', rfl, ha⟩ fl
  simp only [Sen.set4, BitVec.sub_add_cancel] at ha ⊢
  rw [sw_64_32] at ha
  exact x238 (by omega) (keep_st hF.lo hK _) hP rfl hne h0 hy0 hy47 h127 hp ha rfl

/-- The call of `towupper` of `c1` with `c2` `'/'`. -/
theorem vc_356 {Tt : Gprs → (Addr → Byte) → Prop} (hF : Fr F Wl g₀.rsp) (hTt : TtOk g₀ V₀ Tt)
    (hK : Keep g₀ V₀ V) (hP : Pre ci U g₀ V₀ i) (h : I356 ci g₀ V₀ i g) :
    CallK Wl cfn_at 361 Tt (Sen.Rt U) (Nx ci U N g₀ V₀ (20 * (N - i) + 17)) g f V := by
  obtain ⟨rfl, hne, h0, h47, hy, h127, a, c, d, si, rfl⟩ := h
  have := g₀.rsp.isLt
  have e6 := s_6c _ hF.lo
  dsimp only [CallK]
  refine ⟨hF.w6, by omega, hTt _ _ rfl (keep_tt hF.lo hK _), ?_⟩
  rintro g' V' ⟨rfl, a', c', d', si', di', rfl, ha⟩ fl
  simp only [Sen.set4, BitVec.sub_add_cancel] at ha ⊢
  rw [sw_64_32] at ha
  exact x361 (by omega) (keep_st hF.lo hK _) hP rfl hne h0 h47 hy h127 ha rfl

/-! ## The run -/

/-- The cut points' conditions, the calls' from `towupper`'s. -/
def WtC (F : Footprint) (Wl : List Rgn) (Tt : Gprs → (Addr → Byte) → Prop) (U : BitVec 32 → BitVec 32)
    (ℓ : Nat) : Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 200 then CallK Wl cfn_at 205 Tt (Sen.Rt U) else
  if ℓ = 233 then CallK Wl cfn_at 238 Tt (Sen.Rt U) else
  if ℓ = 356 then CallK Wl cfn_at 361 Tt (Sen.Rt U) else
  Wt ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}

theorem spC {Tt : Gprs → (Addr → Byte) → Prop} {tcode : List Byte} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L cfn_at cfn) (hinT : CodeIn L Sen.tup_at tcode) (hlT : 0 < tcode.length)
    (hT : FnK prof F Wl L s₀ o Sen.tup_at Tt (Sen.Rt U)) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o cfn_at ℓ (WtC F Wl Tt U ℓ) := by
  by_cases e200 : ℓ = 200
  · subst e200
    exact SpAt.callK c hin (lt_len (by decide)) (cl200 _) hinT hlT tg200 hT
  by_cases e233 : ℓ = 233
  · subst e233
    exact SpAt.callK c hin (lt_len (by decide)) (cl233 _) hinT hlT tg233 hT
  by_cases e356 : ℓ = 356
  · subst e356
    exact SpAt.callK c hin (lt_len (by decide)) (cl356 _) hinT hlT tg356 hT
  have e : WtC F Wl Tt U ℓ = Wt ℓ F Wl := by simp only [WtC, e200, e233, e356, ↓reduceIte]
  rw [e]
  exact (spAll prof ℓ).at c hin

theorem vcAll {Tt : Gprs → (Addr → Byte) → Prop} (hF : Fr F Wl g₀.rsp) (hN : c1 g₀ V₀ N = 0#32)
    (hw : ∀ k, Pre ci U g₀ V₀ k → ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add g₀.rsi (4 * k)) j))
    (hd : ∀ k, Pre ci U g₀ V₀ k → Sen.Ok g₀.rsp (Addr.add g₀.rdi (4 * k)) ∧ Sen.Ok g₀.rsp (Addr.add g₀.rsi (4 * k)))
    (hTt : TtOk g₀ V₀ Tt) (hci0 : ci = Ci V₀) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv ci U N g₀ V₀ ℓ n g V) : WtC F Wl Tt U ℓ (Nx ci U N g₀ V₀ n) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hK, ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨i, hP,
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩⟩⟩
  · exact vc_0 hF hci0
  · exact vc_97 hK h
  · exact vc_400 hK h
  · exact vc_103 hF hK h
  · exact vc_34 hF hN hw hd hK hP h
  · exact vc_86 hN hK hP h
  · exact vc_125 hF hN hw hd hK hP h
  · exact vc_175 hK hP h
  · exact vc_200 (f := f) hF hTt hK hP h
  · exact vc_205 hK hP h
  · exact vc_208 hK hP h
  · exact vc_233 (f := f) hF hTt hK hP h
  · exact vc_238 hK hP h
  · exact vc_241 hN hK hP h
  · exact vc_328 hK hP h
  · exact vc_356 (f := f) hF hTt hK hP h
  · exact vc_361 hK hP h

variable {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- `CompareFileNames (p, q)` from its entry to the return address, `towupper` (`U`) a hypothesis: `eax` the result
`r` (`Ans`, the case by the byte `g_CaseSensitive`: `Ci`), up to `p`'s 0 (at `N`); `rcx`, `rdx`, `rsi`, `rdi`
changed; the bytes outside the 48 below the return address as they were. -/
theorem cfn_ok {Tt : Gprs → (Addr → Byte) → Prop} {tcode : List Byte} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L cfn_at cfn) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = cfn_at) (hF : Fr F Wl X.cpu.gpr.rsp) (hN : c1 X.cpu.gpr V N = 0#32)
    (hw : ∀ k, Pre (Ci V) U X.cpu.gpr V k → ∀ j < 4, Foot F.data (Addr.add (Addr.add X.cpu.gpr.rdi (4 * k)) j) ∧
      Foot F.data (Addr.add (Addr.add X.cpu.gpr.rsi (4 * k)) j))
    (hd : ∀ k, Pre (Ci V) U X.cpu.gpr V k → Sen.Ok X.cpu.gpr.rsp (Addr.add X.cpu.gpr.rdi (4 * k)) ∧
      Sen.Ok X.cpu.gpr.rsp (Addr.add X.cpu.gpr.rsi (4 * k)))
    (hinT : CodeIn L Sen.tup_at tcode) (hlT : 0 < tcode.length)
    (hT : FnK prof F Wl L s₀ o Sen.tup_at Tt (Sen.Rt U)) (hTt : TtOk X.cpu.gpr V Tt)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte) (r : BitVec 32), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      (∀ y : Addr, y.toNat < X.cpu.gpr.rsp.toNat - 48 ∨ X.cpu.gpr.rsp.toNat ≤ y.toNat → V' y = V y) →
      Ans (Ci V) U X.cpu.gpr V r →
      (∃ c d si di, Z.cpu.gpr = { X.cpu.gpr with
                                                 rax := BitVec.setWidth 64 r, rcx := c, rdx := d, rsi := si,
                                                 rdi := di }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine cfgAt (spC c hin hinT hlT hT) (fun ℓ n g _ V' => Inv (Ci V) U N X.cpu.gpr V ℓ n g V')
    (fun j g _ V' => Fin (Ci V) U X.cpu.gpr V j g V')
    (fun ℓ n g f V' h => vcAll hF hN hw hd hTt rfl ℓ n g f V' h) ?_
    (20 * N + 20) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨hK', rfl, r, c', d', si, di, rfl, hres⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hra' : rdq(V', Y.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [hsY, keep_ra hF.lo hF.hi hK']
    exact hra
  obtain ⟨hjl, hdj⟩ := ret_at prof.feat
  refine c.s_ret hKY hAY hin hjl hrY hdj (by rw [hsY]; exact hF.d0) hin₂ h₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' r hKZ hAZ hrZ (keep_out hF.lo hK') hres ⟨c', d', si, di, by rw [hgZ, hsY, hgY]⟩

end FV7z.Cfn
