import FV7z.Rpl.Cuts
import FV7z.Lemmas.BlkOps12
import FV7z.Lemmas.SpCallK
import FV7z.Tun.Inv
/-!
# `AString::Replace` (PLAN.md §M, M1)

7-Zip 26.06's `AString::Replace (const AString &oldString, const AString &newString)` at `0x44ced0` in `7zzs`
(`CPP/Common/MyString.cpp`; `objdump -d`), `p` = `rdi` (`this`), `q₁` = `rsi`, `q₂` = `rdx`; a string's length is
the 4 bytes at `+ 8`, its characters' pointer the 8 bytes at `+ 0`. If `q₁`'s length `K` is 0, or the lengths are
equal and `strcmp` of the characters gives 0, or `p`'s length is 0, it returns; else from `pos` = 0, while
`pos < p`'s length: `pos = Find (q₁'s characters, pos)`, out if negative, `Delete (pos, K)`, `Insert (pos, q₂)`,
`pos += q₂`'s length `N`.

The four callees are hypotheses `FnK`: `Find` (`0x44cae0`, `RFnd`: no bytes changed, the result negative or a `pos'`
from `pos` with `pos' + K` in the length), `Delete` (`0x44ce70`, `RDel`: the length less the count), `Insert`
(`0x44cd10`, `RIns`: the length plus `N`), `strcmp` (`0x401110`, `RScm`: no bytes changed). `Delete` and `Insert`
keep the frame above their return address's slot (`Fkp`) and an invariant `A` of the bytes, which the bytes of the
frame (the 64 below the return address) do not change (`AIns`). Each callee's entry condition follows from what the
call gives it (`TOk`).

Cut points: the entry (0), 45, the loop (100, 107, 112, 72, 77, 85, 90; the measure 10 (`p`'s length - `pos`) +
a rank), after `strcmp` (143, 148), the epilogue (118); the `ret`s at 132 and 166.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rpl

/-! ## The `ret`s and the calls -/

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_132 : pret <+: rpl.drop 132 := by decide +kernel
theorem w_166 : pret <+: rpl.drop 166 := by decide +kernel
theorem ret_at (feat : Features) {j : Nat} (hj : j = 132 ∨ j = 166) :
    j < rpl.length ∧ Dec feat rpl j (FV7z.mk .ret 64 [] 1) := by
  rcases hj with rfl | rfl
  · exact ⟨lt_len (by decide), Dec.shift (j := 132) (k := 0) (pret_0 feat) w_132 (Nat.zero_le _)⟩
  · exact ⟨lt_len (by decide), Dec.shift (j := 166) (k := 0) (pret_0 feat) w_166 (Nat.zero_le _)⟩

def pc72 : List Byte := [0xe8, 0x53, 0xff, 0xff, 0xff]
def pc85 : List Byte := [0xe8, 0xe6, 0xfd, 0xff, 0xff]
def pc107 : List Byte := [0xe8, 0xa0, 0xfb, 0xff, 0xff]
def pc143 : List Byte := [0xe8, 0xac, 0x41, 0xfb, 0xff]
theorem pc72_0 : ∀ feat, Dec feat pc72 0 (FV7z.mk .call 64 [.rel 18446744073709551443] 5) := by dec_rfl
theorem pc85_0 : ∀ feat, Dec feat pc85 0 (FV7z.mk .call 64 [.rel 18446744073709551078] 5) := by dec_rfl
theorem pc107_0 : ∀ feat, Dec feat pc107 0 (FV7z.mk .call 64 [.rel 18446744073709550496] 5) := by dec_rfl
theorem pc143_0 : ∀ feat, Dec feat pc143 0 (FV7z.mk .call 64 [.rel 18446744073709240748] 5) := by dec_rfl
theorem w_72 : pc72 <+: rpl.drop 72 := by decide +kernel
theorem w_85 : pc85 <+: rpl.drop 85 := by decide +kernel
theorem w_107 : pc107 <+: rpl.drop 107 := by decide +kernel
theorem w_143 : pc143 <+: rpl.drop 143 := by decide +kernel
theorem cl72 (feat : Features) : Dec feat rpl 72 (FV7z.mk .call 64 [.rel 18446744073709551443] 5) :=
  Dec.shift (j := 72) (k := 0) (pc72_0 feat) w_72 (Nat.zero_le _)
theorem cl85 (feat : Features) : Dec feat rpl 85 (FV7z.mk .call 64 [.rel 18446744073709551078] 5) :=
  Dec.shift (j := 85) (k := 0) (pc85_0 feat) w_85 (Nat.zero_le _)
theorem cl107 (feat : Features) : Dec feat rpl 107 (FV7z.mk .call 64 [.rel 18446744073709550496] 5) :=
  Dec.shift (j := 107) (k := 0) (pc107_0 feat) w_107 (Nat.zero_le _)
theorem cl143 (feat : Features) : Dec feat rpl 143 (FV7z.mk .call 64 [.rel 18446744073709240748] 5) :=
  Dec.shift (j := 143) (k := 0) (pc143_0 feat) w_143 (Nat.zero_le _)

/-- `AString::Find (const char *, unsigned)`. -/
abbrev fnd_at : Addr := 0x44cae0
/-- `AString::Delete (unsigned, unsigned)`. -/
abbrev del_at : Addr := 0x44ce70
/-- `AString::Insert (unsigned, const AString &)`. -/
abbrev ins_at : Addr := 0x44cd10
/-- `strcmp`'s PLT entry. -/
abbrev scm_at : Addr := 0x401110
theorem tg72 : Addr.add rpl_at (72 + 5) + BitVec.ofNat 64 18446744073709551443 = del_at := by decide
theorem tg85 : Addr.add rpl_at (85 + 5) + BitVec.ofNat 64 18446744073709551078 = ins_at := by decide
theorem tg107 : Addr.add rpl_at (107 + 5) + BitVec.ofNat 64 18446744073709550496 = fnd_at := by decide
theorem tg143 : Addr.add rpl_at (143 + 5) + BitVec.ofNat 64 18446744073709240748 = scm_at := by decide

/-! ## Arithmetic -/

theorem s_1 (s : Addr) (h : 64 ≤ s.toNat) : (s - 8).toNat = s.toNat - 8 := by bv_omega
theorem s_2 (s : Addr) (h : 64 ≤ s.toNat) : (s - 8 - 8).toNat = s.toNat - 16 := by bv_omega
theorem s_3 (s : Addr) (h : 64 ≤ s.toNat) : (s - 8 - 8 - 8).toNat = s.toNat - 24 := by bv_omega
theorem s_4 (s : Addr) (h : 64 ≤ s.toNat) : (s - 8 - 8 - 8 - 8).toNat = s.toNat - 32 := by bv_omega
theorem s_5 (s : Addr) (h : 64 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8).toNat = s.toNat - 40 := by bv_omega
theorem s_6 (s : Addr) (h : 64 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8 - 8).toNat = s.toNat - 48 := by bv_omega
theorem s_8 (s : Addr) (h : 64 ≤ s.toNat) : (s - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8).toNat = s.toNat - 64 := by
  bv_omega

theorem set4 (g : Gprs) (v : BitVec 64) : g.set 4 v = { g with rsp := v } := rfl

theorem pos32 {x : BitVec 32} (h : ¬ x = 0) : 0 < x.toNat := by
  rcases Nat.eq_zero_or_pos x.toNat with e | e
  · exact absurd (BitVec.eq_of_toNat_eq (by simp [e])) h
  · exact e

/-- `lea edx, [rbx + r14]`. -/
theorem sw_add (x y : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 x + BitVec.setWidth 64 y) = x + y := by
  bv_omega

/-- The loop's exit test after `Insert`: `cmp [r15 + 8], edx; jbe`. -/
theorem step90 {L r n : BitVec 32} {D k : Nat} (h1 : r.toNat + n.toNat ≤ L.toNat)
    (h2 : L.toNat + k ≤ r.toNat + n.toNat + D) (hk : 0 < k)
    (h3 : (decide (L.toNat < (r + n).toNat) || decide (L = r + n)) = false) :
    (r + n).toNat < L.toNat ∧ L.toNat = (r + n).toNat + (L.toNat - (r + n).toNat) ∧
      10 * (L.toNat - (r + n).toNat) + 9 < 10 * D + 3 := by
  have hL : L.toNat < 4294967296 := L.isLt
  have h7 : r.toNat + n.toNat < 4294967296 := by omega
  have e : (r + n).toNat = r.toNat + n.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt h7
  have h4 : ¬ L = r + n := fun h => by simp [h] at h3
  have h5 : L.toNat ≠ (r + n).toNat := fun h => h4 (BitVec.eq_of_toNat_eq h)
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h3
  obtain ⟨h6, -⟩ := h3
  omega

/-! ## The bytes -/

variable {g₀ : Gprs} {V₀ : Addr → Byte} {A : (Addr → Byte) → Prop}

/-- After the six `push`es. -/
def Vp (g₀ : Gprs) (V₀ : Addr → Byte) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V₀ (g₀.rsp - 8) (toBytesLE g₀.r15 8)) (g₀.rsp - 8 - 8) (toBytesLE g₀.r14 8))
    (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.r13 8)) (g₀.rsp - 8 - 8 - 8 - 8) (toBytesLE g₀.r12 8))
    (g₀.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g₀.rbp 8)) (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g₀.rbx 8)

/-- The frame from 56 below the return address through it: as after the `push`es. -/
def Fmm (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  ∀ y : Addr, g₀.rsp.toNat - 56 ≤ y.toNat → y.toNat < g₀.rsp.toNat + 8 → V y = Vp g₀ V₀ y

/-- `n` bytes at `x`: not wrapping, apart from the 64 below the return address at `s`. -/
def Okr (s : Addr) (n : Nat) (x : Addr) : Prop :=
  x.toNat + n ≤ 2 ^ 64 ∧ (x.toNat + n ≤ s.toNat - 64 ∨ s.toNat ≤ x.toNat)

/-- `p`'s length in `W`. -/
def Lnp (p : Addr) (W : Addr → Byte) : Nat := (rdd(W, p + 8#64)).toNat

/-- The lengths of `q₁` and `q₂` at the entry. -/
def Kl (g₀ : Gprs) (V₀ : Addr → Byte) : BitVec 32 := rdd(V₀, g₀.rsi + 8#64)
def Nl (g₀ : Gprs) (V₀ : Addr → Byte) : BitVec 32 := rdd(V₀, g₀.rdx + 8#64)

/-- `A` does not depend on the 64 bytes below the return address at `s`. -/
def AIns (A : (Addr → Byte) → Prop) (s : Addr) : Prop :=
  ∀ W W' : Addr → Byte, (∀ y : Addr, y.toNat < s.toNat - 64 ∨ s.toNat ≤ y.toNat → W' y = W y) → A W → A W'

/-- The frame below the return address at `s`: the `push`es' and the calls' slots, those of the `pop`s and the
`ret`. -/
structure Fr (F : Footprint) (Wl : List Rgn) (s : Addr) : Prop where
  lo : 64 ≤ s.toNat
  hi : s.toNat + 8 ≤ 2 ^ 64
  w1 : ∀ i < 8, Foot Wl (Addr.add (s - 8) i)
  w2 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8) i)
  w3 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8) i)
  w4 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8) i)
  w5 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8 - 8) i)
  w6 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8 - 8 - 8) i)
  w8 : ∀ i < 8, Foot Wl (Addr.add (s - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8) i)
  d0 : ∀ i < 8, Foot F.data (Addr.add s i)
  d1 : ∀ i < 8, Foot F.data (Addr.add (s - 8) i)
  d2 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8) i)
  d3 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8) i)
  d4 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8 - 8) i)
  d5 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8 - 8 - 8) i)
  d6 : ∀ i < 8, Foot F.data (Addr.add (s - 8 - 8 - 8 - 8 - 8 - 8) i)

/-- The strings' bytes the code reads: the lengths and the characters' pointers. -/
structure Fdat (F : Footprint) (g₀ : Gprs) : Prop where
  p8 : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + 8#64) i)
  k8 : ∀ i < 4, Foot F.data (Addr.add (g₀.rsi + 8#64) i)
  n8 : ∀ i < 4, Foot F.data (Addr.add (g₀.rdx + 8#64) i)
  q1 : ∀ i < 8, Foot F.data (Addr.add g₀.rsi i)
  q2 : ∀ i < 8, Foot F.data (Addr.add g₀.rdx i)
  op : Okr g₀.rsp 4 (g₀.rdi + 8#64)
  ok : Okr g₀.rsp 4 (g₀.rsi + 8#64)
  on : Okr g₀.rsp 4 (g₀.rdx + 8#64)
  oq1 : Okr g₀.rsp 8 g₀.rsi
  oq2 : Okr g₀.rsp 8 g₀.rdx

theorem rd_eq {w n : Nat} {W W' : Addr → Byte} {x : Addr} (hx : x.toNat + n ≤ 2 ^ 64)
    (h : ∀ y : Addr, x.toNat ≤ y.toNat → y.toNat < x.toNat + n → W y = W' y) :
    ofBytesLE w (List.map W (byteAddrs x n)) = ofBytesLE w (List.map W' (byteAddrs x n)) := by
  apply congrArg (ofBytesLE w)
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have := toNat_add_of_fits hj hx
  exact h _ (by omega) (by omega)

theorem Vp_out (hlo : 64 ≤ g₀.rsp.toNat) (y : Addr)
    (h : y.toNat < g₀.rsp.toNat - 48 ∨ g₀.rsp.toNat ≤ y.toNat) : Vp g₀ V₀ y = V₀ y := by
  have := g₀.rsp.isLt
  have e1 := s_1 _ hlo
  have e2 := s_2 _ hlo
  have e3 := s_3 _ hlo
  have e4 := s_4 _ hlo
  have e5 := s_5 _ hlo
  have e6 := s_6 _ hlo
  dsimp only [Vp]
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e6]; omega) (by rw [toBytesLE_length, e6]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e5]; omega) (by rw [toBytesLE_length, e5]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e4]; omega) (by rw [toBytesLE_length, e4]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

/-- Bytes apart from the frame read after the `push`es as at the entry. -/
theorem rd_vp {w n : Nat} {x : Addr} (hlo : 64 ≤ g₀.rsp.toNat) (hx : Okr g₀.rsp n x) :
    ofBytesLE w (List.map (Vp g₀ V₀) (byteAddrs x n)) = ofBytesLE w (List.map V₀ (byteAddrs x n)) := by
  obtain ⟨h1, h2⟩ := hx
  exact rd_eq h1 (fun y hy1 hy2 => Vp_out hlo y (by omega))

/-- The store of a call's return address. -/
theorem st_out {s : Addr} (hlo : 64 ≤ s.toNat) (V : Addr → Byte) (v : BitVec 64) (y : Addr)
    (h : y.toNat < s.toNat - 64 ∨ s.toNat - 56 ≤ y.toNat) :
    Vst V (s - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE v 8) y = V y := by
  have := s.isLt
  have e8 := s_8 s hlo
  exact Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e8]; omega) (by rw [toBytesLE_length, e8]; omega)

theorem rd_st {w n : Nat} {s x : Addr} (hlo : 64 ≤ s.toNat) (hx : Okr s n x) (V : Addr → Byte)
    (v : BitVec 64) :
    ofBytesLE w (List.map (Vst V (s - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE v 8)) (byteAddrs x n)) =
      ofBytesLE w (List.map V (byteAddrs x n)) := by
  obtain ⟨h1, h2⟩ := hx
  exact rd_eq h1 (fun y hy1 hy2 => st_out hlo V v y (by omega))

theorem ln_st {s p : Addr} (hlo : 64 ≤ s.toNat) (hp : Okr s 4 (p + 8#64)) (V : Addr → Byte) (v : BitVec 64) :
    Lnp p (Vst V (s - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE v 8)) = Lnp p V :=
  congrArg BitVec.toNat (rd_st hlo hp V v)

theorem ln_lt (p : Addr) (V : Addr → Byte) : Lnp p V < 4294967296 := (rdd(V, p + 8#64)).isLt

theorem a_st {s : Addr} {V : Addr → Byte} (hlo : 64 ≤ s.toNat) (hAi : AIns A s) (hA : A V) (v : BitVec 64) :
    A (Vst V (s - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE v 8)) :=
  hAi _ _ (fun y hy => st_out hlo V v y (by omega)) hA

theorem a_vp (hlo : 64 ≤ g₀.rsp.toNat) (hAi : AIns A g₀.rsp) (hA : A V₀) : A (Vp g₀ V₀) :=
  hAi _ _ (fun y hy => Vp_out hlo y (by omega)) hA

theorem fm_st {V : Addr → Byte} (hlo : 64 ≤ g₀.rsp.toNat) (hK : Fmm g₀ V₀ V) (v : BitVec 64) :
    Fmm g₀ V₀ (Vst V (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8) (toBytesLE v 8)) := fun y h1 h2 => by
  rw [st_out hlo V v y (Or.inr h1)]
  exact hK y h1 h2

/-- A callee keeps the frame above its return address's slot. -/
def Fkp (g : Gprs) (W W' : Addr → Byte) : Prop :=
  ∀ y : Addr, g.rsp.toNat + 8 ≤ y.toNat → y.toNat < g.rsp.toNat + 72 → W' y = W y

theorem fm_fk {W W' : Addr → Byte} (hlo : 64 ≤ g₀.rsp.toNat) (hW : Fmm g₀ V₀ W) {g : Gprs} (hfk : Fkp g W W')
    (hg : g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8) : Fmm g₀ V₀ W' := fun y h1 h2 => by
  have := g₀.rsp.isLt
  have e8 := s_8 _ hlo
  rw [hfk y (by rw [hg, e8]; omega) (by rw [hg, e8]; omega)]
  exact hW y h1 h2

theorem fm_q {V : Addr → Byte} (hK : Fmm g₀ V₀ V) {x : Addr} (h1 : g₀.rsp.toNat - 56 ≤ x.toNat)
    (h2 : x.toNat ≤ g₀.rsp.toNat) (hx : x.toNat + 8 ≤ 2 ^ 64) : rdq(V, x) = rdq(Vp g₀ V₀, x) :=
  rd_eq hx (fun y hy1 hy2 => hK y (by omega) (by omega))

/-- The return address. -/
theorem fm_ra {V : Addr → Byte} (hlo : 64 ≤ g₀.rsp.toNat) (hhi : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hK : Fmm g₀ V₀ V) : rdq(V, g₀.rsp) = rdq(V₀, g₀.rsp) :=
  rd_eq hhi (fun y h1 h2 => by
    rw [hK y (by omega) (by omega)]
    exact Vp_out hlo y (Or.inr h1))

theorem rq_self (V : Addr → Byte) (a : Addr) (v : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst V a (toBytesLE v 8), a) = v := by
  rw [Tun.rd_Vst_self V a (toBytesLE v 8) (toBytesLE_length v 8) ha]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem rq_out (V : Addr → Byte) (a x : Addr) (v : BitVec 64) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (hx : x.toNat + 8 ≤ 2 ^ 64) (h : a.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ a.toNat) :
    rdq(Vst V a (toBytesLE v 8), x) = rdq(V, x) := by
  rw [Tun.rd_Vst V a (toBytesLE v 8) x 8 (by rw [toBytesLE_length]; exact ha) hx
    (by rw [toBytesLE_length]; exact h)]

/-- The `pop`s' loads. -/
theorem pops {V : Addr → Byte} (hlo : 64 ≤ g₀.rsp.toNat) (hK : Fmm g₀ V₀ V) :
    rdq(V, g₀.rsp - 8) = g₀.r15 ∧ rdq(V, g₀.rsp - 8 - 8) = g₀.r14 ∧ rdq(V, g₀.rsp - 8 - 8 - 8) = g₀.r13 ∧
      rdq(V, g₀.rsp - 8 - 8 - 8 - 8) = g₀.r12 ∧ rdq(V, g₀.rsp - 8 - 8 - 8 - 8 - 8) = g₀.rbp ∧
      rdq(V, g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) = g₀.rbx := by
  have := g₀.rsp.isLt
  have e1 := s_1 _ hlo
  have e2 := s_2 _ hlo
  have e3 := s_3 _ hlo
  have e4 := s_4 _ hlo
  have e5 := s_5 _ hlo
  have e6 := s_6 _ hlo
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fm_q hK (x := g₀.rsp - 8) (by omega) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8) (g₀.rsp - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8) _ (by omega)]
  · rw [fm_q hK (x := g₀.rsp - 8 - 8) (by omega) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8) (g₀.rsp - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8 - 8) _ (by omega)]
  · rw [fm_q hK (x := g₀.rsp - 8 - 8 - 8) (by omega) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8 - 8 - 8) _ (by omega)]
  · rw [fm_q hK (x := g₀.rsp - 8 - 8 - 8 - 8) (by omega) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8 - 8) _ (by omega) (by omega) (by omega),
      rq_self _ (g₀.rsp - 8 - 8 - 8 - 8) _ (by omega)]
  · rw [fm_q hK (x := g₀.rsp - 8 - 8 - 8 - 8 - 8) (by omega) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_out _ (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (g₀.rsp - 8 - 8 - 8 - 8 - 8) _ (by omega) (by omega)
      (by omega), rq_self _ (g₀.rsp - 8 - 8 - 8 - 8 - 8) _ (by omega)]
  · rw [fm_q hK (x := g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) (by omega) (by omega) (by omega)]
    dsimp only [Vp]
    rw [rq_self _ (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) _ (by omega)]

/-! ## The callees -/

/-- A callee from its entry to the return address: `rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`..`r11` changed. -/
def Cso (g g' : Gprs) : Prop :=
  ∃ a c d si di x8 x9 x10 x11, g' = { g with
    rax := a, rcx := c, rdx := d, rsi := si, rdi := di, r8 := x8, r9 := x9, r10 := x10, r11 := x11,
    rsp := g.rsp + 8 }

/-- `Find (s, pos)` of the string at `p`: no bytes changed; the result negative, or from `pos` (`edx`) with `k`
bytes after it in the length. -/
def RFnd (p : Addr) (k : BitVec 32) : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop :=
  fun g W g' W' => W' = W ∧ Cso g g' ∧ ((BitVec.setWidth 32 g'.rax).msb = true ∨
    ((BitVec.setWidth 32 g.rdx).toNat ≤ (BitVec.setWidth 32 g'.rax).toNat ∧
      (BitVec.setWidth 32 g'.rax).toNat + k.toNat ≤ Lnp p W))

/-- `Delete (pos, count)` (`esi`, `edx`) of the string at `p`: the length less the count. -/
def RDel (p : Addr) (A : (Addr → Byte) → Prop) : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop :=
  fun g W g' W' => Fkp g W W' ∧ Cso g g' ∧ A W' ∧ Lnp p W' + (BitVec.setWidth 32 g.rdx).toNat = Lnp p W

/-- `Insert (pos, s)` of the string at `p`: the length plus `n`. -/
def RIns (p : Addr) (n : BitVec 32) (A : (Addr → Byte) → Prop) :
    Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop :=
  fun g W g' W' => Fkp g W W' ∧ Cso g g' ∧ A W' ∧ Lnp p W' = Lnp p W + n.toNat

/-- `strcmp`: no bytes changed. -/
def RScm : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop := fun g W g' W' => W' = W ∧ Cso g g'

/-- What the calls give the callees' entry conditions: the return address 64 below that at the entry, `A`, and the
arguments. -/
structure TOk (A : (Addr → Byte) → Prop) (g₀ : Gprs) (Tf Td Ti Ts : Gprs → (Addr → Byte) → Prop) : Prop where
  fnd : ∀ g W, g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8 → g.rdi = g₀.rdi → g.rsi = rdq(W, g₀.rsi) →
    (BitVec.setWidth 32 g.rdx).toNat < Lnp g₀.rdi W → A W → Tf g W
  del : ∀ g W, g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8 → g.rdi = g₀.rdi →
    (BitVec.setWidth 32 g.rsi).toNat + (BitVec.setWidth 32 g.rdx).toNat ≤ Lnp g₀.rdi W → A W → Td g W
  ins : ∀ g W, g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8 → g.rdi = g₀.rdi → g.rdx = g₀.rdx →
    (BitVec.setWidth 32 g.rsi).toNat ≤ Lnp g₀.rdi W → A W → Ti g W
  scm : ∀ g W, g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64 - 8 → g.rdi = rdq(W, g₀.rsi) →
    g.rsi = rdq(W, g₀.rdx) → A W → Ts g W

/-! ## The invariant -/

/-- The registers after the prologue. -/
def Sh (g₀ : Gprs) (V₀ : Addr → Byte) (a d si di b : BitVec 64) (g : Gprs) : Prop :=
  ∃ c x8 x9 x10 x11, g = { g₀ with
    rax := a, rcx := c, rdx := d, rbx := b, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64, rbp := g₀.rsi,
    rsi := si, rdi := di, r8 := x8, r9 := x9, r10 := x10, r11 := x11, r12 := g₀.rdx,
    r13 := BitVec.setWidth 64 (Kl g₀ V₀), r14 := BitVec.setWidth 64 (Nl g₀ V₀), r15 := g₀.rdi }

def I45 (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) : Prop := ∃ a d si di b, Sh g₀ V₀ a d si di b g
def I143 (g₀ : Gprs) (V₀ V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ a d b, Sh g₀ V₀ a d (rdq(V, g₀.rdx)) (rdq(V, g₀.rsi)) b g
def I100 (g₀ : Gprs) (V₀ : Addr → Byte) (D : Nat) (V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ pos : BitVec 32, pos.toNat < Lnp g₀.rdi V ∧ Lnp g₀.rdi V = pos.toNat + D ∧
    ∃ a si di b, Sh g₀ V₀ a (BitVec.setWidth 64 pos) si di b g
def I107 (g₀ : Gprs) (V₀ : Addr → Byte) (D : Nat) (V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ pos : BitVec 32, pos.toNat < Lnp g₀.rdi V ∧ Lnp g₀.rdi V = pos.toNat + D ∧
    ∃ a b, Sh g₀ V₀ a (BitVec.setWidth 64 pos) (rdq(V, g₀.rsi)) g₀.rdi b g
def I112 (g₀ : Gprs) (V₀ : Addr → Byte) (D : Nat) (V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ a d si di b, Sh g₀ V₀ a d si di b g ∧ ((BitVec.setWidth 32 a).msb = true ∨
    ((BitVec.setWidth 32 a).toNat + (Kl g₀ V₀).toNat ≤ Lnp g₀.rdi V ∧
      Lnp g₀.rdi V ≤ (BitVec.setWidth 32 a).toNat + D))
def I72 (g₀ : Gprs) (V₀ : Addr → Byte) (D : Nat) (V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ r : BitVec 32, r.toNat + (Kl g₀ V₀).toNat ≤ Lnp g₀.rdi V ∧ Lnp g₀.rdi V ≤ r.toNat + D ∧
    ∃ a, Sh g₀ V₀ a (BitVec.setWidth 64 (Kl g₀ V₀)) (BitVec.setWidth 64 r) g₀.rdi (BitVec.setWidth 64 r) g
def I77 (g₀ : Gprs) (V₀ : Addr → Byte) (D : Nat) (V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ r : BitVec 32, r.toNat ≤ Lnp g₀.rdi V ∧ Lnp g₀.rdi V + (Kl g₀ V₀).toNat ≤ r.toNat + D ∧
    ∃ a d si di, Sh g₀ V₀ a d si di (BitVec.setWidth 64 r) g
def I85 (g₀ : Gprs) (V₀ : Addr → Byte) (D : Nat) (V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ r : BitVec 32, r.toNat ≤ Lnp g₀.rdi V ∧ Lnp g₀.rdi V + (Kl g₀ V₀).toNat ≤ r.toNat + D ∧
    ∃ a, Sh g₀ V₀ a g₀.rdx (BitVec.setWidth 64 r) g₀.rdi (BitVec.setWidth 64 r) g
def I90 (g₀ : Gprs) (V₀ : Addr → Byte) (D : Nat) (V : Addr → Byte) (g : Gprs) : Prop :=
  ∃ r : BitVec 32, r.toNat + (Nl g₀ V₀).toNat ≤ Lnp g₀.rdi V ∧
    Lnp g₀.rdi V + (Kl g₀ V₀).toNat ≤ r.toNat + (Nl g₀ V₀).toNat + D ∧
    ∃ a d si di, Sh g₀ V₀ a d si di (BitVec.setWidth 64 r) g

/-- The invariant at the cut points, `n` the measure. -/
def Inv (A : (Addr → Byte) → Prop) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) :
    Prop :=
  (ℓ = 0 ∧ n = 42949672990 ∧ g = g₀ ∧ V = V₀) ∨
  (Fmm g₀ V₀ V ∧ A V ∧ ((ℓ = 118 ∧ n = 2 ∧ g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64) ∨
    (0 < (Kl g₀ V₀).toNat ∧ ((ℓ = 143 ∧ n = 42949672982 ∧ I143 g₀ V₀ V g) ∨
      (ℓ = 148 ∧ n = 42949672981 ∧ I45 g₀ V₀ g) ∨ (ℓ = 45 ∧ n = 42949672980 ∧ I45 g₀ V₀ g) ∨
      ∃ D, (ℓ = 100 ∧ n = 10 * D + 9 ∧ I100 g₀ V₀ D V g) ∨ (ℓ = 107 ∧ n = 10 * D + 8 ∧ I107 g₀ V₀ D V g) ∨
        (ℓ = 112 ∧ n = 10 * D + 7 ∧ I112 g₀ V₀ D V g) ∨ (ℓ = 72 ∧ n = 10 * D + 6 ∧ I72 g₀ V₀ D V g) ∨
        (ℓ = 77 ∧ n = 10 * D + 5 ∧ I77 g₀ V₀ D V g) ∨ (ℓ = 85 ∧ n = 10 * D + 4 ∧ I85 g₀ V₀ D V g) ∨
        (ℓ = 90 ∧ n = 10 * D + 3 ∧ I90 g₀ V₀ D V g)))))

/-- At a `ret`: the callee-saved registers restored, the frame as after the `push`es, `A`. -/
def Fin (A : (Addr → Byte) → Prop) (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) :
    Prop :=
  Fmm g₀ V₀ V ∧ A V ∧ (j = 132 ∨ j = 166) ∧ ∃ a c d si di x8 x9 x10 x11, g = { g₀ with
    rax := a, rcx := c, rdx := d, rsi := si, rdi := di, r8 := x8, r9 := x9, r10 := x10, r11 := x11 }

def Nx (A : (Addr → Byte) → Prop) (g₀ : Gprs) (V₀ : Addr → Byte) (m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv A g₀ V₀ j m' g V) ∨ Fin A g₀ V₀ j g V

/-! ## The exits -/

section X
variable {m D : Nat} {V : Addr → Byte} {g : Gprs} {fl : Rflags} {a c d si di b x8 x9 x10 x11 : BitVec 64}

theorem x118 (hm : 2 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hg : g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64) :
    Nx A g₀ V₀ m 118 g fl V :=
  Or.inl ⟨2, hm, Or.inr ⟨hK, hA, Or.inl ⟨rfl, rfl, hg⟩⟩⟩

theorem x143 (hm : 42949672982 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I143 g₀ V₀ V g) : Nx A g₀ V₀ m 143 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inl ⟨rfl, rfl, h⟩⟩⟩⟩

theorem x148 (hm : 42949672981 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I45 g₀ V₀ g) : Nx A g₀ V₀ m 148 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inl ⟨rfl, rfl, h⟩)⟩⟩⟩

theorem x45 (hm : 42949672980 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I45 g₀ V₀ g) : Nx A g₀ V₀ m 45 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h⟩))⟩⟩⟩

theorem x100 (hm : 10 * D + 9 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I100 g₀ V₀ D V g) : Nx A g₀ V₀ m 100 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inr ⟨D, Or.inl ⟨rfl, rfl, h⟩⟩))⟩⟩⟩

theorem x107 (hm : 10 * D + 8 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I107 g₀ V₀ D V g) : Nx A g₀ V₀ m 107 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inr ⟨D, Or.inr (Or.inl ⟨rfl, rfl, h⟩)⟩))⟩⟩⟩

theorem x112 (hm : 10 * D + 7 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I112 g₀ V₀ D V g) : Nx A g₀ V₀ m 112 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inr ⟨D, Or.inr (Or.inr (Or.inl
    ⟨rfl, rfl, h⟩))⟩))⟩⟩⟩

theorem x72 (hm : 10 * D + 6 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I72 g₀ V₀ D V g) : Nx A g₀ V₀ m 72 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inr ⟨D, Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, rfl, h⟩)))⟩))⟩⟩⟩

theorem x77 (hm : 10 * D + 5 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I77 g₀ V₀ D V g) : Nx A g₀ V₀ m 77 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inr ⟨D, Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, h⟩))))⟩))⟩⟩⟩

theorem x85 (hm : 10 * D + 4 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I85 g₀ V₀ D V g) : Nx A g₀ V₀ m 85 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inr ⟨D, Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inl ⟨rfl, rfl, h⟩)))))⟩))⟩⟩⟩

theorem x90 (hm : 10 * D + 3 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I90 g₀ V₀ D V g) : Nx A g₀ V₀ m 90 g fl V :=
  Or.inl ⟨_, hm, Or.inr ⟨hK, hA, Or.inr ⟨hk, Or.inr (Or.inr (Or.inr ⟨D, Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr (Or.inr ⟨rfl, rfl, h⟩)))))⟩))⟩⟩⟩

theorem xF {j : Nat} (hK : Fmm g₀ V₀ V) (hA : A V) (hj : j = 132 ∨ j = 166)
    (hg : ∃ a c d si di x8 x9 x10 x11, g = { g₀ with
      rax := a, rcx := c, rdx := d, rsi := si, rdi := di, r8 := x8, r9 := x9, r10 := x10, r11 := x11 }) :
    Nx A g₀ V₀ m j g fl V :=
  Or.inr ⟨hK, hA, hj, hg⟩

/-- From the entry to 143, the lengths as loaded. -/
theorem x143z {k n : BitVec 32} (hm : 42949672982 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : k = Kl g₀ V₀)
    (hn : n = Nl g₀ V₀) (hz : ¬ k = 0)
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := b, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64, rbp := g₀.rsi,
      rsi := rdq(V, g₀.rdx), rdi := rdq(V, g₀.rsi), r8 := x8, r9 := x9, r10 := x10, r11 := x11,
      r12 := g₀.rdx, r13 := BitVec.setWidth 64 k, r14 := BitVec.setWidth 64 n, r15 := g₀.rdi }) :
    Nx A g₀ V₀ m 143 g fl V := by
  subst hk hn
  exact x143 hm hK hA (pos32 hz) ⟨a, d, b, c, x8, x9, x10, x11, hg⟩

/-- From the entry to 45, the lengths as loaded. -/
theorem x45z {k n : BitVec 32} (hm : 42949672980 < m) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : k = Kl g₀ V₀)
    (hn : n = Nl g₀ V₀) (hz : ¬ k = 0)
    (hg : g = { g₀ with
      rax := a, rcx := c, rdx := d, rbx := b, rsp := g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64, rbp := g₀.rsi,
      rsi := si, rdi := di, r8 := x8, r9 := x9, r10 := x10, r11 := x11, r12 := g₀.rdx,
      r13 := BitVec.setWidth 64 k, r14 := BitVec.setWidth 64 n, r15 := g₀.rdi }) :
    Nx A g₀ V₀ m 45 g fl V := by
  subst hk hn
  exact x45 hm hK hA (pos32 hz) ⟨a, d, si, di, b, c, x8, x9, x10, x11, hg⟩

end X

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn} {D : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}
  {Tf Td Ti Ts : Gprs → (Addr → Byte) → Prop}

set_option maxHeartbeats 2000000 in
/-- The entry: the `push`es, the loads of the lengths; `K` = 0 to the epilogue, equal lengths to `strcmp`. -/
theorem vc_0 (hF : Fr F Wl g₀.rsp) (hd : Fdat F g₀) (hAi : AIns A g₀.rsp) (hA : A V₀) :
    W_0 F Wl (Nx A g₀ V₀ 42949672990) g₀ f V₀ := by
  have hK : Fmm g₀ V₀ (Vp g₀ V₀) := fun _ _ _ => rfl
  have hA' : A (Vp g₀ V₀) := a_vp hF.lo hAi hA
  have hk : rdd(Vp g₀ V₀, g₀.rsi + 8#64) = Kl g₀ V₀ := rd_vp hF.lo hd.ok
  have hn : rdd(Vp g₀ V₀, g₀.rdx + 8#64) = Nl g₀ V₀ := rd_vp hF.lo hd.on
  obtain ⟨-, -, w1, w2, w3, w4, w5, w6, -, -, -, -, -, -, -, -⟩ := hF
  obtain ⟨-, k8, n8, q1, q2, -, -, -, -, -⟩ := hd
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at w1 w2 w3 w4 w5 w6 k8 n8 q1 q2
  wpx [W_0, W_27, W_136, o0, o1, o10, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne]
  all_goals repeat' (first
    | with_reducible exact w1
    | with_reducible exact w2
    | with_reducible exact w3
    | with_reducible exact w4
    | with_reducible exact w5
    | with_reducible exact w6
    | with_reducible exact k8
    | with_reducible exact n8
    | with_reducible exact q1
    | with_reducible exact q2
    | apply And.intro
    | intro)
  all_goals first
    | exact x118 (by omega) hK hA' rfl
    | exact x143z (by omega) hK hA' hk hn (by assumption) rfl
    | exact x45z (by omega) hK hA' hk hn (by assumption) rfl

set_option maxHeartbeats 1000000 in
/-- `p`'s length: 0 to the epilogue, else `Find` from 0. -/
theorem vc_45 (hd : Fdat F g₀) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat) (h : I45 g₀ V₀ g) :
    W_45 F Wl (Nx A g₀ V₀ 42949672980) g f V := by
  obtain ⟨a, d, si, di, b, c, x8, x9, x10, x11, rfl⟩ := h
  have hl := ln_lt g₀.rdi V
  wpx [W_45, W_53, o2, o3, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, BitVec.xor_self]
  refine ⟨hd.p8, fun af => ⟨fun _ => x118 (by omega) hK hA rfl, fun h1 af1 => ?_⟩⟩
  have hL : 0 < Lnp g₀.rdi V := pos32 h1
  exact x100 (D := Lnp g₀.rdi V) (by omega) hK hA hk
    ⟨_, by exact hL, by exact (Nat.zero_add _).symm, _, _, _, _, _, _, _, _, _, rfl⟩

set_option maxHeartbeats 1000000 in
/-- The arguments of `Find`. -/
theorem vc_100 (hd : Fdat F g₀) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I100 g₀ V₀ D V g) : W_100 F Wl (Nx A g₀ V₀ (10 * D + 9)) g f V := by
  obtain ⟨pos, hp, hD, a, si, di, b, c, x8, x9, x10, x11, rfl⟩ := h
  wpx [W_100, o7]
  exact ⟨hd.q1, x107 (by omega) hK hA hk ⟨pos, hp, hD, a, b, c, x8, x9, x10, x11, rfl⟩⟩

set_option maxHeartbeats 1000000 in
/-- `Find`'s result: negative to the epilogue, else the arguments of `Delete`. -/
theorem vc_112 (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat) (h : I112 g₀ V₀ D V g) :
    W_112 F Wl (Nx A g₀ V₀ (10 * D + 7)) g f V := by
  obtain ⟨a, d, si, di, b, ⟨c, x8, x9, x10, x11, rfl⟩, hr⟩ := h
  wpx [W_112, W_64, o8, o4, BitVec.and_self, Bool.not_eq_true', Bool.not_eq_false']
  intro af
  refine ⟨fun h1 => ?_, fun _ => x118 (by omega) hK hA rfl⟩
  rcases hr with h2 | ⟨h2, h3⟩
  · simp [h2] at h1
  · exact x72 (by omega) hK hA hk ⟨_, h2, h3, a, c, x8, x9, x10, x11, rfl⟩

set_option maxHeartbeats 1000000 in
/-- The arguments of `Insert`. -/
theorem vc_77 (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat) (h : I77 g₀ V₀ D V g) :
    W_77 F Wl (Nx A g₀ V₀ (10 * D + 5)) g f V := by
  obtain ⟨r, h1, h2, a, d, si, di, c, x8, x9, x10, x11, rfl⟩ := h
  wpx [W_77, o5]
  exact x85 (by omega) hK hA hk ⟨r, h1, h2, a, c, x8, x9, x10, x11, rfl⟩

set_option maxHeartbeats 1000000 in
/-- `pos += N`; out if not below `p`'s length, else `Find` again. -/
theorem vc_90 (hd : Fdat F g₀) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I90 g₀ V₀ D V g) : W_90 F Wl (Nx A g₀ V₀ (10 * D + 3)) g f V := by
  obtain ⟨r, h1, h2, a, d, si, di, c, x8, x9, x10, x11, rfl⟩ := h
  wpx [W_90, o6, Op.cmpmr, sw_add]
  refine ⟨hd.p8, fun _ => x118 (by omega) hK hA rfl, fun h3 => ?_⟩
  obtain ⟨hp, hD, hm⟩ := step90 (L := rdd(V, g₀.rdi + 8#64)) h1 h2 hk h3
  exact x100 hm hK hA hk ⟨r + Nl g₀ V₀, hp, hD, _, _, _, _, _, _, _, _, _, rfl⟩

set_option maxHeartbeats 1000000 in
/-- The epilogue: the `pop`s. -/
theorem vc_118 (hF : Fr F Wl g₀.rsp) (hK : Fmm g₀ V₀ V) (hA : A V)
    (h : g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8#64) : W_118 F Wl (Nx A g₀ V₀ 2) g f V := by
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := pops hF.lo hK
  have d1 := hF.d1
  have d2 := hF.d2
  have d3 := hF.d3
  have d4 := hF.d4
  have d5 := hF.d5
  have d6 := hF.d6
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h
  subst h
  wpx [W_118, o9, BitVec.sub_add_cancel, q1, q2, q3, q4, q5, q6]
  all_goals repeat' (first
    | with_reducible exact d1
    | with_reducible exact d2
    | with_reducible exact d3
    | with_reducible exact d4
    | with_reducible exact d5
    | with_reducible exact d6
    | apply And.intro
    | intro)
  all_goals exact xF hK hA (Or.inl rfl) ⟨_, _, _, _, _, _, _, _, _, rfl⟩

set_option maxHeartbeats 1000000 in
/-- After `strcmp`: not equal to 45, else the epilogue. -/
theorem vc_148 (hF : Fr F Wl g₀.rsp) (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat)
    (h : I45 g₀ V₀ g) : W_148 F Wl (Nx A g₀ V₀ 42949672981) g f V := by
  obtain ⟨a, d, si, di, b, c, x8, x9, x10, x11, rfl⟩ := h
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := pops hF.lo hK
  have d1 := hF.d1
  have d2 := hF.d2
  have d3 := hF.d3
  have d4 := hF.d4
  have d5 := hF.d5
  have d6 := hF.d6
  wpx [W_148, W_152, o11, o9, BitVec.and_self, BitVec.sub_add_cancel, q1, q2, q3, q4, q5, q6]
  all_goals repeat' (first
    | with_reducible exact d1
    | with_reducible exact d2
    | with_reducible exact d3
    | with_reducible exact d4
    | with_reducible exact d5
    | with_reducible exact d6
    | apply And.intro
    | intro)
  all_goals first
    | exact x45 (by omega) hK hA hk ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
    | exact xF hK hA (Or.inr rfl) ⟨_, _, _, _, _, _, _, _, _, rfl⟩

/-- `strcmp` of the characters, at equal lengths. -/
theorem vc_143 (hF : Fr F Wl g₀.rsp) (hd : Fdat F g₀) (hAi : AIns A g₀.rsp) (hT : TOk A g₀ Tf Td Ti Ts)
    (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat) (h : I143 g₀ V₀ V g) :
    CallK Wl rpl_at 148 Ts RScm (Nx A g₀ V₀ 42949672982) g f V := by
  obtain ⟨a, d, b, c, x8, x9, x10, x11, rfl⟩ := h
  have := g₀.rsp.isLt
  have e8 := s_8 _ hF.lo
  dsimp only [CallK]
  refine ⟨hF.w8, by omega, hT.scm _ _ rfl (rd_st hF.lo hd.oq1 V _).symm (rd_st hF.lo hd.oq2 V _).symm
    (a_st hF.lo hAi hA _), ?_⟩
  rintro g' V' ⟨rfl, a', c', d', si', di', y8, y9, y10, y11, rfl⟩ fl
  simp only [set4, BitVec.sub_add_cancel]
  exact x148 (by omega) (fm_st hF.lo hK _) (a_st hF.lo hAi hA _) hk
    ⟨a', d', si', di', b, c', y8, y9, y10, y11, rfl⟩

/-- `Find`. -/
theorem vc_107 (hF : Fr F Wl g₀.rsp) (hd : Fdat F g₀) (hAi : AIns A g₀.rsp) (hT : TOk A g₀ Tf Td Ti Ts)
    (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat) (h : I107 g₀ V₀ D V g) :
    CallK Wl rpl_at 112 Tf (RFnd g₀.rdi (Kl g₀ V₀)) (Nx A g₀ V₀ (10 * D + 8)) g f V := by
  obtain ⟨pos, hp, hD, a, b, c, x8, x9, x10, x11, rfl⟩ := h
  have := g₀.rsp.isLt
  have e8 := s_8 _ hF.lo
  have eL := ln_st hF.lo hd.op V (Addr.add rpl_at 112)
  dsimp only [CallK]
  refine ⟨hF.w8, by omega, hT.fnd _ _ rfl rfl (rd_st hF.lo hd.oq1 V _).symm ?_ (a_st hF.lo hAi hA _), ?_⟩
  · simp only [set4, sw_64_32, eL]
    exact hp
  rintro g' V' ⟨rfl, ⟨a', c', d', si', di', y8, y9, y10, y11, rfl⟩, hr⟩ fl
  simp only [set4, BitVec.sub_add_cancel, sw_64_32] at hr ⊢
  rw [← eL] at hD
  refine x112 (D := D) (by omega) (fm_st hF.lo hK _) (a_st hF.lo hAi hA _) hk
    ⟨a', d', si', di', b, ⟨c', y8, y9, y10, y11, rfl⟩, ?_⟩
  rcases hr with h1 | ⟨h1, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, by omega⟩

/-- `Delete (pos, K)`. -/
theorem vc_72 (hF : Fr F Wl g₀.rsp) (hd : Fdat F g₀) (hAi : AIns A g₀.rsp) (hT : TOk A g₀ Tf Td Ti Ts)
    (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat) (h : I72 g₀ V₀ D V g) :
    CallK Wl rpl_at 77 Td (RDel g₀.rdi A) (Nx A g₀ V₀ (10 * D + 6)) g f V := by
  obtain ⟨r, h1, h2, a, c, x8, x9, x10, x11, rfl⟩ := h
  have := g₀.rsp.isLt
  have e8 := s_8 _ hF.lo
  have eL := ln_st hF.lo hd.op V (Addr.add rpl_at 77)
  dsimp only [CallK]
  refine ⟨hF.w8, by omega, hT.del _ _ rfl rfl ?_ (a_st hF.lo hAi hA _), ?_⟩
  · simp only [set4, sw_64_32, eL]
    exact h1
  rintro g' V' ⟨hfk, ⟨a', c', d', si', di', y8, y9, y10, y11, rfl⟩, hA', hl⟩ fl
  simp only [set4, BitVec.sub_add_cancel, sw_64_32, eL] at hl ⊢
  exact x77 (D := D) (by omega) (fm_fk hF.lo (fm_st hF.lo hK _) hfk rfl) hA' hk
    ⟨r, by omega, by omega, a', d', si', di', c', y8, y9, y10, y11, rfl⟩

/-- `Insert (pos, q₂)`. -/
theorem vc_85 (hF : Fr F Wl g₀.rsp) (hd : Fdat F g₀) (hAi : AIns A g₀.rsp) (hT : TOk A g₀ Tf Td Ti Ts)
    (hK : Fmm g₀ V₀ V) (hA : A V) (hk : 0 < (Kl g₀ V₀).toNat) (h : I85 g₀ V₀ D V g) :
    CallK Wl rpl_at 90 Ti (RIns g₀.rdi (Nl g₀ V₀) A) (Nx A g₀ V₀ (10 * D + 4)) g f V := by
  obtain ⟨r, h1, h2, a, c, x8, x9, x10, x11, rfl⟩ := h
  have := g₀.rsp.isLt
  have e8 := s_8 _ hF.lo
  have eL := ln_st hF.lo hd.op V (Addr.add rpl_at 90)
  dsimp only [CallK]
  refine ⟨hF.w8, by omega, hT.ins _ _ rfl rfl rfl ?_ (a_st hF.lo hAi hA _), ?_⟩
  · simp only [set4, sw_64_32, eL]
    exact h1
  rintro g' V' ⟨hfk, ⟨a', c', d', si', di', y8, y9, y10, y11, rfl⟩, hA', hl⟩ fl
  simp only [set4, BitVec.sub_add_cancel, eL] at hl ⊢
  exact x90 (D := D) (by omega) (fm_fk hF.lo (fm_st hF.lo hK _) hfk rfl) hA' hk
    ⟨r, by omega, by omega, a', d', si', di', c', y8, y9, y10, y11, rfl⟩

/-! ## The run -/

/-- The cut points' conditions, the calls' from the callees'. -/
def WtC (F : Footprint) (Wl : List Rgn) (Tf Td Ti Ts : Gprs → (Addr → Byte) → Prop)
    (Rf Rd Ri Rs : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop) (ℓ : Nat) :
    Post → Gprs → Rflags → (Addr → Byte) → Prop :=
  if ℓ = 72 then CallK Wl rpl_at 77 Td Rd else
  if ℓ = 85 then CallK Wl rpl_at 90 Ti Ri else
  if ℓ = 107 then CallK Wl rpl_at 112 Tf Rf else
  if ℓ = 143 then CallK Wl rpl_at 148 Ts Rs else
  Wt ℓ F Wl

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {Rf Rd Ri Rs : Gprs → (Addr → Byte) → Gprs → (Addr → Byte) → Prop} {cf cd ci cs : List Byte}

theorem spC (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rpl_at rpl)
    (hinF : CodeIn L fnd_at cf) (hlF : 0 < cf.length) (hFn : FnK prof F Wl L s₀ o fnd_at Tf Rf)
    (hinD : CodeIn L del_at cd) (hlD : 0 < cd.length) (hDl : FnK prof F Wl L s₀ o del_at Td Rd)
    (hinI : CodeIn L ins_at ci) (hlI : 0 < ci.length) (hIn : FnK prof F Wl L s₀ o ins_at Ti Ri)
    (hinS : CodeIn L scm_at cs) (hlS : 0 < cs.length) (hSc : FnK prof F Wl L s₀ o scm_at Ts Rs) (ℓ : Nat) :
    SpAt prof F Wl L s₀ o rpl_at ℓ (WtC F Wl Tf Td Ti Ts Rf Rd Ri Rs ℓ) := by
  by_cases e72 : ℓ = 72
  · subst e72
    exact SpAt.callK c hin (lt_len (by decide)) (cl72 _) hinD hlD tg72 hDl
  by_cases e85 : ℓ = 85
  · subst e85
    exact SpAt.callK c hin (lt_len (by decide)) (cl85 _) hinI hlI tg85 hIn
  by_cases e107 : ℓ = 107
  · subst e107
    exact SpAt.callK c hin (lt_len (by decide)) (cl107 _) hinF hlF tg107 hFn
  by_cases e143 : ℓ = 143
  · subst e143
    exact SpAt.callK c hin (lt_len (by decide)) (cl143 _) hinS hlS tg143 hSc
  have e : WtC F Wl Tf Td Ti Ts Rf Rd Ri Rs ℓ = Wt ℓ F Wl := by
    simp only [WtC, e72, e85, e107, e143, ↓reduceIte]
  rw [e]
  exact (spAll prof ℓ).at c hin

theorem vcAll (hF : Fr F Wl g₀.rsp) (hd : Fdat F g₀) (hAi : AIns A g₀.rsp) (hA₀ : A V₀)
    (hT : TOk A g₀ Tf Td Ti Ts) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv A g₀ V₀ ℓ n g V) :
    WtC F Wl Tf Td Ti Ts (RFnd g₀.rdi (Kl g₀ V₀)) (RDel g₀.rdi A) (RIns g₀.rdi (Nl g₀ V₀) A) RScm ℓ
      (Nx A g₀ V₀ n) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hK, hA, ⟨rfl, rfl, h⟩ | ⟨hk, ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨D, ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ |
    ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩⟩⟩⟩
  · exact vc_0 hF hd hAi hA₀
  · exact vc_118 hF hK hA h
  · exact vc_143 (f := f) hF hd hAi hT hK hA hk h
  · exact vc_148 hF hK hA hk h
  · exact vc_45 hd hK hA hk h
  · exact vc_100 hd hK hA hk h
  · exact vc_107 (f := f) hF hd hAi hT hK hA hk h
  · exact vc_112 hK hA hk h
  · exact vc_72 (f := f) hF hd hAi hT hK hA hk h
  · exact vc_77 hK hA hk h
  · exact vc_85 (f := f) hF hd hAi hT hK hA hk h
  · exact vc_90 hd hK hA hk h

variable {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- `AString::Replace (q₁, q₂)` of the string at `p` from its entry to the return address, the callees
hypotheses: the bytes from 56 below the return address through it as after the `push`es (the return address as at
the entry), `A` of the bytes; `rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`..`r11` changed. -/
theorem rpl_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rpl_at rpl) (hK : KeptW Wl s₀ X)
    (hAg : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rpl_at) (hF : Fr F Wl X.cpu.gpr.rsp)
    (hd : Fdat F X.cpu.gpr) (hAi : AIns A X.cpu.gpr.rsp) (hA : A V) (hT : TOk A X.cpu.gpr Tf Td Ti Ts)
    (hinF : CodeIn L fnd_at cf) (hlF : 0 < cf.length)
    (hFn : FnK prof F Wl L s₀ o fnd_at Tf (RFnd X.cpu.gpr.rdi (Kl X.cpu.gpr V)))
    (hinD : CodeIn L del_at cd) (hlD : 0 < cd.length) (hDl : FnK prof F Wl L s₀ o del_at Td (RDel X.cpu.gpr.rdi A))
    (hinI : CodeIn L ins_at ci) (hlI : 0 < ci.length)
    (hIn : FnK prof F Wl L s₀ o ins_at Ti (RIns X.cpu.gpr.rdi (Nl X.cpu.gpr V) A))
    (hinS : CodeIn L scm_at cs) (hlS : 0 < cs.length) (hSc : FnK prof F Wl L s₀ o scm_at Ts RScm)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ → Fmm X.cpu.gpr V V' → A V' →
      (∃ a c d si di x8 x9 x10 x11, Z.cpu.gpr = { X.cpu.gpr with
                                                  rax := a, rcx := c, rdx := d, rsi := si, rdi := di,
                                                  r8 := x8, r9 := x9, r10 := x10,
                                                  r11 := x11 }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine cfgAt (spC c hin hinF hlF hFn hinD hlD hDl hinI hlI hIn hinS hlS hSc)
    (fun ℓ n g _ V' => Inv A X.cpu.gpr V ℓ n g V') (fun j g _ V' => Fin A X.cpu.gpr V j g V')
    (fun ℓ n g f V' h => vcAll hF hd hAi hA hT ℓ n g f V' h) ?_
    42949672990 0 hK hAg (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨hK', hA', hj, a, c', d', si, di, x8, x9, x10, x11, rfl⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hra' : rdq(V', Y.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [hsY, fm_ra hF.lo hF.hi hK']
    exact hra
  obtain ⟨hjl, hdj⟩ := ret_at prof.feat hj
  refine c.s_ret hKY hAY hin hjl hrY hdj (by rw [hsY]; exact hF.d0) hin₂ h₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' hKZ hAZ hrZ hK' hA' ⟨a, c', d', si, di, x8, x9, x10, x11, by rw [hgZ, hsY, hgY]⟩

end FV7z.Rpl
