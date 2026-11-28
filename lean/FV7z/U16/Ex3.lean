import FV7z.U16.Ex2
/-!
# `Utf8_To_Utf16`: a form's end (PLAN.md §M, M1)

`v192` (the bytes left: none, so the escape test on the kept flag bit `rdFl`, then 392, 109 or 141; else 201), `v201`
(the next byte), `v272` (a form that fails: `rdx` past the lead byte or the bytes read), `v392` (a whole form's one or
two characters). Tests on the loop's registers go through `sw_64_32` by `Eq.trans` (defeq on `Gu`'s fields), never by
rewriting a hypothesis.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16

local notation:max "w64(" x ")" => BitVec.setWidth 64 x
local notation:max "w32(" x ")" => BitVec.setWidth 32 x

theorem nzq {x : BitVec 64} (h : (!zq x) = true) : x ≠ 0 := fun e => by
  subst e; exact absurd h (by decide)
theorem z0 {ms : Nat} (h : ms ≤ 2) : zr w32(w64(BitVec.ofNat 32 ms)) = decide (ms = 0) := by
  rcases (by omega : ms = 0 ∨ ms = 1 ∨ ms = 2) with rfl | rfl | rfl <;> decide
theorem r272 {s p : BitVec 64} {e j : Nat} (he : e ≤ 3) (hs : w32(s) = BitVec.ofNat 32 e) :
    w64(w32(s)) + (p + BitVec.ofNat 64 j) = p + BitVec.ofNat 64 (j + e) := by
  rw [hs, ske he, BitVec.add_comm (BitVec.ofNat 64 e), ← addK]

variable {F : Footprint} {Wl : List Rgn} {g₀ : Gprs} {V₀ : Addr → Byte} {n W k c : Nat} {f : Rflags}
  {V : Addr → Byte}

theorem tsA (pr : Pr F Wl g₀ n W) {c i : Nat} (h1 : i < c) (h2 : c ≤ 60) :
    (Addr.add (g₀.rsp - BitVec.ofNat 64 c) i).toNat = g₀.rsp.toNat - c + i := by
  have hs := pr.sp
  have hl := g₀.rsp.isLt
  have e0 : (g₀.rsp - BitVec.ofNat 64 c).toNat = g₀.rsp.toNat - c := ts (by omega)
  rw [← e0]; exact tA (by omega)
theorem fsrk (pr : Pr F Wl g₀ n W) {c m : Nat} (h1 : m ≤ c) (h2 : c ≤ 60) :
    ∀ i < m, Foot F.data (Addr.add (g₀.rsp - BitVec.ofNat 64 c) i) := by
  intro i hi
  have hs := pr.sp
  have e := tsA pr (c := c) (i := i) (by omega) h2
  exact pr.fsr _ (by omega) (by omega)

/-- The flag bit kept at `rsp - 60`. -/
theorem rdFl (pr : Pr F Wl g₀ n W) (hF : FR g₀ V₀ W V) :
    rdd(V, S6 g₀.rsp + 18446744073709551604#64) = Fl g₀ &&& 4#32 := by
  refine Eq.trans (congrArg (ofBytesLE 32) (rdF hF fun i hi => ?_)) (vs1_fl (V := V₀) pr.sp)
  rw [k60, tsA pr (c := 60) (i := i) (by omega) (Nat.le_refl 60)]
  have := pr.sDS; have := pr.sp; omega

theorem fD8 (pr : Pr F Wl g₀ n W) (h : 4 * c + 8 ≤ W) :
    ∀ i < 4, Foot Wl (Addr.add (g₀.rdi + BitVec.ofNat 64 c * 4#64 + 4#64) i) := by
  intro i hi
  have h0 := pr.fw (4 * c + 4 + i) (by omega) 0 (by omega)
  rw [addr_add_zero, addK] at h0
  rw [m4, ad4]; exact h0
theorem frD8 (pr : Pr F Wl g₀ n W) (h : 4 * c + 8 ≤ W) (hF : FR g₀ V₀ W V) (w₁ w₂ : BitVec 32) :
    FR g₀ V₀ W (Vst (Vst V (g₀.rdi + BitVec.ofNat 64 c * 4#64) (toBytesLE w₁ 4))
      (g₀.rdi + BitVec.ofNat 64 c * 4#64 + 4#64) (toBytesLE w₂ 4)) := by
  rw [m4, ad4]; exact frS pr.dT (frS pr.dT hF (by omega) w₁) (by omega) w₂

/-! ## The cut points -/

theorem v392 {e q : Nat} {dd : BitVec 32} {a cx bp i x : BitVec 64} (pr : Pr F Wl g₀ n W) (hB : Bud g₀ V₀ n W)
    (hq : (big dd = true ∧ q = 2) ∨ (big dd = false ∧ q = 1)) (he1 : 1 ≤ e) (he3 : e ≤ 3) (hk : k + 1 + e ≤ n)
    (hc : c + q + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_392 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 8))
      (Gu g₀ a cx (w64(dd)) bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c))
      f V := by
  have q2 : big w32(w64(dd)) = true → q = 2 := fun h => by
    rw [sw_64_32] at h
    rcases hq with ⟨_, hq⟩ | ⟨h', _⟩
    · exact hq
    · rw [h] at h'; exact absurd h' (by decide)
  have q1 : big w32(w64(dd)) = false → q = 1 := fun h => by
    rw [sw_64_32] at h
    rcases hq with ⟨h', _⟩ | ⟨_, hq⟩
    · rw [h] at h'; exact absurd h' (by decide)
    · exact hq
  refine vc_392 (fun h hz fl => ?_) (fun h hz => ?_) (fun h hz => ?_) (fun h hz fl a' d' w₁ w₂ => ?_)
    (fun h hz fl => ?_) (fun h hz => ?_) (fun h hz fl w => ?_)
  · obtain rfl := q2 h
    exact i10 (Or.inl ⟨rfl, rfl, rfl⟩) he1 he3 hk (by omega) hc hF
  · obtain rfl := q2 h
    have := hB (zqf hz)
    exact fD pr (by omega)
  · obtain rfl := q2 h
    have := hB (zqf hz)
    exact fD8 pr (by omega)
  · obtain rfl := q2 h
    have := hB (zqf hz)
    exact i10 (Or.inl ⟨rfl, rfl, rfl⟩) he1 he3 hk (by omega) hc (frD8 pr (by omega) hF w₁ w₂)
  · obtain rfl := q1 h
    exact i10 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) he1 he3 hk (by omega) hc hF
  · obtain rfl := q1 h
    have := hB (zqf hz)
    exact fD pr (by omega)
  · obtain rfl := q1 h
    have := hB (zqf hz)
    exact i10 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) he1 he3 hk (by omega) hc (frD pr (by omega) hF w)

theorem v272 {e : Nat} {a cx d bp s i x : BitVec 64} (pr : Pr F Wl g₀ n W) (hB : Bud g₀ V₀ n W) (he : e ≤ 3)
    (hk : k + 1 + e ≤ n) (hc : c + Rm g₀ V₀ n k (.err e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V)
    (hs : w32(s) = BitVec.ofNat 32 e) :
    W_272 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 8))
      (Gu g₀ a cx d bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  refine vc_272 (fun h hz fl bp' => ?_) (fun h hz fl bp' => ?_) (fun h hz fl bp' => ?_) (fun h hz fl bp' => ?_)
  · have h2 : Z2 g₀ = true := (congrArg zr (sw_64_32 (Fl g₀ &&& 2#32))).symm.trans h
    rw [rm_e1 h2] at hc
    rw [r272 (p := g₀.rdx) (j := k + 1) he hs]
    exact i8 (Or.inl ⟨rfl, rfl, nzq hz⟩) hk (by omega) (by omega) hF
  · have h2 : Z2 g₀ = true := (congrArg zr (sw_64_32 (Fl g₀ &&& 2#32))).symm.trans h
    rw [rm_e1 h2] at hc
    rw [r272 (p := g₀.rdx) (j := k + 1) he hs]
    exact i8 (Or.inr ⟨rfl, rfl⟩) hk (by omega) (by omega) hF
  · have h2 : Z2 g₀ = false := (congrArg zr (sw_64_32 (Fl g₀ &&& 2#32))).symm.trans h
    rw [rm_e2 h2] at hc
    exact i8 (Or.inr ⟨rfl, rfl⟩) (by omega) (by omega) (by omega) hF
  · have h2 : Z2 g₀ = false := (congrArg zr (sw_64_32 (Fl g₀ &&& 2#32))).symm.trans h
    rw [rm_e2 h2] at hc
    exact i8 (Or.inl ⟨rfl, rfl, zqf hz⟩) (by omega) (by omega) (by omega) hF

theorem v201 {j ms e : Nat} {dd : BitVec 32} {a bp : BitVec 64} (hj : ms + e + 1 = j) (hj3 : j ≤ 3)
    (hk : k + 1 + e < n) (hms : ms ≠ 0)
    (hc : c + Rm g₀ V₀ n k (if ms = 0 then .ok dd (e + 1) else Ib g₀ V₀ n k j (ms - 1) (e + 1) dd) = NN g₀ V₀ n)
    (hF : FR g₀ V₀ W V) :
    W_201 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 21 - 5 * e))
      (Gu g₀ a (w64(128#32 >>> j)) (w64(dd)) bp (w64(BitVec.ofNat 32 (e + 1))) (g₀.rdx + BitVec.ofNat 64 (k + 1 + e))
        (w64(BitVec.ofNat 32 ms)) (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  refine vc_201 fun fl => ?_
  have e2 : w64(w32(w64(BitVec.ofNat 32 ms)) - 1#32) = w64(BitVec.ofNat 32 (ms - 1)) := by
    rcases (by omega : ms = 1 ∨ ms = 2) with rfl | rfl <;> decide
  have e3 : k + 1 + e + 1 = k + 1 + (e + 1) := by omega
  rw [if_neg hms] at hc
  rw [e2, adv1, e3]
  exact i5 (ms := ms - 1) (e := e + 1) (by omega) hj3 (by omega) (by omega) hc hF

/-- 392 from a whole form's value (`fin`'s `.ok` without an escape). -/
theorem x392 {e : Nat} {dd : BitVec 32} {μ : Nat} {fl : Rflags} {a cx bp i x : BitVec 64} (hk : k + 1 + e < n)
    (he : e ≤ 2) (hz : (!Z4 g₀ && esc dd) = false) (hc : c + Rm g₀ V₀ n k (.ok dd (e + 1)) = NN g₀ V₀ n)
    (hF : FR g₀ V₀ W V) (hμ : 30 * (n - k) + 8 < μ) :
    Nx g₀ V₀ n W μ 392 (Gu g₀ a cx (w64(dd)) bp (w64(BitVec.ofNat 32 (e + 1))) i x (g₀.rdx + BitVec.ofNat 64 (k + 1))
      (BitVec.ofNat 64 c)) fl V := by
  cases hbg : big dd
  · rw [rm_ok1 hz hbg] at hc
    exact i9 (Or.inr ⟨hbg, rfl⟩) (by omega) (by omega) (by omega) hμ (by omega) hF
  · rw [rm_ok2 hz hbg] at hc
    exact i9 (Or.inl ⟨hbg, rfl⟩) (by omega) (by omega) (by omega) hμ (by omega) hF

theorem v192 {j ms e : Nat} {dd : BitVec 32} {a bp : BitVec 64} (pr : Pr F Wl g₀ n W) (hB : Bud g₀ V₀ n W)
    (hj : ms + e + 1 = j) (hj3 : j ≤ 3) (hk : k + 1 + e < n)
    (hc : c + Rm g₀ V₀ n k (if ms = 0 then .ok dd (e + 1) else Ib g₀ V₀ n k j (ms - 1) (e + 1) dd) = NN g₀ V₀ n)
    (hF : FR g₀ V₀ W V) :
    W_192 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 22 - 5 * e))
      (Gu g₀ a (w64(128#32 >>> j)) (w64(dd)) bp (w64(BitVec.ofNat 32 (e + 1))) (g₀.rdx + BitVec.ofNat 64 (k + 1 + e))
        (w64(BitVec.ofNat 32 ms)) (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  have hz0 := z0 (ms := ms) (by omega)
  have hfl := rdFl pr hF
  have hsd : w32(w64(dd)) = dd := sw_64_32 dd
  refine vc_192 (fun _ => ?_) (fun h h4 fl a' => ?_) (fun h h4 hs hz fl a' => ?_) (fun h h4 hs hz fl a' => ?_)
    (fun h h4 hs fl a' => ?_) (fun h fl => ?_)
  · show ∀ i < 4, Foot F.data (Addr.add (S6 g₀.rsp + 18446744073709551604#64) i)
    rw [k60]; exact fsrk pr (by omega) (by omega)
  · obtain rfl : ms = 0 := of_decide_eq_true (hz0.symm.trans h)
    have hz4 : Z4 g₀ = true := (congrArg zr hfl).symm.trans h4
    rw [if_pos (rfl : (0 : Nat) = 0)] at hc
    exact x392 hk (by omega) (by simp [hz4]) hc hF (by omega)
  · obtain rfl : ms = 0 := of_decide_eq_true (hz0.symm.trans h)
    have hz4 : Z4 g₀ = false := (congrArg zr hfl).symm.trans h4
    have he : esc dd = true := (congrArg esc hsd).symm.trans hs
    have hx : (!Z4 g₀ && esc dd) = true := by simp [hz4, he]
    rw [if_pos (rfl : (0 : Nat) = 0), rm_esc hx] at hc
    exact i3 (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by omega) hF
  · obtain rfl : ms = 0 := of_decide_eq_true (hz0.symm.trans h)
    have hz4 : Z4 g₀ = false := (congrArg zr hfl).symm.trans h4
    have he : esc dd = true := (congrArg esc hsd).symm.trans hs
    have hx : (!Z4 g₀ && esc dd) = true := by simp [hz4, he]
    rw [if_pos (rfl : (0 : Nat) = 0), rm_esc hx] at hc
    exact i3 (Or.inr ⟨rfl, rfl, zqf hz⟩) (by omega) (by omega) (by omega) hF
  · obtain rfl : ms = 0 := of_decide_eq_true (hz0.symm.trans h)
    have hz4 : Z4 g₀ = false := (congrArg zr hfl).symm.trans h4
    have he : esc dd = false := (congrArg esc hsd).symm.trans hs
    rw [if_pos (rfl : (0 : Nat) = 0)] at hc
    exact x392 hk (by omega) (by simp [hz4, he]) hc hF (by omega)
  · have hms : ms ≠ 0 := of_decide_eq_false (hz0.symm.trans h)
    exact i6 (Or.inr ⟨rfl, rfl⟩) hj hj3 hk (fun _ => hms) (by omega) hc hF

end FV7z.U16
