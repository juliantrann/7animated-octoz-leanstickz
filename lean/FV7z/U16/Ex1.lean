import FV7z.U16.Inv
/-!
# `Utf8_To_Utf16`: the plain cut points (PLAN.md §M, M1)

`v109`, `v116`, `v141`, `v295`, `v299`, `v409`, `v413`, `v492`: each `W_ℓ` from `Inv`'s facts at `ℓ`, the exits to
`Nx` with a smaller measure (`i2`–`i11`). Helpers: the count in `r11` (`oc`, `oc2`), the end test (`dk`, `dk'`, `dkn`,
`dkn'`), a character's store (`fD`, `frD`), `ske` (`esi` as a 64-bit count).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16

local notation:max "w64(" x ")" => BitVec.setWidth 64 x
local notation:max "w32(" x ")" => BitVec.setWidth 32 x

theorem oc (c : Nat) : BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) := (BitVec.ofNat_add c 1).symm
theorem oc2 (c : Nat) : BitVec.ofNat 64 c + 2#64 = BitVec.ofNat 64 (c + 2) := (BitVec.ofNat_add c 2).symm
theorem ske {e : Nat} (h : e ≤ 3) : w64(BitVec.ofNat 32 e) = BitVec.ofNat 64 e := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3) with rfl | rfl | rfl | rfl <;> decide

variable {F : Footprint} {Wl : List Rgn} {g₀ : Gprs} {V₀ : Addr → Byte} {n W k c : Nat} {f : Rflags}
  {V : Addr → Byte}

/-! ## The end test (`rdx` against `srcLim` in `r10`) -/

theorem dk (pr : Pr F Wl g₀ n W) (hk : k ≤ n) (h : decide (g₀.rdx + BitVec.ofNat 64 k = g₀.rcx) = true) : k = n :=
  pinj1 pr.pn hk (Nat.le_refl n) ((of_decide_eq_true h).trans pr.lim)
theorem dk' (pr : Pr F Wl g₀ n W) (hk : k ≤ n) (h : decide (g₀.rdx + BitVec.ofNat 64 k = g₀.rcx) = false) :
    k < n :=
  Nat.lt_of_le_of_ne hk fun e => by
    subst e
    exact Bool.false_ne_true (h.symm.trans (decide_eq_true pr.lim.symm))
theorem dkn (pr : Pr F Wl g₀ n W) (hk : k ≤ n) (h : (!decide (g₀.rdx + BitVec.ofNat 64 k = g₀.rcx)) = true) :
    k < n := by
  cases hb : decide (g₀.rdx + BitVec.ofNat 64 k = g₀.rcx)
  · exact dk' pr hk hb
  · rw [hb] at h; exact absurd h (by decide)
theorem dkn' (pr : Pr F Wl g₀ n W) (hk : k ≤ n) (h : (!decide (g₀.rdx + BitVec.ofNat 64 k = g₀.rcx)) = false) :
    k = n := by
  cases hb : decide (g₀.rdx + BitVec.ofNat 64 k = g₀.rcx)
  · rw [hb] at h; exact absurd h (by decide)
  · exact dk pr hk hb

/-! ## A character's store at `dest + 4c` -/

theorem fD (pr : Pr F Wl g₀ n W) (h : 4 * c + 4 ≤ W) :
    ∀ i < 4, Foot Wl (Addr.add (g₀.rdi + BitVec.ofNat 64 c * 4#64) i) := by
  intro i hi
  have h0 := pr.fw (4 * c + i) (by omega) 0 (by omega)
  rw [addr_add_zero, addK] at h0
  rw [m4]; exact h0
theorem frD (pr : Pr F Wl g₀ n W) (h : 4 * c + 4 ≤ W) (hF : FR g₀ V₀ W V) (w : BitVec 32) :
    FR g₀ V₀ W (Vst V (g₀.rdi + BitVec.ofNat 64 c * 4#64) (toBytesLE w 4)) := by
  rw [m4]; exact frS pr.dT hF h w

/-! ## The cut points -/

theorem v109 {a cx d bp s i x : BitVec 64} (hk : k < n) (hc : c + 1 + Ct g₀ V₀ n (k + 1) = NN g₀ V₀ n)
    (hF : FR g₀ V₀ W V) :
    W_109 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 2))
      (Gu g₀ a cx d bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  refine vc_109 fun fl => ?_
  rw [oc]
  exact i2 (Or.inl ⟨rfl, rfl⟩) hk (fun h => absurd h (by decide)) (by omega) (by omega) hF

theorem v116 {a cx bp s i x y : BitVec 64} (pr : Pr F Wl g₀ n W) (hk : k ≤ n)
    (hc : c + Ct g₀ V₀ n k = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_116 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 30))
      (Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) f V := by
  refine vc_116 (fun h fl => ?_) (fun h fl => ?_)
  · have e := dk pr hk h
    have h0 : Ct g₀ V₀ n k = 0 := ct_ge (by omega)
    exact i11 (by omega) rfl (show BitVec.ofNat 64 c = _ by rw [show c = NN g₀ V₀ n by omega]) (Or.inr hF)
  · exact i2 (Or.inr ⟨rfl, rfl⟩) hk (fun _ => dk' pr hk h) (by omega) hc hF

theorem v141 {a cx d bp s i x : BitVec 64} (pr : Pr F Wl g₀ n W) (hB : Bud g₀ V₀ n W) (h0 : g₀.rdi ≠ 0)
    (hk : k < n) (hc : c + 1 + Ct g₀ V₀ n (k + 1) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_141 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 3))
      (Gu g₀ a cx d bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  have h4 : 4 * c + 4 ≤ W := by have := hB h0; omega
  refine vc_141 (fD pr h4) fun fl w => ?_
  exact i3 (Or.inl ⟨rfl, rfl⟩) hk (by omega) hc (frD pr h4 hF w)

theorem v295 {a cx bp s i x y : BitVec 64} (pr : Pr F Wl g₀ n W) (hB : Bud g₀ V₀ n W) (h0 : g₀.rdi ≠ 0)
    (hk : k ≤ n) (hc : c + 1 + Ct g₀ V₀ n k = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_295 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 33))
      (Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) f V := by
  have h4 : 4 * c + 4 ≤ W := by have := hB h0; omega
  refine vc_295 (fD pr h4) fun fl w => ?_
  exact i8 (Or.inr ⟨rfl, rfl⟩) hk (by omega) hc (frD pr h4 hF w)

theorem v299 {a cx bp s i x y : BitVec 64} (pr : Pr F Wl g₀ n W) (hk : k ≤ n)
    (hc : c + 1 + Ct g₀ V₀ n k = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_299 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 32))
      (Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) f V := by
  refine vc_299 (fun h fl => ?_) (fun h fl => ?_)
  · rw [oc]
    exact i2 (Or.inr ⟨rfl, rfl⟩) hk (fun _ => dkn pr hk h) (by omega) (by omega) hF
  · have e := dkn' pr hk h
    have h0 : Ct g₀ V₀ n k = 0 := ct_ge (by omega)
    rw [oc]
    exact i11 (by omega) rfl (show BitVec.ofNat 64 (c + 1) = _ by rw [show c + 1 = NN g₀ V₀ n by omega])
      (Or.inr hF)

theorem v409 {e : Nat} {a cx d bp i x : BitVec 64} (he1 : 1 ≤ e) (he3 : e ≤ 3) (hk : k + 1 + e ≤ n)
    (hc : c + 1 + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_409 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 7))
      (Gu g₀ a cx d bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  refine vc_409 fun fl => ?_
  rw [oc]
  exact i10 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) he1 he3 hk (by omega) (by omega) hF

theorem v492 {e : Nat} {a cx d bp i x : BitVec 64} (he1 : 1 ≤ e) (he3 : e ≤ 3) (hk : k + 1 + e ≤ n)
    (hc : c + 2 + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_492 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 7))
      (Gu g₀ a cx d bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  refine vc_492 fun fl => ?_
  rw [oc2]
  exact i10 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)) he1 he3 hk (by omega) (by omega) hF

theorem v413 {e : Nat} {a cx d bp i x : BitVec 64} (he1 : 1 ≤ e) (he3 : e ≤ 3) (hk : k + 1 + e ≤ n)
    (hc : c + 0 + Ct g₀ V₀ n (k + 1 + e) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_413 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 6))
      (Gu g₀ a cx d bp (w64(BitVec.ofNat 32 e)) i x (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  refine vc_413 fun fl => ?_
  dsimp only [Gu]
  rw [ske he3, ← addK]
  exact i2 (Or.inl ⟨rfl, rfl⟩) hk (fun h => absurd h (by decide)) (by omega) (by omega) hF

end FV7z.U16
