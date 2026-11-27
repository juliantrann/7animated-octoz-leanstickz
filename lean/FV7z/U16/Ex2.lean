import FV7z.U16.Ex1
/-!
# `Utf8_To_Utf16`: the entry, the loop's head and a form's set-up (PLAN.md §M, M1)

`v0` (the six pushes, `destLen` and the flag bit kept on the stack: `fstk`), `v125` (the byte at `rdx`: `rdS` reads it
from the entry's memory), `v174` (a lead byte's form: the shift, `esi = 0`, `r8d = j - 1`). `zqf`: `rbx` tested
nonzero is `dest ≠ 0`; `xz`: a register xor'd with itself.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16

local notation:max "w64(" x ")" => BitVec.setWidth 64 x
local notation:max "w32(" x ")" => BitVec.setWidth 32 x

theorem zqf {x : BitVec 64} (h : zq x = false) : x ≠ 0 := fun e => by
  subst e; exact absurd h (by decide)
theorem xz (x : BitVec 64) : w64(w32(x) ^^^ w32(x)) = BitVec.ofNat 64 0 :=
  (congrArg (BitVec.setWidth 64) BitVec.xor_self).trans (by decide)

variable {F : Footprint} {Wl : List Rgn} {g₀ : Gprs} {V₀ : Addr → Byte} {n W k c : Nat} {f : Rflags}
  {V : Addr → Byte}

/-- The 60 bytes below `rsp`. -/
theorem fstk (pr : Pr F Wl g₀ n W) {c m : Nat} (h1 : m ≤ c) (h2 : c ≤ 60) :
    ∀ i < m, Foot Wl (Addr.add (g₀.rsp - BitVec.ofNat 64 c) i) := by
  intro i hi
  have hs := pr.sp
  have hl := g₀.rsp.isLt
  have e0 : (g₀.rsp - BitVec.ofNat 64 c).toNat = g₀.rsp.toNat - c := ts (by omega)
  have e : (Addr.add (g₀.rsp - BitVec.ofNat 64 c) i).toNat = g₀.rsp.toNat - c + i := by
    rw [← e0]; exact tA (by omega)
  exact pr.fst _ (by omega) (by omega)

/-- The `k`-th byte, as at the entry. -/
theorem rdS (pr : Pr F Wl g₀ n W) (hF : FR g₀ V₀ W V) (hk : k < n) :
    rb V (g₀.rdx + BitVec.ofNat 64 k) = by8 V₀ g₀.rdx k := by
  have ht : (Addr.add (g₀.rdx + BitVec.ofNat 64 k) 0).toNat = g₀.rdx.toNat + k := by
    rw [addr_add_zero]; exact tO (by have := pr.pn; omega)
  have e1 := rdF (a := g₀.rdx + BitVec.ofNat 64 k) (m := 1) hF (fun i hi => by
    obtain rfl : i = 0 := by omega
    rw [ht]; have := pr.sDp; omega)
  have e2 : List.map (Vs1 g₀ V₀) (byteAddrs (g₀.rdx + BitVec.ofNat 64 k) 1) =
      List.map V₀ (byteAddrs (g₀.rdx + BitVec.ofNat 64 k) 1) := by
    apply List.map_congr_left
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
    obtain rfl : i = 0 := by omega
    exact vs1_out pr.sp (by rw [ht]; have := pr.spS; omega)
  show ofBytesLE 8 (List.map V _) = ofBytesLE 8 (List.map V₀ _)
  rw [e1, e2]

/-! ## The cut points -/

theorem v0 (pr : Pr F Wl g₀ n W) : W_0 F Wl (Nx g₀ V₀ n W (30 * n + 40)) g₀ f V₀ := by
  refine vc_0 (fstk pr (c := 8) (m := 8) (by omega) (by omega))
    (by rw [k16]; exact fstk pr (by omega) (by omega)) (by rw [k24]; exact fstk pr (by omega) (by omega))
    (by rw [k32]; exact fstk pr (by omega) (by omega)) (by rw [k40]; exact fstk pr (by omega) (by omega))
    (by rw [k48]; exact fstk pr (by omega) (by omega)) (by rw [k56]; exact fstk pr (by omega) (by omega))
    (fun _ => by rw [k60]; exact fstk pr (by omega) (by omega)) (fun h fl => ?_) (fun h fl => ?_)
  · have e := pinj1 pr.pn (Nat.zero_le n) (Nat.le_refl n)
      ((BitVec.add_zero g₀.rdx).trans ((of_decide_eq_true h).trans pr.lim))
    have h0 : NN g₀ V₀ n = 0 := ct_ge (by omega)
    refine i11 (by omega) rfl ?_ (Or.inl fr0)
    show w64(w32(g₀.r11) ^^^ w32(g₀.r11)) = BitVec.ofNat 64 (NN g₀ V₀ n)
    rw [xz, h0]
  · have hn : 0 < n := Nat.pos_of_ne_zero fun e => by
      subst e
      exact Bool.false_ne_true (h.symm.trans (decide_eq_true (pr.lim.trans (BitVec.add_zero _)).symm))
    have e : g₀.rdx = g₀.rdx + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    rw [xz, e]
    exact i2 (c := 0) (k := 0) (Or.inr ⟨rfl, rfl⟩) (Nat.zero_le n) (fun _ => hn) (by omega) (Nat.zero_add _) fr0

theorem v125 {a cx bp s i x y : BitVec 64} (pr : Pr F Wl g₀ n W) (hB : Bud g₀ V₀ n W) (hk : k < n)
    (hc : c + Ct g₀ V₀ n k = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_125 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 29))
      (Gu g₀ a cx (g₀.rdx + BitVec.ofNat 64 k) bp s i x y (BitVec.ofNat 64 c)) f V := by
  have hr := rdS pr hF hk
  refine vc_125 (pr.fa k hk) (fun h1 h2 h3 h4 fl a' bp' => ?_) (fun h1 h2 h3 h4 fl a' bp' => ?_)
    (fun h1 h2 h3 fl a' bp' => ?_) (fun h1 h2 hz fl a' d' => ?_) (fun h1 h2 hz => ?_)
    (fun h1 h2 hz fl a' d' w => ?_) (fun h1 hz fl a' => ?_) (fun h1 hz fl a' => ?_)
  · rw [hr] at h1 h2 h3 h4 ⊢
    rw [adv1]
    rw [ct_c hk h1 h2 (nc_3 h3 h4)] at hc
    exact i4 (j := 3) hk (by omega) (by omega) (by omega) hc hF
  · rw [hr] at h1 h2 h3 h4 ⊢
    rw [adv1]
    rw [ct_c hk h1 h2 (nc_2 h3 h4)] at hc
    exact i4 (j := 2) hk (by omega) (by omega) (by omega) hc hF
  · rw [hr] at h1 h2 h3 ⊢
    rw [adv1]
    rw [ct_c hk h1 h2 (nc_1 h3)] at hc
    exact i4 (j := 1) hk (by omega) (by omega) (by omega) hc hF
  · rw [hr] at h1 h2
    rw [adv1]
    rw [ct_b hk h2] at hc
    exact i3 (Or.inl ⟨rfl, rfl⟩) hk (by omega) (by omega) hF
  · rw [hr] at h1 h2
    rw [ct_b hk h2] at hc
    have := hB (zqf hz)
    exact fD pr (by omega)
  · rw [hr] at h1 h2
    rw [adv1]
    rw [ct_b hk h2] at hc
    have := hB (zqf hz)
    exact i3 (Or.inl ⟨rfl, rfl⟩) hk (by omega) (by omega) (frD pr (by omega) hF w)
  · rw [hr] at h1
    rw [adv1]
    rw [ct_a hk h1] at hc
    exact i3 (Or.inl ⟨rfl, rfl⟩) hk (by omega) (by omega) hF
  · rw [hr] at h1
    rw [adv1]
    rw [ct_a hk h1] at hc
    exact i3 (Or.inr ⟨rfl, rfl, zqf hz⟩) hk (by omega) (by omega) hF

theorem v174 {j : Nat} {a bp s i x : BitVec 64} (hk : k < n) (hj1 : 1 ≤ j) (hj3 : j ≤ 3)
    (hc : c + Rm g₀ V₀ n k (Ib g₀ V₀ n k j (j - 1) 0 (d0 (by8 V₀ g₀.rdx k) j)) = NN g₀ V₀ n) (hF : FR g₀ V₀ W V) :
    W_174 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 28))
      (Gu g₀ a (w64(BitVec.ofNat 32 j)) (w64(d0 (by8 V₀ g₀.rdx k) j)) bp s i x (g₀.rdx + BitVec.ofNat 64 (k + 1))
        (BitVec.ofNat 64 c)) f V := by
  refine vc_174 fun fl a' => ?_
  have e1 : w64(w32(w64(128#32)) >>> ((BitVec.setWidth 8 (w64(BitVec.ofNat 32 j))).toNat % 32)) =
      w64(128#32 >>> j) := by
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;> decide
  have e2 : w64(w32(w64(BitVec.ofNat 32 j) + 18446744073709551615#64)) = w64(BitVec.ofNat 32 (j - 1)) := by
    rcases (by omega : j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl <;> decide
  have e3 : w64(w32(s) ^^^ w32(s)) = w64(BitVec.ofNat 32 0) := congrArg (BitVec.setWidth 64) BitVec.xor_self
  rw [e1, e2, e3]
  exact i5 (ms := j - 1) (e := 0) (by omega) hj3 (by omega) (by omega) hc hF

end FV7z.U16
