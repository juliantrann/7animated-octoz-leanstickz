import FV7z.U16.Ex3
/-!
# `Utf8_To_Utf16`: the inner loop and the exit (PLAN.md §M, M1)

`v209` (a continuation byte: the end, a bad byte, the checks at the first one, the form's next byte or its end) and
`v312` (`*destLen` stored, the six `pop`s, the `ret`), generic in the memory below `rsp` (`Vs0` or `Vs1`).
Helpers: the register tests in `Ib`'s terms (`u4e0`, `u4m1`, `u4m3`, `u4uf`), `u4a1` (bit 0 set), the byte's
value (`u4cA` and its forms), the stack reads past the `destLen` store (`u4pp`, `u4rd`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (addK pret pret_0)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
namespace FV7z.U16

local notation:max "w64(" x ")" => BitVec.setWidth 64 x
local notation:max "w32(" x ")" => BitVec.setWidth 32 x

/-! ## The register tests -/

theorem u4e0 {e : Nat} (h : e ≤ 2) :
    (!decide (w32(w64(BitVec.ofNat 32 e)) + 1#32 = 1#32)) = decide (e ≠ 0) := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with rfl | rfl | rfl <;> decide
theorem u4er {e : Nat} (h : e ≤ 2) :
    w64(w32(w64(BitVec.ofNat 32 e)) + 1#32) = w64(BitVec.ofNat 32 (e + 1)) := by
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with rfl | rfl | rfl <;> decide
theorem u4m1 {ms : Nat} (h : ms ≤ 2) : decide (w32(w64(BitVec.ofNat 32 ms)) = 1#32) = decide (ms = 1) := by
  rcases (by omega : ms = 0 ∨ ms = 1 ∨ ms = 2) with rfl | rfl | rfl <;> decide
theorem u4m3 {ms : Nat} (h : ms ≤ 2) :
    (!decide (w32(w64(BitVec.ofNat 32 ms) + 1#64) = 3#32)) = decide (ms ≠ 2) := by
  rcases (by omega : ms = 0 ∨ ms = 1 ∨ ms = 2) with rfl | rfl | rfl <;> decide
theorem u4w1 : w32(w64(w32(w64(BitVec.ofNat 32 0)) + 1#32)) = BitVec.ofNat 32 1 := by decide

/-- Bit 0 set. -/
theorem u4a1 {x : BitVec 32} (h : zr (x &&& 1#32) = false) : x &&& 1#32 = 1#32 := by
  have h0 : x &&& 1#32 ≠ 0#32 := fun e => by
    rw [e] at h
    exact absurd h (by decide)
  have h3 : (1#32 : BitVec 32).toNat = 1 := rfl
  have h1 : (x &&& 1#32).toNat = x.toNat % 2 := by rw [BitVec.toNat_and, h3, Nat.and_one_is_mod]
  have h2 : (x &&& 1#32).toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq (e.trans rfl))
  apply BitVec.eq_of_toNat_eq
  rw [h1, h3]
  rw [h1] at h2
  omega

variable {F : Footprint} {Wl : List Rgn} {g₀ : Gprs} {V₀ : Addr → Byte} {n W k c : Nat} {f : Rflags}
  {V : Addr → Byte}

theorem u4uf {b : Bool} (h : zr w32(w64(Fl g₀ &&& 1#32)) = b) : Uf g₀ = !b :=
  congrArg (fun b => !b) ((congrArg zr (sw_64_32 (Fl g₀ &&& 1#32))).symm.trans h)
theorem u4r15 (h : zr w32(w64(Fl g₀ &&& 1#32)) = false) :
    w32(w64(w32(w64(Fl g₀ &&& 1#32)))) = BitVec.ofNat 32 1 := by
  rw [sw_64_32, sw_64_32]
  exact u4a1 ((congrArg zr (sw_64_32 (Fl g₀ &&& 1#32))).symm.trans h)

/-! ## The byte's value -/

section byte
variable {k' : Nat} {j : Nat} {dd : BitVec 32}
  (hr : rb V (g₀.rdx + BitVec.ofNat 64 k') = by8 V₀ g₀.rdx k')
include hr

theorem u4cA : acc w32(w64(dd)) (rb V (g₀.rdx + BitVec.ofNat 64 k')) = acc dd (by8 V₀ g₀.rdx k') := by
  rw [sw_64_32 dd, hr]
theorem u4cE :
    w64(acc w32(w64(dd)) (rb V (g₀.rdx + BitVec.ofNat 64 k'))) = w64(acc dd (by8 V₀ g₀.rdx k')) :=
  congrArg (BitVec.setWidth 64) (u4cA hr)
theorem u4cO : ovl w32(w64(128#32 >>> j)) (acc w32(w64(dd)) (rb V (g₀.rdx + BitVec.ofNat 64 k'))) =
    ovl (128#32 >>> j) (acc dd (by8 V₀ g₀.rdx k')) := by
  rw [sw_64_32 (128#32 >>> j), u4cA hr]
theorem u4cN : nsg (acc w32(w64(dd)) (rb V (g₀.rdx + BitVec.ofNat 64 k'))) = nsg (acc dd (by8 V₀ g₀.rdx k')) :=
  congrArg nsg (u4cA hr)
theorem u4cL :
    l271 (acc w32(w64(dd)) (rb V (g₀.rdx + BitVec.ofNat 64 k'))) = l271 (acc dd (by8 V₀ g₀.rdx k')) :=
  congrArg l271 (u4cA hr)

end byte

/-- Past the end test: the byte is in the source, as at the entry. -/
theorem u4cv {k' : Nat} (pr : Pr F Wl g₀ n W) (hF : FR g₀ V₀ W V) (hk : k' ≤ n)
    (h : decide (g₀.rdx + BitVec.ofNat 64 k' = g₀.rcx) = false) :
    k' < n ∧ rb V (g₀.rdx + BitVec.ofNat 64 k') = by8 V₀ g₀.rdx k' :=
  ⟨dk' pr hk h, rdS pr hF (dk' pr hk h)⟩

/-! ## 209 -/

theorem v209 {j ms e : Nat} {dd : BitVec 32} {a bp : BitVec 64} (pr : Pr F Wl g₀ n W) (hj : ms + e + 1 = j)
    (hj3 : j ≤ 3) (hk : k + 1 + e ≤ n) (hc : c + Rm g₀ V₀ n k (Ib g₀ V₀ n k j ms e dd) = NN g₀ V₀ n)
    (hF : FR g₀ V₀ W V) :
    W_209 F Wl (Nx g₀ V₀ n W (30 * (n - k) + 24 - 5 * e))
      (Gu g₀ a (w64(128#32 >>> j)) (w64(dd)) bp (w64(BitVec.ofNat 32 e)) (g₀.rdx + BitVec.ofNat 64 (k + 1 + e))
        (w64(BitVec.ofNat 32 ms)) (g₀.rdx + BitVec.ofNat 64 (k + 1)) (BitVec.ofNat 64 c)) f V := by
  have he2 : e ≤ 2 := by omega
  have hm2 : ms ≤ 2 := by omega
  refine vc_209 (fun h fl => ?_) (fun h => ?_) (fun h hb fl a' => ?_) (fun h hb he fl a' => ?_)
    (fun h hb he ho fl a' => ?_) (fun h hb he ho h1 hz fl a' => ?_) (fun h hb he ho h1 hz hn fl a' => ?_)
    (fun h hb he ho h1 hz hn fl a' => ?_) (fun h hb he ho h1 h3 fl a' => ?_)
    (fun h hb he ho h1 h3 hl fl a' => ?_) (fun h hb he ho h1 h3 hl fl a' => ?_)
  · -- the source's end
    have e1 := dk pr hk h
    rw [ib_end e1] at hc
    exact i7 (by omega) hk (by omega) hc hF (sw_64_32 (BitVec.ofNat 32 e))
  · exact pr.fa (k + 1 + e) (dk' pr hk h)
  · -- not a continuation byte
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    have hb' := (congrArg bad hr).symm.trans hb
    rw [ib_bad (Nat.ne_of_lt hk') hb'] at hc
    exact i7 (by omega) hk (by omega) hc hF (sw_64_32 (BitVec.ofNat 32 e))
  · -- a byte past the first
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    have hb' := (congrArg bad hr).symm.trans hb
    have he' : e ≠ 0 := of_decide_eq_true ((u4e0 he2).symm.trans he)
    rw [ib_go (Nat.ne_of_lt hk') hb' he'] at hc
    rw [u4cE (dd := dd) hr, u4er he2]
    exact i6 (Or.inl ⟨rfl, rfl⟩) hj hj3 hk' (fun h => absurd h (by decide)) (by omega) hc hF
  · -- the first: overlong
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    obtain rfl : e = 0 := by
      have := of_decide_eq_false ((u4e0 he2).symm.trans he)
      omega
    have hb' := (congrArg bad hr).symm.trans hb
    have ho' := (u4cO (j := j) (dd := dd) hr).symm.trans ho
    rw [ib_ovl (Nat.ne_of_lt hk') hb' ho'] at hc
    exact i7 (e := 1) (by omega) (by omega) (by omega) hc hF u4w1
  · -- the first, `ms = 1`, bit 0 clear
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    obtain rfl : e = 0 := by
      have := of_decide_eq_false ((u4e0 he2).symm.trans he)
      omega
    obtain rfl : ms = 1 := of_decide_eq_true ((u4m1 hm2).symm.trans h1)
    have hb' := (congrArg bad hr).symm.trans hb
    have ho' := (u4cO (j := j) (dd := dd) hr).symm.trans ho
    have hu := u4uf hz
    have hs1 : ¬ (1 = 1 ∧ Uf g₀ = true ∧ nsg (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) :=
      fun h' => Bool.false_ne_true (hu.symm.trans h'.2.1)
    have hl1 : ¬ (1 = 2 ∧ l271 (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) := fun h' => absurd h'.1 (by decide)
    rw [ib_g0 (m := 1) (Nat.ne_of_lt hk') hb' ho' hs1 hl1] at hc
    rw [u4cE (dd := dd) hr, u4er (e := 0) (by omega)]
    exact i6 (Or.inr ⟨rfl, rfl⟩) hj hj3 hk' (fun _ => Nat.one_ne_zero) (by omega) hc hF
  · -- the first, `ms = 1`, bit 0 set, not a surrogate
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    obtain rfl : e = 0 := by
      have := of_decide_eq_false ((u4e0 he2).symm.trans he)
      omega
    obtain rfl : ms = 1 := of_decide_eq_true ((u4m1 hm2).symm.trans h1)
    have hb' := (congrArg bad hr).symm.trans hb
    have ho' := (u4cO (j := j) (dd := dd) hr).symm.trans ho
    have hn' := (u4cN (dd := dd) hr).symm.trans hn
    have hs1 : ¬ (1 = 1 ∧ Uf g₀ = true ∧ nsg (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) :=
      fun h' => Bool.false_ne_true (h'.2.2.symm.trans hn')
    have hl1 : ¬ (1 = 2 ∧ l271 (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) := fun h' => absurd h'.1 (by decide)
    rw [ib_g0 (m := 1) (Nat.ne_of_lt hk') hb' ho' hs1 hl1] at hc
    rw [u4cE (dd := dd) hr, u4er (e := 0) (by omega)]
    exact i6 (Or.inr ⟨rfl, rfl⟩) hj hj3 hk' (fun _ => Nat.one_ne_zero) (by omega) hc hF
  · -- the first, `ms = 1`, bit 0 set, a surrogate
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    obtain rfl : e = 0 := by
      have := of_decide_eq_false ((u4e0 he2).symm.trans he)
      omega
    obtain rfl : ms = 1 := of_decide_eq_true ((u4m1 hm2).symm.trans h1)
    have hb' := (congrArg bad hr).symm.trans hb
    have ho' := (u4cO (j := j) (dd := dd) hr).symm.trans ho
    have hu : Uf g₀ = true := u4uf hz
    have hn' := (u4cN (dd := dd) hr).symm.trans hn
    rw [ib_sur (Nat.ne_of_lt hk') hb' ho' hu hn'] at hc
    exact i7 (e := 1) (by omega) (by omega) (by omega) hc hF (u4r15 hz)
  · -- the first, `ms = 0`
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    obtain rfl : e = 0 := by
      have := of_decide_eq_false ((u4e0 he2).symm.trans he)
      omega
    obtain rfl : ms = 0 := by
      have := of_decide_eq_false ((u4m1 hm2).symm.trans h1)
      have := of_decide_eq_true ((u4m3 hm2).symm.trans h3)
      omega
    have hb' := (congrArg bad hr).symm.trans hb
    have ho' := (u4cO (j := j) (dd := dd) hr).symm.trans ho
    have hs0 : ¬ (0 = 1 ∧ Uf g₀ = true ∧ nsg (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) :=
      fun h' => absurd h'.1 (by decide)
    have hl0 : ¬ (0 = 2 ∧ l271 (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) := fun h' => absurd h'.1 (by decide)
    rw [ib_g0 (m := 0) (Nat.ne_of_lt hk') hb' ho' hs0 hl0] at hc
    rw [u4cE (dd := dd) hr, u4er (e := 0) (by omega)]
    exact i6 (Or.inl ⟨rfl, rfl⟩) hj hj3 hk' (fun h => absurd h (by decide)) (by omega) hc hF
  · -- the first, `ms = 2`, at most `0x10FFFF`
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    obtain rfl : e = 0 := by
      have := of_decide_eq_false ((u4e0 he2).symm.trans he)
      omega
    obtain rfl : ms = 2 := by
      have := of_decide_eq_false ((u4m1 hm2).symm.trans h1)
      have := of_decide_eq_false ((u4m3 hm2).symm.trans h3)
      omega
    have hb' := (congrArg bad hr).symm.trans hb
    have ho' := (u4cO (j := j) (dd := dd) hr).symm.trans ho
    have hl' := (u4cL (dd := dd) hr).symm.trans hl
    have hs2 : ¬ (2 = 1 ∧ Uf g₀ = true ∧ nsg (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) :=
      fun h' => absurd h'.1 (by decide)
    have hl2 : ¬ (2 = 2 ∧ l271 (acc dd (by8 V₀ g₀.rdx (k + 1 + 0))) = false) :=
      fun h' => Bool.false_ne_true (h'.2.symm.trans hl')
    rw [ib_g0 (m := 2) (Nat.ne_of_lt hk') hb' ho' hs2 hl2] at hc
    rw [u4cE (dd := dd) hr, u4er (e := 0) (by omega)]
    exact i6 (Or.inl ⟨rfl, rfl⟩) hj hj3 hk' (fun h => absurd h (by decide)) (by omega) hc hF
  · -- the first, `ms = 2`, past `0x10FFFF`
    obtain ⟨hk', hr⟩ := u4cv pr hF hk h
    obtain rfl : e = 0 := by
      have := of_decide_eq_false ((u4e0 he2).symm.trans he)
      omega
    obtain rfl : ms = 2 := by
      have := of_decide_eq_false ((u4m1 hm2).symm.trans h1)
      have := of_decide_eq_false ((u4m3 hm2).symm.trans h3)
      omega
    have hb' := (congrArg bad hr).symm.trans hb
    have ho' := (u4cO (j := j) (dd := dd) hr).symm.trans ho
    have hl' := (u4cL (dd := dd) hr).symm.trans hl
    rw [ib_hi (Nat.ne_of_lt hk') hb' ho' hl'] at hc
    exact i7 (e := 1) (by omega) (by omega) (by omega) hc hF u4w1

/-! ## 312: the exit -/

/-- A slot of the saved registers, past the `destLen` store. -/
theorem u4pp (pr : Pr F Wl g₀ n W) {w : BitVec 64} {c : Nat} (h1 : 8 ≤ c) (h2 : c ≤ 48) :
    rdq(Vst V g₀.rsi (toBytesLE w 8), g₀.rsp - BitVec.ofNat 64 c) = rdq(V, g₀.rsp - BitVec.ofNat 64 c) := by
  have hs := pr.sp
  have hl := g₀.rsp.isLt
  have ht : (g₀.rsp - BitVec.ofNat 64 c).toNat = g₀.rsp.toNat - c := ts (by omega)
  refine congrArg (ofBytesLE 64) (rd_Vst V g₀.rsi _ _ 8 ?_ ?_ ?_)
  · rw [toBytesLE_length]; exact pr.pT
  · rw [ht]; omega
  · rw [toBytesLE_length, ht]; have := pr.sPS; omega

/-- A slot below `rsp`, apart from `dest`. -/
theorem u4rd (pr : Pr F Wl g₀ n W) {Vb : Addr → Byte} (hF : Fr Vb g₀.rdi W V) {c : Nat} (h1 : 8 ≤ c)
    (h2 : c ≤ 60) : rdq(V, g₀.rsp - BitVec.ofNat 64 c) = rdq(Vb, g₀.rsp - BitVec.ofNat 64 c) := by
  refine congrArg (ofBytesLE 64) (rdF hF fun i hi => ?_)
  rw [tsA pr (c := c) (i := i) (by omega) h2]
  have := pr.sDS; have := pr.sp; omega

theorem v312 {μ : Nat} {g : Gprs} {Vb : Addr → Byte} (pr : Pr F Wl g₀ n W)
    (hb : ∀ c, (c = 8 ∨ c = 16 ∨ c = 24 ∨ c = 32 ∨ c = 40 ∨ c = 48 ∨ c = 56) →
      rdq(Vb, g₀.rsp - BitVec.ofNat 64 c) = rdq(Vs0 g₀ V₀, g₀.rsp - BitVec.ofNat 64 c))
    (ho : ∀ x : Addr, (x.toNat + 60 < g₀.rsp.toNat ∨ g₀.rsp.toNat ≤ x.toNat) → Vb x = V₀ x)
    (hs : g.rsp = S6 g₀.rsp) (hr : g.r11 = BitVec.ofNat 64 (NN g₀ V₀ n)) (hF : Fr Vb g₀.rdi W V) :
    W_312 F Wl (Nx g₀ V₀ n W μ) g f V := by
  obtain ⟨e8, e16, e24, e32, e40, e48, e56⟩ := vs0_rd (V := V₀) pr.sp
  have hP : rdq(V, S6 g₀.rsp + 18446744073709551608#64) = g₀.rsi := by
    rw [k56]
    exact (u4rd pr hF (by omega) (by omega)).trans ((hb 56 (by decide)).trans e56)
  have b : ∀ c, (c = 8 ∨ c = 16 ∨ c = 24 ∨ c = 32 ∨ c = 40 ∨ c = 48) →
      rdq(Vst V g₀.rsi (toBytesLE (BitVec.ofNat 64 (NN g₀ V₀ n)) 8), g₀.rsp - BitVec.ofNat 64 c) =
        rdq(Vs0 g₀ V₀, g₀.rsp - BitVec.ofNat 64 c) := fun c hc =>
    (u4pp pr (by omega) (by omega)).trans ((u4rd pr hF (by omega) (by omega)).trans (hb c (by omega)))
  refine vc_312 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ fun fl => ?_
  · rw [hs, k56]; exact fsrk pr (by omega) (by omega)
  · rw [hs, hP]; exact pr.fP
  · rw [hs, k48]; exact fsrk pr (by omega) (by omega)
  · rw [hs, q40]; exact fsrk pr (by omega) (by omega)
  · rw [hs, q32]; exact fsrk pr (by omega) (by omega)
  · rw [hs, q24]; exact fsrk pr (by omega) (by omega)
  · rw [hs, q16]; exact fsrk pr (by omega) (by omega)
  · rw [hs, q8]; exact fsrk pr (by omega) (by omega)
  · rw [hs, hP, hr]
    refine Or.inr ⟨rfl, fun x h1 h2 h3 => ?_, ?_, g.rcx, g.rdx, g.rsi, g.rdi, g.r8, g.r9, g.r10,
      BitVec.ofNat 64 (NN g₀ V₀ n), ?_⟩
    · rw [Vst_out V g₀.rsi (toBytesLE (BitVec.ofNat 64 (NN g₀ V₀ n)) 8) x
        (by rw [toBytesLE_length]; exact pr.pT) (by rw [toBytesLE_length]; exact h3)]
      exact (hF x h2).trans (ho x h1)
    · rw [rd_Vst_self _ _ _ (toBytesLE_length _ _) pr.pT]
      exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
    · rw [q0, q8, q16, q24, q32, q40, k48, b 48 (by decide), b 40 (by decide), b 32 (by decide),
        b 24 (by decide), b 16 (by decide), b 8 (by decide), e48, e40, e32, e24, e16, e8]
      try rfl

end FV7z.U16
