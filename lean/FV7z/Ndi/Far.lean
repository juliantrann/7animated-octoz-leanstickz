import FV7z.Ndi.Loop
import FV7z.Ndi.Body
import FV7z.Ndi.Head
import FV7z.Ndi.Vc1
import FV7z.Ndi.Mv
import FV7z.Gor.Run
import FV7z.Hwc.Vc
/-!
# Bytes far from `_dl_non_dynamic_init`'s stores (PLAN.md G3, startup)

`ndi_ok`'s continuation gives the bytes `W₂` at the return as `lV (bV U m)` outside the scratch below `sp`, `U` as
`hV W' …` on some bytes (the brk below the TLS block among them, `Mal.Kf`), and `W'` as the bytes at the entry
`fV W sp g` below the break (`Lo`) and from `sp` up (`Same`). The stores of `lV`, `bV`, `hV` are all to globals below
the end of the bss (`0x7a9000`). Here:

- `ndi_tls`: a byte of the brk below the TLS block but its last 40 bytes is the entry's (for `__libc_init_first`'s
  `__ctype_init`, which reads the TLS word at `fs - 112`).
- `ndi_stk`: a byte from `sp + 120` up (the caller's frame) is the entry's.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Gor (Lo)
namespace FV7z.Ndi

/-- A byte apart from a store of `n` bytes that fits. -/
theorem vap {V : Addr → Byte} {a x : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (hf : a.toNat + n ≤ 2 ^ 64) (h : x.toNat < a.toNat ∨ a.toNat + n ≤ x.toNat) : Vst V a bs x = V x := by
  subst hn
  apply Vst_apart
  intro i hi e
  have := congrArg BitVec.toNat e
  rw [toNat_add_of_fits hi hf] at this
  omega

/-- A byte at or above the end of the bss, apart from a store below it. -/
theorem vhb {V : Addr → Byte} {a x : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (ha : a.toNat + n ≤ 8032256) (hx : 8032256 ≤ x.toNat) : Vst V a bs x = V x :=
  vap hn (by omega) (.inr (by omega))

/-- `lV (bV U m)` is `U` at or above the end of the bss. -/
theorem lbV_hb {U : Addr → Byte} {m : Nat} {x : Addr} (hx : 8032256 ≤ x.toNat) : lV (bV U m) x = U x := by
  unfold lV bV
  rw [vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx]

/-- `hV V' …` is `V'` at or above the end of the bss. -/
theorem hV_hb {V' : Addr → Byte} {r ph pn x : BitVec 64} (hx : 8032256 ≤ x.toNat) : hV V' r ph pn x = V' x := by
  unfold hV aV
  rw [vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx, vhb (toBytesLE_length _ _) (by decide) hx,
    vhb (toBytesLE_length _ _) (by decide) hx]

/-- `fV W sp g` is `W` outside `[sp + 80, sp + 120)`. -/
theorem fV_out {W : Addr → Byte} {sp x : Addr} {g : Gprs} (hs : sp.toNat + 120 ≤ 2 ^ 64)
    (hx : x.toNat < sp.toNat + 80 ∨ sp.toNat + 120 ≤ x.toNat) : fV W sp g x = W x := by
  have e80 : (sp + 80#64).toNat = sp.toNat + 80 := by bv_omega
  have e88 : (sp + 88#64).toNat = sp.toNat + 88 := by bv_omega
  have e96 : (sp + 96#64).toNat = sp.toNat + 96 := by bv_omega
  have e104 : (sp + 104#64).toNat = sp.toNat + 104 := by bv_omega
  have e112 : (sp + 112#64).toNat = sp.toNat + 112 := by bv_omega
  unfold fV
  rw [vap (a := sp + 80#64) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vap (a := sp + 88#64) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vap (a := sp + 96#64) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vap (a := sp + 104#64) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vap (a := sp + 112#64) (x := x) (toBytesLE_length _ _) (by omega) (by omega)]

/-- A byte of the brk below the TLS block `fsb` (but its last 40 bytes) at the return of `_dl_non_dynamic_init` is
the one at its entry. -/
theorem ndi_tls {W W' U W₂ : Addr → Byte} {sp b fsb r x : Addr} {m : Nat} {g : Gprs}
    (hE : Eqo sp W₂ (lV (bV U m)))
    (hU : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fsb a) → U a = hV W' r 4194368#64 8#64 a)
    (hL : ∀ a : Addr, Lo b fsb a → W' a = fV W sp g a) (hb : fsb.toNat ≤ b.toNat) (hsp : fsb.toNat + 72 ≤ sp.toNat)
    (hs : sp.toNat + 120 ≤ 2 ^ 64) (h1 : 8032256 ≤ x.toNat) (h2 : x.toNat + 40 < fsb.toNat) : W₂ x = W x := by
  rw [hE x (by unfold Scr; omega), lbV_hb h1, hU x (.inr (.inr (.inr (.inr ⟨h1, Nat.le_of_lt h2⟩)))), hV_hb h1,
    hL x ⟨by omega, by omega, by omega, by omega, by omega⟩, fV_out hs (.inl (by omega))]

/-- A byte from `sp + 120` up at the return of `_dl_non_dynamic_init` is the one at its entry. -/
theorem ndi_stk {W W' U W₂ : Addr → Byte} {sp fsb r x : Addr} {m : Nat} {g : Gprs}
    (hE : Eqo sp W₂ (lV (bV U m)))
    (hU : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fsb a) → U a = hV W' r 4194368#64 8#64 a)
    (hS : Same sp (fV W sp g) W') (hsp : 8032256 ≤ sp.toNat) (hs : sp.toNat + 120 ≤ 2 ^ 64)
    (hx : sp.toNat + 120 ≤ x.toNat) : W₂ x = W x := by
  rw [hE x (by unfold Scr; omega), lbV_hb (by omega), hU x (.inr (.inr (.inl (by omega)))), hV_hb (by omega),
    hS x (.inl (by omega)), fV_out hs (.inr hx)]

/-- A byte apart from a store at a literal address. -/
theorem vlt {V : Addr → Byte} {a : Nat} {x : Addr} {bs : List Byte} {n : Nat} (hn : bs.length = n)
    (ha : a + n < 2 ^ 64) (h : x.toNat < a ∨ a + n ≤ x.toNat) : Vst V (BitVec.ofNat 64 a) bs x = V x := by
  have e : (BitVec.ofNat 64 a).toNat = a := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  exact vap hn (by rw [e]; exact Nat.le_of_lt ha) (by rw [e]; exact h)

/-- `lV (bV U m)` is `U` below `0x7933c8`. -/
theorem lbV_gb {U : Addr → Byte} {m : Nat} {x : Addr} (hx : x.toNat < 7943112) : lV (bV U m) x = U x := by
  unfold lV bV
  rw [vlt (a := 7944528) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944520) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7943112) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029520) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029600) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029600) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029536) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029608) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029584) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029616) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega)]

/-- `hV V' …` is `V'` below `0x791cb8` and in `[0x791ce0, 0x793788)`. -/
theorem hV_gb {V' : Addr → Byte} {r ph pn : BitVec 64} {x : Addr}
    (hx : x.toNat < 7937208 ∨ 7937248 ≤ x.toNat ∧ x.toNat < 7944072) : hV V' r ph pn x = V' x := by
  unfold hV aV
  rw [vlt (a := 8029532) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937208) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937216) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937224) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937232) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937240) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944088) (n := 2) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944072) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944232) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega)]

/-- A byte of the image below `_dl_get_origin`'s variables, or of the GOT page but `main_arena`, at the return of
`_dl_non_dynamic_init` is the one at its entry (`__ctype_init`'s locale words and tables). -/
theorem ndi_glob {W W' U W₂ : Addr → Byte} {sp b fsb r x : Addr} {m : Nat} {g : Gprs}
    (hE : Eqo sp W₂ (lV (bV U m)))
    (hU : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fsb a) → U a = hV W' r 4194368#64 8#64 a)
    (hL : ∀ a : Addr, Lo b fsb a → W' a = fV W sp g a) (hb : 7940480 ≤ b.toNat) (hf : 7940480 + 40 ≤ fsb.toNat)
    (hsp : 7940480 + 72 ≤ sp.toNat) (hs : sp.toNat + 120 ≤ 2 ^ 64)
    (hx : x.toNat < 7937208 ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480) : W₂ x = W x := by
  have hu : x.toNat < 7937664 ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480 ∨ sp.toNat ≤ x.toNat ∨ Mal.Kf fsb x :=
    hx.elim (fun h => .inl (by omega)) (fun h => .inr (.inl h))
  have hl : Lo b fsb x := ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hn : ¬ Scr sp x := by unfold Scr; omega
  rw [hE x hn, lbV_gb (U := U) (m := m) (x := x) (by omega), hU x hu,
    hV_gb (V' := W') (r := r) (ph := 4194368#64) (pn := 8#64) (x := x) (by omega), hL x hl,
    fV_out (W := W) (g := g) (x := x) hs (.inl (by omega))]

end FV7z.Ndi
