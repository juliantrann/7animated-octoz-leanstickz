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
    (hs : sp.toNat + 120 ≤ 2 ^ 64) (h1 : 8032256 ≤ x.toNat) (h2 : x.toNat + 40 ≤ fsb.toNat) : W₂ x = W x := by
  rw [hE x (by unfold Scr; omega), lbV_hb h1, hU x (.inr (.inr (.inr (.inr ⟨h1, h2⟩)))), hV_hb h1,
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

end FV7z.Ndi
