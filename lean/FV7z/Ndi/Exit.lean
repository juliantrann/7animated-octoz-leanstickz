import FV7z.Ndi.Far
/-!
# `__cxa_atexit`'s variables after `_dl_non_dynamic_init` (PLAN.md G3, startup)

`__libc_start_main` calls `__cxa_atexit (fini, …)` after `__libc_init_first`; it reads `__exit_funcs_done`
(`0x7a3a94`), the list `initial` (`0x7a3aa0`, 1040 bytes) and the lock `__exit_funcs_lock` (`0x7a8400`, with
`__new_exitfn_called` after it), all in the bss. `_dl_non_dynamic_init` stores to none of them.

- `ExitB x`: `x` is one of those bytes.
- `lbV_ex`, `hV_ex`: the stores of `lV`, `bV` and `hV` miss them.
- `ndi_exit`: such a byte at the return of `_dl_non_dynamic_init` is the one at its entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Gor (Lo)
namespace FV7z.Ndi

/-- A byte of `__exit_funcs_done`, `initial` or `__exit_funcs_lock` and `__new_exitfn_called`. -/
def ExitB (x : Addr) : Prop :=
  8010388 ≤ x.toNat ∧ x.toNat < 8011440 ∨ 8029184 ≤ x.toNat ∧ x.toNat < 8029200

/-- `lV (bV U m)` is `U` on `ExitB`. -/
theorem lbV_ex {U : Addr → Byte} {m : Nat} {x : Addr} (hx : ExitB x) : lV (bV U m) x = U x := by
  unfold ExitB at hx
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

/-- `hV V' …` is `V'` on `ExitB`. -/
theorem hV_ex {V' : Addr → Byte} {r ph pn : BitVec 64} {x : Addr} (hx : ExitB x) : hV V' r ph pn x = V' x := by
  unfold ExitB at hx
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

/-- A byte of `__cxa_atexit`'s variables at the return of `_dl_non_dynamic_init` is the one at its entry. -/
theorem ndi_exit {W W' U W₂ : Addr → Byte} {sp b fsb r x : Addr} {m : Nat} {g : Gprs}
    (hE : Eqo sp W₂ (lV (bV U m)))
    (hU : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fsb a) → U a = hV W' r 4194368#64 8#64 a)
    (hL : ∀ a : Addr, Lo b fsb a → W' a = fV W sp g a) (hb : 8032256 ≤ b.toNat) (hf : 8032256 ≤ fsb.toNat)
    (hsp : 8032256 + 72 ≤ sp.toNat) (hs : sp.toNat + 120 ≤ 2 ^ 64) (hx : ExitB x) : W₂ x = W x := by
  have hx' := hx
  unfold ExitB at hx'
  have hu : x.toNat < 7937664 ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480 ∨ sp.toNat ≤ x.toNat ∨ Mal.Kf fsb x :=
    .inr (.inr (.inr (Or.inl (by unfold Mal.Kn; omega))))
  have hl : Lo b fsb x := ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hn : ¬ Scr sp x := by unfold Scr; omega
  rw [hE x hn, lbV_ex (U := U) (m := m) hx, hU x hu, hV_ex (V' := W') (r := r) (ph := 4194368#64) (pn := 8#64) hx,
    hL x hl, fV_out (W := W) (g := g) (x := x) hs (.inl (by omega))]

end FV7z.Ndi
