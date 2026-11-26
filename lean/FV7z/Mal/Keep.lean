import FV7z.Mal.Ok
/-!
# What a `malloc` keeps below the old top (PLAN.md G3)

The posts of `Mal.at_hpW`, `Onw.onw_hpWT` and the constructors' `Po` give the bytes as they were below the block `p`
less 8 (but for the word `main_arena.top`), and the block 16 above the old top `T` or more. So every byte below
`T + 8` but for that word is as it was: a string in static data or in an older live block (below the old top) is
untouched by the call.

- `keep_low`: that, for any other disjunct `Q` the frame allows and any side condition `R` it needs.
-/
open ZellicX86 FV7z
namespace FV7z.Mal

/-- The bytes below the old top `T` plus 8, but for `main_arena.top`, as they were: see the module doc. -/
theorem keep_low {V V₂ : Addr → Byte} {p : Addr} {T : Nat} {Q R : Addr → Prop} (hT : T + 16 ≤ p.toNat)
    (hV : ∀ a : Addr, (a.toNat < 7940768 ∨ 7940776 ≤ a.toNat ∧ a.toNat + 8 < p.toNat ∨ Q a) → R a → V₂ a = V a) :
    ∀ a : Addr, a.toNat < T + 8 → ¬ (7940768 ≤ a.toNat ∧ a.toNat < 7940776) → R a → V₂ a = V a :=
  fun a h1 h2 hR => hV a (if h : a.toNat < 7940768 then .inl h else .inr (.inl ⟨by omega, by omega⟩)) hR

end FV7z.Mal
