import FV7z.Ctor.ChainGo
import FV7z.Ctor.Regs
/-!
# The registrars' tables after a chain of registrar calls (PLAN.md §M, constructors)

- `RegsIn.far`: the tables are as before when the bytes of `[7981024, 7991300)` are.
- `updAll R cs`: the lists `R` with the arguments of the calls `cs` added in order; `Fits R cs`: each call has room.
- `RegsIn.chain`: after the calls (`ChainOut`), the tables hold `updAll R cs`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- The tables are as before when the bytes of `[7981024, 7991300)` are. -/
theorem RegsIn.far {R : Nat → List (BitVec 64)} {V V' : Addr → Byte} (h : RegsIn R V)
    (hV : ∀ a : Addr, 7981024 ≤ a.toNat → a.toNat < 7991300 → V' a = V a) : RegsIn R V' := by
  intro r hr
  obtain ⟨hc, hle, he⟩ := h r hr
  obtain ⟨c4, t8, ap⟩ := reg_lay r
  have hx := reg_max r
  have hi := reg_in r
  refine ⟨?_, hle, fun i hi' => ?_⟩
  · rw [rdd_eq c4 fun a h4 h5 => hV a (by omega) (by omega)]
    exact hc
  · have ht := ent_toNat r i (by omega)
    rw [rdq_eq (by omega) fun a h4 h5 => hV a (by omega) (by omega)]
    exact he i hi'

/-- The lists `R` with the arguments of the calls `cs` added in order. -/
def updAll : (Nat → List (BitVec 64)) → List (Nat × Nat) → Nat → List (BitVec 64)
  | R, [] => R
  | R, (r, A) :: cs => updAll (upd R r (BitVec.ofNat 64 A)) cs

/-- Each call of `cs` is to one of the three registrars and has room in its table. -/
def Fits : (Nat → List (BitVec 64)) → List (Nat × Nat) → Prop
  | _, [] => True
  | R, (r, A) :: cs => r < 3 ∧ (R r).length < regMax r ∧ Fits (upd R r (BitVec.ofNat 64 A)) cs

/-- After the calls `cs` with room, the tables hold `updAll R cs`. -/
theorem RegsIn.chain {S : Addr} (hS : 7991300 + 16 ≤ S.toNat) :
    ∀ (cs : List (Nat × Nat)) (R : Nat → List (BitVec 64)) (V V' : Addr → Byte), RegsIn R V → Fits R cs →
      ChainOut S cs V V' → RegsIn (updAll R cs) V'
  | [], R, V, V', h, _, hO => by
    rw [show V' = V from hO]
    exact h
  | [(r, A)], R, V, V', h, hF, hO => by
    obtain ⟨hr, hn, -⟩ := hF
    exact h.push hr hn hO
  | (r, A) :: c :: cs, R, V, V', h, hF, hO => by
    obtain ⟨hr, hn, hF'⟩ := hF
    obtain ⟨ra, V₁, h1, h2⟩ := hO
    have e := sub16 S (by omega)
    have hs : (S - 8 - 8).toNat + (toBytesLE ra 8).length ≤ 2 ^ 64 := by
      rw [e, toBytesLE_length]
      have := S.isLt
      omega
    have h0 : RegsIn R (Vst V (S - 8 - 8) (toBytesLE ra 8)) :=
      h.far fun a h4 h5 => Tun.Vst_out V _ _ a hs (by rw [e]; omega)
    exact RegsIn.chain hS (c :: cs) _ V₁ V' (h0.push hr hn h1) hF' h2

end FV7z.Ctor
