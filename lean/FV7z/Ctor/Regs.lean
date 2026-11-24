import FV7z.Ctor.Runs
/-!
# The three registrars' tables as lists (PLAN.md §M, constructors)

The invariant of the constructors keeps the tables of 7-Zip's registrars exactly: `RegsIn R V`, the table of the
registrar `r` (0 `RegisterArc`, 1 `RegisterCodec`, 2 `RegisterHasher`) holds the list `R r` in `V`, its count the
length. A registrar's call with room adds its argument at the end (`RegsIn.push`), the other tables unchanged.

- `reg_apart`: the tables with their counts are apart.
- `ent_toNat`: the address of an entry, as a number.
- `RegsIn`, `upd`, `RegsIn.push`.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

theorem reg_max : ∀ r, regMax r ≤ 72
  | 0 => by decide
  | 1 => by decide
  | _ + 2 => by decide

/-- The registrars' tables with their counts are apart. -/
theorem reg_apart : ∀ r < 3, ∀ r' < 3, r ≠ r' →
    (regCnt r').toNat + 4 ≤ (regTab r).toNat ∨ (regCnt r).toNat + 4 ≤ (regTab r').toNat := by decide

/-- The entry `i` of the registrar `r`'s table, as a number. -/
theorem ent_toNat (r i : Nat) (hi : i ≤ regMax r) :
    (regTab r + BitVec.ofNat 64 (8 * i)).toNat = (regTab r).toNat + 8 * i := by
  obtain ⟨c4, t8, ap⟩ := reg_lay r
  have := reg_max r
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Eight bytes where `V'` is `V`. -/
theorem rdq_eq {V V' : Addr → Byte} {x : Addr} (hx : x.toNat + 8 ≤ 2 ^ 64)
    (h : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + 8 → V' a = V a) : rdq(V', x) = rdq(V, x) :=
  congrArg (ofBytesLE 64) (Csu.rd_in (lo := x.toNat) (hi := x.toNat + 8) (fun a ha => h a ha.1 ha.2) hx
    (Nat.le_refl _) (Nat.le_refl _))

/-- Four bytes where `V'` is `V`. -/
theorem rdd_eq {V V' : Addr → Byte} {x : Addr} (hx : x.toNat + 4 ≤ 2 ^ 64)
    (h : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + 4 → V' a = V a) : rdd(V', x) = rdd(V, x) :=
  congrArg (ofBytesLE 32) (Csu.rd_in (lo := x.toNat) (hi := x.toNat + 4) (fun a ha => h a ha.1 ha.2) hx
    (Nat.le_refl _) (Nat.le_refl _))

/-- The table of each registrar `r` holds the list `R r`, its count the length. -/
def RegsIn (R : Nat → List (BitVec 64)) (V : Addr → Byte) : Prop :=
  ∀ r < 3, rdd(V, regCnt r).toNat = (R r).length ∧ (R r).length ≤ regMax r ∧
    ∀ i < (R r).length, rdq(V, regTab r + BitVec.ofNat 64 (8 * i)) = (R r).getD i 0

/-- `p` added at the end of the list of `r`. -/
def upd (R : Nat → List (BitVec 64)) (r : Nat) (p : BitVec 64) : Nat → List (BitVec 64) :=
  fun r' => if r' = r then R r ++ [p] else R r'

/-- A registrar's call with room adds its argument at the end of its table. -/
theorem RegsIn.push {R : Nat → List (BitVec 64)} {V V' : Addr → Byte} {r : Nat} {p : BitVec 64}
    (h : RegsIn R V) (hr : r < 3) (hn : (R r).length < regMax r)
    (hO : RegOut (regCnt r) (regTab r) (regMax r) p V V') : RegsIn (upd R r p) V' := by
  obtain ⟨hc, -, he⟩ := h r hr
  obtain ⟨c4, t8, ap⟩ := reg_lay r
  have hx := reg_max r
  have hm : rdd(V, regCnt r).toNat < regMax r := hc ▸ hn
  unfold RegOut at hO
  rw [if_pos hm] at hO
  obtain ⟨h1, h2, h3⟩ := hO
  intro r' hr'
  by_cases e : r' = r
  · rw [e, upd, if_pos rfl, List.length_append, List.length_singleton]
    refine ⟨?_, by omega, fun i hi => ?_⟩
    · rw [h1, BitVec.toNat_add, BitVec.toNat_ofNat, hc]
      omega
    rcases Nat.lt_or_ge i (R r).length with hi' | hi'
    · have hg : (R r ++ [p]).getD i 0 = (R r).getD i 0 := List.getD_append _ _ _ _ hi'
      have ht := ent_toNat r i (by omega)
      rw [hg, ← he i hi']
      exact rdq_eq (by omega) fun a h4 h5 => h3 a (by omega) (by omega)
    · obtain rfl : i = (R r).length := by omega
      have hg : (R r ++ [p]).getD (R r).length 0 = p := by simp
      have ha : regTab r + BitVec.ofNat 64 (8 * (R r).length) =
          regTab r + rdd(V, regCnt r).setWidth 64 * 8#64 :=
        BitVec.eq_of_toNat_eq ((ent_toNat r _ (by omega)).trans (by rw [slot_toNat _ _ t8, hc]))
      rw [hg, ha]
      exact h2
  · rw [upd, if_neg e]
    obtain ⟨hc', hle', he'⟩ := h r' hr'
    obtain ⟨c4', t8', ap'⟩ := reg_lay r'
    have hx' := reg_max r'
    have hap := reg_apart r hr r' hr' (Ne.symm e)
    refine ⟨?_, hle', fun i hi => ?_⟩
    · rw [← hc', rdd_eq c4' fun a h4 h5 => h3 a (by omega) (by omega)]
    · have ht := ent_toNat r' i (by omega)
      rw [← he' i hi]
      exact rdq_eq (by omega) fun a h4 h5 => h3 a (by omega) (by omega)

end FV7z.Ctor
