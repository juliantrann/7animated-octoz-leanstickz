import FV7z.Lemmas.StoreX
/-!
# Bytes copied by stores (PLAN.md M, `__memmove_sse2_unaligned`)

`FillP` (`StoreX.lean`) for a copy: `CopyP V V₂ d s n P`, the bytes `V₂` are `V` outside the `n` bytes from `d`, and
at those of them whose offsets are in `P` the bytes of `V` as many bytes from `s` on. A copy of 16 to 32 bytes is
two loads and two stores that overlap; each store adds its offsets (`CopyP.st`).

- `map_byteAddrs_get?`, `Vst_get`: the `k`-th byte of a load; the `k`-th byte stored.
- `CopyP.start`, `CopyP.mono`, `CopyP.st`, `CopyP.ld`: the bytes loaded from `V` at `s + o`, stored at `d + o`.
-/
namespace FV7z
open ZellicX86

theorem map_byteAddrs_get? (f : Addr → Byte) :
    ∀ (n : Nat) (a : Addr) (k : Nat), k < n → ((byteAddrs a n).map f)[k]? = some (f (a.add k))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, 0, _ => by rw [byteAddrs_succ, List.map_cons, List.getElem?_cons_zero, addr_add_zero]
  | n + 1, a, k + 1, h => by
    rw [byteAddrs_succ, List.map_cons, List.getElem?_cons_succ, map_byteAddrs_get? f n (a.add 1) k (by omega),
      addr_add_add, Nat.add_comm 1 k]

theorem Vst_get (bs : List Byte) (V : Addr → Byte) (a : Addr) (hf : a.toNat + bs.length ≤ 2 ^ 64) {k : Nat}
    (hk : k < bs.length) : Vst V a bs (a.add k) = bs[k] := by
  have e := congrArg (·[k]?) (Vst_self bs V a hf)
  dsimp only at e
  rw [map_byteAddrs_get? _ bs.length a k hk, List.getElem?_eq_getElem hk] at e
  exact Option.some.inj e

/-- The bytes `V₂`: `V` outside the `n` bytes from `d`, those of `V` from `s` at the offsets `P`. -/
def CopyP (V V₂ : Addr → Byte) (d s : Addr) (n : Nat) (P : Nat → Prop) : Prop :=
  (∀ i < n, P i → V₂ (d.add i) = V (s.add i)) ∧ ∀ x : Addr, ¬ (d.toNat ≤ x.toNat ∧ x.toNat < d.toNat + n) → V₂ x = V x

theorem CopyP.start (V : Addr → Byte) (d s : Addr) (n : Nat) : CopyP V V d s n fun _ => False :=
  ⟨fun _ _ h => h.elim, fun _ _ => rfl⟩

theorem CopyP.mono {V V₂ : Addr → Byte} {d s : Addr} {n : Nat} {P Q : Nat → Prop} (h : CopyP V V₂ d s n P)
    (hq : ∀ i < n, Q i → P i) : CopyP V V₂ d s n Q :=
  ⟨fun i hi hQ => h.1 i hi (hq i hi hQ), h.2⟩

/-- The bytes of a load of `k` bytes of `V` at `s + o`. -/
theorem CopyP.ld {V : Addr → Byte} {s : Addr} {o k : Nat} :
    ∀ j (hj : j < ((byteAddrs (s.add o) k).map V).length),
      ((byteAddrs (s.add o) k).map V)[j] = V (s.add (o + j)) := by
  intro j hj
  have hk : j < k := by simpa using hj
  have e := map_byteAddrs_get? V k (s.add o) j hk
  rw [List.getElem?_eq_getElem hj, addr_add_add] at e
  exact Option.some.inj e

/-- A store at offset `o` of the `n` bytes of `k` bytes, those of `V` at offset `o` from `s`. -/
theorem CopyP.st {V V₂ : Addr → Byte} {d s : Addr} {n : Nat} {P : Nat → Prop} (h : CopyP V V₂ d s n P)
    (hn : d.toNat + n ≤ 2 ^ 64) {o k : Nat} {bs : List Byte} (hl : bs.length = k) (ho : o + k ≤ n)
    (hb : ∀ j (hj : j < bs.length), bs[j] = V (s.add (o + j))) :
    CopyP V (Vst V₂ (d.add o) bs) d s n fun i => P i ∨ (o ≤ i ∧ i < o + k) := by
  subst hl
  have hao : (d.add o).toNat = d.toNat + o ∨ bs.length = 0 := by
    rcases Nat.eq_zero_or_pos bs.length with h0 | h0
    · exact .inr h0
    · exact .inl (toNat_add_of_fits (n := n) (by omega) hn)
  refine ⟨fun i hi hp => ?_, fun x hx => ?_⟩
  · by_cases hio : o ≤ i ∧ i < o + bs.length
    · have e : d.add i = (d.add o).add (i - o) := by rw [addr_add_add]; congr 1; omega
      have hf : (d.add o).toNat + bs.length ≤ 2 ^ 64 := by
        rcases hao with h1 | h1
        · rw [h1]; omega
        · omega
      rw [e, Vst_get bs V₂ (d.add o) hf (by omega), hb _ (by omega), show o + (i - o) = i by omega]
    · rcases hp with hp | hp
      · rw [Vst_apart bs _ _ _ fun k hk e => ?_]
        · exact h.1 i hi hp
        · have h1 := congrArg BitVec.toNat e
          rw [toNat_add_of_fits (n := n) hi hn, addr_add_add, toNat_add_of_fits (n := n) (by omega) hn] at h1
          omega
      · exact absurd hp hio
  · rw [Vst_apart bs _ _ _ fun k hk e => hx ?_]
    · exact h.2 x hx
    · rw [e, addr_add_add, toNat_add_of_fits (n := n) (by omega) hn]
      omega

end FV7z
