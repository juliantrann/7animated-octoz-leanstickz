import FV7z.Tun.Inv
/-!
# `_dl_important_hwcaps`: the table of the result and the frame as facts about the bytes (PLAN.md G3, startup)

The pieces after `malloc` store into the table of `E` entries of 16 bytes at `P` (a pointer at `P + 16 i`, a length
at `P + 16 i + 8`) and read the frame. The composition keeps, instead of the chain of stores:

- `Tab V P E σ ℓ`: the pointers `σ i` and the lengths `ℓ i` of the table in `V`; `Tab.stL`, `Tab.stS` (a store to
  an entry: `upd`), `Tab.out` (a store apart from the table), `Tab.congr`.
- `Same V W lo hi`: the bytes from `lo` to `hi` (the frame, `temp`) the same; `Same.st` (a store apart),
  `Same.rd` (a load inside), `Same.trans`.
-/
open ZellicX86 Decode FV7z
namespace FV7z.Hwc

/-- `P + k` fits: its `toNat`. -/
theorem toNat_off {P : Addr} {k : Nat} (h : P.toNat + k < 2 ^ 64) :
    (P + BitVec.ofNat 64 k).toNat = P.toNat + k := by
  have hk : k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega)]

/-- `f` with `v` at `j`. -/
def upd (f : Nat → Addr) (j : Nat) (v : Addr) : Nat → Addr := fun i => if i = j then v else f i

/-- The table at `P`: entry `i < E` the pointer `σ i` at `P + 16 i` and the length `ℓ i` at `P + 16 i + 8`. -/
def Tab (V : Addr → Byte) (P : Addr) (E : Nat) (σ ℓ : Nat → Addr) : Prop :=
  ∀ i < E, rdq(V, P + BitVec.ofNat 64 (16 * i)) = σ i ∧ rdq(V, P + BitVec.ofNat 64 (16 * i + 8)) = ℓ i

variable {V : Addr → Byte} {P : Addr} {E : Nat} {σ ℓ : Nat → Addr}

theorem Tab.congr (hT : Tab V P E σ ℓ) {σ' ℓ' : Nat → Addr} (hs : ∀ i < E, σ i = σ' i)
    (hl : ∀ i < E, ℓ i = ℓ' i) : Tab V P E σ' ℓ' := fun i hi =>
  ⟨(hT i hi).1.trans (hs i hi), (hT i hi).2.trans (hl i hi)⟩

/-- A store apart from the table. -/
theorem Tab.out (hT : Tab V P E σ ℓ) (hP : P.toNat + 16 * E ≤ 2 ^ 64) {a : Addr} {bs : List Byte}
    (ha : a.toNat + bs.length ≤ 2 ^ 64) (h : a.toNat + bs.length ≤ P.toNat ∨ P.toNat + 16 * E ≤ a.toNat) :
    Tab (Vst V a bs) P E σ ℓ := by
  intro i hi
  obtain ⟨h1, h2⟩ := hT i hi
  have e1 : (P + BitVec.ofNat 64 (16 * i)).toNat = P.toNat + 16 * i := toNat_off (by omega)
  have e2 : (P + BitVec.ofNat 64 (16 * i + 8)).toNat = P.toNat + (16 * i + 8) := toNat_off (by omega)
  refine ⟨?_, ?_⟩
  · rw [Tun.rd_Vst _ _ _ _ _ ha (by rw [e1]; omega) (by rw [e1]; omega)]
    exact h1
  · rw [Tun.rd_Vst _ _ _ _ _ ha (by rw [e2]; omega) (by rw [e2]; omega)]
    exact h2

/-- The length of entry `j` stored. -/
theorem Tab.stL (hT : Tab V P E σ ℓ) (hP : P.toNat + 16 * E ≤ 2 ^ 64) {j : Nat} (hj : j < E) (v : Addr) :
    Tab (Vst V (P + BitVec.ofNat 64 (16 * j + 8)) (toBytesLE v 8)) P E σ (upd ℓ j v) := by
  intro i hi
  obtain ⟨h1, h2⟩ := hT i hi
  have l8 : (toBytesLE v 8).length = 8 := toBytesLE_length _ _
  have ej : (P + BitVec.ofNat 64 (16 * j + 8)).toNat = P.toNat + (16 * j + 8) := toNat_off (by omega)
  have e1 : (P + BitVec.ofNat 64 (16 * i)).toNat = P.toNat + 16 * i := toNat_off (by omega)
  have e2 : (P + BitVec.ofNat 64 (16 * i + 8)).toNat = P.toNat + (16 * i + 8) := toNat_off (by omega)
  refine ⟨?_, ?_⟩
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [l8, ej]; omega) (by rw [e1]; omega) (by rw [l8, ej, e1]; omega)]
    exact h1
  · unfold upd
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, Tun.rd_Vst_self _ _ _ l8 (by rw [ej]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    · rw [ite_eq_right hij, Tun.rd_Vst _ _ _ _ _ (by rw [l8, ej]; omega) (by rw [e2]; omega) (by rw [l8, ej, e2]; omega)]
      exact h2

/-- The pointer of entry `j` stored. -/
theorem Tab.stS (hT : Tab V P E σ ℓ) (hP : P.toNat + 16 * E ≤ 2 ^ 64) {j : Nat} (hj : j < E) (v : Addr) :
    Tab (Vst V (P + BitVec.ofNat 64 (16 * j)) (toBytesLE v 8)) P E (upd σ j v) ℓ := by
  intro i hi
  obtain ⟨h1, h2⟩ := hT i hi
  have l8 : (toBytesLE v 8).length = 8 := toBytesLE_length _ _
  have ej : (P + BitVec.ofNat 64 (16 * j)).toNat = P.toNat + 16 * j := toNat_off (by omega)
  have e1 : (P + BitVec.ofNat 64 (16 * i)).toNat = P.toNat + 16 * i := toNat_off (by omega)
  have e2 : (P + BitVec.ofNat 64 (16 * i + 8)).toNat = P.toNat + (16 * i + 8) := toNat_off (by omega)
  refine ⟨?_, ?_⟩
  · unfold upd
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, Tun.rd_Vst_self _ _ _ l8 (by rw [ej]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    · rw [ite_eq_right hij, Tun.rd_Vst _ _ _ _ _ (by rw [l8, ej]; omega) (by rw [e1]; omega) (by rw [l8, ej, e1]; omega)]
      exact h1
  · rw [Tun.rd_Vst _ _ _ _ _ (by rw [l8, ej]; omega) (by rw [e2]; omega) (by rw [l8, ej, e2]; omega)]
    exact h2

/-- The bytes from `lo` to `hi` the same in `V` and `W`. -/
def Same (V W : Addr → Byte) (lo hi : Nat) : Prop := ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → W a = V a

theorem Same.refl (V : Addr → Byte) (lo hi : Nat) : Same V V lo hi := fun _ _ _ => rfl

theorem Same.trans {U W : Addr → Byte} {lo hi : Nat} (h1 : Same U V lo hi) (h2 : Same V W lo hi) :
    Same U W lo hi := fun a h h' => (h2 a h h').trans (h1 a h h')

/-- A store apart from `lo`, `hi`. -/
theorem Same.st {W : Addr → Byte} {lo hi : Nat} (hS : Same V W lo hi) {a : Addr} {bs : List Byte}
    (ha : a.toNat + bs.length ≤ 2 ^ 64) (h : a.toNat + bs.length ≤ lo ∨ hi ≤ a.toNat) :
    Same V (Vst W a bs) lo hi := fun x h1 h2 => by
  rw [Tun.Vst_out _ _ _ _ ha (by omega)]
  exact hS x h1 h2

/-- A load of `n` bytes inside `lo`, `hi`. -/
theorem Same.rd {W : Addr → Byte} {lo hi : Nat} (hS : Same V W lo hi) {x : Addr} {n : Nat}
    (h1 : lo ≤ x.toNat) (h2 : x.toNat + n ≤ hi) (hx : x.toNat + n ≤ 2 ^ 64) :
    List.map W (byteAddrs x n) = List.map V (byteAddrs x n) := by
  apply List.map_congr_left
  intro y hy
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  have e := toNat_add_of_fits hj hx
  exact hS _ (by rw [e]; omega) (by rw [e]; omega)

end FV7z.Hwc
