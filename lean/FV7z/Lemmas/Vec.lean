import ZellicX86.Spec.Semantics
/-!
# Vectors, bit by bit (PLAN.md G2.1)

The model builds the values of its vector instructions with `ofBits` and `ofElems` (folds over `List.range`) and takes
them apart with `elem`; memory is read as `ofBytesLE`. Here each is described one bit at a time (`getLsbD`), and from
that one element or byte at a time: what `memcmp`'s vector code needs of `VPCMPEQB`, `VPMOVMSKB`, `VPAND`, `VPTEST`.
-/
namespace FV7z
open ZellicX86

attribute [-simp] BitVec.getLsbD_eq_getElem

/-! ## Bits -/

theorem getLsbD_one_shiftLeft {n j i : Nat} :
    ((1 : BitVec n) <<< j).getLsbD i = (decide (i = j) && decide (i < n)) := by
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases h : i = j <;> by_cases h' : i < n <;> by_cases h'' : i < j <;> simp_all <;> omega

theorem ofBits_foldl (n : Nat) (f : Nat → Bool) (i : Nat) : ∀ (l : List Nat) (acc : BitVec n),
    (l.foldl (fun acc j => if f j then acc ||| ((1 : BitVec n) <<< j) else acc) acc).getLsbD i =
      (acc.getLsbD i || (decide (i ∈ l) && f i && decide (i < n)))
  | [], acc => by simp
  | j :: l, acc => by
    rw [List.foldl_cons, ofBits_foldl n f i l]
    by_cases hj : f j
    · simp only [hj, ↓reduceIte, BitVec.getLsbD_or, getLsbD_one_shiftLeft, List.mem_cons]
      by_cases h : i = j
      · subst h; cases acc.getLsbD i <;> by_cases hn : i < n <;> simp [hj, hn]
      · simp [h]
    · simp only [hj, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      by_cases h : i = j
      · subst h; simp [hj]
      · simp [h]

@[simp] theorem getLsbD_ofBits (n : Nat) (f : Nat → Bool) (i : Nat) :
    (ofBits n f).getLsbD i = (decide (i < n) && f i) := by
  unfold ofBits
  rw [ofBits_foldl]
  cases f i <;> by_cases h : i < n <;> simp [h]

theorem ofBits_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) : ofBits n f = ofBits n g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_ofBits, getLsbD_ofBits, h i hi]

theorem getLsbD_elemAt (w k : Nat) (hk : 0 < k) (x : BitVec k) (i j : Nat) :
    (x.setWidth w <<< (k * j)).getLsbD i = (decide (i / k = j) && decide (i < w) && x.getLsbD (i % k)) := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h1 : i < k * j
  · have : i / k ≠ j := by
      intro e; subst e; have := Nat.div_mul_le_self i k; rw [Nat.mul_comm] at h1; omega
    simp [h1, this]
  · by_cases h2 : i - k * j < k
    · have e1 : i / k = j := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · rw [Nat.mul_comm]; omega
        · rw [Nat.succ_mul, Nat.mul_comm]; omega
      have e2 : i % k = i - k * j := by subst e1; have := Nat.mod_add_div i k; omega
      by_cases hw : i < w
      · have : i - k * j < w := by omega
        simp [h1, e1, e2, hw, this]
      · simp [h1, e1, hw]
    · have : i / k ≠ j := by
        intro e; subst e; have := Nat.mod_add_div i k; have := Nat.mod_lt i hk; omega
      simp [h1, this, BitVec.getLsbD_of_ge x (i - k * j) (by omega)]

theorem ofElems_foldl (w k : Nat) (hk : 0 < k) (f : Nat → BitVec k) (i : Nat) : ∀ (l : List Nat) (acc : BitVec w),
    (l.foldl (fun acc j => acc ||| ((f j).setWidth w <<< (k * j))) acc).getLsbD i =
      (acc.getLsbD i || (decide (i / k ∈ l) && decide (i < w) && (f (i / k)).getLsbD (i % k)))
  | [], acc => by simp
  | j :: l, acc => by
    rw [List.foldl_cons, ofElems_foldl w k hk f i l, BitVec.getLsbD_or, getLsbD_elemAt w k hk]
    by_cases h : i / k = j
    · subst h
      cases acc.getLsbD i <;> cases (f (i / k)).getLsbD (i % k) <;> simp
    · simp [h]

@[simp] theorem getLsbD_ofElems (w k : Nat) (hk : 0 < k) (f : Nat → BitVec k) (i : Nat) :
    (ofElems w k f).getLsbD i = (decide (i / k < w / k) && decide (i < w) && (f (i / k)).getLsbD (i % k)) := by
  unfold ofElems
  rw [ofElems_foldl w k hk]
  simp

@[simp] theorem getLsbD_elem {w : Nat} (k : Nat) (x : BitVec w) (j i : Nat) :
    (elem k x j).getLsbD i = (decide (i < k) && x.getLsbD (k * j + i)) := by
  simp [elem, BitVec.getLsbD_extractLsb']

theorem elem_ofElems {w k : Nat} (hk : 0 < k) (f : Nat → BitVec k) {j : Nat} (hj : j < w / k) :
    elem k (ofElems w k f) j = f j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : (k * j + i) / k = j := by
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hi]; simp
  have h2 : (k * j + i) % k = i := by rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have h3 : k * j + i < w := by
    have := Nat.div_mul_le_self w k
    have : (j + 1) * k ≤ w / k * k := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at this; rw [Nat.mul_comm]; omega
  simp [getLsbD_ofElems w k hk, h1, h2, hj, h3, hi]

/-! ## Bytes -/

theorem getLsbD_ofBytesLE (w : Nat) : ∀ (bs : List Byte) (i : Nat),
    (ofBytesLE w bs).getLsbD i = (decide (i < w) && decide (i / 8 < bs.length) && (bs.getD (i / 8) 0).getLsbD (i % 8))
  | [], i => by simp [ofBytesLE]
  | b :: bs, i => by
    simp only [ofBytesLE, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
      getLsbD_ofBytesLE w bs (i - 8), List.length_cons]
    by_cases h8 : i < 8
    · rw [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8]
      by_cases hw : i < w <;> simp [h8, hw]
    · rw [show i / 8 = (i - 8) / 8 + 1 by omega, show i % 8 = (i - 8) % 8 by omega,
        BitVec.getLsbD_of_ge b i (by omega)]
      by_cases hw : i < w
      · have : i - 8 < w := by omega
        simp [h8, hw, this]
      · simp [hw]

theorem elem_ofBytesLE {w : Nat} {bs : List Byte} {j : Nat} (hj : j < bs.length) (hw : 8 * bs.length ≤ w) :
    elem 8 (ofBytesLE w bs) j = bs[j] := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h1 : (8 * j + i) / 8 = j := by omega
  have h2 : (8 * j + i) % 8 = i := by omega
  simp only [getLsbD_elem, getLsbD_ofBytesLE, h1, h2, hj]
  have : 8 * j + i < w := by omega
  simp [this, hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

end FV7z
