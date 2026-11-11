import Examples.Memcmp.Statement
import FV7z.Lemmas.Vec
/-!
# The order of byte strings (PLAN.md G2.1)

What `memcmp`'s implementations compute, related to `Memcmp.cmpBytes` (the C standard's order: the first byte that
differs decides, as an `unsigned char`):
- by the first index where the strings differ (`cmp_first`, `cmp_all`);
- by blocks (`cmp_append`), and by two blocks that overlap and cover the strings (`cmp_cover`), as the short cases of
  `__memcmp_avx2_movbe` compare `n` bytes as the first `k` and the last `n - j`;
- by the big-endian value of the bytes (`cmp_be`), as `MOVBE` and `BSWAP` load them.
-/
namespace FV7z.Order
open ZellicX86 Memcmp

theorem cmp_self : ∀ xs : List Byte, cmpBytes xs xs = .eq
  | [] => rfl
  | x :: xs => by simp [cmpBytes, cmp_self xs]

theorem compare_byte_eq {x y : Byte} : compare x.toNat y.toNat = .eq ↔ x = y := by
  rw [Nat.compare_eq_eq]
  exact ⟨BitVec.eq_of_toNat_eq, fun h => h ▸ rfl⟩

/-- Of strings of one length, the order is `eq` exactly when they are equal. -/
theorem cmp_eq_iff : ∀ {xs ys : List Byte}, xs.length = ys.length → (cmpBytes xs ys = .eq ↔ xs = ys)
  | [], [], _ => by simp [cmpBytes]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    by_cases hxy : x = y
    · simp [cmpBytes, hxy, cmp_eq_iff h]
    · simp only [cmpBytes, hxy, ↓reduceIte, List.cons.injEq, false_and, iff_false]
      exact fun e => hxy (compare_byte_eq.1 e)

/-- Two blocks: the first decides, unless equal. -/
theorem cmp_append : ∀ {a c : List Byte} (b d : List Byte), a.length = c.length →
    cmpBytes (a ++ b) (c ++ d) = if a = c then cmpBytes b d else cmpBytes a c
  | [], [], b, d, _ => by simp
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: a, y :: c, b, d, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.cons_append, cmpBytes, List.cons.injEq, cmp_append b d h]
    by_cases hxy : x = y <;> by_cases hac : a = c <;> simp [hxy, hac]

/-- The first difference decides. -/
theorem cmp_first : ∀ (xs ys : List Byte) (q : Nat) (hx : q < xs.length) (hy : q < ys.length),
    (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), i < q → xs[i] = ys[i]) → xs[q] ≠ ys[q] →
      cmpBytes xs ys = compare xs[q].toNat ys[q].toNat
  | [], _, _, hx, _, _, _ => by simp at hx
  | _ :: _, [], _, _, hy, _, _ => by simp at hy
  | x :: xs, y :: ys, 0, _, _, _, hne => by
    simp only [List.getElem_cons_zero] at hne ⊢
    simp [cmpBytes, hne]
  | x :: xs, y :: ys, q + 1, hx, hy, hp, hne => by
    have h0 : x = y := hp 0 (by simp) (by simp) (by omega)
    simp only [List.getElem_cons_succ] at hne ⊢
    simp only [cmpBytes, h0, ↓reduceIte]
    exact cmp_first xs ys q (by simpa using hx) (by simpa using hy)
      (fun i h₁ h₂ hi => hp (i + 1) (by simpa using h₁) (by simpa using h₂) (by omega)) hne

/-- No difference: `eq`. -/
theorem cmp_all : ∀ (xs ys : List Byte), xs.length = ys.length →
    (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), xs[i] = ys[i]) → cmpBytes xs ys = .eq
  | xs, ys, hl, h => (cmp_eq_iff hl).2 (List.ext_getElem hl fun i h₁ h₂ => h i h₁ h₂)

/-- The first `k` bytes and the bytes from `j ≤ k` on, two blocks that overlap and cover the strings, compare as the
strings do. -/
theorem cmp_cover {xs ys : List Byte} {j k : Nat} (hl : xs.length = ys.length) (hjk : j ≤ k) :
    cmpBytes (xs.take k ++ xs.drop j) (ys.take k ++ ys.drop j) = cmpBytes xs ys := by
  have htk : (xs.take k).length = (ys.take k).length := by simp [hl]
  have hsplit : ∀ zs : List Byte, zs.drop j = (zs.take k).drop j ++ zs.drop k := fun zs => by
    conv => lhs; rw [← List.take_append_drop k zs]
    rw [List.drop_append]
    congr 1
    by_cases h : k ≤ zs.length
    · rw [List.length_take, Nat.min_eq_left h, Nat.sub_eq_zero_of_le hjk, List.drop_zero]
    · simp [List.drop_eq_nil_of_le (show zs.length ≤ k by omega)]
  rw [cmp_append _ _ htk]
  conv => rhs; rw [← List.take_append_drop k xs, ← List.take_append_drop k ys, cmp_append _ _ htk]
  split
  · next h => rw [hsplit xs, hsplit ys, h, cmp_append _ _ rfl]; simp
  · rfl

/-! ## Big-endian values -/

/-- The value of bytes read as a big-endian number. -/
def beV : List Byte → Nat
  | [] => 0
  | x :: xs => x.toNat * 256 ^ xs.length + beV xs

theorem beV_lt : ∀ xs : List Byte, beV xs < 256 ^ xs.length
  | [] => by simp [beV]
  | x :: xs => by
    have := beV_lt xs; have hx := x.isLt
    simp only [beV, List.length_cons, Nat.pow_succ]
    have : x.toNat * 256 ^ xs.length + beV xs < (x.toNat + 1) * 256 ^ xs.length := by rw [Nat.succ_mul]; omega
    have : (x.toNat + 1) * 256 ^ xs.length ≤ 256 * 256 ^ xs.length := Nat.mul_le_mul_right _ hx
    rw [Nat.mul_comm (256 ^ xs.length)]; omega

/-- Of strings of one length, the order of their big-endian values is theirs. -/
theorem cmp_be : ∀ {xs ys : List Byte}, xs.length = ys.length → compare (beV xs) (beV ys) = cmpBytes xs ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [beV, cmpBytes]
    have hu : beV xs < 256 ^ ys.length := h ▸ beV_lt xs
    have hv := beV_lt ys
    by_cases hxy : x = y
    · subst hxy; simp only [↓reduceIte, h]; rw [← cmp_be h]
      rcases Nat.lt_trichotomy (beV xs) (beV ys) with c | c | c
      · rw [Nat.compare_eq_lt.2 c, Nat.compare_eq_lt.2 (by omega)]
      · rw [Nat.compare_eq_eq.2 c, Nat.compare_eq_eq.2 (by omega)]
      · rw [Nat.compare_eq_gt.2 c, Nat.compare_eq_gt.2 (by omega)]
    · simp only [hxy, ↓reduceIte, h]
      have hne : x.toNat ≠ y.toNat := fun e => hxy (BitVec.eq_of_toNat_eq e)
      rcases Nat.lt_or_gt_of_ne hne with c | c
      · have : (x.toNat + 1) * 256 ^ ys.length ≤ y.toNat * 256 ^ ys.length := Nat.mul_le_mul_right _ c
        rw [Nat.succ_mul] at this
        rw [Nat.compare_eq_lt.2 c, Nat.compare_eq_lt.2 (by omega)]
      · have : (y.toNat + 1) * 256 ^ ys.length ≤ x.toNat * 256 ^ ys.length := Nat.mul_le_mul_right _ c
        rw [Nat.succ_mul] at this
        rw [Nat.compare_eq_gt.2 c, Nat.compare_eq_gt.2 (by omega)]

/-! ## Strings in memory -/

theorem readBytes_length (m : Memory) (a : Addr) (n : Nat) : (readBytes m a n).length = n := by
  simp [readBytes, byteAddrs]

theorem readBytes_getElem (m : Memory) (a : Addr) (n i : Nat) (h : i < (readBytes m a n).length) :
    (readBytes m a n)[i] = m.readByte (a.add i) := by
  simp [readBytes, byteAddrs]

theorem readBytes_take (m : Memory) (a : Addr) (n i : Nat) (h : i ≤ n) :
    (readBytes m a n).take i = readBytes m a i := by
  simp [readBytes, byteAddrs, ← List.map_take, List.take_range, Nat.min_eq_left h]

theorem readBytes_drop (m : Memory) (a : Addr) (n i : Nat) :
    (readBytes m a n).drop i = readBytes m (a.add i) (n - i) := by
  apply List.ext_getElem (by simp [readBytes_length])
  intro j h₁ h₂
  simp only [List.getElem_drop, readBytes_getElem, Addr.add]
  congr 1
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp

/-- The bytes of the strings at `p` and `q` in `m` agree at index `i`. -/
abbrev Agree (m : Memory) (p q : Addr) (i : Nat) : Prop := m.readByte (p.add i) = m.readByte (q.add i)

theorem cmp_mem_all {m : Memory} {p q : Addr} {n : Nat} (h : ∀ i < n, Agree m p q i) :
    cmpBytes (readBytes m p n) (readBytes m q n) = .eq :=
  cmp_all _ _ (by simp [readBytes_length]) fun i h₁ _ => by
    simp only [readBytes_getElem]; exact h i (by simpa [readBytes_length] using h₁)

theorem cmp_mem_first {m : Memory} {p q : Addr} {n k : Nat} (hk : k < n) (h : ∀ i < k, Agree m p q i)
    (hne : ¬ Agree m p q k) :
    cmpBytes (readBytes m p n) (readBytes m q n) =
      compare (m.readByte (p.add k)).toNat (m.readByte (q.add k)).toNat := by
  rw [cmp_first _ _ k (by simp [readBytes_length, hk]) (by simp [readBytes_length, hk])
    (fun i _ _ hi => by simp only [readBytes_getElem]; exact h i hi) (by simp only [readBytes_getElem]; exact hne)]
  simp only [readBytes_getElem]

end FV7z.Order
