import FV7z.Utr.Cuts
import FV7z.Rfw.Holds
/-!
# `UString::TrimRight` (PLAN.md §M, M1)

7-Zip 26.06's `UString::TrimRight ()` at `0x44de20` in `7zzs` (`CPP/Common/MyString.cpp`; `objdump -d`): for the
string at `p` = `rdi` (`Rfw.chs`, `Rfw.len`, `Rfw.ch`: the characters, the length, the `k`-th character), from the
end back past the characters 9, 10 and ' ' (`Ws`); if any were passed, the 0 at the index `k` of the first of them
(`_chars[k]` = 0) and `_len` = `k`. Cut points: the entry (0), the loop's head (32, `edx` the characters left), the
step back (50) and the stores (59); the `ret` at 69.

- `Ws`, `Tail k`: a blank character; the characters from `k` on blank.
- `Sh n`: the registers in the loop (`rax` = 4 `n`, `edx` = `n`, `r8` the characters, `r9` the length).
- `Inv`, `Fin`, `Nx`: the invariant (measure 2 `n` at 32, 2 `n` - 1 at 50, 0 at 59), the end, the post of
  `Seg.cfg`; `vc_*`: the cut points' conditions; `utr_ok`: from the entry to the return address, `k` the new
  length and the bytes `Out` (as they were when nothing was trimmed).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Rfw (chs len ch Fp)
namespace FV7z.Utr

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_69 : pret <+: utr.drop 69 := by decide +kernel
theorem ret_69 (feat : Features) : Dec feat utr 69 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 69) (k := 0) (pret_0 feat) w_69 (Nat.zero_le _)

/-! ## Arithmetic -/

/-- `lea esi, [rcx - 9]; cmp esi, 1; jbe` not taken for a character other than 9 and 10. -/
theorem b1f {c : BitVec 32} (h1 : c ≠ 9#32) (h2 : c ≠ 10#32) :
    (decide ((BitVec.setWidth 32 (BitVec.setWidth 64 c + 18446744073709551607#64)).toNat < 1) ||
      decide (BitVec.setWidth 32 (BitVec.setWidth 64 c + 18446744073709551607#64) = 1#32)) = false := by
  have e : BitVec.setWidth 32 (BitVec.setWidth 64 c + 18446744073709551607#64) = c - 9#32 := by bv_omega
  rw [e, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
  exact ⟨fun h => h1 (by bv_omega), fun h => h2 (by bv_omega)⟩

theorem shl4 (x : BitVec 32) : BitVec.setWidth 64 x <<< 2 = BitVec.ofNat 64 (4 * x.toNat) := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem swl (x : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 x) = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem o4s (m : Nat) : BitVec.ofNat 64 (4 * (m + 1)) = BitVec.ofNat 64 (4 * m) + 4#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The address of the character `m`, `rax` = 4 (`m` + 1). -/
theorem ldA (C : Addr) {a : BitVec 64} {m : Nat} (ha : a = BitVec.ofNat 64 (4 * (m + 1))) :
    C + a + 18446744073709551612#64 = Addr.add C (4 * m) := by
  subst ha
  rw [o4s, BitVec.add_assoc, BitVec.add_assoc, show (4#64 : BitVec 64) + 18446744073709551612#64 = 0#64 by decide,
    BitVec.add_zero]
  first | rfl | simp only [Addr.add]

theorem sub4 (m : Nat) : BitVec.ofNat 64 (4 * (m + 1)) - 4#64 = BitVec.ofNat 64 (4 * m) := by
  rw [o4s, BitVec.add_sub_cancel]

theorem dec32 {m : Nat} (h : m + 1 < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 (m + 1) - 1#32)) = BitVec.ofNat 32 m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ne1 {m : Nat} (h1 : 1 ≤ m) (h : m + 1 < 2 ^ 32) : decide (BitVec.ofNat 32 (m + 1) = 1#32) = false := by
  rw [decide_eq_false_iff_not]
  intro e
  have e' := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at e'
  omega

theorem eqL {L : BitVec 32} {n : Nat} (h : L.toNat = n) : decide (L = BitVec.ofNat 32 n) = true := by
  rw [decide_eq_true_iff]
  apply BitVec.eq_of_toNat_eq
  have := L.isLt
  simp only [BitVec.toNat_ofNat]
  omega

theorem neL {L : BitVec 32} {n : Nat} (h : L.toNat ≠ n) (hn : n < 2 ^ 32) :
    decide (L = BitVec.ofNat 32 n) = false := by
  rw [decide_eq_false_iff_not]
  intro e
  have e' := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at e'
  omega

/-! ## The invariant -/

/-- A blank character: 9, 10 or ' '. -/
def Ws (c : BitVec 32) : Prop := c = 9#32 ∨ c = 10#32 ∨ c = 32#32

/-- The characters from `k` on blank. -/
def Tail (V : Addr → Byte) (p : Addr) (k : Nat) : Prop := ∀ j < (len V p).toNat, k ≤ j → Ws (ch V p j)

/-- The registers in the loop, `n` characters left. -/
def Sh (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) (g : Gprs) : Prop :=
  ∃ a c d s, g = { g₀ with rax := a, rcx := c, rdx := d, rsi := s, r8 := chs V₀ g₀.rdi,
                           r9 := BitVec.setWidth 64 (len V₀ g₀.rdi) } ∧
    a = BitVec.ofNat 64 (4 * n) ∧ BitVec.setWidth 32 d = BitVec.ofNat 32 n

/-- At the loop's head: `n` characters left, those after them blank. -/
def I32 (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) (g : Gprs) : Prop :=
  1 ≤ n ∧ n ≤ (len V₀ g₀.rdi).toNat ∧ Tail V₀ g₀.rdi n ∧ Sh g₀ V₀ n g
/-- At the step back: the character `n - 1` blank as well. -/
def I50 (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) (g : Gprs) : Prop :=
  1 ≤ n ∧ n ≤ (len V₀ g₀.rdi).toNat ∧ Tail V₀ g₀.rdi (n - 1) ∧ Sh g₀ V₀ n g
/-- At the stores: the new length `k`, below the old. -/
def I59 (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) : Prop :=
  ∃ k < (len V₀ g₀.rdi).toNat, Tail V₀ g₀.rdi k ∧ (k = 0 ∨ ¬ Ws (ch V₀ g₀.rdi (k - 1))) ∧
    ∃ a c d s, g = { g₀ with rax := a, rcx := c, rdx := d, rsi := s, r8 := Addr.add (chs V₀ g₀.rdi) (4 * k),
                             r9 := BitVec.setWidth 64 (len V₀ g₀.rdi) } ∧ BitVec.setWidth 32 d = BitVec.ofNat 32 k

/-- The invariant at the cut points. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ ((ℓ = 0 ∧ m = 2 * (len V₀ g₀.rdi).toNat + 1 ∧ g = g₀) ∨ (ℓ = 32 ∧ ∃ n, m = 2 * n ∧ I32 g₀ V₀ n g) ∨
    (ℓ = 50 ∧ ∃ n, m = 2 * n - 1 ∧ I50 g₀ V₀ n g) ∨ (ℓ = 59 ∧ m = 0 ∧ I59 g₀ V₀ g))

/-- The bytes at the end: as they were when `k` is the length, else the 0 at the index `k` and the length `k`. -/
def Out (g₀ : Gprs) (V₀ : Addr → Byte) (k : Nat) (V : Addr → Byte) : Prop :=
  (k = (len V₀ g₀.rdi).toNat ∧ V = V₀) ∨ (k < (len V₀ g₀.rdi).toNat ∧
    V = Vst (Vst V₀ (Addr.add (chs V₀ g₀.rdi) (4 * k)) (toBytesLE (0#32) 4)) (g₀.rdi + 8#64)
      (toBytesLE (BitVec.ofNat 32 k) 4))

/-- At the `ret`: the new length `k`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 69 ∧ ∃ k ≤ (len V₀ g₀.rdi).toNat, Tail V₀ g₀.rdi k ∧ (k = 0 ∨ ¬ Ws (ch V₀ g₀.rdi (k - 1))) ∧
    Out g₀ V₀ k V ∧ ∃ a c d s r8 r9, g = { g₀ with rax := a, rcx := c, rdx := d, rsi := s, r8 := r8, r9 := r9 }

/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (m : Nat) : Post :=
  fun j' g' _ V' => (∃ m' < m, Inv g₀ V₀ j' m' g' V') ∨ Fin g₀ V₀ j' g' V'

variable {g₀ : Gprs} {V₀ : Addr → Byte}

theorem x32 {m n : Nat} (h1 : 1 ≤ n) (hn : n ≤ (len V₀ g₀.rdi).toNat) (ht : Tail V₀ g₀.rdi n) (hm : 2 * n < m)
    {a c d s : BitVec 64} (ha : a = BitVec.ofNat 64 (4 * n)) (hd : BitVec.setWidth 32 d = BitVec.ofNat 32 n)
    {g : Gprs} {fl : Rflags} (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rsi := s, r8 := chs V₀ g₀.rdi,
                                                 r9 := BitVec.setWidth 64 (len V₀ g₀.rdi) }) : Nx g₀ V₀ m 32 g fl V₀ :=
  Or.inl ⟨2 * n, hm, rfl, Or.inr (Or.inl ⟨rfl, n, rfl, h1, hn, ht, a, c, d, s, hg, ha, hd⟩)⟩

theorem x50 {m n : Nat} (h1 : 1 ≤ n) (hn : n ≤ (len V₀ g₀.rdi).toNat) (ht : Tail V₀ g₀.rdi (n - 1))
    (hm : 2 * n - 1 < m) {a c d s : BitVec 64} (ha : a = BitVec.ofNat 64 (4 * n))
    (hd : BitVec.setWidth 32 d = BitVec.ofNat 32 n) {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rsi := s, r8 := chs V₀ g₀.rdi,
                        r9 := BitVec.setWidth 64 (len V₀ g₀.rdi) }) : Nx g₀ V₀ m 50 g fl V₀ :=
  Or.inl ⟨2 * n - 1, hm, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, n, rfl, h1, hn, ht, a, c, d, s, hg, ha, hd⟩))⟩

theorem x59 {m k : Nat} (hm : 0 < m) (hk : k < (len V₀ g₀.rdi).toNat) (ht : Tail V₀ g₀.rdi k)
    (hb : k = 0 ∨ ¬ Ws (ch V₀ g₀.rdi (k - 1))) {a c d s r : BitVec 64} (hr : r = Addr.add (chs V₀ g₀.rdi) (4 * k))
    (hd : BitVec.setWidth 32 d = BitVec.ofNat 32 k) {g : Gprs} {fl : Rflags}
    (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rsi := s, r8 := r,
                        r9 := BitVec.setWidth 64 (len V₀ g₀.rdi) }) : Nx g₀ V₀ m 59 g fl V₀ := by
  subst hr
  exact Or.inl ⟨0, hm, rfl, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, k, hk, ht, hb, a, c, d, s, hg, hd⟩))⟩

theorem xFin {m k : Nat} {V : Addr → Byte} (hk : k ≤ (len V₀ g₀.rdi).toNat) (ht : Tail V₀ g₀.rdi k)
    (hb : k = 0 ∨ ¬ Ws (ch V₀ g₀.rdi (k - 1))) (hV : Out g₀ V₀ k V) {a c d s r8 r9 : BitVec 64} {g : Gprs}
    {fl : Rflags} (hg : g = { g₀ with rax := a, rcx := c, rdx := d, rsi := s, r8 := r8, r9 := r9 }) :
    Nx g₀ V₀ m 69 g fl V :=
  Or.inr ⟨rfl, k, hk, ht, hb, hV, a, c, d, s, r8, r9, hg⟩

/-! ## The conditions -/

variable {F : Footprint} {Wl : List Rgn}

/-- `omega` past the projections of the registers. -/
local macro "om" : tactic => `(tactic| ((try dsimp only); omega))

/-- The entry: the `ret` for the length 0, else the loop's head with all characters left. -/
theorem vc_0 {f : Rflags} (hF : Fp F V₀ g₀.rdi) :
    W_0 F Wl (Nx g₀ V₀ (2 * (len V₀ g₀.rdi).toNat + 1)) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨f0, f8, -⟩ := hF
  dsimp only at f0 f8 ⊢
  wpx [W_0, W_16, o0, o1, Op.shl64, BitVec.and_self]
  refine ⟨f8, f0, fun _ => ⟨fun hb => ?_, fun hb _ => ?_⟩⟩
  · have hz : len V₀ rdi = 0 := beq_iff_eq.mp hb
    have hz' : (len V₀ rdi).toNat = 0 := by rw [hz]; rfl
    exact xFin (k := 0) (by exact Nat.zero_le _) (by exact fun j hj _ => absurd hj (by omega))
      (by exact Or.inl rfl) (by exact Or.inl ⟨hz'.symm, rfl⟩) rfl
  · have hz : len V₀ rdi ≠ 0 := beq_eq_false_iff_ne.mp hb
    have hz' : (len V₀ rdi).toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    exact x32 (n := (len V₀ rdi).toNat) (by om) (by exact Nat.le_refl _)
      (by exact fun j hj h => absurd hj (by omega)) (by om) (by exact shl4 _) (by exact swl _) rfl

/-- The loop's head, the character `m` blank: the step back. -/
theorem vc_32w {m : Nat} {g : Gprs} {f : Rflags} {cv : BitVec 32} (hF : Fp F V₀ g₀.rdi)
    (h : I32 g₀ V₀ (m + 1) g) (hc : ch V₀ g₀.rdi m = cv) (hw : Ws cv) :
    W_32 F Wl (Nx g₀ V₀ (2 * (m + 1))) g f V₀ := by
  obtain ⟨-, hn, ht, a, c, d, s, rfl, ha, hd⟩ := h
  have ht' : Tail V₀ g₀.rdi (m + 1 - 1) := fun j hj hk => by
    by_cases e : j = m
    · subst e
      rw [hc]
      exact hw
    · exact ht j hj (by omega)
  have hA := ldA (chs V₀ g₀.rdi) ha
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  have fm := fk m (by omega)
  dsimp only at hn ht' fm hc hA ⊢
  have hA' := hA
  dsimp only [chs] at hA'
  have hc1 : rdd(V₀, Addr.add (chs V₀ rdi) (4 * m)) = cv := hc
  have hc2 : rdd(V₀, Addr.add (rdq(V₀, rdi)) (4 * m)) = cv := hc
  rcases hw with rfl | rfl | rfl
  all_goals
    wpx [W_32, W_45, W_80, W_85, o2, o3, o6, o7, hA, hA', hc1, hc2, eq_self_iff_true, decide_true, decide_false,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, Bool.true_or, Bool.false_or,
      false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fm
      | apply And.intro
      | intro)
    all_goals exact x50 (n := m + 1) (by om) (by exact hn) (by exact ht') (by om) (by exact ha) (by exact hd) rfl

/-- The loop's head, the character `m` not blank: the `ret` if none was passed, else the stores. -/
theorem vc_32n {m : Nat} {g : Gprs} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (h : I32 g₀ V₀ (m + 1) g)
    (hc : ¬ Ws (ch V₀ g₀.rdi m)) :
    W_32 F Wl (Nx g₀ V₀ (2 * (m + 1))) g f V₀ := by
  obtain ⟨-, hn, ht, a, c, d, s, rfl, ha, hd⟩ := h
  have hl := (len V₀ g₀.rdi).isLt
  have hb : m + 1 = 0 ∨ ¬ Ws (ch V₀ g₀.rdi (m + 1 - 1)) := Or.inr (by rw [Nat.add_sub_cancel]; exact hc)
  have hA := ldA (chs V₀ g₀.rdi) ha
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  have fm := fk m (by omega)
  dsimp only at hn ht hl fm hc hb hA ⊢
  have hA' := hA
  dsimp only [chs] at hA'
  have h9 : rdd(V₀, Addr.add (chs V₀ rdi) (4 * m)) ≠ 9#32 := fun e => hc (Or.inl e)
  have h10 : rdd(V₀, Addr.add (chs V₀ rdi) (4 * m)) ≠ 10#32 := fun e => hc (Or.inr (Or.inl e))
  have h32 : decide (rdd(V₀, Addr.add (chs V₀ rdi) (4 * m)) = 32#32) = false :=
    decide_eq_false fun e => hc (Or.inr (Or.inr e))
  have hb1 := b1f h9 h10
  have h32' : decide (rdd(V₀, Addr.add (rdq(V₀, rdi)) (4 * m)) = 32#32) = false := h32
  have hb1' : (decide ((BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V₀, Addr.add (rdq(V₀, rdi)) (4 * m)) +
      18446744073709551607#64)).toNat < 1) || decide (BitVec.setWidth 32 (BitVec.setWidth 64
      rdd(V₀, Addr.add (rdq(V₀, rdi)) (4 * m)) + 18446744073709551607#64) = 1#32)) = false := hb1
  by_cases hL : (len V₀ rdi).toNat = m + 1
  · have e1 := eqL hL
    have e2 : decide (rdd(V₀, rdi + 8#64) = BitVec.ofNat 32 (m + 1)) = true := e1
    wpx [W_32, W_45, W_80, W_85, o2, o3, o6, o7, hA, hA', hb1, hb1', h32, h32', hd, e1, e2, eq_self_iff_true,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies,
      true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fm
      | apply And.intro
      | intro)
    all_goals exact xFin (k := m + 1) (by exact Nat.le_of_eq hL.symm) (by exact ht) (by exact hb)
      (by exact Or.inl ⟨hL.symm, rfl⟩) rfl
  · have e1 := neL hL (by omega)
    have e2 : decide (rdd(V₀, rdi + 8#64) = BitVec.ofNat 32 (m + 1)) = false := e1
    wpx [W_32, W_45, W_80, W_85, o2, o3, o6, o7, hA, hA', hb1, hb1', h32, h32', hd, e1, e2, eq_self_iff_true,
      Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies,
      true_and, and_true, implies_true]
    all_goals repeat' (first
      | with_reducible exact fm
      | apply And.intro
      | intro)
    all_goals exact x59 (k := m + 1) (by om) (by om) (by exact ht) (by exact hb) (by rw [ha]; rfl) (by exact hd)
      rfl

/-- The step back: the stores with the length 0 when no character is left, else the loop's head. -/
theorem vc_50 {m : Nat} {g : Gprs} {f : Rflags} (h : I50 g₀ V₀ (m + 1) g) :
    W_50 F Wl (Nx g₀ V₀ (2 * (m + 1) - 1)) g f V₀ := by
  obtain ⟨-, hn, ht, a, c, d, s, rfl, ha, hd⟩ := h
  have hl := (len V₀ g₀.rdi).isLt
  have ht0 : Tail V₀ g₀.rdi m := by
    rw [Nat.add_sub_cancel] at ht
    exact ht
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hn ht0 hl ⊢
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · wpx [W_50, o4, hd, eq_self_iff_true, decide_true, Bool.not_true, Bool.true_eq_false, Bool.false_eq_true,
      false_implies, true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | apply And.intro
      | intro)
    all_goals exact x59 (k := 0) (by om) (by om) (by exact ht0) (by exact Or.inl rfl)
      (by exact (addr_add_zero _).symm) (by decide) rfl
  · wpx [W_50, o4, hd, ne1 hm (by omega), Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies,
      true_implies, true_and, and_true, implies_true]
    all_goals repeat' (first
      | apply And.intro
      | intro)
    all_goals exact x32 (n := m) (by om) (by om) (by exact ht0) (by om) (by rw [ha]; exact sub4 m)
      (by exact dec32 (by omega)) rfl

/-- The stores: the 0 at the index `k`, the length `k`; the `ret`. -/
theorem vc_59 {g : Gprs} {f : Rflags} (h : I59 g₀ V₀ g)
    (hw1 : ∀ k < (len V₀ g₀.rdi).toNat, ∀ i < 4, Foot Wl (Addr.add (Addr.add (chs V₀ g₀.rdi) (4 * k)) i))
    (hw2 : ∀ i < 4, Foot Wl (Addr.add (g₀.rdi + 8#64) i)) :
    W_59 F Wl (Nx g₀ V₀ 0) g f V₀ := by
  obtain ⟨k, hk, ht, hb, a, c, d, s, rfl, hd⟩ := h
  have w1 := hw1 k hk
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hk ht hb w1 hw2 ⊢
  wpx [W_59, o5, hd]
  exact ⟨w1, hw2, xFin (k := k) (by exact Nat.le_of_lt hk) (by exact ht) (by exact hb) (by exact Or.inr ⟨hk, rfl⟩)
    rfl⟩

theorem vc_32 {m : Nat} {g : Gprs} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (h : I32 g₀ V₀ (m + 1) g) :
    W_32 F Wl (Nx g₀ V₀ (2 * (m + 1))) g f V₀ := by
  by_cases hw : Ws (ch V₀ g₀.rdi m)
  · exact vc_32w hF h rfl hw
  · exact vc_32n hF h hw

theorem vcAll (hF : Fp F V₀ g₀.rdi)
    (hw1 : ∀ k < (len V₀ g₀.rdi).toNat, ∀ i < 4, Foot Wl (Addr.add (Addr.add (chs V₀ g₀.rdi) (4 * k)) i))
    (hw2 : ∀ i < 4, Foot Wl (Addr.add (g₀.rdi + 8#64) i)) (ℓ m : Nat) (g : Gprs) (f : Rflags)
    (V : Addr → Byte) (h : Inv g₀ V₀ ℓ m g V) : Wt ℓ F Wl (Nx g₀ V₀ m) g f V := by
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, n, rfl, h⟩ | ⟨rfl, n, rfl, h⟩ | ⟨rfl, rfl, h⟩⟩ := h
  · exact vc_0 hF
  · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := h.1; omega⟩
    exact vc_32 hF h
  · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := h.1; omega⟩
    exact vc_50 h
  · exact vc_59 h hw1 hw2

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::TrimRight ()` from its entry to the return address: the new length `n` (the characters from `n` on
blank, the one before not), the bytes `Out`, `rax`, `rcx`, `rdx`, `rsi`, `r8`, `r9` changed. The stores (the 0 at
the index `n` and the length) apart from the return address. -/
theorem utr_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L utr_at utr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = utr_at) (hF : Fp F V X.cpu.gpr.rdi)
    (hw1 : ∀ k < (len V X.cpu.gpr.rdi).toNat, ∀ i < 4,
      Foot Wl (Addr.add (Addr.add (chs V X.cpu.gpr.rdi) (4 * k)) i))
    (hw2 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hs : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (h8 : (X.cpu.gpr.rdi + 8#64).toNat + 4 ≤ 2 ^ 64 ∧ (X.cpu.gpr.rsp.toNat + 8 ≤ (X.cpu.gpr.rdi + 8#64).toNat ∨
      (X.cpu.gpr.rdi + 8#64).toNat + 4 ≤ X.cpu.gpr.rsp.toNat))
    (hcs : ∀ k < (len V X.cpu.gpr.rdi).toNat, (Addr.add (chs V X.cpu.gpr.rdi) (4 * k)).toNat + 4 ≤ 2 ^ 64 ∧
      (X.cpu.gpr.rsp.toNat + 8 ≤ (Addr.add (chs V X.cpu.gpr.rdi) (4 * k)).toNat ∨
        (Addr.add (chs V X.cpu.gpr.rdi) (4 * k)).toNat + 4 ≤ X.cpu.gpr.rsp.toNat))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte) (n : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Z.cpu.rip = e₂.add j₂ → n ≤ (len V X.cpu.gpr.rdi).toNat → Tail V X.cpu.gpr.rdi n →
      (n = 0 ∨ ¬ Ws (ch V X.cpu.gpr.rdi (n - 1))) → Out X.cpu.gpr V n V' →
      (∃ a c d s r8 r9, Z.cpu.gpr = { X.cpu.gpr with rax := a, rcx := c, rdx := d, rsi := s, r8 := r8,
                                                     r9 := r9 }.set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv X.cpu.gpr V ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ m g f V' h => vcAll hF hw1 hw2 ℓ m g f V' h) ?_
    (2 * (len V X.cpu.gpr.rdi).toNat + 1) 0 hK hA (by rw [addr_add_zero]; exact hrip)
    ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rintro j g fl V' ⟨rfl, n, hn, ht, hb, hO, a, c', d, s, r8, r9, rfl⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hra' : rdq(V', Y.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [hsY]
    rcases hO with ⟨-, rfl⟩ | ⟨hk, rfl⟩
    · exact hra
    · obtain ⟨hc1, hc2⟩ := hcs n hk
      obtain ⟨h81, h82⟩ := h8
      show ofBytesLE 64 (List.map _ (byteAddrs X.cpu.gpr.rsp 8)) = _
      rw [Tun.rd_Vst _ (X.cpu.gpr.rdi + 8#64) (toBytesLE (BitVec.ofNat 32 n) 4) X.cpu.gpr.rsp 8
          (by rw [toBytesLE_length]; exact h81) hs (by rw [toBytesLE_length]; omega),
        Tun.rd_Vst V (Addr.add (chs V X.cpu.gpr.rdi) (4 * n)) (toBytesLE (0#32) 4) X.cpu.gpr.rsp 8
          (by rw [toBytesLE_length]; exact hc1) hs (by rw [toBytesLE_length]; omega)]
      exact hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_69 _) (by rw [hsY]; exact hl) hin₂ h₂ hra' ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' n hKZ hAZ hrZ hn ht hb hO ⟨a, c', d, s, r8, r9, by rw [hgZ, hsY, hgY]⟩

end FV7z.Utr
