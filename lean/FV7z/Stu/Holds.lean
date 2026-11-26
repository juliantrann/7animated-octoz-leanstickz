import FV7z.Stu.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `ConvertStringToUInt64` (PLAN.md §M, M1)

7-Zip 26.06's `ConvertStringToUInt64 (const wchar_t *s, const wchar_t **end)` at `0x451330` in `7zzs`
(`CPP/Common/StringToInt.cpp`; `objdump -d`): the digits of `s` = `p` (`rdi`, 4-byte characters) from the first on,
the value in `rax` (0 on an overflow); with `end` = `s` (`rsi`) not null, `*end` = `p` at the entry and, after the
last digit without an overflow, `*end` = the first character that is not a digit. Cut points: the entry, 22 (the
first digit), the loop's head 40 (`rdi` at the digit just read), 83 (`xor eax, eax`, an overflow or no digit) and 101
(`*end` stored); the `ret`s at 85, 104, 119.

- `isD`: a digit, as `sub/lea -48; cmp 9; jbe/ja` has it; `ch V p k`: the `k`-th character.
- `M1`: the memory after the entry (`*end` = `p` when `end` is not null); `Mem`: at the `ret`s, that or with
  `*end` = `p + 4n` after the `n` digits.
- `Inv`, `Fin`, `Nx`: the invariant at the cut points, the end, and the post of `Seg.cfg`.
- `stu_ok`: from the entry to the return address with `Mem` of the memory and `rax`, `rcx`, `rdx`, `rdi`, `r8` some
  values. The value is not followed: the spec is the control flow and the stores.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Stu

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_85 : pret <+: stu.drop 85 := by decide +kernel
theorem ret_85 (feat : Features) : Dec feat stu 85 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 85) (k := 0) (pret_0 feat) w_85 (Nat.zero_le _)
theorem w_104 : pret <+: stu.drop 104 := by decide +kernel
theorem ret_104 (feat : Features) : Dec feat stu 104 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 104) (k := 0) (pret_0 feat) w_104 (Nat.zero_le _)
theorem w_119 : pret <+: stu.drop 119 := by decide +kernel
theorem ret_119 (feat : Features) : Dec feat stu 119 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 119) (k := 0) (pret_0 feat) w_119 (Nat.zero_le _)

/-- A digit: `c - 48 ≤ 9` unsigned at 32 bits, as `cmp 9; jbe` has it. -/
def isD (w : BitVec 32) : Bool := decide ((w - 48#32).toNat < 9) || decide (w - 48#32 = 9#32)
/-- The `k`-th character. -/
abbrev ch (V : Addr → Byte) (p : Addr) (k : Nat) : BitVec 32 := rdd(V, p + BitVec.ofNat 64 (4 * k))
/-- A pointer's bytes. -/
abbrev bp (a : Addr) : List Byte := toBytesLE a 8

/-- `lea edx, [rcx - 48]` with `rcx` a zero-extended character. -/
theorem lea48 (w : BitVec 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 w + 18446744073709551568#64) = w - 48#32 := by
  have h : BitVec.setWidth 32 (18446744073709551568#64) = -48#32 := by decide
  rw [BitVec.setWidth_add _ _ (by decide), sw_64_32, h, BitVec.sub_eq_add_neg]
/-- One character on: `add rdi, 4`. -/
theorem adv4 (p : Addr) (k : Nat) : p + BitVec.ofNat 64 (4 * k) + 4#64 = p + BitVec.ofNat 64 (4 * (k + 1)) := by
  have e : 4 * (k + 1) = 4 * k + 4 := by omega
  rw [e, BitVec.ofNat_add, BitVec.add_assoc]
theorem z0 (p : Addr) : p + BitVec.ofNat 64 (4 * 0) = p := BitVec.add_zero p

/-- The registers the function changes. -/
abbrev G5 (g₀ : Gprs) (a c d di x : BitVec 64) : Gprs := { g₀ with rax := a, rcx := c, rdx := d, rdi := di, r8 := x }

/-- The memory after the entry: `*end` = `p` when `end` is not null. -/
def M1 (g₀ : Gprs) (V₀ V : Addr → Byte) : Prop :=
  (g₀.rsi = 0 ∧ V = V₀) ∨ (g₀.rsi ≠ 0 ∧ V = Vst V₀ g₀.rsi (bp g₀.rdi))
/-- The memory at the `ret`s: as after the entry, or `*end` = `p + 4n` after the `n` digits. -/
def Mem (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) (V : Addr → Byte) : Prop :=
  M1 g₀ V₀ V ∨
    (g₀.rsi ≠ 0 ∧ V = Vst (Vst V₀ g₀.rsi (bp g₀.rdi)) g₀.rsi (bp (g₀.rdi + BitVec.ofNat 64 (4 * n))))

/-- The invariant at the cut points: the entry; 22, a digit first; 40, the digit `kk` just read; 83; 101 with `rdi`
at the character after the digits. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (n ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = n + 2 ∧ g = g₀ ∧ V = V₀) ∨
  (M1 g₀ V₀ V ∧ ((ℓ = 22 ∧ m = n + 1 ∧ 0 < n ∧ ∃ a, g = G5 g₀ a g₀.rcx g₀.rdx g₀.rdi g₀.r8) ∨
    (ℓ = 40 ∧ ∃ kk < n, m = n - kk ∧ ∃ a c d x, g = G5 g₀ a c d (g₀.rdi + BitVec.ofNat 64 (4 * kk)) x) ∨
    (ℓ = 83 ∧ m = 0 ∧ ∃ a c d di x, g = G5 g₀ a c d di x) ∨
    (ℓ = 101 ∧ m = 0 ∧ g₀.rsi ≠ 0 ∧ ∃ a c d x, g = G5 g₀ a c d (g₀.rdi + BitVec.ofNat 64 (4 * n)) x)))
/-- At a `ret`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (n j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (j = 85 ∨ j = 104 ∨ j = 119) ∧ Mem g₀ V₀ n V ∧ ∃ a c d di x, g = G5 g₀ a c d di x
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv g₀ V₀ n j m' g V) ∨ Fin g₀ V₀ n j g V

/-! ## The exits -/

variable {g₀ : Gprs} {V₀ : Addr → Byte} {n m : Nat} {g : Gprs} {f : Rflags} {V : Addr → Byte}
  {a c d di x : BitVec 64}

theorem e22 (hpos : 0 < n) (hM : M1 g₀ V₀ V) (hg : g = G5 g₀ a g₀.rcx g₀.rdx g₀.rdi g₀.r8) :
    Nx g₀ V₀ n (n + 2) 22 g f V :=
  Or.inl ⟨n + 1, by omega, Or.inr ⟨hM, Or.inl ⟨rfl, rfl, hpos, a, hg⟩⟩⟩

theorem e83 (hM : M1 g₀ V₀ V) (hm : 0 < m) (hg : g = G5 g₀ a c d di x) : Nx g₀ V₀ n m 83 g f V :=
  Or.inl ⟨0, hm, Or.inr ⟨hM, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, a, c, d, di, x, hg⟩))⟩⟩

theorem e101z (hn0 : n = 0) (hs : g₀.rsi ≠ 0) (hM : M1 g₀ V₀ V) (hm : 0 < m) (hg : g = G5 g₀ a c d g₀.rdi x) :
    Nx g₀ V₀ n m 101 g f V :=
  Or.inl ⟨0, hm, Or.inr ⟨hM, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hs, a, c, d, x, by rw [hn0, z0]; exact hg⟩))⟩⟩

theorem e40z (hpos : 0 < n) (hM : M1 g₀ V₀ V) (hg : g = G5 g₀ a c d g₀.rdi x) : Nx g₀ V₀ n (n + 1) 40 g f V :=
  Or.inl ⟨n, by omega, Or.inr ⟨hM, Or.inr (Or.inl ⟨rfl, 0, hpos, by omega, a, c, d, x, by rw [z0]; exact hg⟩)⟩⟩

theorem e40s {kk : Nat} (hk : kk + 1 < n) (hM : M1 g₀ V₀ V)
    (hg : g = G5 g₀ a c d (g₀.rdi + BitVec.ofNat 64 (4 * kk) + 4#64) x) : Nx g₀ V₀ n (n - kk) 40 g f V :=
  Or.inl ⟨n - (kk + 1), by omega, Or.inr ⟨hM, Or.inr (Or.inl ⟨rfl, kk + 1, hk, rfl, a, c, d, x,
    by rw [← adv4]; exact hg⟩)⟩⟩

theorem e101 {kk : Nat} (hk : kk + 1 = n) (hs : g₀.rsi ≠ 0) (hM : M1 g₀ V₀ V) (hm : 0 < m)
    (hg : g = G5 g₀ a c d (g₀.rdi + BitVec.ofNat 64 (4 * kk) + 4#64) x) : Nx g₀ V₀ n m 101 g f V :=
  Or.inl ⟨0, hm, Or.inr ⟨hM, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hs, a, c, d, x,
    by rw [← hk, ← adv4]; exact hg⟩))⟩⟩

theorem e85 (hM : M1 g₀ V₀ V) (hg : g = G5 g₀ a c d di x) : Nx g₀ V₀ n m 85 g f V :=
  Or.inr ⟨Or.inl rfl, Or.inl hM, a, c, d, di, x, hg⟩

theorem e119 (hM : M1 g₀ V₀ V) (hg : g = G5 g₀ a c d di x) : Nx g₀ V₀ n m 119 g f V :=
  Or.inr ⟨Or.inr (Or.inr rfl), Or.inl hM, a, c, d, di, x, hg⟩

theorem e104 (hM : M1 g₀ V₀ V) (hs : g₀.rsi ≠ 0) (hg : g = G5 g₀ a c d di x) :
    Nx g₀ V₀ n m 104 g f (Vst V g₀.rsi (bp (g₀.rdi + BitVec.ofNat 64 (4 * n)))) := by
  rcases hM with ⟨h, -⟩ | ⟨-, rfl⟩
  · exact absurd h hs
  · exact Or.inr ⟨Or.inr (Or.inl rfl), Or.inr ⟨hs, rfl⟩, a, c, d, di, x, hg⟩

/-! ## The cut points -/

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- The entry: no digit, to 83 (`end` null) or 101; a digit, to 22. -/
theorem vc_0 (hd : ∀ k < n, isD (ch V₀ g₀.rdi k) = true) (hn : isD (ch V₀ g₀.rdi n) = false)
    (f0 : ∀ i < 4, Foot F.data (Addr.add g₀.rdi i)) (fs : g₀.rsi ≠ 0 → ∀ i < 8, Foot Wl (Addr.add g₀.rsi i)) :
    W_0 F Wl (Nx g₀ V₀ n (n + 2)) g₀ f V₀ := by
  have e0 : ch V₀ g₀.rdi 0 = rdd(V₀, g₀.rdi) := by unfold ch; rw [z0]
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hd hn f0 fs e0 ⊢
  by_cases hs : rsi = 0
  · have hz : (rsi == 0) = true := beq_iff_eq.2 hs
    cases hD : isD (rdd(V₀, rdi))
    · have hD' := hD
      unfold isD at hD'
      wpx [W_0, W_112, W_117, W_14, W_120, o0, o9, o1, o6, BitVec.and_self, hz, hD', Bool.not_true,
        Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
      all_goals repeat' (first | exact f0 | apply And.intro | intro _)
      all_goals first
        | exact e83 (Or.inl ⟨hs, rfl⟩) (by omega) rfl
        | (exfalso; simp_all)
    · have hpos : 0 < n := Nat.pos_of_ne_zero fun h => by
        subst h
        rw [e0, hD] at hn
        exact absurd hn (by decide)
      have hD' := hD
      unfold isD at hD'
      wpx [W_0, W_112, W_117, W_14, W_120, o0, o9, o1, o6, BitVec.and_self, hz, hD', Bool.not_true,
        Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
      all_goals repeat' (first | exact f0 | apply And.intro | intro _)
      all_goals first
        | exact e22 hpos (Or.inl ⟨hs, rfl⟩) rfl
        | (exfalso; simp_all)
  · have hz : (rsi == 0) = false := beq_eq_false_iff_ne.2 hs
    have fs' := fs hs
    cases hD : isD (rdd(V₀, rdi))
    · have hn0 : n = 0 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · exact h
        · have h1 := hd 0 h
          rw [e0, hD] at h1
          exact absurd h1 (by decide)
      have hD' := hD
      unfold isD at hD'
      wpx [W_0, W_112, W_117, W_14, W_120, o0, o9, o1, o6, BitVec.and_self, hz, hD', Bool.not_true,
        Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
      all_goals repeat' (first | exact f0 | exact fs' | apply And.intro | intro _)
      all_goals first
        | exact e101z hn0 hs (Or.inr ⟨hs, rfl⟩) (by omega) rfl
        | (exfalso; simp_all)
    · have hpos : 0 < n := Nat.pos_of_ne_zero fun h => by
        subst h
        rw [e0, hD] at hn
        exact absurd hn (by decide)
      have hD' := hD
      unfold isD at hD'
      wpx [W_0, W_112, W_117, W_14, W_120, o0, o9, o1, o6, BitVec.and_self, hz, hD', Bool.not_true,
        Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
      all_goals repeat' (first | exact f0 | exact fs' | apply And.intro | intro _)
      all_goals first
        | exact e22 hpos (Or.inr ⟨hs, rfl⟩) rfl
        | (exfalso; simp_all)

/-- 22: `r8` the bound, `ecx` 0, to the loop's head with digit 0 read. -/
theorem vc_22 (hpos : 0 < n) (hM : M1 g₀ V₀ V) :
    W_22 F Wl (Nx g₀ V₀ n (n + 1)) (G5 g₀ a g₀.rcx g₀.rdx g₀.rdi g₀.r8) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G5] at hM ⊢
  wpx [W_22, o2]
  all_goals repeat' (first | apply And.intro | intro _)
  exact e40z hpos hM rfl

set_option maxHeartbeats 1000000 in
/-- The loop's head, digit `kk` read: the next character a digit, back to 40 (or 83 on an overflow); not, to 119
(`end` null) or 101. -/
theorem vc_40 {kk : Nat} (hk : kk < n) (hM : M1 g₀ V₀ V)
    (hdV : ∀ k < n, isD (ch V g₀.rdi k) = true) (hnV : isD (ch V g₀.rdi n) = false)
    (fa : ∀ k ≤ n, ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + BitVec.ofNat 64 (4 * k)) i)) :
    W_40 F Wl (Nx g₀ V₀ n (n - kk)) (G5 g₀ a c d (g₀.rdi + BitVec.ofNat 64 (4 * kk)) x) f V := by
  have fk : ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + BitVec.ofNat 64 (4 * kk) + 4#64) i) := by
    rw [adv4]
    exact fa (kk + 1) hk
  have hm : 0 < n - kk := by omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G5] at hM hdV hnV fk ⊢
  cases hD : isD (rdd(V, rdi + BitVec.ofNat 64 (4 * kk) + 4#64))
  · have he : kk + 1 = n := by
      rcases Nat.lt_or_ge (kk + 1) n with h | h
      · have h1 := hdV (kk + 1) h
        unfold ch at h1
        rw [← adv4, hD] at h1
        exact absurd h1 (by decide)
      · omega
    have hD' := hD
    unfold isD at hD'
    by_cases hs : rsi = 0
    · have hz : (rsi == 0) = true := beq_iff_eq.2 hs
      wpx [W_40, W_96, W_57, W_62, o3, o7, o4, o5, Op.not64, lea48, BitVec.and_self, hz, hD', Bool.not_true,
        Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
      all_goals repeat' (first | exact fk | apply And.intro | intro _)
      all_goals first
        | exact e119 hM rfl
        | (exfalso; simp_all)
    · have hz : (rsi == 0) = false := beq_eq_false_iff_ne.2 hs
      wpx [W_40, W_96, W_57, W_62, o3, o7, o4, o5, Op.not64, lea48, BitVec.and_self, hz, hD', Bool.not_true,
        Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
      all_goals repeat' (first | exact fk | apply And.intro | intro _)
      all_goals first
        | exact e101 he hs hM hm rfl
        | (exfalso; simp_all)
  · have hlt : kk + 1 < n := by
      rcases Nat.lt_or_ge (kk + 1) n with h | h
      · exact h
      · have e : kk + 1 = n := by omega
        rw [← e] at hnV
        unfold ch at hnV
        rw [← adv4, hD] at hnV
        exact absurd hnV (by decide)
    have hD' := hD
    unfold isD at hD'
    wpx [W_40, W_96, W_57, W_62, o3, o7, o4, o5, Op.not64, lea48, BitVec.and_self, hD', Bool.not_true,
      Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact fk | apply And.intro | intro _)
    all_goals first
      | exact e40s hlt hM rfl
      | exact e83 hM hm rfl
      | (exfalso; simp_all)

/-- 83: `xor eax, eax`, to the `ret` at 85. -/
theorem vc_83 (hM : M1 g₀ V₀ V) : W_83 F Wl (Nx g₀ V₀ n 0) (G5 g₀ a c d di x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G5] at hM ⊢
  wpx [W_83, o6]
  all_goals repeat' (first | apply And.intro | intro _)
  exact e85 hM rfl

/-- 101: `*end` = `p + 4n`, to the `ret` at 104. -/
theorem vc_101 (hs : g₀.rsi ≠ 0) (hM : M1 g₀ V₀ V) (fs : ∀ i < 8, Foot Wl (Addr.add g₀.rsi i)) :
    W_101 F Wl (Nx g₀ V₀ n 0) (G5 g₀ a c d (g₀.rdi + BitVec.ofNat 64 (4 * n)) x) f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G5] at hs hM fs ⊢
  wpx [W_101, o8]
  all_goals repeat' (first | exact fs | apply And.intro | intro _)
  exact e104 hM hs rfl

/-- The characters `k ≤ n` are disjoint from `*end` (when `end` is not null), and do not wrap. -/
def Sep (g₀ : Gprs) (n : Nat) : Prop :=
  g₀.rsi ≠ 0 → g₀.rsi.toNat + 8 ≤ 2 ^ 64 ∧ ∀ k ≤ n, (g₀.rdi + BitVec.ofNat 64 (4 * k)).toNat + 4 ≤ 2 ^ 64 ∧
    (g₀.rsi.toNat + 8 ≤ (g₀.rdi + BitVec.ofNat 64 (4 * k)).toNat ∨
      (g₀.rdi + BitVec.ofNat 64 (4 * k)).toNat + 4 ≤ g₀.rsi.toNat)

/-- The characters after the entry's store are those before it. -/
theorem chM (hsep : Sep g₀ n) (hM : M1 g₀ V₀ V) {k : Nat} (hk : k ≤ n) : ch V g₀.rdi k = ch V₀ g₀.rdi k := by
  rcases hM with ⟨-, rfl⟩ | ⟨hs, rfl⟩
  · rfl
  · obtain ⟨h1, h2⟩ := hsep hs
    obtain ⟨h3, h4⟩ := h2 k hk
    have hb : (bp g₀.rdi).length = 8 := toBytesLE_length _ _
    unfold ch
    rw [Tun.rd_Vst V₀ g₀.rsi (bp g₀.rdi) (g₀.rdi + BitVec.ofNat 64 (4 * k)) 4 (by rw [hb]; exact h1) h3
      (by rw [hb]; exact h4)]

theorem vcAll (hsep : Sep g₀ n) (hd : ∀ k < n, isD (ch V₀ g₀.rdi k) = true) (hn : isD (ch V₀ g₀.rdi n) = false)
    (fa : ∀ k ≤ n, ∀ i < 4, Foot F.data (Addr.add (g₀.rdi + BitVec.ofNat 64 (4 * k)) i))
    (fs : g₀.rsi ≠ 0 → ∀ i < 8, Foot Wl (Addr.add g₀.rsi i)) (ℓ m : Nat) (g : Gprs) (f : Rflags)
    (V : Addr → Byte) (h : Inv g₀ V₀ n ℓ m g V) : Wt ℓ F Wl (Nx g₀ V₀ n m) g f V := by
  have f0 : ∀ i < 4, Foot F.data (Addr.add g₀.rdi i) := by
    have h0 := fa 0 (Nat.zero_le _)
    rw [z0] at h0
    exact h0
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨hM, ⟨rfl, rfl, hpos, a, rfl⟩ | ⟨rfl, kk, hk, rfl, a, c, d, x, rfl⟩ |
    ⟨rfl, rfl, a, c, d, di, x, rfl⟩ | ⟨rfl, rfl, hs, a, c, d, x, rfl⟩⟩
  · exact vc_0 hd hn f0 fs
  · exact vc_22 hpos hM
  · exact vc_40 hk hM (fun k hk' => by rw [chM hsep hM (Nat.le_of_lt hk')]; exact hd k hk')
      (by rw [chM hsep hM (Nat.le_refl n)]; exact hn) fa
  · exact vc_83 hM
  · exact vc_101 hs hM (fs hs)

/-- The return address is not under `*end`. -/
theorem rdM {r : Addr} (hr : r.toNat + 8 ≤ 2 ^ 64)
    (hs8 : g₀.rsi ≠ 0 → g₀.rsi.toNat + 8 ≤ 2 ^ 64 ∧ (g₀.rsi.toNat + 8 ≤ r.toNat ∨ r.toNat + 8 ≤ g₀.rsi.toNat))
    (hV : Mem g₀ V₀ n V) : rdq(V, r) = rdq(V₀, r) := by
  have hb : ∀ a : Addr, (bp a).length = 8 := fun a => toBytesLE_length _ _
  rcases hV with (⟨-, rfl⟩ | ⟨hs, rfl⟩) | ⟨hs, rfl⟩
  · rfl
  · obtain ⟨h1, h2⟩ := hs8 hs
    rw [Tun.rd_Vst V₀ g₀.rsi (bp g₀.rdi) r 8 (by rw [hb]; exact h1) hr (by rw [hb]; exact h2)]
  · obtain ⟨h1, h2⟩ := hs8 hs
    rw [Tun.rd_Vst (Vst V₀ g₀.rsi (bp g₀.rdi)) g₀.rsi (bp (g₀.rdi + BitVec.ofNat 64 (4 * n))) r 8
        (by rw [hb]; exact h1) hr (by rw [hb]; exact h2),
      Tun.rd_Vst V₀ g₀.rsi (bp g₀.rdi) r 8 (by rw [hb]; exact h1) hr (by rw [hb]; exact h2)]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat}

/-- `ConvertStringToUInt64 (s, end)` from its entry, with `n` digits at `s` and a character that is not one after
them: at the return address, the return address popped, the memory `Mem` (`*end` = `s`, or `s + 4n` after the digits
when the value did not overflow; nothing when `end` is null), `rax`, `rcx`, `rdx`, `rdi`, `r8` some values. -/
theorem stu_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L stu_at stu) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = stu_at)
    (hd : ∀ k < n, isD (ch V X.cpu.gpr.rdi k) = true) (hn : isD (ch V X.cpu.gpr.rdi n) = false)
    (fa : ∀ k ≤ n, ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + BitVec.ofNat 64 (4 * k)) i))
    (fs : X.cpu.gpr.rsi ≠ 0 → ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rsi i)) (hsep : Sep X.cpu.gpr n)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) (hsp : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hss : X.cpu.gpr.rsi ≠ 0 →
      X.cpu.gpr.rsi.toNat + 8 ≤ X.cpu.gpr.rsp.toNat ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rsi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ V' : Addr → Byte, Mem X.cpu.gpr V n V' → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      (∃ a c d di x, Z.cpu.gpr = (G5 X.cpu.gpr a c d di x).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv X.cpu.gpr V n ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr V n j g V') (fun ℓ m g f V' h => vcAll hsep hd hn fa fs ℓ m g f V' h) ?_
    (n + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨hj, hV, a, c', d, di, x, rfl⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hraV : rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [rdM hsp (fun hs => ⟨(hsep hs).1, hss hs⟩) hV]
    exact hra
  have hdec : Dec prof.feat stu j (FV7z.mk .ret 64 [] 1) := by
    rcases hj with rfl | rfl | rfl
    · exact ret_85 _
    · exact ret_104 _
    · exact ret_119 _
  have hj' : j < 124 := by omega
  refine c.s_ret hKY hAY hin (lt_len hj') hrY hdec (by rw [hsY]; exact hl) hin₂ h₂ (by rw [hsY]; exact hraV) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k V' hV Z t₂ hKZ hAZ hrZ ⟨a, c', d, di, x, by rw [hgZ, hsY, hgY]⟩

end FV7z.Stu
