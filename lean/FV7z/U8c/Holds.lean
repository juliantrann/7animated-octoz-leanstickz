import FV7z.U8c.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `Utf16_To_Utf8_Calc` (PLAN.md §M, M1)

7-Zip 26.06's `Utf16_To_Utf8_Calc (const wchar_t *src, const wchar_t *srcLim, unsigned flags)` at `0x4518e0` in
`7zzs` (`CPP/Common/UTFConvert.cpp`; `objdump -d`; `wchar_t` is 4 bytes): the UTF-8 size of the characters in
`[src, srcLim)`. `rax` starts at the number of characters (`(srcLim - src) >> 2`, `sar`) and each character adds what
its UTF-8 form needs beyond one byte; a high surrogate followed by a low one is read as a pair (two characters, 2
more bytes). Nothing is written. Cut points: the entry, the loop's head 24 (`ecx` loaded), 67 (past the one-byte,
two-byte and `0xEF80` classes), 128/184/224 (0, 2 or 3 to add, `r8` at the next character), 131 (`rdi` = `r8`: back
to 24 or out); the `ret`s at 122 and 136.

- `le127` … `ns`: the code's comparisons as `Bool`s, in the form `simp` leaves them (`cmp; jbe` is `cf || zf`).
- `ex V p n e k`: what the characters from the `k`-th on add, as the code goes (`e` the masked `flags`).
- `T`: the result, `(srcLim - src) >> 2` plus `ex` from the first character.
- `vc_*`: the pieces from the cut points, each with its exits as hypotheses on `Q`, the branch conditions as
  premises (no `simp` meets a condition the proof has to match); `x*`: the exits as `Nx`; `vcAll`: `Seg.cfg`'s
  condition; `u8c_ok`: from the entry to the return address, `rax` = `T`, the memory as it was, reading only the
  `n` characters (the 4 bytes at `src + 4k`, `k < n`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.U8c

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_122 : pret <+: u8c.drop 122 := by decide +kernel
theorem ret_122 (feat : Features) : Dec feat u8c 122 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 122) (k := 0) (pret_0 feat) w_122 (Nat.zero_le _)
theorem w_136 : pret <+: u8c.drop 136 := by decide +kernel
theorem ret_136 (feat : Features) : Dec feat u8c 136 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 136) (k := 0) (pret_0 feat) w_136 (Nat.zero_le _)

/-! ## The classes, as the comparisons have them -/

/-- `cmp ecx, 0x7f; jbe`. -/
abbrev le127 (c : BitVec 32) : Bool := decide (c.toNat < 127) || decide (c = 127#32)
/-- `cmp ecx, 0x7ff; jbe`. -/
abbrev le2047 (c : BitVec 32) : Bool := decide (c.toNat < 2047) || decide (c = 2047#32)
/-- `and r9d, -0x80; cmp r9d, 0xef80; je`. -/
abbrev m51 (c : BitVec 32) : Bool := decide (c &&& 4294967168#32 = 61312#32)
/-- `and r9d, -0x800; cmp r9d, 0xd800; je`: a surrogate. -/
abbrev sur (c : BitVec 32) : Bool := decide (c &&& 4294965248#32 = 55296#32)
/-- `cmp ecx, 0xdbff; ja`: a low surrogate. -/
abbrev hi (c : BitVec 32) : Bool := !(decide (c.toNat < 56319) || decide (c = 56319#32))
/-- `sub ecx, 0xdc00; cmp ecx, 0x400; cmovb`: the next character a low surrogate. -/
abbrev lo2 (c : BitVec 32) : Bool := decide ((c - 56320#32).toNat < 1024)
/-- `cmp ecx, 0xffff; jbe`. -/
abbrev le65535 (c : BitVec 32) : Bool := decide (c.toNat < 65535) || decide (c = 65535#32)
/-- `cmp ecx, 0x1fffff; jbe`. -/
abbrev le2097151 (c : BitVec 32) : Bool := decide (c.toNat < 2097151) || decide (c = 2097151#32)
/-- `cmp ecx, 0x3ffffff; ja`. -/
abbrev gt26 (c : BitVec 32) : Bool := !(decide (c.toNat < 67108863) || decide (c = 67108863#32))
/-- `test ecx, ecx; jns`. -/
abbrev ns (c : BitVec 32) : Bool := !(c &&& c).msb
/-- `test edx, edx; je` not taken. -/
abbrev nz (e : BitVec 32) : Bool := !(e &&& e == 0)

/-- The `k`-th character. -/
abbrev ch (V : Addr → Byte) (p : Addr) (k : Nat) : BitVec 32 := rdd(V, p + BitVec.ofNat 64 (4 * k))

set_option linter.unusedVariables false in
/-- What the characters from the `k`-th on add to the count, as the code goes. -/
def ex (V : Addr → Byte) (p : Addr) (n : Nat) (e : BitVec 32) (k : Nat) : Nat :=
  if hk : k < n then
    bif le127 (ch V p k) then ex V p n e (k + 1)
    else bif le2047 (ch V p k) then 1 + ex V p n e (k + 1)
    else bif nz e && m51 (ch V p k) then ex V p n e (k + 1)
    else bif sur (ch V p k) then
      (bif hi (ch V p k) then 2 + ex V p n e (k + 1)
      else if h2 : k + 1 < n then
        (bif lo2 (ch V p (k + 1)) then 2 + ex V p n e (k + 2) else 2 + ex V p n e (k + 1))
      else 2 + ex V p n e (k + 1))
    else bif le65535 (ch V p k) then 2 + ex V p n e (k + 1)
    else bif le2097151 (ch V p k) then 3 + ex V p n e (k + 1)
    else bif gt26 (ch V p k) then
      (bif ns (ch V p k) then 5 + ex V p n e (k + 1) else 3 + ex V p n e (k + 1))
    else 4 + ex V p n e (k + 1)
  else 0
termination_by n - k

section ex
variable {V : Addr → Byte} {p : Addr} {n : Nat} {e : BitVec 32} {k : Nat}

theorem ex_n : ex V p n e n = 0 := by
  rw [ex.eq_1 V p n e n, dif_neg (Nat.lt_irrefl n)]

theorem ex_a (hk : k < n) (h1 : le127 (ch V p k) = true) : ex V p n e k = ex V p n e (k + 1) := by
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, cond_true]

theorem ex_b (hk : k < n) (h1 : le127 (ch V p k) = false) (h2 : le2047 (ch V p k) = true) :
    ex V p n e k = 1 + ex V p n e (k + 1) := by
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, cond_true, cond_false]

theorem ex_c (hk : k < n) (h1 : le127 (ch V p k) = false) (h2 : le2047 (ch V p k) = false)
    (h3 : (nz e && m51 (ch V p k)) = true) : ex V p n e k = ex V p n e (k + 1) := by
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, cond_true, cond_false]

/-- Past the first three classes. -/
abbrev Past (V : Addr → Byte) (p : Addr) (e : BitVec 32) (k : Nat) : Prop :=
  le127 (ch V p k) = false ∧ le2047 (ch V p k) = false ∧ (nz e && m51 (ch V p k)) = false

theorem ex_d (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = true) :
    ex V p n e k = 2 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, cond_true, cond_false]

theorem ex_e (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = false)
    (h6 : k + 1 = n) : ex V p n e k = 2 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, cond_true, cond_false,
    dif_neg (show ¬k + 1 < n by omega)]

theorem ex_f (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = false)
    (h6 : k + 1 < n) (h7 : lo2 (ch V p (k + 1)) = true) : ex V p n e k = 2 + ex V p n e (k + 2) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, cond_true, cond_false, dif_pos h6, h7]

theorem ex_g (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = false)
    (h6 : k + 1 < n) (h7 : lo2 (ch V p (k + 1)) = false) : ex V p n e k = 2 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, cond_true, cond_false, dif_pos h6, h7]

theorem ex_h (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = true) :
    ex V p n e k = 2 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, cond_true, cond_false]

theorem ex_i (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = true) : ex V p n e k = 3 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, cond_true, cond_false]

theorem ex_j (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = false) (h7 : gt26 (ch V p k) = true) (h8 : ns (ch V p k) = true) :
    ex V p n e k = 5 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, h7, h8, cond_true, cond_false]

theorem ex_k (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = false) (h7 : gt26 (ch V p k) = true) (h8 : ns (ch V p k) = false) :
    ex V p n e k = 3 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, h7, h8, cond_true, cond_false]

theorem ex_l (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = false) (h7 : gt26 (ch V p k) = false) :
    ex V p n e k = 4 + ex V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [ex.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, h7, cond_true, cond_false]

end ex

theorem nz_t {e c : BitVec 32} (h : (e &&& e == 0) = true) : (nz e && m51 c) = false := by
  simp only [nz, h, Bool.not_true, Bool.false_and]
theorem nz_f {e c : BitVec 32} (h : (e &&& e == 0) = false) (hm : m51 c = false) : (nz e && m51 c) = false := by
  simp only [nz, h, hm, Bool.not_false, Bool.and_false]
theorem nz_ft {e c : BitVec 32} (h : (e &&& e == 0) = false) (hm : m51 c = true) : (nz e && m51 c) = true := by
  simp only [nz, h, hm, Bool.not_false, Bool.and_self]

/-! ## Addresses -/

theorem adv4 (p : Addr) (k : Nat) : p + BitVec.ofNat 64 (4 * k) + 4#64 = p + BitVec.ofNat 64 (4 * (k + 1)) := by
  have e : 4 * (k + 1) = 4 * k + 4 := by omega
  rw [e, BitVec.ofNat_add, BitVec.add_assoc]
theorem adv8 (p : Addr) (k : Nat) : p + BitVec.ofNat 64 (4 * k) + 8#64 = p + BitVec.ofNat 64 (4 * (k + 2)) := by
  have e : 4 * (k + 2) = 4 * k + 8 := by omega
  rw [e, BitVec.ofNat_add, BitVec.add_assoc]
theorem z0 (p : Addr) : p + BitVec.ofNat 64 (4 * 0) = p := BitVec.add_zero p

theorem tnk {p : Addr} {n k : Nat} (hp : p.toNat + 4 * n < 2 ^ 64) (hk : k ≤ n) :
    (p + BitVec.ofNat 64 (4 * k)).toNat = p.toNat + 4 * k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 4 * k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show p.toNat + 4 * k < 2 ^ 64 by omega)]

theorem pinj {p : Addr} {n k j : Nat} (hp : p.toNat + 4 * n < 2 ^ 64) (hk : k ≤ n) (hj : j ≤ n)
    (h : p + BitVec.ofNat 64 (4 * k) = p + BitVec.ofNat 64 (4 * j)) : k = j := by
  have := congrArg BitVec.toNat h
  rw [tnk hp hk, tnk hp hj] at this
  omega

theorem addK (a : BitVec 64) (d x : Nat) : a + BitVec.ofNat 64 (d + x) = a + BitVec.ofNat 64 d + BitVec.ofNat 64 x := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-! ## The invariant -/

/-- The masked `flags`. -/
abbrev E (g₀ : Gprs) : BitVec 32 := BitVec.setWidth 32 g₀.rdx &&& 512#32
/-- The result. -/
def T (g₀ : Gprs) (V : Addr → Byte) (n : Nat) : BitVec 64 :=
  (g₀.rsi - g₀.rdi).sshiftRight 2 + BitVec.ofNat 64 (ex V g₀.rdi n (E g₀) 0)
/-- The registers in the loop. -/
abbrev Gs (g₀ : Gprs) (a c i x y : BitVec 64) : Gprs :=
  { g₀ with rax := a, rcx := c, rdx := BitVec.setWidth 64 (E g₀), rdi := i, r8 := x, r9 := y }

/-- The invariant at the cut points: the entry; 24 at the `k`-th character; 67 with it past the first three classes;
128, 184, 224 with `d` = 0, 2, 3 to add and `r8` at the `k`-th; 131 with `rdi` = `r8` at the `k`-th. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (n ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ (
  (ℓ = 0 ∧ m = 5 * n + 10 ∧ g = g₀) ∨
  (ℓ = 24 ∧ ∃ k < n, m = 5 * (n - k) + 4 ∧ ∃ a c x y,
    g = Gs g₀ a c (g₀.rdi + BitVec.ofNat 64 (4 * k)) x y ∧
    a + BitVec.ofNat 64 (ex V₀ g₀.rdi n (E g₀) k) = T g₀ V₀ n) ∨
  (ℓ = 67 ∧ ∃ k < n, m = 5 * (n - k) + 3 ∧ ∃ a y,
    g = Gs g₀ a (BitVec.setWidth 64 (ch V₀ g₀.rdi k)) (g₀.rdi + BitVec.ofNat 64 (4 * k))
      (g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64) y ∧
    a + BitVec.ofNat 64 (ex V₀ g₀.rdi n (E g₀) k) = T g₀ V₀ n ∧ Past V₀ g₀.rdi (E g₀) k) ∨
  (∃ d, ((ℓ = 128 ∧ d = 0) ∨ (ℓ = 184 ∧ d = 2) ∨ (ℓ = 224 ∧ d = 3)) ∧ ∃ k ≤ n, m = 5 * (n - k) + 6 ∧ ∃ a c i y,
    g = Gs g₀ a c i (g₀.rdi + BitVec.ofNat 64 (4 * k)) y ∧
    a + BitVec.ofNat 64 (d + ex V₀ g₀.rdi n (E g₀) k) = T g₀ V₀ n) ∨
  (ℓ = 131 ∧ ∃ k ≤ n, m = 5 * (n - k) + 5 ∧ ∃ a c y,
    g = Gs g₀ a c (g₀.rdi + BitVec.ofNat 64 (4 * k)) (g₀.rdi + BitVec.ofNat 64 (4 * k)) y ∧
    a + BitVec.ofNat 64 (ex V₀ g₀.rdi n (E g₀) k) = T g₀ V₀ n))
/-- At a `ret`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (n j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (j = 122 ∨ j = 136) ∧ V = V₀ ∧
    ∃ c d i x y, g = { g₀ with rax := T g₀ V₀ n, rcx := c, rdx := d, rdi := i, r8 := x, r9 := y }
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv g₀ V₀ n j m' g V) ∨ Fin g₀ V₀ n j g V

/-! ## The pieces (`Q` generic) -/

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: no character, to 122; else `edx` masked, to 24. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h122 : decide (g.rsi = g.rdi) = true → ∀ fl, Q 122 { g with rax := (g.rsi - g.rdi).sshiftRight 2 } fl V)
    (h24 : decide (g.rsi = g.rdi) = false → ∀ fl,
      Q 24 { g with rax := (g.rsi - g.rdi).sshiftRight 2,
        rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx &&& 512#32) } fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h122 h24 ⊢
  wpx [W_0, W_15, o0, o1, Op.sar64]
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | (apply h122 <;> assumption)
    | (apply h24 <;> assumption)

/-- The loop's head: `ecx` the character; to 128 (one byte, or `0xEF80` with the flag), 131 (two bytes), 67. -/
theorem vc_24 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {e : BitVec 32}
    (he : g.rdx = BitVec.setWidth 64 e) (fq : ∀ i < 4, Foot F.data (Addr.add g.rdi i))
    (h128 : le127 (rdd(V, g.rdi)) = true → ∀ fl,
      Q 128 { g with rcx := BitVec.setWidth 64 (rdd(V, g.rdi)), r8 := g.rdi + 4#64 } fl V)
    (h131 : le127 (rdd(V, g.rdi)) = false → le2047 (rdd(V, g.rdi)) = true → ∀ fl,
      Q 131 { g with rax := g.rax + 1#64, rcx := BitVec.setWidth 64 (rdd(V, g.rdi)), rdi := g.rdi + 4#64,
        r8 := g.rdi + 4#64 } fl V)
    (h128b : le127 (rdd(V, g.rdi)) = false → le2047 (rdd(V, g.rdi)) = false → (e &&& e == 0) = false →
      m51 (rdd(V, g.rdi)) = true → ∀ fl,
      Q 128 { g with rcx := BitVec.setWidth 64 (rdd(V, g.rdi)), r8 := g.rdi + 4#64,
        r9 := BitVec.setWidth 64 (rdd(V, g.rdi) &&& 4294967168#32) } fl V)
    (h67a : le127 (rdd(V, g.rdi)) = false → le2047 (rdd(V, g.rdi)) = false → (e &&& e == 0) = true → ∀ fl,
      Q 67 { g with rcx := BitVec.setWidth 64 (rdd(V, g.rdi)), r8 := g.rdi + 4#64 } fl V)
    (h67b : le127 (rdd(V, g.rdi)) = false → le2047 (rdd(V, g.rdi)) = false → (e &&& e == 0) = false →
      m51 (rdd(V, g.rdi)) = false → ∀ fl,
      Q 67 { g with rcx := BitVec.setWidth 64 (rdd(V, g.rdi)), r8 := g.rdi + 4#64,
        r9 := BitVec.setWidth 64 (rdd(V, g.rdi) &&& 4294967168#32) } fl V) :
    W_24 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he fq h128 h131 h128b h67a h67b ⊢
  subst he
  wpx [W_24, W_35, W_200, W_47, W_51, o2, o3, o16, o4, o5]
  repeat' (first | exact fq | apply And.intro | intro _)
  all_goals first
    | (apply h128 <;> assumption)
    | (apply h131 <;> assumption)
    | (apply h128b <;> assumption)
    | (apply h67a <;> assumption)
    | (apply h67b <;> assumption)

/-- 67: a surrogate (to 184, the pair read when there is a next character), or by its size to 184, 224, 131 (5
bytes), 24 or 122 (4 bytes, `rdi` on). -/
theorem vc_67 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {c : BitVec 32}
    (hc : g.rcx = BitVec.setWidth 64 c)
    (fq2 : decide (g.rsi = g.r8) = false → ∀ i < 4, Foot F.data (Addr.add (g.rdi + 4#64) i))
    (h184a : sur c = true → hi c = true → ∀ fl,
      Q 184 { g with rcx := BitVec.setWidth 64 c, r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V)
    (h184b : sur c = true → hi c = false → decide (g.rsi = g.r8) = true → ∀ fl,
      Q 184 { g with rcx := BitVec.setWidth 64 c, r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V)
    (h184c : sur c = true → hi c = false → decide (g.rsi = g.r8) = false → ∀ fl,
      Q 184 (if lo2 (rdd(V, g.rdi + 4#64)) = true then
          { g with rcx := BitVec.setWidth 64 (rdd(V, g.rdi + 4#64) - 56320#32), rdi := g.rdi + 8#64,
            r8 := g.rdi + 8#64, r9 := BitVec.setWidth 64 (c &&& 4294965248#32) }
        else
          { g with rcx := BitVec.setWidth 64 (rdd(V, g.rdi + 4#64) - 56320#32), rdi := g.rdi + 8#64,
            r9 := BitVec.setWidth 64 (c &&& 4294965248#32) }) fl V)
    (h184d : sur c = false → le65535 c = true → ∀ fl,
      Q 184 { g with rcx := BitVec.setWidth 64 c, r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V)
    (h224a : sur c = false → le65535 c = false → le2097151 c = true → ∀ fl,
      Q 224 { g with rcx := BitVec.setWidth 64 c, r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V)
    (h131 : sur c = false → le65535 c = false → le2097151 c = false → gt26 c = true → ns c = true → ∀ fl,
      Q 131 { g with rax := g.rax + 5#64, rcx := BitVec.setWidth 64 c, rdi := g.r8,
        r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V)
    (h224b : sur c = false → le65535 c = false → le2097151 c = false → gt26 c = true → ns c = false → ∀ fl,
      Q 224 { g with rcx := BitVec.setWidth 64 c, r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V)
    (h24 : sur c = false → le65535 c = false → le2097151 c = false → gt26 c = false →
      (!decide (g.rsi = g.r8)) = true → ∀ fl,
      Q 24 { g with rax := g.rax + 4#64, rcx := BitVec.setWidth 64 c, rdi := g.r8,
        r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V)
    (h122 : sur c = false → le65535 c = false → le2097151 c = false → gt26 c = false →
      (!decide (g.rsi = g.r8)) = false → ∀ fl,
      Q 122 { g with rax := g.rax + 4#64, rcx := BitVec.setWidth 64 c, rdi := g.r8,
        r9 := BitVec.setWidth 64 (c &&& 4294965248#32) } fl V) :
    W_67 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc fq2 h184a h184b h184c h184d h224a h131 h224b h24 h122 ⊢
  subst hc
  wpx [W_67, W_144, W_152, W_157, W_86, W_94, W_102, W_216, W_240, W_220, W_110, o6, o13, o12, o14, o7, o8,
    o9, o17, o20, o18, o10]
  repeat' (first | (apply fq2 <;> assumption) | apply And.intro | intro _)
  all_goals first
    | (apply h184a <;> assumption)
    | (apply h184b <;> assumption)
    | (apply h184c <;> assumption)
    | (apply h184d <;> assumption)
    | (apply h224a <;> assumption)
    | (apply h131 <;> assumption)
    | (apply h224b <;> assumption)
    | (apply h24 <;> assumption)
    | (apply h122 <;> assumption)

/-- 128: `rdi` = `r8`. -/
theorem vc_128 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 131 { g with rdi := g.r8 } fl V) : W_128 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_128, o11]
  exact h _

/-- 184: 2 more, `rdi` = `r8`. -/
theorem vc_184 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 131 { g with rax := g.rax + 2#64, rdi := g.r8 } fl V) : W_184 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_184, o15]
  exact h _

/-- 224: 3 more, `rdi` = `r8`. -/
theorem vc_224 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 131 { g with rax := g.rax + 3#64, rdi := g.r8 } fl V) : W_224 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_224, o19]
  exact h _

/-- 131: `r8` at `srcLim` or not. -/
theorem vc_131 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h24 : (!decide (g.rsi = g.r8)) = true → ∀ fl, Q 24 g fl V)
    (h136 : (!decide (g.rsi = g.r8)) = false → ∀ fl, Q 136 g fl V) : W_131 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h24 h136 ⊢
  wpx [W_131, o12]
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | (apply h24 <;> assumption)
    | (apply h136 <;> assumption)

attribute [local irreducible] W_0 W_24 W_67 W_128 W_131 W_184 W_224

/-! ## The exits -/

section exits
variable {g₀ : Gprs} {V : Addr → Byte} {n : Nat}

/-- `srcLim` = `src + 4n`, with no wrap. -/
abbrev Lim (g₀ : Gprs) (n : Nat) : Prop :=
  g₀.rsi = g₀.rdi + BitVec.ofNat 64 (4 * n) ∧ g₀.rdi.toNat + 4 * n < 2 ^ 64

theorem x0_122 (hl : Lim g₀ n) : decide (g₀.rsi = g₀.rdi) = true → ∀ fl,
    Nx g₀ V n (5 * n + 10) 122 { g₀ with rax := (g₀.rsi - g₀.rdi).sshiftRight 2 } fl V := by
  intro h fl
  have h' : g₀.rsi = g₀.rdi := of_decide_eq_true h
  have hn : n = 0 := pinj hl.2 (Nat.le_refl n) (Nat.zero_le n) (by rw [← hl.1, z0]; exact h')
  subst hn
  refine Or.inr ⟨Or.inl rfl, rfl, g₀.rcx, g₀.rdx, g₀.rdi, g₀.r8, g₀.r9, ?_⟩
  rw [T, ex_n, BitVec.add_zero]

theorem x0_24 (hl : Lim g₀ n) : decide (g₀.rsi = g₀.rdi) = false → ∀ fl,
    Nx g₀ V n (5 * n + 10) 24 { g₀ with rax := (g₀.rsi - g₀.rdi).sshiftRight 2,
      rdx := BitVec.setWidth 64 (BitVec.setWidth 32 g₀.rdx &&& 512#32) } fl V := by
  intro h fl
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact absurd (decide_eq_true (by rw [hl.1, z0])) (by rw [h]; decide)
    · exact hn
  refine Or.inl ⟨5 * (n - 0) + 4, by omega, rfl, Or.inr (Or.inl ⟨rfl, 0, hn, rfl,
    (g₀.rsi - g₀.rdi).sshiftRight 2, g₀.rcx, g₀.r8, g₀.r9, by rw [z0], rfl⟩)⟩

variable {k : Nat} {a c x y : BitVec 64}

/-- The registers at 24. -/
abbrev G24 (g₀ : Gprs) (k : Nat) (a c x y : BitVec 64) : Gprs := Gs g₀ a c (g₀.rdi + BitVec.ofNat 64 (4 * k)) x y

theorem x24_128 (hk : k < n) (hX : a + BitVec.ofNat 64 (ex V g₀.rdi n (E g₀) k) = T g₀ V n) :
    le127 (ch V g₀.rdi k) = true → ∀ fl, Nx g₀ V n (5 * (n - k) + 4) 128
      { G24 g₀ k a c x y with rcx := BitVec.setWidth 64 (ch V g₀.rdi k),
        r8 := g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64 } fl V := by
  intro h1 fl
  refine Or.inl ⟨5 * (n - (k + 1)) + 6, by omega, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨0, Or.inl ⟨rfl, rfl⟩,
    k + 1, by omega, rfl, a, BitVec.setWidth 64 (ch V g₀.rdi k), g₀.rdi + BitVec.ofNat 64 (4 * k), y,
    by rw [← adv4], by rw [Nat.zero_add, ← ex_a hk h1]; exact hX⟩)))⟩

theorem x24_131 (hk : k < n) (hX : a + BitVec.ofNat 64 (ex V g₀.rdi n (E g₀) k) = T g₀ V n) :
    le127 (ch V g₀.rdi k) = false → le2047 (ch V g₀.rdi k) = true → ∀ fl, Nx g₀ V n (5 * (n - k) + 4) 131
      { G24 g₀ k a c x y with rax := a + 1#64, rcx := BitVec.setWidth 64 (ch V g₀.rdi k),
        rdi := g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64, r8 := g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64 } fl V := by
  intro h1 h2 fl
  refine Or.inl ⟨5 * (n - (k + 1)) + 5, by omega, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,
    k + 1, by omega, rfl, a + 1#64, BitVec.setWidth 64 (ch V g₀.rdi k), y, by rw [← adv4], ?_⟩)))⟩
  rw [← hX, ex_b hk h1 h2, addK]
  rfl

theorem x24_128b (hk : k < n) (hX : a + BitVec.ofNat 64 (ex V g₀.rdi n (E g₀) k) = T g₀ V n) :
    le127 (ch V g₀.rdi k) = false → le2047 (ch V g₀.rdi k) = false → (E g₀ &&& E g₀ == 0) = false →
      m51 (ch V g₀.rdi k) = true → ∀ fl, Nx g₀ V n (5 * (n - k) + 4) 128
      { G24 g₀ k a c x y with rcx := BitVec.setWidth 64 (ch V g₀.rdi k),
        r8 := g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64,
        r9 := BitVec.setWidth 64 (ch V g₀.rdi k &&& 4294967168#32) } fl V := by
  intro h1 h2 h3 h4 fl
  refine Or.inl ⟨5 * (n - (k + 1)) + 6, by omega, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨0, Or.inl ⟨rfl, rfl⟩,
    k + 1, by omega, rfl, a, BitVec.setWidth 64 (ch V g₀.rdi k), g₀.rdi + BitVec.ofNat 64 (4 * k),
    BitVec.setWidth 64 (ch V g₀.rdi k &&& 4294967168#32),
    by rw [← adv4], by rw [Nat.zero_add, ← ex_c hk h1 h2 (nz_ft h3 h4)]; exact hX⟩)))⟩

theorem x24_67a (hk : k < n) (hX : a + BitVec.ofNat 64 (ex V g₀.rdi n (E g₀) k) = T g₀ V n) :
    le127 (ch V g₀.rdi k) = false → le2047 (ch V g₀.rdi k) = false → (E g₀ &&& E g₀ == 0) = true →
      ∀ fl, Nx g₀ V n (5 * (n - k) + 4) 67
      { G24 g₀ k a c x y with rcx := BitVec.setWidth 64 (ch V g₀.rdi k),
        r8 := g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64 } fl V := by
  intro h1 h2 h3 fl
  exact Or.inl ⟨5 * (n - k) + 3, by omega, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, k, hk, rfl, a, y, rfl, hX,
    h1, h2, nz_t h3⟩))⟩

theorem x24_67b (hk : k < n) (hX : a + BitVec.ofNat 64 (ex V g₀.rdi n (E g₀) k) = T g₀ V n) :
    le127 (ch V g₀.rdi k) = false → le2047 (ch V g₀.rdi k) = false → (E g₀ &&& E g₀ == 0) = false →
      m51 (ch V g₀.rdi k) = false → ∀ fl, Nx g₀ V n (5 * (n - k) + 4) 67
      { G24 g₀ k a c x y with rcx := BitVec.setWidth 64 (ch V g₀.rdi k),
        r8 := g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64,
        r9 := BitVec.setWidth 64 (ch V g₀.rdi k &&& 4294967168#32) } fl V := by
  intro h1 h2 h3 h4 fl
  exact Or.inl ⟨5 * (n - k) + 3, by omega, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, k, hk, rfl, a,
    BitVec.setWidth 64 (ch V g₀.rdi k &&& 4294967168#32), rfl, hX, h1, h2, nz_f h3 h4⟩))⟩

/-- The registers at 67. -/
abbrev G67 (g₀ : Gprs) (V : Addr → Byte) (k : Nat) (a y : BitVec 64) : Gprs :=
  Gs g₀ a (BitVec.setWidth 64 (ch V g₀.rdi k)) (g₀.rdi + BitVec.ofNat 64 (4 * k))
    (g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64) y

/-- 67 to 184, 224 with `r8` at the next character. -/
theorem x67_d (hk : k < n) {d : Nat} (hd : (d = 2) ∨ (d = 3)) {j : Nat} (hj : (j = 184 ∧ d = 2) ∨ (j = 224 ∧ d = 3))
    (hX : a + BitVec.ofNat 64 (d + ex V g₀.rdi n (E g₀) (k + 1)) = T g₀ V n) {fl : Rflags} :
    Nx g₀ V n (5 * (n - k) + 3) j
      { G67 g₀ V k a y with rcx := BitVec.setWidth 64 (ch V g₀.rdi k),
        r9 := BitVec.setWidth 64 (ch V g₀.rdi k &&& 4294965248#32) } fl V := by
  refine Or.inl ⟨5 * (n - (k + 1)) + 6, by omega, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨d, Or.inr hj,
    k + 1, by omega, rfl, a, BitVec.setWidth 64 (ch V g₀.rdi k), g₀.rdi + BitVec.ofNat 64 (4 * k),
    BitVec.setWidth 64 (ch V g₀.rdi k &&& 4294965248#32), by rw [← adv4], hX⟩)))⟩

/-- The next character's address is not `srcLim`: it is in the string. -/
theorem nxt (hl : Lim g₀ n) (hk : k < n)
    (h : decide (g₀.rsi = g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64) = false) : k + 1 < n := by
  rcases Nat.lt_or_ge (k + 1) n with h' | h'
  · exact h'
  · have e : k + 1 = n := by omega
    rw [hl.1, adv4, e] at h
    exact absurd h (by simp)

theorem lst (hl : Lim g₀ n) (hk : k < n)
    (h : decide (g₀.rsi = g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64) = true) : k + 1 = n := by
  have h' : g₀.rsi = g₀.rdi + BitVec.ofNat 64 (4 * k) + 4#64 := of_decide_eq_true h
  rw [hl.1, adv4] at h'
  exact (pinj hl.2 (Nat.le_refl n) (by omega) h').symm

end exits

end FV7z.U8c
