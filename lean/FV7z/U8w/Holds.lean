import FV7z.U8w.Cuts
import FV7z.U8c.Holds
/-!
# `Utf16_To_Utf8` (PLAN.md §M, M1)

7-Zip 26.06's `Utf16_To_Utf8 (char *dest, const wchar_t *src, const wchar_t *srcLim, unsigned flags)` at
`0x4519e0` in `7zzs` (`CPP/Common/UTFConvert.cpp`; `objdump -d`; `wchar_t` is 4 bytes): the UTF-8 form of the
characters in `[src, srcLim)` stored from `dest`, `rax` the end. Each character takes 1 to 6 bytes by its class
(a high surrogate with a low one after it: the pair, 4 bytes); with bit 9 of `flags` the `0xEF80` class takes one
byte; bit 8 picks what an unpaired surrogate's 3 bytes are. Cut points: the entry; 32, the loop's head (`ecx`
loaded); 83, past the one-byte, two-byte and `0xEF80` classes; 141, 152, the first byte and the next ones of a 4 to
6 byte form (`ecx` 6 times the bytes left); 184, `rsi` at the next character; 200 one byte; 296, 328, three bytes;
the `ret` at 193.

The contract is the one M1 needs: every byte stored is one of the `W` bytes from `dest` the caller gives (`fw`,
with `wb`, the bytes the characters take, at most `W`), the source and the return address apart from them, and the
function returns. The bytes' values are not tracked.

- `wb V p n e k`: the bytes the characters from the `k`-th on take, as the code goes (`e` the flag bit 9).
- `Fr V₀ d c V`: `V` is `V₀` but at the `c` bytes from `d`.
- `vc_*`: the pieces from the cut points, `Q` generic, the exits as hypotheses, the values the proof does not
  follow (stored bytes, scratch registers) bound by `∀`; `x*`: the exits as `Nx`; `vcAll`: `Seg.cfg`'s condition;
  `u8w_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.U8c (le127 le2047 m51 sur hi le65535 le2097151 gt26 ns nz ch Past nz_t nz_f nz_ft adv4 adv8 z0 pinj
  addK pret pret_0)
namespace FV7z.U8w

/-- The `ret`. -/
theorem w_193 : pret <+: u8w.drop 193 := by decide +kernel
theorem ret_193 (feat : Features) : Dec feat u8w 193 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 193) (k := 0) (pret_0 feat) w_193 (Nat.zero_le _)

/-! ## The bytes the characters take -/

/-- `and r11d, -0x400; cmp r11d, 0xdc00; je`: the next character a low surrogate. -/
abbrev lo4 (c : BitVec 32) : Bool := decide (c &&& 4294966272#32 = 56320#32)

set_option linter.unusedVariables false in
/-- The bytes the characters from the `k`-th on take, as the code goes. -/
def wb (V : Addr → Byte) (p : Addr) (n : Nat) (e : BitVec 32) (k : Nat) : Nat :=
  if hk : k < n then
    bif le127 (ch V p k) then 1 + wb V p n e (k + 1)
    else bif le2047 (ch V p k) then 2 + wb V p n e (k + 1)
    else bif nz e && m51 (ch V p k) then 1 + wb V p n e (k + 1)
    else bif sur (ch V p k) then
      (bif hi (ch V p k) then 3 + wb V p n e (k + 1)
      else if h2 : k + 1 < n then
        (bif lo4 (ch V p (k + 1)) then 4 + wb V p n e (k + 2) else 3 + wb V p n e (k + 1))
      else 3 + wb V p n e (k + 1))
    else bif le65535 (ch V p k) then 3 + wb V p n e (k + 1)
    else bif le2097151 (ch V p k) then 4 + wb V p n e (k + 1)
    else bif gt26 (ch V p k) then
      (bif ns (ch V p k) then 6 + wb V p n e (k + 1) else 4 + wb V p n e (k + 1))
    else 5 + wb V p n e (k + 1)
  else 0
termination_by n - k

section wb
variable {V : Addr → Byte} {p : Addr} {n : Nat} {e : BitVec 32} {k : Nat}

theorem wb_a (hk : k < n) (h1 : le127 (ch V p k) = true) : wb V p n e k = 1 + wb V p n e (k + 1) := by
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, Bool.cond_true]

theorem wb_b (hk : k < n) (h1 : le127 (ch V p k) = false) (h2 : le2047 (ch V p k) = true) :
    wb V p n e k = 2 + wb V p n e (k + 1) := by
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, Bool.cond_true, Bool.cond_false]

theorem wb_c (hk : k < n) (h1 : le127 (ch V p k) = false) (h2 : le2047 (ch V p k) = false)
    (h3 : (nz e && m51 (ch V p k)) = true) : wb V p n e k = 1 + wb V p n e (k + 1) := by
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, Bool.cond_true, Bool.cond_false]

theorem wb_d (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = true) :
    wb V p n e k = 3 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, Bool.cond_true, Bool.cond_false]

theorem wb_e (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = false)
    (h6 : k + 1 = n) : wb V p n e k = 3 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, Bool.cond_true, Bool.cond_false,
    dif_neg (show ¬k + 1 < n by omega)]

theorem wb_f (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = false)
    (h6 : k + 1 < n) (h7 : lo4 (ch V p (k + 1)) = true) : wb V p n e k = 4 + wb V p n e (k + 2) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, Bool.cond_true, Bool.cond_false, dif_pos h6, h7]

theorem wb_g (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = true) (h5 : hi (ch V p k) = false)
    (h6 : k + 1 < n) (h7 : lo4 (ch V p (k + 1)) = false) : wb V p n e k = 3 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, Bool.cond_true, Bool.cond_false, dif_pos h6, h7]

theorem wb_h (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = true) :
    wb V p n e k = 3 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, Bool.cond_true, Bool.cond_false]

theorem wb_i (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = true) : wb V p n e k = 4 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, Bool.cond_true, Bool.cond_false]

theorem wb_j (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = false) (h7 : gt26 (ch V p k) = true) (h8 : ns (ch V p k) = true) :
    wb V p n e k = 6 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, h7, h8, Bool.cond_true, Bool.cond_false]

theorem wb_k (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = false) (h7 : gt26 (ch V p k) = true) (h8 : ns (ch V p k) = false) :
    wb V p n e k = 4 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, h7, h8, Bool.cond_true, Bool.cond_false]

theorem wb_l (hk : k < n) (h : Past V p e k) (h4 : sur (ch V p k) = false) (h5 : le65535 (ch V p k) = false)
    (h6 : le2097151 (ch V p k) = false) (h7 : gt26 (ch V p k) = false) :
    wb V p n e k = 5 + wb V p n e (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [wb.eq_1 V p n e k, dif_pos hk, h1, h2, h3, h4, h5, h6, h7, Bool.cond_false]

end wb

theorem nt {b : Bool} (h : (!b) = true) : b = false := by revert h; cases b <;> decide
theorem nn {b : Bool} (h : (!b) = false) : b = true := by revert h; cases b <;> decide

/-! ## Addresses, stores and the frame -/

/-- `d + c + x + y` with `x + y = j`. -/
theorem ad (d : Addr) (c j : Nat) (x y : BitVec 64) (h : x + y = BitVec.ofNat 64 j) :
    d + BitVec.ofNat 64 c + x + y = d + BitVec.ofNat 64 (c + j) := by
  rw [BitVec.add_assoc (d + BitVec.ofNat 64 c) x y, h, addK]

theorem d0 (d : Addr) : d + BitVec.ofNat 64 0 = d := BitVec.add_zero d

/-- `V` is `V₀` but at the `c` bytes from `d`. -/
def Fr (V₀ : Addr → Byte) (d : Addr) (c : Nat) (V : Addr → Byte) : Prop :=
  ∀ x, (∀ j < c, x ≠ d + BitVec.ofNat 64 j) → V x = V₀ x

section fr
variable {V₀ V : Addr → Byte} {d : Addr}

theorem fr0 : Fr V₀ d 0 V₀ := fun _ _ => rfl

theorem frW {c W : Nat} (hF : Fr V₀ d c V) (h : c ≤ W) : Fr V₀ d W V :=
  fun x hx => hF x fun j hj => hx j (by omega)

/-- One byte stored at the `j`-th. -/
theorem fr1 {c c' j : Nat} (hF : Fr V₀ d c V) (hc : c ≤ c') (hj : j < c') (b : BitVec 8) :
    Fr V₀ d c' (Vst V (d + BitVec.ofNat 64 j) (toBytesLE b 1)) := by
  intro x hx
  rw [Vst_apart _ V _ x fun i hi => by
    have hi0 : i = 0 := by rw [toBytesLE_length] at hi; omega
    rw [hi0, addr_add_zero]
    exact hx j hj]
  exact hF x fun j' hj' => hx j' (by omega)

/-- A load apart from the stored bytes. -/
theorem rdN {c m : Nat} {a : Addr} (hF : Fr V₀ d c V) (h : ∀ i < m, ∀ j < c, Addr.add a i ≠ d + BitVec.ofNat 64 j) :
    List.map V (byteAddrs a m) = List.map V₀ (byteAddrs a m) := by
  apply List.map_congr_left
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_byteAddrs.1 hx
  exact hF _ (h i hi)

end fr

/-! ## The invariant -/

/-- Bit 8 of `flags`. -/
abbrev E8 (g₀ : Gprs) : BitVec 32 := BitVec.setWidth 32 g₀.rcx &&& 256#32
/-- Bit 9 of `flags`. -/
abbrev E9 (g₀ : Gprs) : BitVec 32 := BitVec.setWidth 32 g₀.rcx &&& 512#32
/-- The registers in the loop. -/
abbrev Gs (g₀ : Gprs) (a c s i x y : BitVec 64) : Gprs :=
  { g₀ with
    rax := a, rcx := c, rsi := s, rdi := i, r8 := BitVec.setWidth 64 (E8 g₀), r9 := BitVec.setWidth 64 (E9 g₀),
    r10 := x, r11 := y }

/-- `srcLim` = `src + 4n`, with no wrap. -/
abbrev Lim (g₀ : Gprs) (n : Nat) : Prop :=
  g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * n) ∧ g₀.rsi.toNat + 4 * n < 2 ^ 64

/-- The characters apart from the `W` bytes from `dest`. -/
abbrev Sep (g₀ : Gprs) (n W : Nat) : Prop :=
  ∀ k < n, ∀ i < 4, ∀ j < W, Addr.add (g₀.rsi + BitVec.ofNat 64 (4 * k)) i ≠ g₀.rdi + BitVec.ofNat 64 j

/-- The invariant at the cut points, `cc` the bytes stored: the entry; 32 and 184 at the `k`-th character; 83 with it
past the first three classes; 200, 296, 328 with 1, 3, 3 bytes to store for it, `rdi` at the next; 141 with `1 + j`,
152 with `j` (`ecx` = `6j`). -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (n W ℓ m : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ m = 10 * n + 20 ∧ g = g₀ ∧ V = V₀) ∨
  (ℓ = 32 ∧ ∃ k < n, m = 10 * (n - k) + 9 ∧ ∃ cc, cc + wb V₀ g₀.rsi n (E9 g₀) k ≤ W ∧ Fr V₀ g₀.rdi cc V ∧
    ∃ c i x y, g = Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) c (g₀.rsi + BitVec.ofNat 64 (4 * k)) i x y) ∨
  (ℓ = 83 ∧ ∃ k < n, m = 10 * (n - k) + 8 ∧ ∃ cc, cc + wb V₀ g₀.rsi n (E9 g₀) k ≤ W ∧ Fr V₀ g₀.rdi cc V ∧
    Past V₀ g₀.rsi (E9 g₀) k ∧ ∃ x y, g = Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) (BitVec.setWidth 64 (ch V₀ g₀.rsi k))
      (g₀.rsi + BitVec.ofNat 64 (4 * k)) (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) x y) ∨
  (∃ b o, ((ℓ = 200 ∧ b = 1 ∧ o = 7) ∨ (ℓ = 296 ∧ b = 3 ∧ o = 7) ∨ (ℓ = 328 ∧ b = 3 ∧ o = 6)) ∧
    ∃ k < n, m = 10 * (n - k) + o ∧ ∃ cc, cc + b + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W ∧ Fr V₀ g₀.rdi cc V ∧
    ∃ c s x y, g = Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) c s (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) x y) ∨
  (ℓ = 141 ∧ ∃ k < n, m = 10 * (n - k) + 6 ∧ ∃ j, (j = 3 ∨ j = 4 ∨ j = 5) ∧
    ∃ cc, cc + 1 + j + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W ∧ Fr V₀ g₀.rdi cc V ∧
    ∃ s x y, g = Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) (BitVec.setWidth 64 (BitVec.ofNat 32 (6 * j))) s
      (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) x y) ∨
  (ℓ = 152 ∧ ∃ k < n, ∃ j, 1 ≤ j ∧ j ≤ 5 ∧ m = 10 * (n - k) + j ∧
    ∃ cc, cc + j + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W ∧ Fr V₀ g₀.rdi cc V ∧
    ∃ s x y, g = Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) (BitVec.setWidth 64 (BitVec.ofNat 32 (6 * j))) s
      (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) x y) ∨
  (ℓ = 184 ∧ ∃ k ≤ n, m = 10 * (n - k) + 10 ∧ ∃ cc, cc + wb V₀ g₀.rsi n (E9 g₀) k ≤ W ∧ Fr V₀ g₀.rdi cc V ∧
    ∃ c i x y, g = Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) c (g₀.rsi + BitVec.ofNat 64 (4 * k)) i x y)
/-- At the `ret`: `rax` past the `cc` bytes stored. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (W j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  j = 193 ∧ ∃ cc ≤ W, Fr V₀ g₀.rdi cc V ∧ ∃ c s i u v x y,
    g = { g₀ with
      rax := g₀.rdi + BitVec.ofNat 64 cc, rcx := c, rsi := s, rdi := i, r8 := u, r9 := v, r10 := x, r11 := y }
/-- At an exit: a cut point's invariant with a smaller measure, or the `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n W m : Nat) : Post :=
  fun j g _ V => (∃ m' < m, Inv g₀ V₀ n W j m' g V) ∨ Fin g₀ V₀ W j g V

/-! ## The pieces (`Q` generic) -/

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: no character, to 193; else the flag bits, to 32. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h193 : decide (g.rsi = g.rdx) = true → ∀ fl,
      Q 193 { g with rax := g.rdi, r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx) } fl V)
    (h32 : decide (g.rsi = g.rdx) = false → ∀ fl,
      Q 32 { g with
          rax := g.rdi, r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx &&& 256#32),
          r9 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rcx &&& 512#32) } fl V) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h193 h32 ⊢
  wpx [W_0, W_15, o0, o1]
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | (apply h193 <;> assumption)
    | (apply h32 <;> assumption)

/-- The loop's head: `ecx` the character; to 200 (one byte, or `0xEF80` with the flag), two bytes stored and to
184, or 83. -/
theorem vc_32 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {e : BitVec 32}
    (he : g.r9 = BitVec.setWidth 64 e) (fq : ∀ i < 4, Foot F.data (Addr.add g.rsi i))
    (h200a : le127 (rdd(V, g.rsi)) = true → ∀ fl,
      Q 200 { g with
          rcx := BitVec.setWidth 64 (rdd(V, g.rsi)), rdi := g.rsi + 4#64,
          r10 := BitVec.setWidth 64 (rdd(V, g.rsi)) } fl V)
    (fw1 : le127 (rdd(V, g.rsi)) = false → le2047 (rdd(V, g.rsi)) = true →
      ∀ i < 1, Foot Wl (Addr.add (g.rax + 2#64 + 18446744073709551615#64) i))
    (fw0 : le127 (rdd(V, g.rsi)) = false → le2047 (rdd(V, g.rsi)) = true →
      ∀ i < 1, Foot Wl (Addr.add (g.rax + 2#64 + 18446744073709551614#64) i))
    (h184 : le127 (rdd(V, g.rsi)) = false → le2047 (rdd(V, g.rsi)) = true → ∀ fl c (b0 b1 : BitVec 8),
      Q 184 { g with
          rax := g.rax + 2#64, rcx := c, rsi := g.rsi + 4#64, rdi := g.rsi + 4#64,
          r10 := BitVec.setWidth 64 (rdd(V, g.rsi)) } fl
        (Vst (Vst V (g.rax + 2#64 + 18446744073709551615#64) (toBytesLE b0 1))
          (g.rax + 2#64 + 18446744073709551614#64) (toBytesLE b1 1)))
    (h83a : le127 (rdd(V, g.rsi)) = false → le2047 (rdd(V, g.rsi)) = false → (e &&& e == 0) = true → ∀ fl,
      Q 83 { g with
          rcx := BitVec.setWidth 64 (rdd(V, g.rsi)), rdi := g.rsi + 4#64,
          r10 := BitVec.setWidth 64 (rdd(V, g.rsi)) } fl V)
    (h200b : le127 (rdd(V, g.rsi)) = false → le2047 (rdd(V, g.rsi)) = false → (e &&& e == 0) = false →
      m51 (rdd(V, g.rsi)) = true → ∀ fl,
      Q 200 { g with
          rcx := BitVec.setWidth 64 (rdd(V, g.rsi)), rdi := g.rsi + 4#64,
          r10 := BitVec.setWidth 64 (rdd(V, g.rsi)),
          r11 := BitVec.setWidth 64 (rdd(V, g.rsi) &&& 4294967168#32) } fl V)
    (h83b : le127 (rdd(V, g.rsi)) = false → le2047 (rdd(V, g.rsi)) = false → (e &&& e == 0) = false →
      m51 (rdd(V, g.rsi)) = false → ∀ fl,
      Q 83 { g with
          rcx := BitVec.setWidth 64 (rdd(V, g.rsi)), rdi := g.rsi + 4#64,
          r10 := BitVec.setWidth 64 (rdd(V, g.rsi)),
          r11 := BitVec.setWidth 64 (rdd(V, g.rsi) &&& 4294967168#32) } fl V) :
    W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he fq h200a fw1 fw0 h184 h83a h200b h83b ⊢
  subst he
  wpx [W_32, W_50, W_216, W_62, W_67, o2, o3, o15, o4, o5]
  repeat' (first | with_reducible exact fq | with_reducible (apply fw1 <;> assumption) |
    with_reducible (apply fw0 <;> assumption) | apply And.intro | intro _)
  all_goals first
    | (apply h200a <;> assumption)
    | (apply h184 <;> assumption)
    | (apply h83a <;> assumption)
    | (apply h200b <;> assumption)
    | (apply h83b <;> assumption)

/-- 83: a surrogate (an unpaired one to 296, a pair stored and to 184), or by its size to 328 (3 bytes) or 141
(`ecx` 18, 24, 30: 4, 5, 6 bytes). -/
theorem vc_83 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {c : BitVec 32}
    (hc : g.rcx = BitVec.setWidth 64 c)
    (h296a : sur c = true → hi c = true → ∀ fl r y, Q 296 { g with r10 := r, r11 := y } fl V)
    (h296b : sur c = true → hi c = false → decide (g.rdx = g.rdi) = true → ∀ fl r y,
      Q 296 { g with r10 := r, r11 := y } fl V)
    (fq2 : sur c = true → hi c = false → decide (g.rdx = g.rdi) = false →
      ∀ i < 4, Foot F.data (Addr.add (g.rsi + 4#64) i))
    (fp0 : sur c = true → hi c = false → decide (g.rdx = g.rdi) = false → lo4 (rdd(V, g.rsi + 4#64)) = true →
      ∀ i < 1, Foot Wl (Addr.add (g.rax + 4#64 + 18446744073709551612#64) i))
    (fp1 : sur c = true → hi c = false → decide (g.rdx = g.rdi) = false → lo4 (rdd(V, g.rsi + 4#64)) = true →
      ∀ i < 1, Foot Wl (Addr.add (g.rax + 4#64 + 18446744073709551613#64) i))
    (fp2 : sur c = true → hi c = false → decide (g.rdx = g.rdi) = false → lo4 (rdd(V, g.rsi + 4#64)) = true →
      ∀ i < 1, Foot Wl (Addr.add (g.rax + 4#64 + 18446744073709551615#64) i))
    (fp3 : sur c = true → hi c = false → decide (g.rdx = g.rdi) = false → lo4 (rdd(V, g.rsi + 4#64)) = true →
      ∀ i < 1, Foot Wl (Addr.add (g.rax + 4#64 + 18446744073709551614#64) i))
    (h184 : sur c = true → hi c = false → decide (g.rdx = g.rdi) = false → lo4 (rdd(V, g.rsi + 4#64)) = true →
      ∀ fl c' i r y (b0 b1 b2 b3 : BitVec 8),
      Q 184 { g with rax := g.rax + 4#64, rcx := c', rsi := g.rsi + 8#64, rdi := i, r10 := r, r11 := y } fl
        (Vst (Vst (Vst (Vst V (g.rax + 4#64 + 18446744073709551612#64) (toBytesLE b0 1))
          (g.rax + 4#64 + 18446744073709551613#64) (toBytesLE b1 1))
          (g.rax + 4#64 + 18446744073709551615#64) (toBytesLE b2 1))
          (g.rax + 4#64 + 18446744073709551614#64) (toBytesLE b3 1)))
    (h296c : sur c = true → hi c = false → decide (g.rdx = g.rdi) = false → lo4 (rdd(V, g.rsi + 4#64)) = false →
      ∀ fl r y, Q 296 { g with r10 := r, r11 := y } fl V)
    (h328 : sur c = false → le65535 c = true → ∀ fl c' s r y,
      Q 328 { g with rcx := c', rsi := s, r10 := r, r11 := y } fl V)
    (h141a : sur c = false → le65535 c = false → (!le2097151 c) = false → ∀ fl s r y,
      Q 141 { g with rcx := BitVec.setWidth 64 18#32, rsi := s, r10 := r, r11 := y } fl V)
    (h141b : sur c = false → le65535 c = false → (!le2097151 c) = true → gt26 c = false → ∀ fl s r y,
      Q 141 { g with rcx := BitVec.setWidth 64 24#32, rsi := s, r10 := r, r11 := y } fl V)
    (h141c : sur c = false → le65535 c = false → (!le2097151 c) = true → gt26 c = true → (c &&& c).msb = false →
      ∀ fl s r y, Q 141 { g with rcx := BitVec.setWidth 64 30#32, rsi := s, r10 := r, r11 := y } fl V)
    (h141d : sur c = false → le65535 c = false → (!le2097151 c) = true → gt26 c = true → (c &&& c).msb = true →
      ∀ fl s r y, Q 141 { g with rcx := BitVec.setWidth 64 18#32, rsi := s, r10 := r, r11 := y } fl V) :
    W_83 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc h296a h296b fq2 fp0 fp1 fp2 fp3 h184 h296c h328 h141a h141b h141c h141d ⊢
  subst hc
  wpx [W_83, W_256, W_264, W_269, W_488, W_106, W_352, W_118, W_384, W_416, W_464, W_420, W_392, W_130, o6, o16,
      o17, o18, o29, o7, o22, o8, o23, o25, o28, o26, o24, o9]
  repeat' (first | with_reducible (apply fq2 <;> assumption) | with_reducible (apply fp0 <;> assumption) |
    with_reducible (apply fp1 <;> assumption) | with_reducible (apply fp2 <;> assumption) |
    with_reducible (apply fp3 <;> assumption) | apply And.intro | intro _)
  all_goals first
    | (apply h296a <;> assumption)
    | (apply h296b <;> assumption)
    | (apply h184 <;> assumption)
    | (apply h296c <;> assumption)
    | (apply h328 <;> assumption)
    | (apply h141a <;> assumption)
    | (apply h141b <;> assumption)
    | (apply h141c <;> assumption)
    | (apply h141d <;> assumption)

/-- 141: the first byte of a 4 to 6 byte form. -/
theorem vc_141 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 1, Foot Wl (Addr.add g.rax i))
    (h : ∀ fl (b : BitVec 8), Q 152 { g with rax := g.rax + 1#64 } fl (Vst V g.rax (toBytesLE b 1))) :
    W_141 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_141, o10]
  repeat' (first | with_reducible exact fw | apply And.intro | intro _)
  all_goals apply h

/-- 152: the next byte; `ecx` less 6, to 152 again or to 184. -/
theorem vc_152 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {c : BitVec 32}
    (hc : g.rcx = BitVec.setWidth 64 c)
    (fw : ∀ i < 1, Foot Wl (Addr.add (g.rax + 1#64 + 18446744073709551615#64) i))
    (h152 : (!(c - 6#32 &&& c - 6#32 == 0)) = true → ∀ fl s (b : BitVec 8),
      Q 152 { g with rax := g.rax + 1#64, rcx := BitVec.setWidth 64 (c - 6#32), rsi := s } fl
        (Vst V (g.rax + 1#64 + 18446744073709551615#64) (toBytesLE b 1)))
    (h184 : (!(c - 6#32 &&& c - 6#32 == 0)) = false → ∀ fl (b : BitVec 8),
      Q 184 { g with rax := g.rax + 1#64, rcx := BitVec.setWidth 64 (c - 6#32), rsi := g.rdi } fl
        (Vst V (g.rax + 1#64 + 18446744073709551615#64) (toBytesLE b 1))) :
    W_152 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc fw h152 h184 ⊢
  subst hc
  wpx [W_152, W_178, o11, o12]
  repeat' (first | with_reducible exact fw | apply And.intro | intro _)
  all_goals first
    | (apply h152 <;> assumption)
    | (apply h184 <;> assumption)

/-- 184: `rsi` at `srcLim` (to 193) or not (to 32). -/
theorem vc_184 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h32 : (!decide (g.rsi = g.rdx)) = true → ∀ fl, Q 32 g fl V)
    (h193 : (!decide (g.rsi = g.rdx)) = false → ∀ fl, Q 193 g fl V) : W_184 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h32 h193 ⊢
  wpx [W_184, o13]
  repeat' (first | apply And.intro | intro _)
  all_goals first
    | (apply h32 <;> assumption)
    | (apply h193 <;> assumption)

/-- 200: one byte. -/
theorem vc_200 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fw : ∀ i < 1, Foot Wl (Addr.add g.rax i))
    (h : ∀ fl (b : BitVec 8), Q 184 { g with rax := g.rax + 1#64, rsi := g.rdi } fl (Vst V g.rax (toBytesLE b 1))) :
    W_200 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_200, o14]
  repeat' (first | with_reducible exact fw | apply And.intro | intro _)
  all_goals apply h

/-- 296: the three bytes of an unpaired surrogate (by the flag bit 8), to 328. -/
theorem vc_296 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl c s r, Q 328 { g with rcx := c, rsi := s, r10 := r } fl V) : W_296 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_296, W_440, W_305, o19, o27, o20]
  repeat' (first | apply And.intro | intro _)
  all_goals apply h

/-- 328: three bytes. -/
theorem vc_328 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i < 1, Foot Wl (Addr.add (g.rax + 1#64) i))
    (fb : ∀ i < 1, Foot Wl (Addr.add (g.rax + 3#64 + 18446744073709551613#64) i))
    (fc : ∀ i < 1, Foot Wl (Addr.add (g.rax + 3#64 + 18446744073709551615#64) i))
    (h : ∀ fl (b0 b1 b2 : BitVec 8), Q 184 { g with rax := g.rax + 3#64, rsi := g.rdi } fl
      (Vst (Vst (Vst V (g.rax + 1#64) (toBytesLE b0 1)) (g.rax + 3#64 + 18446744073709551613#64) (toBytesLE b1 1))
        (g.rax + 3#64 + 18446744073709551615#64) (toBytesLE b2 1))) :
    W_328 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fa fb fc h ⊢
  wpx [W_328, o21]
  repeat' (first | with_reducible exact fa | with_reducible exact fb | with_reducible exact fc | apply And.intro |
    intro _)
  all_goals apply h

attribute [local irreducible] W_0 W_32 W_83 W_141 W_152 W_184 W_200 W_296 W_328

/-! ## The exits -/

section exits
variable {g₀ : Gprs} {V₀ V : Addr → Byte} {n W : Nat}

/-- A store at the `j`-th byte from `dest`, `j < W`. -/
theorem fwA (fw : ∀ j < W, ∀ i < 1, Foot Wl (Addr.add (g₀.rdi + BitVec.ofNat 64 j) i)) {a : Addr} {j : Nat}
    (h : a = g₀.rdi + BitVec.ofNat 64 j) (hj : j < W) : ∀ i < 1, Foot Wl (Addr.add a i) := by
  rw [h]; exact fw j hj

/-- The `k`-th character, read with the bytes stored. -/
theorem rdk (hs : Sep g₀ n W) {cc k : Nat} (hF : Fr V₀ g₀.rdi cc V) (hc : cc ≤ W) (hk : k < n) :
    rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k)) = ch V₀ g₀.rsi k :=
  congrArg (ofBytesLE 32) (rdN hF fun i hi j hj => hs k hk i hi j (by omega))

/-- The next character's address is not `srcLim`: it is in the string. -/
theorem nxt {k : Nat} (hl : Lim g₀ n) (hk : k < n)
    (h : decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = false) : k + 1 < n := by
  rcases Nat.lt_or_ge (k + 1) n with h' | h'
  · exact h'
  · have e : k + 1 = n := by omega
    rw [hl.1, adv4, e] at h
    exact absurd h (by simp)

theorem lst {k : Nat} (hl : Lim g₀ n) (hk : k < n)
    (h : decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = true) : k + 1 = n := by
  have h' : g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64 := of_decide_eq_true h
  rw [hl.1, adv4] at h'
  exact (pinj hl.2 (Nat.le_refl n) (by omega) h').symm

/-! ### The entry -/

theorem x0_193 : decide (g₀.rsi = g₀.rdx) = true → ∀ fl,
    Nx g₀ V₀ n W (10 * n + 20) 193 { g₀ with rax := g₀.rdi, r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g₀.rcx) }
      fl V₀ := fun _ _ =>
  Or.inr ⟨rfl, 0, Nat.zero_le _, fr0, g₀.rcx, g₀.rsi, g₀.rdi, BitVec.setWidth 64 (BitVec.setWidth 32 g₀.rcx), g₀.r9,
    g₀.r10, g₀.r11, by rw [d0]⟩

theorem x0_32 (hl : Lim g₀ n) (hW : wb V₀ g₀.rsi n (E9 g₀) 0 ≤ W) : decide (g₀.rsi = g₀.rdx) = false → ∀ fl,
    Nx g₀ V₀ n W (10 * n + 20) 32 { g₀ with
        rax := g₀.rdi, r8 := BitVec.setWidth 64 (BitVec.setWidth 32 g₀.rcx &&& 256#32),
        r9 := BitVec.setWidth 64 (BitVec.setWidth 32 g₀.rcx &&& 512#32) } fl V₀ := by
  intro h fl
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hl.1, z0] at h
      simp at h
    · exact hn
  refine Or.inl ⟨10 * (n - 0) + 9, by omega, Or.inr (Or.inl ⟨rfl, 0, hn, rfl, 0, by omega, fr0, g₀.rcx, g₀.rdi,
    g₀.r10, g₀.r11, ?_⟩)⟩
  rw [d0, z0]

variable {k cc : Nat} {c i x y : BitVec 64}

/-! ### 32 -/

/-- The registers at 32. -/
abbrev G32 (g₀ : Gprs) (k cc : Nat) (c i x y : BitVec 64) : Gprs :=
  Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) c (g₀.rsi + BitVec.ofNat 64 (4 * k)) i x y

section x32
variable (hk : k < n) (hb : cc + wb V₀ g₀.rsi n (E9 g₀) k ≤ W) (hF : Fr V₀ g₀.rdi cc V)
  (hr : rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k)) = ch V₀ g₀.rsi k)
include hk hb hF hr

theorem x32_200a : le127 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = true → ∀ fl,
    Nx g₀ V₀ n W (10 * (n - k) + 9) 200 { G32 g₀ k cc c i x y with
        rcx := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))),
        rdi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64,
        r10 := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) } fl V := by
  intro h1 fl
  rw [hr] at h1
  have e := wb_a (e := E9 g₀) hk h1
  exact Or.inl ⟨10 * (n - k) + 7, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨1, 7, Or.inl ⟨rfl, rfl, rfl⟩, k, hk,
    rfl, cc, by omega, hF, _, _, _, _, rfl⟩)))⟩

theorem b32 : le127 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false →
    le2047 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = true → cc + 2 ≤ W := by
  intro h1 h2
  rw [hr] at h1 h2
  have e := wb_b (e := E9 g₀) hk h1 h2
  omega

theorem x32_184 : le127 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false →
    le2047 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = true → ∀ fl c' (b0 b1 : BitVec 8),
    Nx g₀ V₀ n W (10 * (n - k) + 9) 184 { G32 g₀ k cc c i x y with
        rax := g₀.rdi + BitVec.ofNat 64 cc + 2#64, rcx := c', rsi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64,
        rdi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64,
        r10 := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) } fl
      (Vst (Vst V (g₀.rdi + BitVec.ofNat 64 cc + 2#64 + 18446744073709551615#64) (toBytesLE b0 1))
        (g₀.rdi + BitVec.ofNat 64 cc + 2#64 + 18446744073709551614#64) (toBytesLE b1 1)) := by
  intro h1 h2 fl c' b0 b1
  rw [hr] at h1 h2
  have e := wb_b (e := E9 g₀) hk h1 h2
  rw [ad g₀.rdi cc 1 2#64 18446744073709551615#64 (by decide),
    ad g₀.rdi cc 0 2#64 18446744073709551614#64 (by decide), ← addK g₀.rdi cc 2]
  exact Or.inl ⟨10 * (n - (k + 1)) + 10, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k + 1,
    by omega, rfl, cc + 2, by omega, fr1 (fr1 (c' := cc + 2) hF (by omega) (by omega) b0) (by omega) (by omega) b1, c',
    g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64, BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))), y,
    by rw [← adv4]⟩)))))⟩

theorem x32_83a : le127 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false →
    le2047 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false → (E9 g₀ &&& E9 g₀ == 0) = true → ∀ fl,
    Nx g₀ V₀ n W (10 * (n - k) + 9) 83 { G32 g₀ k cc c i x y with
        rcx := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))),
        rdi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64,
        r10 := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) } fl V := by
  intro h1 h2 h3 fl
  rw [hr] at h1 h2 ⊢
  exact Or.inl ⟨10 * (n - k) + 8, by omega, Or.inr (Or.inr (Or.inl ⟨rfl, k, hk, rfl, cc, hb, hF,
    ⟨h1, h2, nz_t h3⟩, _, _, rfl⟩))⟩

theorem x32_200b : le127 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false →
    le2047 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false → (E9 g₀ &&& E9 g₀ == 0) = false →
    m51 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = true → ∀ fl,
    Nx g₀ V₀ n W (10 * (n - k) + 9) 200 { G32 g₀ k cc c i x y with
        rcx := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))),
        rdi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64,
        r10 := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))),
        r11 := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k)) &&& 4294967168#32) } fl V := by
  intro h1 h2 h3 h4 fl
  rw [hr] at h1 h2 h4
  have e := wb_c hk h1 h2 (nz_ft h3 h4)
  exact Or.inl ⟨10 * (n - k) + 7, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨1, 7, Or.inl ⟨rfl, rfl, rfl⟩, k, hk,
    rfl, cc, by omega, hF, _, _, _, _, rfl⟩)))⟩

theorem x32_83b : le127 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false →
    le2047 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false → (E9 g₀ &&& E9 g₀ == 0) = false →
    m51 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))) = false → ∀ fl,
    Nx g₀ V₀ n W (10 * (n - k) + 9) 83 { G32 g₀ k cc c i x y with
        rcx := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))),
        rdi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64,
        r10 := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k))),
        r11 := BitVec.setWidth 64 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k)) &&& 4294967168#32) } fl V := by
  intro h1 h2 h3 h4 fl
  rw [hr] at h1 h2 h4 ⊢
  exact Or.inl ⟨10 * (n - k) + 8, by omega, Or.inr (Or.inr (Or.inl ⟨rfl, k, hk, rfl, cc, hb, hF,
    ⟨h1, h2, nz_f h3 h4⟩, _, _, rfl⟩))⟩

end x32

/-! ### 83 -/

/-- The registers at 83. -/
abbrev G83 (g₀ : Gprs) (V₀ : Addr → Byte) (k cc : Nat) (x y : BitVec 64) : Gprs :=
  Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) (BitVec.setWidth 64 (ch V₀ g₀.rsi k)) (g₀.rsi + BitVec.ofNat 64 (4 * k))
    (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) x y

/-- The next character is read only when it is in the string. -/
theorem fq83 (hl : Lim g₀ n) (hk : k < n)
    (fa : ∀ k < n, ∀ i < 4, Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 (4 * k)) i)) :
    sur (ch V₀ g₀.rsi k) = true → hi (ch V₀ g₀.rsi k) = false →
    decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = false →
      ∀ i < 4, Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) i) := fun _ _ h => by
  rw [adv4]
  exact fa (k + 1) (nxt hl hk h)

section x83
variable (hk : k < n) (hb : cc + wb V₀ g₀.rsi n (E9 g₀) k ≤ W) (hF : Fr V₀ g₀.rdi cc V)
  (hP : Past V₀ g₀.rsi (E9 g₀) k)
include hk hb hF hP

theorem x83_296a : sur (ch V₀ g₀.rsi k) = true → hi (ch V₀ g₀.rsi k) = true → ∀ fl r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 296 { G83 g₀ V₀ k cc x y with r10 := r, r11 := y' } fl V := by
  intro h4 h5 fl r y'
  have e := wb_d hk hP h4 h5
  exact Or.inl ⟨10 * (n - k) + 7, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 7, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
    k, hk, rfl, cc, by omega, hF, _, _, _, _, rfl⟩)))⟩

theorem x83_296b (hl : Lim g₀ n) : sur (ch V₀ g₀.rsi k) = true → hi (ch V₀ g₀.rsi k) = false →
    decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = true → ∀ fl r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 296 { G83 g₀ V₀ k cc x y with r10 := r, r11 := y' } fl V := by
  intro h4 h5 h6 fl r y'
  have e := wb_e hk hP h4 h5 (lst hl hk h6)
  exact Or.inl ⟨10 * (n - k) + 7, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 7, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
    k, hk, rfl, cc, by omega, hF, _, _, _, _, rfl⟩)))⟩

/-- The next character, a low surrogate or not, read with the bytes stored. -/
theorem rd83 (hl : Lim g₀ n) (hs : Sep g₀ n W)
    (h6 : decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = false) :
    rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = ch V₀ g₀.rsi (k + 1) := by
  rw [adv4]
  exact rdk hs hF (by omega) (nxt hl hk h6)

theorem b83 (hl : Lim g₀ n) (hs : Sep g₀ n W) : sur (ch V₀ g₀.rsi k) = true → hi (ch V₀ g₀.rsi k) = false →
    decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = false →
    lo4 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64)) = true → cc + 4 ≤ W := by
  intro h4 h5 h6 h7
  rw [rd83 hk hb hF hP hl hs h6] at h7
  have e := wb_f hk hP h4 h5 (nxt hl hk h6) h7
  omega

theorem x83_184 (hl : Lim g₀ n) (hs : Sep g₀ n W) : sur (ch V₀ g₀.rsi k) = true → hi (ch V₀ g₀.rsi k) = false →
    decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = false →
    lo4 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64)) = true → ∀ fl c' i' r y' (b0 b1 b2 b3 : BitVec 8),
    Nx g₀ V₀ n W (10 * (n - k) + 8) 184 { G83 g₀ V₀ k cc x y with
        rax := g₀.rdi + BitVec.ofNat 64 cc + 4#64, rcx := c', rsi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 8#64,
        rdi := i', r10 := r, r11 := y' } fl
      (Vst (Vst (Vst (Vst V (g₀.rdi + BitVec.ofNat 64 cc + 4#64 + 18446744073709551612#64) (toBytesLE b0 1))
        (g₀.rdi + BitVec.ofNat 64 cc + 4#64 + 18446744073709551613#64) (toBytesLE b1 1))
        (g₀.rdi + BitVec.ofNat 64 cc + 4#64 + 18446744073709551615#64) (toBytesLE b2 1))
        (g₀.rdi + BitVec.ofNat 64 cc + 4#64 + 18446744073709551614#64) (toBytesLE b3 1)) := by
  intro h4 h5 h6 h7 fl c' i' r y' b0 b1 b2 b3
  have h8 := nxt hl hk h6
  rw [rd83 hk hb hF hP hl hs h6] at h7
  have e := wb_f hk hP h4 h5 h8 h7
  rw [ad g₀.rdi cc 0 4#64 18446744073709551612#64 (by decide), ad g₀.rdi cc 1 4#64 18446744073709551613#64 (by decide),
    ad g₀.rdi cc 3 4#64 18446744073709551615#64 (by decide), ad g₀.rdi cc 2 4#64 18446744073709551614#64 (by decide),
    ← addK g₀.rdi cc 4]
  exact Or.inl ⟨10 * (n - (k + 2)) + 10, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k + 2,
    by omega, rfl, cc + 4, by omega,
    fr1 (fr1 (c' := cc + 4) (fr1 (c' := cc + 4) (fr1 (c' := cc + 4) hF (by omega) (by omega) b0) (by omega) (by omega)
      b1) (by omega) (by omega) b2) (by omega) (by omega) b3,
    c', i', r, y', by rw [← adv8]⟩)))))⟩

theorem x83_296c (hl : Lim g₀ n) (hs : Sep g₀ n W) : sur (ch V₀ g₀.rsi k) = true → hi (ch V₀ g₀.rsi k) = false →
    decide (g₀.rdx = g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) = false →
    lo4 (rdd(V, g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64)) = false → ∀ fl r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 296 { G83 g₀ V₀ k cc x y with r10 := r, r11 := y' } fl V := by
  intro h4 h5 h6 h7 fl r y'
  rw [rd83 hk hb hF hP hl hs h6] at h7
  have e := wb_g hk hP h4 h5 (nxt hl hk h6) h7
  exact Or.inl ⟨10 * (n - k) + 7, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 7, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩),
    k, hk, rfl, cc, by omega, hF, _, _, _, _, rfl⟩)))⟩

theorem x83_328 : sur (ch V₀ g₀.rsi k) = false → le65535 (ch V₀ g₀.rsi k) = true → ∀ fl c' s r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 328 { G83 g₀ V₀ k cc x y with rcx := c', rsi := s, r10 := r, r11 := y' } fl V := by
  intro h4 h5 fl c' s r y'
  have e := wb_h hk hP h4 h5
  exact Or.inl ⟨10 * (n - k) + 6, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 6, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩),
    k, hk, rfl, cc, by omega, hF, _, _, _, _, rfl⟩)))⟩

/-- 83 to 141 with `j` bytes after the first. -/
theorem x83_141 {j w : Nat} (hj : j = 3 ∨ j = 4 ∨ j = 5) (hw : w = 1 + j)
    (e : wb V₀ g₀.rsi n (E9 g₀) k = w + wb V₀ g₀.rsi n (E9 g₀) (k + 1)) {fl : Rflags} {s r y' : BitVec 64} :
    Nx g₀ V₀ n W (10 * (n - k) + 8) 141 { G83 g₀ V₀ k cc x y with
        rcx := BitVec.setWidth 64 (BitVec.ofNat 32 (6 * j)), rsi := s, r10 := r, r11 := y' } fl V :=
  Or.inl ⟨10 * (n - k) + 6, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k, hk, rfl, j, hj, cc,
    by omega, hF, _, _, _, rfl⟩))))⟩

theorem x83_141a : sur (ch V₀ g₀.rsi k) = false → le65535 (ch V₀ g₀.rsi k) = false →
    (!le2097151 (ch V₀ g₀.rsi k)) = false → ∀ fl s r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 141 { G83 g₀ V₀ k cc x y with
        rcx := BitVec.setWidth 64 18#32, rsi := s, r10 := r, r11 := y' } fl V := fun h4 h5 h6 _ _ _ _ =>
  x83_141 (j := 3) hk hb hF hP (Or.inl rfl) rfl (wb_i hk hP h4 h5 (nn h6))

theorem x83_141b : sur (ch V₀ g₀.rsi k) = false → le65535 (ch V₀ g₀.rsi k) = false →
    (!le2097151 (ch V₀ g₀.rsi k)) = true → gt26 (ch V₀ g₀.rsi k) = false → ∀ fl s r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 141 { G83 g₀ V₀ k cc x y with
        rcx := BitVec.setWidth 64 24#32, rsi := s, r10 := r, r11 := y' } fl V := fun h4 h5 h6 h7 _ _ _ _ =>
  x83_141 (j := 4) hk hb hF hP (Or.inr (Or.inl rfl)) rfl (wb_l hk hP h4 h5 (nt h6) h7)

theorem x83_141c : sur (ch V₀ g₀.rsi k) = false → le65535 (ch V₀ g₀.rsi k) = false →
    (!le2097151 (ch V₀ g₀.rsi k)) = true → gt26 (ch V₀ g₀.rsi k) = true →
    (ch V₀ g₀.rsi k &&& ch V₀ g₀.rsi k).msb = false → ∀ fl s r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 141 { G83 g₀ V₀ k cc x y with
        rcx := BitVec.setWidth 64 30#32, rsi := s, r10 := r, r11 := y' } fl V := fun h4 h5 h6 h7 h8 _ _ _ _ =>
  x83_141 (j := 5) hk hb hF hP (Or.inr (Or.inr rfl)) rfl
    (wb_j hk hP h4 h5 (nt h6) h7 (by show (!(ch V₀ g₀.rsi k &&& ch V₀ g₀.rsi k).msb) = true; rw [h8]; rfl))

theorem x83_141d : sur (ch V₀ g₀.rsi k) = false → le65535 (ch V₀ g₀.rsi k) = false →
    (!le2097151 (ch V₀ g₀.rsi k)) = true → gt26 (ch V₀ g₀.rsi k) = true →
    (ch V₀ g₀.rsi k &&& ch V₀ g₀.rsi k).msb = true → ∀ fl s r y',
    Nx g₀ V₀ n W (10 * (n - k) + 8) 141 { G83 g₀ V₀ k cc x y with
        rcx := BitVec.setWidth 64 18#32, rsi := s, r10 := r, r11 := y' } fl V := fun h4 h5 h6 h7 h8 _ _ _ _ =>
  x83_141 (j := 3) hk hb hF hP (Or.inl rfl) rfl
    (wb_k hk hP h4 h5 (nt h6) h7 (by show (!(ch V₀ g₀.rsi k &&& ch V₀ g₀.rsi k).msb) = false; rw [h8]; rfl))

end x83

/-! ### 200, 296, 328: `rdi` at the next character -/

/-- The registers at 200, 296, 328. -/
abbrev G2 (g₀ : Gprs) (k cc : Nat) (c s x y : BitVec 64) : Gprs :=
  Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) c s (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) x y

variable {s : BitVec 64}

theorem x200 (hk : k < n) (hb : cc + 1 + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W) (hF : Fr V₀ g₀.rdi cc V) :
    ∀ fl (b : BitVec 8), Nx g₀ V₀ n W (10 * (n - k) + 7) 184 { G2 g₀ k cc c s x y with
        rax := g₀.rdi + BitVec.ofNat 64 cc + 1#64, rsi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64 } fl
      (Vst V (g₀.rdi + BitVec.ofNat 64 cc) (toBytesLE b 1)) := by
  intro fl b
  rw [← addK g₀.rdi cc 1]
  exact Or.inl ⟨10 * (n - (k + 1)) + 10, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k + 1,
    by omega, rfl, cc + 1, by omega, fr1 hF (by omega) (by omega) b, c, g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64,
    x, y, by rw [← adv4]⟩)))))⟩

theorem x296 (hk : k < n) (hb : cc + 3 + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W) (hF : Fr V₀ g₀.rdi cc V) :
    ∀ fl c' s' r, Nx g₀ V₀ n W (10 * (n - k) + 7) 328 { G2 g₀ k cc c s x y with rcx := c', rsi := s', r10 := r } fl V :=
  fun _ _ _ _ => Or.inl ⟨10 * (n - k) + 6, by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨3, 6,
    Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), k, hk, rfl, cc, hb, hF, _, _, _, _, rfl⟩)))⟩

theorem x328 (hk : k < n) (hb : cc + 3 + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W) (hF : Fr V₀ g₀.rdi cc V) :
    ∀ fl (b0 b1 b2 : BitVec 8), Nx g₀ V₀ n W (10 * (n - k) + 6) 184 { G2 g₀ k cc c s x y with
        rax := g₀.rdi + BitVec.ofNat 64 cc + 3#64, rsi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64 } fl
      (Vst (Vst (Vst V (g₀.rdi + BitVec.ofNat 64 cc + 1#64) (toBytesLE b0 1))
        (g₀.rdi + BitVec.ofNat 64 cc + 3#64 + 18446744073709551613#64) (toBytesLE b1 1))
        (g₀.rdi + BitVec.ofNat 64 cc + 3#64 + 18446744073709551615#64) (toBytesLE b2 1)) := by
  intro fl b0 b1 b2
  rw [ad g₀.rdi cc 0 3#64 18446744073709551613#64 (by decide), ad g₀.rdi cc 2 3#64 18446744073709551615#64 (by decide),
    ← addK g₀.rdi cc 1, ← addK g₀.rdi cc 3]
  exact Or.inl ⟨10 * (n - (k + 1)) + 10, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k + 1,
    by omega, rfl, cc + 3, by omega,
    fr1 (fr1 (c' := cc + 3) (fr1 (c' := cc + 3) hF (by omega) (by omega) b0) (by omega) (by omega) b1) (by omega)
      (by omega) b2,
    c, g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64, x, y, by rw [← adv4]⟩)))))⟩

/-! ### 141, 152: the bytes of a 4 to 6 byte form -/

/-- The registers at 141, 152. -/
abbrev G5 (g₀ : Gprs) (k cc j : Nat) (s x y : BitVec 64) : Gprs :=
  Gs g₀ (g₀.rdi + BitVec.ofNat 64 cc) (BitVec.setWidth 64 (BitVec.ofNat 32 (6 * j))) s
    (g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64) x y

variable {j : Nat}

theorem x141 (hk : k < n) (hj : j = 3 ∨ j = 4 ∨ j = 5) (hb : cc + 1 + j + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W)
    (hF : Fr V₀ g₀.rdi cc V) : ∀ fl (b : BitVec 8), Nx g₀ V₀ n W (10 * (n - k) + 6) 152
      { G5 g₀ k cc j s x y with rax := g₀.rdi + BitVec.ofNat 64 cc + 1#64 } fl
      (Vst V (g₀.rdi + BitVec.ofNat 64 cc) (toBytesLE b 1)) := by
  intro fl b
  rw [← addK g₀.rdi cc 1]
  exact Or.inl ⟨10 * (n - k) + j, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k, hk, j,
    by omega, by omega, rfl, cc + 1, by omega, fr1 hF (by omega) (by omega) b, _, _, _, rfl⟩)))))⟩

theorem s6 (h1 : 1 ≤ j) (h5 : j ≤ 5) : BitVec.ofNat 32 (6 * j) - 6#32 = BitVec.ofNat 32 (6 * (j - 1)) := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  all_goals decide

theorem s6z (h1 : 1 ≤ j) (h5 : j ≤ 5)
    (h : (!(BitVec.ofNat 32 (6 * j) - 6#32 &&& BitVec.ofNat 32 (6 * j) - 6#32 == 0)) = true) : 2 ≤ j := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  all_goals first | omega | (revert h; decide)

section x152
variable (hk : k < n) (hj1 : 1 ≤ j) (hj5 : j ≤ 5) (hb : cc + j + wb V₀ g₀.rsi n (E9 g₀) (k + 1) ≤ W)
  (hF : Fr V₀ g₀.rdi cc V)
include hk hj1 hj5 hb hF

theorem x152a : (!(BitVec.ofNat 32 (6 * j) - 6#32 &&& BitVec.ofNat 32 (6 * j) - 6#32 == 0)) = true →
    ∀ fl s' (b : BitVec 8), Nx g₀ V₀ n W (10 * (n - k) + j) 152 { G5 g₀ k cc j s x y with
        rax := g₀.rdi + BitVec.ofNat 64 cc + 1#64,
        rcx := BitVec.setWidth 64 (BitVec.ofNat 32 (6 * j) - 6#32), rsi := s' } fl
      (Vst V (g₀.rdi + BitVec.ofNat 64 cc + 1#64 + 18446744073709551615#64) (toBytesLE b 1)) := by
  intro h fl s' b
  have h2 := s6z hj1 hj5 h
  rw [s6 hj1 hj5, ad g₀.rdi cc 0 1#64 18446744073709551615#64 (by decide), ← addK g₀.rdi cc 1]
  exact Or.inl ⟨10 * (n - k) + (j - 1), by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, k, hk,
    j - 1, by omega, by omega, rfl, cc + 1, by omega, fr1 hF (by omega) (by omega) b, _, _, _, rfl⟩)))))⟩

theorem x152b : (!(BitVec.ofNat 32 (6 * j) - 6#32 &&& BitVec.ofNat 32 (6 * j) - 6#32 == 0)) = false →
    ∀ fl (b : BitVec 8), Nx g₀ V₀ n W (10 * (n - k) + j) 184 { G5 g₀ k cc j s x y with
        rax := g₀.rdi + BitVec.ofNat 64 cc + 1#64,
        rcx := BitVec.setWidth 64 (BitVec.ofNat 32 (6 * j) - 6#32),
        rsi := g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64 } fl
      (Vst V (g₀.rdi + BitVec.ofNat 64 cc + 1#64 + 18446744073709551615#64) (toBytesLE b 1)) := by
  intro _ fl b
  rw [ad g₀.rdi cc 0 1#64 18446744073709551615#64 (by decide), ← addK g₀.rdi cc 1]
  exact Or.inl ⟨10 * (n - (k + 1)) + 10, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, k + 1,
    by omega, rfl, cc + 1, by omega, fr1 hF (by omega) (by omega) b,
    BitVec.setWidth 64 (BitVec.ofNat 32 (6 * j) - 6#32), g₀.rsi + BitVec.ofNat 64 (4 * k) + 4#64, x, y,
    by rw [← adv4]⟩)))))⟩

end x152

/-! ### 184: on to 32, or out at 193 -/

theorem x184_32 (hl : Lim g₀ n) (hk : k ≤ n) (hb : cc + wb V₀ g₀.rsi n (E9 g₀) k ≤ W) (hF : Fr V₀ g₀.rdi cc V) :
    (!decide (g₀.rsi + BitVec.ofNat 64 (4 * k) = g₀.rdx)) = true → ∀ fl,
      Nx g₀ V₀ n W (10 * (n - k) + 10) 32 (G32 g₀ k cc c i x y) fl V := by
  intro h fl
  have hk' : k < n := by
    rcases Nat.lt_or_ge k n with h' | h'
    · exact h'
    · have e : k = n := by omega
      rw [e, ← hl.1] at h
      simp at h
  exact Or.inl ⟨10 * (n - k) + 9, by omega, Or.inr (Or.inl ⟨rfl, k, hk', rfl, cc, hb, hF, c, i, x, y, rfl⟩)⟩

theorem x184_193 (hb : cc + wb V₀ g₀.rsi n (E9 g₀) k ≤ W) (hF : Fr V₀ g₀.rdi cc V) :
    (!decide (g₀.rsi + BitVec.ofNat 64 (4 * k) = g₀.rdx)) = false → ∀ fl,
      Nx g₀ V₀ n W (10 * (n - k) + 10) 193 (G32 g₀ k cc c i x y) fl V := fun _ _ =>
  Or.inr ⟨rfl, cc, by omega, hF, c, g₀.rsi + BitVec.ofNat 64 (4 * k), i, BitVec.setWidth 64 (E8 g₀),
    BitVec.setWidth 64 (E9 g₀), x, y, rfl⟩

end exits

/-! ## The cut points' conditions -/

theorem vcAll {g₀ : Gprs} {V₀ : Addr → Byte} {n W : Nat} (hl : Lim g₀ n)
    (fa : ∀ k < n, ∀ i < 4, Foot F.data (Addr.add (g₀.rsi + BitVec.ofNat 64 (4 * k)) i))
    (fw : ∀ j < W, ∀ i < 1, Foot Wl (Addr.add (g₀.rdi + BitVec.ofNat 64 j) i))
    (hW : wb V₀ g₀.rsi n (E9 g₀) 0 ≤ W) (hs : Sep g₀ n W) (ℓ m : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ n W ℓ m g V) : Wt ℓ F Wl (Nx g₀ V₀ n W m) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, k, hk, rfl, cc, hb, hF, c, i, x, y, rfl⟩ |
    ⟨rfl, k, hk, rfl, cc, hb, hF, hP, x, y, rfl⟩ |
    ⟨b, o, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩, k, hk, rfl, cc, hb, hF, c, s, x, y, rfl⟩ |
    ⟨rfl, k, hk, rfl, j, hj, cc, hb, hF, s, x, y, rfl⟩ |
    ⟨rfl, k, hk, j, hj1, hj5, rfl, cc, hb, hF, s, x, y, rfl⟩ |
    ⟨rfl, k, hk, rfl, cc, hb, hF, c, i, x, y, rfl⟩
  · exact vc_0 x0_193 (x0_32 hl hW)
  · have hr := rdk hs hF (by omega) hk
    refine vc_32 (g := G32 g₀ k cc c i x y) (V := V) (Q := Nx g₀ V₀ n W (10 * (n - k) + 9)) (e := E9 g₀) rfl
      (fa k hk) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact x32_200a hk hb hF hr
    · exact fun h1 h2 => fwA fw (ad _ _ 1 _ _ (by decide)) (by have := b32 hk hb hF hr h1 h2; omega)
    · exact fun h1 h2 => fwA fw (ad _ _ 0 _ _ (by decide)) (by have := b32 hk hb hF hr h1 h2; omega)
    · exact x32_184 hk hb hF hr
    · exact x32_83a hk hb hF hr
    · exact x32_200b hk hb hF hr
    · exact x32_83b hk hb hF hr
  · refine vc_83 (g := G83 g₀ V₀ k cc x y) (V := V) (Q := Nx g₀ V₀ n W (10 * (n - k) + 8))
      (c := ch V₀ g₀.rsi k) rfl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact x83_296a hk hb hF hP
    · exact x83_296b hk hb hF hP hl
    · dsimp only [G83, Gs]
      exact fq83 (F := F) hl hk fa
    · exact fun h4 h5 h6 h7 => fwA fw (ad _ _ 0 _ _ (by decide))
        (by have := b83 hk hb hF hP hl hs h4 h5 h6 h7; omega)
    · exact fun h4 h5 h6 h7 => fwA fw (ad _ _ 1 _ _ (by decide))
        (by have := b83 hk hb hF hP hl hs h4 h5 h6 h7; omega)
    · exact fun h4 h5 h6 h7 => fwA fw (ad _ _ 3 _ _ (by decide))
        (by have := b83 hk hb hF hP hl hs h4 h5 h6 h7; omega)
    · exact fun h4 h5 h6 h7 => fwA fw (ad _ _ 2 _ _ (by decide))
        (by have := b83 hk hb hF hP hl hs h4 h5 h6 h7; omega)
    · exact x83_184 hk hb hF hP hl hs
    · exact x83_296c hk hb hF hP hl hs
    · exact x83_328 hk hb hF hP
    · exact x83_141a hk hb hF hP
    · exact x83_141b hk hb hF hP
    · exact x83_141c hk hb hF hP
    · exact x83_141d hk hb hF hP
  · exact vc_200 (g := G2 g₀ k cc c s x y) (fwA fw rfl (by omega)) (x200 hk hb hF)
  · exact vc_296 (g := G2 g₀ k cc c s x y) (x296 hk hb hF)
  · exact vc_328 (g := G2 g₀ k cc c s x y) (fwA fw (addK _ cc 1).symm (by omega))
      (fwA fw (ad _ _ 0 _ _ (by decide)) (by omega)) (fwA fw (ad _ _ 2 _ _ (by decide)) (by omega)) (x328 hk hb hF)
  · exact vc_141 (g := G5 g₀ k cc j s x y) (fwA fw rfl (by omega)) (x141 hk hj hb hF)
  · refine vc_152 (g := G5 g₀ k cc j s x y) (V := V) (Q := Nx g₀ V₀ n W (10 * (n - k) + j))
      (c := BitVec.ofNat 32 (6 * j)) rfl (fwA fw (ad _ _ 0 _ _ (by decide)) (by omega)) ?_ ?_
    · exact x152a hk hj1 hj5 hb hF
    · exact x152b hk hj1 hj5 hb hF
  · exact vc_184 (g := G32 g₀ k cc c i x y) (x184_32 hl hk hb hF) (x184_193 hb hF)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {n W : Nat}

/-- `Utf16_To_Utf8 (dest, src, srcLim, flags)` from its entry, with `srcLim` = `src + 4n` (no wrap), the `n`
characters readable, `W` bytes from `dest` writable where the characters take at most `W` (`wb`), and the characters
and the return address apart from them: at the return address, the return address popped, the memory as it was but
at the `W` bytes, `rax` = `dest + cc` with `cc ≤ W`, `rcx`, `rsi`, `rdi`, `r8`–`r11` some values. -/
theorem u8w_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L u8w_at u8w) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = u8w_at) (hl : Lim X.cpu.gpr n)
    (fa : ∀ k < n, ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + BitVec.ofNat 64 (4 * k)) i))
    (fw : ∀ j < W, ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rdi + BitVec.ofNat 64 j) i))
    (hW : wb V X.cpu.gpr.rsi n (E9 X.cpu.gpr) 0 ≤ W) (hs : Sep X.cpu.gpr n W)
    (hsl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hss : ∀ i < 8, ∀ j < W, Addr.add X.cpu.gpr.rsp i ≠ X.cpu.gpr.rdi + BitVec.ofNat 64 j)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), Fr V X.cpu.gpr.rdi W V' → KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      (∃ cc ≤ W, ∃ c s i u v x y, Z.cpu.gpr = ({ X.cpu.gpr with
          rax := X.cpu.gpr.rdi + BitVec.ofNat 64 cc, rcx := c, rsi := s, rdi := i, r8 := u, r9 := v, r10 := x,
          r11 := y } : Gprs).set 4 (X.cpu.gpr.rsp + 8)) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ m g _ V' => Inv X.cpu.gpr V n W ℓ m g V')
    (fun j g _ V' => Fin X.cpu.gpr V W j g V') (fun ℓ m g f V' h => vcAll hl fa fw hW hs ℓ m g f V' h) ?_
    (10 * n + 20) 0 hK hA (by rw [addr_add_zero]; exact hrip) (Or.inl ⟨rfl, rfl, rfl, rfl⟩)
  rintro j g fl V' ⟨rfl, cc, hcc, hF, c', s', i, u, v, x, y, rfl⟩ Y t' hKY hAY hrY hgY -
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  have hF' : Fr V X.cpu.gpr.rdi W V' := frW hF hcc
  have hra' : rdq(V', X.cpu.gpr.rsp) = e₂.add j₂ := by rw [rdN hF' hss]; exact hra
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_193 _) (by rw [hsY]; exact hsl) hin₂ h₂
    (by rw [hsY]; exact hra') ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ V' hF' hKZ hAZ hrZ ⟨cc, hcc, c', s', i, u, v, x, y, by rw [hgZ, hsY, hgY]⟩

end FV7z.U8w
