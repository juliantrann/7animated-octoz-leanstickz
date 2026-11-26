import FV7z.Cpp.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Env
/-!
# `Correct_PathPart (UString &s)` (PLAN.md §M, M1)

7-Zip 26.06's `Correct_PathPart (s)` at `0x5c6ee0` in `7zzs` (`CPP/7zip/UI/Common/ExtractingFilePath.cpp`;
`objdump -d`).
`rdi` is the `UString`: its characters' pointer at `[rdi]` (`s` here), its length (32 bits) at `[rdi + 8]`; a character
is a `wchar_t` (4 bytes). The code empties "." and ".." (the length and the first character 0, `ret` at 30); else,
the length not 0, makes each '/' '_' (the loop from 66, `rcx` at the character, `rdi` at the end) and then, when the
byte at `0x79eda0` is not 0, the trailing '.'s and ' 's '_' from the last character down (the loop from 130, `rax` at
the character, `rdx` at the first). The `ret`s are at 30, 101 and 142.

- `Sl V s k`: the first `k` characters with '/' made '_'; `Tr s i W`: from the `i`-th character down, while '.' or ' ',
  made '_' (read from `W` as it is then); `Res`: what the function leaves; `res_out`: the bytes it keeps.
- `vc_*`: the verification conditions of the pieces; `step66`, `loop1`: the first loop; `step130`, `loop2`: the second.
- `cpp_ok`: from the entry to the return address, the bytes `Res`, the registers a call keeps (`Str.Back`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Cpp

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_30 : pret <+: cpp.drop 30 := by decide +kernel
theorem w_101 : pret <+: cpp.drop 101 := by decide +kernel
theorem w_142 : pret <+: cpp.drop 142 := by decide +kernel
theorem ret_30 (feat : Features) : Dec feat cpp 30 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 30) (k := 0) (pret_0 feat) w_30 (Nat.zero_le _)
theorem ret_101 (feat : Features) : Dec feat cpp 101 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 101) (k := 0) (pret_0 feat) w_101 (Nat.zero_le _)
theorem ret_142 (feat : Features) : Dec feat cpp 142 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 142) (k := 0) (pret_0 feat) w_142 (Nat.zero_le _)

/-! ## What the function does -/

/-- The `i`-th character of the string at `s`. -/
abbrev el (V : Addr → Byte) (s : Addr) (i : Nat) : BitVec 32 := rdd(V, s.add (4 * i))
/-- '_', as stored. -/
abbrev u95 : List Byte := toBytesLE 95#32 4
/-- The byte at `0x79eda0` (Windows-style names). -/
abbrev flg (V : Addr → Byte) : BitVec 8 := ofBytesLE 8 ((byteAddrs 7990688#64 1).map V)

/-- The first `k` characters at `s` with each '/' made '_', one by one as the code stores them. -/
def Sl (V : Addr → Byte) (s : Addr) : Nat → Addr → Byte
  | 0 => V
  | k + 1 => if el V s k = 47#32 then Vst (Sl V s k) (s.add (4 * k)) u95 else Sl V s k

/-- From the `i`-th character at `s` down: while it is '.' or ' ' (in `W` as it is then), made '_'. -/
def Tr (s : Addr) : Nat → (Addr → Byte) → Addr → Byte
  | 0, W => if el W s 0 = 46#32 ∨ el W s 0 = 32#32 then Vst W (s.add (4 * 0)) u95 else W
  | i + 1, W => if el W s (i + 1) = 46#32 ∨ el W s (i + 1) = 32#32 then
      Tr s i (Vst W (s.add (4 * (i + 1))) u95) else W

/-- "." or "..". -/
abbrev Dot (V : Addr → Byte) (s : Addr) : Prop :=
  el V s 0 = 46#32 ∧ (el V s 1 = 0#32 ∨ el V s 1 = 46#32 ∧ el V s 2 = 0#32)

/-- The bytes after `Correct_PathPart`, the `UString` at `p`, its characters at `s`, its length `n`. -/
def Res (V : Addr → Byte) (p s : Addr) (n : Nat) : Addr → Byte :=
  if Dot V s then Vst (Vst V (p + 8#64) (toBytesLE 0#32 4)) s (toBytesLE 0#32 4)
  else if n = 0 then V
  else if flg V = 0#8 then Sl V s n
  else Tr s (n - 1) (Sl V s n)

/-- The registers the first loop keeps, as at `g₀`. -/
def K1 (g₀ g : Gprs) : Prop := g.rax = g₀.rax ∧ g.rdx = g₀.rdx ∧ g.rdi = g₀.rdi ∧ Kp g₀ g

theorem Sl_succ (V : Addr → Byte) (s : Addr) (k : Nat) :
    Sl V s (k + 1) = if el V s k = 47#32 then Vst (Sl V s k) (s.add (4 * k)) u95 else Sl V s k := rfl
theorem Tr_zero (s : Addr) (W : Addr → Byte) :
    Tr s 0 W = if el W s 0 = 46#32 ∨ el W s 0 = 32#32 then Vst W (s.add (4 * 0)) u95 else W := rfl
theorem Tr_succ (s : Addr) (i : Nat) (W : Addr → Byte) :
    Tr s (i + 1) W = if el W s (i + 1) = 46#32 ∨ el W s (i + 1) = 32#32 then
      Tr s i (Vst W (s.add (4 * (i + 1))) u95) else W := rfl

/-- A byte not of the first `k` characters: as it was. -/
theorem Sl_out (V : Addr → Byte) (s : Addr) :
    ∀ (k : Nat) (x : Addr), (∀ i < k, ∀ b < 4, x ≠ (s.add (4 * i)).add b) → Sl V s k x = V x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    have h4 : u95.length = 4 := toBytesLE_length _ _
    rw [Sl_succ]
    by_cases hc : el V s k = 47#32
    · rw [if_pos hc, Vst_apart u95 _ (s.add (4 * k)) x fun b hb => h k (by omega) b (by omega)]
      exact Sl_out V s k x fun i hi => h i (by omega)
    · rw [if_neg hc]
      exact Sl_out V s k x fun i hi => h i (by omega)

/-- A byte not of the characters from the `i`-th down: as it was. -/
theorem Tr_out (s : Addr) :
    ∀ (i : Nat) (W : Addr → Byte) (x : Addr), (∀ j, j ≤ i → ∀ b < 4, x ≠ (s.add (4 * j)).add b) → Tr s i W x = W x
  | 0, W, x, h => by
    have h4 : u95.length = 4 := toBytesLE_length _ _
    rw [Tr_zero]
    by_cases hc : el W s 0 = 46#32 ∨ el W s 0 = 32#32
    · rw [if_pos hc]
      exact Vst_apart u95 W (s.add (4 * 0)) x fun b hb => h 0 (Nat.le_refl _) b (by omega)
    · rw [if_neg hc]
  | i + 1, W, x, h => by
    have h4 : u95.length = 4 := toBytesLE_length _ _
    rw [Tr_succ]
    by_cases hc : el W s (i + 1) = 46#32 ∨ el W s (i + 1) = 32#32
    · rw [if_pos hc, Tr_out s i _ x fun j hj => h j (by omega)]
      exact Vst_apart u95 W (s.add (4 * (i + 1))) x fun b hb => h (i + 1) (Nat.le_refl _) b (by omega)
    · rw [if_neg hc]

/-- Bytes apart from the first `k` characters: as they were. -/
theorem Sl_far (V : Addr → Byte) (s : Addr) {k : Nat} {a : Addr} {m : Nat}
    (h : ∀ b' < m, ∀ i < k, ∀ b < 4, a.add b' ≠ (s.add (4 * i)).add b) :
    (byteAddrs a m).map (Sl V s k) = (byteAddrs a m).map V :=
  List.map_congr_left fun y hy => by
    obtain ⟨b', hb', rfl⟩ := mem_byteAddrs.1 hy
    exact Sl_out V s k _ fun i hi b hb => h b' hb' i hi b hb

/-- The `j`-th character while the first `k ≤ j` are being done: as it was. -/
theorem Sl_self (V : Addr → Byte) (s : Addr) {k j : Nat} (hk : k ≤ j) (hj : 4 * j + 4 ≤ 2 ^ 64) :
    el (Sl V s k) s j = el V s j := by
  have h : ∀ b' < 4, ∀ i < k, ∀ b < 4, (s.add (4 * j)).add b' ≠ (s.add (4 * i)).add b := fun b' hb' i hi b hb e => by
    rw [addr_add_add, addr_add_add] at e
    exact add_ne' s (by omega) (by omega) (by omega) e
  exact congrArg (ofBytesLE 32) (Sl_far V s h)

theorem res_dot {V : Addr → Byte} {p s : Addr} {n : Nat} (h : Dot V s) :
    Res V p s n = Vst (Vst V (p + 8#64) (toBytesLE 0#32 4)) s (toBytesLE 0#32 4) := by
  unfold Res
  rw [if_pos h]

theorem res_empty {V : Addr → Byte} {p s : Addr} (h : ¬Dot V s) : Res V p s 0 = V := by
  unfold Res
  rw [if_neg h, if_pos rfl]

theorem res_flag0 {V : Addr → Byte} {p s : Addr} {n : Nat} (h : ¬Dot V s) (hn : n ≠ 0) (hf : flg V = 0#8) :
    Res V p s n = Sl V s n := by
  unfold Res
  rw [if_neg h, if_neg hn, if_pos hf]

theorem res_tail {V : Addr → Byte} {p s : Addr} {n : Nat} (h : ¬Dot V s) (hn : n ≠ 0) (hf : flg V ≠ 0#8) :
    Res V p s n = Tr s (n - 1) (Sl V s n) := by
  unfold Res
  rw [if_neg h, if_neg hn, if_neg hf]

/-- A byte not of the `n` characters, of the length or of the first character: as it was. -/
theorem res_out (V : Addr → Byte) (p s : Addr) (n : Nat) (x : Addr)
    (hx : ∀ i < n, ∀ b < 4, x ≠ (s.add (4 * i)).add b) (hp : ∀ b < 4, x ≠ (p + 8#64).add b)
    (hs : ∀ b < 4, x ≠ s.add b) : Res V p s n x = V x := by
  have h4 : (toBytesLE 0#32 4).length = 4 := toBytesLE_length _ _
  unfold Res
  by_cases hD : Dot V s
  · rw [if_pos hD, Vst_apart (toBytesLE 0#32 4) _ s x fun b hb => hs b (by omega)]
    exact Vst_apart (toBytesLE 0#32 4) V (p + 8#64) x fun b hb => hp b (by omega)
  · rw [if_neg hD]
    by_cases hn : n = 0
    · rw [if_pos hn]
    · rw [if_neg hn]
      by_cases hf : flg V = 0#8
      · rw [if_pos hf]
        exact Sl_out V s n x hx
      · rw [if_neg hf, Tr_out s (n - 1) _ x fun j hj => hx j (by omega)]
        exact Sl_out V s n x hx

theorem res_rd (V : Addr → Byte) (p s : Addr) (n : Nat) {a : Addr} {m : Nat}
    (hx : ∀ b' < m, ∀ i < n, ∀ b < 4, a.add b' ≠ (s.add (4 * i)).add b)
    (hd : ∀ b' < m, ∀ b < 4, a.add b' ≠ (p + 8#64).add b ∧ a.add b' ≠ s.add b) :
    (byteAddrs a m).map (Res V p s n) = (byteAddrs a m).map V :=
  List.map_congr_left fun y hy => by
    obtain ⟨b', hb', rfl⟩ := mem_byteAddrs.1 hy
    exact res_out V p s n _ (hx b' hb') (fun b hb => (hd b' hb' b hb).1) fun b hb => (hd b' hb' b hb).2

/-! ## Pointers -/

/-- `rax` at 66: `(len - 1) << 2`, `sub eax, 1; shl rax, 2`. -/
abbrev lstC (c : BitVec 32) : BitVec 64 := BitVec.setWidth 64 (c - 1#32) <<< 2
/-- `rdi` at 66: `lea rdi, [rdx + rax + 4]`. -/
abbrev endC (p : Addr) (c : BitVec 32) : Addr := p + lstC c + 4#64

theorem lst_eq (c : BitVec 32) (hc : c.toNat ≠ 0) : lstC c = BitVec.ofNat 64 (4 * (c.toNat - 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h2 := c.isLt
  simp only [lstC, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at h2 ⊢
  omega

theorem endC_eq (p : Addr) (c : BitVec 32) (hc : c.toNat ≠ 0) : endC p c = p.add (4 * c.toNat) := by
  show p + lstC c + BitVec.ofNat 64 4 = _
  rw [lst_eq c hc, ptr_step, show 4 * (c.toNat - 1) + 4 = 4 * c.toNat by omega]
  all_goals exact ptr_add _ _

theorem lst_add (s : Addr) (c : BitVec 32) (hc : c.toNat ≠ 0) : lstC c + s = s.add (4 * (c.toNat - 1)) := by
  rw [lst_eq c hc, BitVec.add_comm]
  all_goals exact ptr_add _ _

theorem p4 (s : Addr) (j : Nat) : s.add (4 * j) + 4#64 = s.add (4 * (j + 1)) := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega]
  exact ptr_step s (4 * j) 4

theorem m4s (s : Addr) (i : Nat) : s.add (4 * (i + 1)) + 18446744073709551612#64 = s.add (4 * i) := by
  rw [← p4, BitVec.add_assoc, show (4#64 : BitVec 64) + 18446744073709551612#64 = 0#64 by decide, BitVec.add_zero]

/-- Closes what `wpx` leaves: equalities by `rfl`, footprints from the hypotheses. -/
macro "cpx" : tactic => `(tactic| (
  all_goals repeat'
    (first
      | exact rfl
      | exact trivial
      | assumption
      | apply And.intro
      | intro _)))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- At 17 or 37 from the entry: `rdx` the characters, `rsi` the first as loaded. -/
abbrev Q0 (V : Addr → Byte) (g : Gprs) (s : Addr) (N : Nat) : Nat → Gprs → Rflags → (Addr → Byte) → Prop :=
  fun j' g' _ V' => j' = N ∧ g'.rdx = s ∧ g'.rsi = BitVec.setWidth 64 rdd(V, s) ∧ g'.rdi = g.rdi ∧ Kp g g' ∧ V' = V

/-- The first character not '.': to 37. -/
theorem vc_0a {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rdi) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (f0 : ∀ i < 4, Foot F.data (Addr.add s i))
    (h0 : rdd(V, s) ≠ 46#32) : W_0 F Wl (Q0 V g s 37) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fp ⊢
  have h0' : decide (rdd(V, s) = 46#32) = false := decide_eq_false h0
  wpx [W_0, W_10, W_32, W_144, W_151, o0, o1, o3, o15, Q0, Kp, hs, h0', BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  cpx

/-- "." : to 17. -/
theorem vc_0b {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rdi) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (f0 : ∀ i < 4, Foot F.data (Addr.add s i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (s + 4#64) i))
    (h0 : rdd(V, s) = 46#32) (h1 : rdd(V, s + 4#64) = 0#32) : W_0 F Wl (Q0 V g s 17) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fp ⊢
  have h0' : decide (rdd(V, s) = 46#32) = true := decide_eq_true h0
  have h1' : (rdd(V, s + 4#64) == 0) = true := by rw [h1]; rfl
  wpx [W_0, W_10, W_32, W_144, W_151, o0, o1, o3, o15, Q0, Kp, hs, h0', h1', BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  cpx

/-- '.' and then neither 0 nor '.': to 37. -/
theorem vc_0c {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rdi) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (f0 : ∀ i < 4, Foot F.data (Addr.add s i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (s + 4#64) i))
    (h0 : rdd(V, s) = 46#32) (h1 : rdd(V, s + 4#64) ≠ 0#32) (h1d : rdd(V, s + 4#64) ≠ 46#32) :
    W_0 F Wl (Q0 V g s 37) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fp ⊢
  have h0' : decide (rdd(V, s) = 46#32) = true := decide_eq_true h0
  have h1' : (rdd(V, s + 4#64) == 0) = false := beq_eq_false_iff_ne.2 h1
  have h1d' : decide (rdd(V, s + 4#64) = 46#32) = false := decide_eq_false h1d
  wpx [W_0, W_10, W_32, W_144, W_151, o0, o1, o3, o15, Q0, Kp, hs, h0', h1', h1d', BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  cpx

/-- "..": to 17. -/
theorem vc_0d {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rdi) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (f0 : ∀ i < 4, Foot F.data (Addr.add s i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (s + 4#64) i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (s + 8#64) i))
    (h0 : rdd(V, s) = 46#32) (h1 : rdd(V, s + 4#64) = 46#32) (h2 : rdd(V, s + 8#64) = 0#32) :
    W_0 F Wl (Q0 V g s 17) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fp ⊢
  have h0' : decide (rdd(V, s) = 46#32) = true := decide_eq_true h0
  have h1' : (rdd(V, s + 4#64) == 0) = false := by rw [h1]; rfl
  have h1d' : decide (rdd(V, s + 4#64) = 46#32) = true := decide_eq_true h1
  have h2' : (rdd(V, s + 8#64) == 0) = true := by rw [h2]; rfl
  wpx [W_0, W_10, W_32, W_144, W_151, o0, o1, o3, o15, Q0, Kp, hs, h0', h1', h1d', h2', BitVec.and_self,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  cpx

/-- ".." and then not 0: to 37. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rdi) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (f0 : ∀ i < 4, Foot F.data (Addr.add s i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (s + 4#64) i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (s + 8#64) i))
    (h0 : rdd(V, s) = 46#32) (h1 : rdd(V, s + 4#64) = 46#32) (h2 : rdd(V, s + 8#64) ≠ 0#32) :
    W_0 F Wl (Q0 V g s 37) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fp ⊢
  have h0' : decide (rdd(V, s) = 46#32) = true := decide_eq_true h0
  have h1' : (rdd(V, s + 4#64) == 0) = false := by rw [h1]; rfl
  have h1d' : decide (rdd(V, s + 4#64) = 46#32) = true := decide_eq_true h1
  have h2' : (rdd(V, s + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h2
  wpx [W_0, W_10, W_32, W_144, W_151, o0, o1, o3, o15, Q0, Kp, hs, h0', h1', h1d', h2', BitVec.and_self,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  cpx

/-- "." or "..": the length and the first character 0, to the `ret` (30). -/
theorem vc_17 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hw8 : ∀ i < 4, Foot Wl (Addr.add (g.rdi + 8#64) i))
    (hw0 : ∀ i < 4, Foot Wl (Addr.add g.rdx i)) :
    W_17 F Wl (fun j' g' _ V' => j' = 30 ∧ g' = g ∧
      V' = Vst (Vst V (g.rdi + 8#64) (toBytesLE 0#32 4)) g.rdx (toBytesLE 0#32 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw8 hw0 ⊢
  wpx [W_17, o2, eq_self_iff_true, and_self]
  cpx

/-- The length 0: to the `ret` (101). -/
theorem vc_37z {g : Gprs} {f : Rflags} {V : Addr → Byte} (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (h0 : rdd(V, g.rdi + 8#64) = 0#32) :
    W_37 F Wl (fun j' g' _ V' => j' = 101 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fl h0 ⊢
  have hz : (rdd(V, rdi + 8#64) == 0) = true := by rw [h0]; rfl
  wpx [W_37, W_44, o4, o5, Op.shl64, Kp, hz, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- The length not 0: `rcx` the first character, `rdi` the end, `rax` `(len - 1) << 2`, to 66. -/
theorem vc_37n {g : Gprs} {f : Rflags} {V : Addr → Byte} (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (h0 : rdd(V, g.rdi + 8#64) ≠ 0#32) :
    W_37 F Wl (fun j' g' _ V' => j' = 66 ∧ g'.rax = lstC rdd(V, g.rdi + 8#64) ∧ g'.rcx = g.rdx ∧
      g'.rdx = g.rdx ∧ g'.rsi = g.rsi ∧ g'.rdi = endC g.rdx rdd(V, g.rdi + 8#64) ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [lstC, endC] at fl h0 ⊢
  have hz : (rdd(V, rdi + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_37, W_44, o4, o5, Op.shl64, Kp, hz, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- A '/': made '_', to 77. -/
theorem vc_66s {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : BitVec.setWidth 32 g.rsi = 47#32)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rcx i)) :
    W_66 F Wl (fun j' g' _ V' => j' = 77 ∧ g' = g ∧ V' = Vst V g.rcx u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc hw ⊢
  have hc' : decide (BitVec.setWidth 32 rsi = 47#32) = true := decide_eq_true hc
  wpx [W_66, W_71, o7, o8, hc', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- Not a '/': to 77. -/
theorem vc_66n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : BitVec.setWidth 32 g.rsi ≠ 47#32) :
    W_66 F Wl (fun j' g' _ V' => j' = 77 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc ⊢
  have hc' : decide (BitVec.setWidth 32 rsi = 47#32) = false := decide_eq_false hc
  wpx [W_66, W_71, o7, o8, hc', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- Not the end: the next character in `rsi`, back to 66. -/
theorem vc_77c {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rcx + 4#64 ≠ g.rdi)
    (hf : ∀ i < 4, Foot F.data (Addr.add (g.rcx + 4#64) i)) :
    W_77 F Wl (fun j' g' _ V' => j' = 66 ∧
      g' = { g with rcx := g.rcx + 4#64, rsi := BitVec.setWidth 64 rdd(V, g.rcx + 4#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hf ⊢
  have he' : decide (rcx + 4#64 = rdi) = false := decide_eq_false he
  wpx [W_77, W_64, W_86, o9, o6, o10, Op.cmpmi, he', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- The end, the byte at `0x79eda0` 0: to the `ret` (101). -/
theorem vc_77z {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rcx + 4#64 = g.rdi) (hz : flg V = 0#8)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 7990688#64 i)) :
    W_77 F Wl (fun j' g' _ V' => j' = 101 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [flg] at he hz ⊢
  have he' : decide (rcx + 4#64 = rdi) = true := decide_eq_true he
  have hz' : decide (ofBytesLE 8 ((byteAddrs 7990688#64 1).map V) = 0#8) = true := decide_eq_true hz
  wpx [W_77, W_64, W_86, o9, o6, o10, Op.cmpmi, Kp, he', hz', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- The end, the byte at `0x79eda0` not 0: `rax` the last character, to 130. -/
theorem vc_77f {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rcx + 4#64 = g.rdi) (hz : flg V ≠ 0#8)
    (hfl : ∀ i < 1, Foot F.data (Addr.add 7990688#64 i)) :
    W_77 F Wl (fun j' g' _ V' => j' = 130 ∧ g'.rax = g.rax + g.rdx ∧ g'.rdx = g.rdx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [flg] at he hz ⊢
  have he' : decide (rcx + 4#64 = rdi) = true := decide_eq_true he
  have hz' : decide (ofBytesLE 8 ((byteAddrs 7990688#64 1).map V) = 0#8) = false := decide_eq_false hz
  wpx [W_77, W_64, W_86, o9, o6, o10, Op.cmpmi, Kp, he', hz', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- From 130: '.' or ' ', to 112. -/
theorem vc_130d {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rax) = 46#32 ∨ rdd(V, g.rax) = 32#32)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) :
    W_130 F Wl (fun j' g' _ V' => j' = 112 ∧ g' = { g with rcx := BitVec.setWidth 64 rdd(V, g.rax) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf ⊢
  have hb : decide (rdd(V, rax) = 46#32) = true ∨
      (decide (rdd(V, rax) = 46#32) = false ∧ decide (rdd(V, rax) = 32#32) = true) := by
    rcases h with h | h <;> rw [h] <;> decide
  rcases hb with h1 | ⟨h1, h2⟩
  · wpx [W_130, W_137, o13, o14, h1, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
      false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
    cpx
  · wpx [W_130, W_137, o13, o14, h1, h2, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
      false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
    cpx

/-- From 130: neither '.' nor ' ', to the `ret` (142). -/
theorem vc_130r {g : Gprs} {f : Rflags} {V : Addr → Byte} (h1 : rdd(V, g.rax) ≠ 46#32) (h2 : rdd(V, g.rax) ≠ 32#32)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) :
    W_130 F Wl (fun j' g' _ V' => j' = 142 ∧ g' = { g with rcx := BitVec.setWidth 64 rdd(V, g.rax) } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 hf ⊢
  have h1' : decide (rdd(V, rax) = 46#32) = false := decide_eq_false h1
  have h2' : decide (rdd(V, rax) = 32#32) = false := decide_eq_false h2
  wpx [W_130, W_137, o13, o14, h1', h2', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- From 112 at the first character: made '_', to the `ret` (101). -/
theorem vc_112e {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rdx = g.rax)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_112 F Wl (fun j' g' _ V' => j' = 101 ∧ Kp g g' ∧ V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hw ⊢
  have he' : decide (rdx = rax) = true := decide_eq_true he
  wpx [W_112, W_127, o11, o12, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-- From 112 after the first character: made '_', `rax` one down, to 130. -/
theorem vc_112n {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rdx ≠ g.rax)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_112 F Wl (fun j' g' _ V' => j' = 130 ∧
      g' = { g with rax := g.rax + 18446744073709551612#64, rcx := g.rax + 18446744073709551612#64 } ∧
      V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hw ⊢
  have he' : decide (rdx = rax) = false := decide_eq_false he
  wpx [W_112, W_127, o11, o12, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  cpx

/-! ## The loops -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 66 at the `j`-th character (`rcx`), in `rsi` as it was: to 77 with it done, the registers as they were. -/
theorem step66 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpp_at cpp) {V : Addr → Byte} {s : Addr} {n j : Nat}
    (hj : j < n) (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b)) {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem (Sl V s j)) (hrip : X.cpu.rip = cpp_at.add 66)
    (hrc : X.cpu.gpr.rcx = s.add (4 * j)) (hsi : BitVec.setWidth 32 X.cpu.gpr.rsi = el V s j)
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Sl V s (j + 1)) →
      Y.cpu.rip = cpp_at.add 77 → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  by_cases hsl : el V s j = 47#32
  · have hw1 : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rcx i) := fun i hi => by
      rw [hrc]
      exact hw j hj i hi
    refine (c_66 prof).run c hin _ hK hA hrip (vc_66s (hsi.trans hsl) hw1) ?_
    rintro j' g fl V' ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine k Y t₁ hKY ?_ hrY hgY
    rw [Sl_succ, if_pos hsl, ← hrc]
    exact hAY
  · refine (c_66 prof).run c hin _ hK hA hrip (vc_66n fun h => hsl (hsi.symm.trans h)) ?_
    rintro j' g fl V' ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine k Y t₁ hKY ?_ hrY hgY
    rw [Sl_succ, if_neg hsl]
    exact hAY

/-- The first loop from 66 at the `j`-th of the `n` characters at `s`, the first `j` done: on to 77 at the last with
all `n` done (`Sl V s n`), the registers of `K1` as at `g₀`. By induction on the characters left. -/
theorem loop1 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpp_at cpp) {V : Addr → Byte} {s : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 61) (hd : g₀.rdi = s.add (4 * n))
    (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Sl V s n) → Z.cpu.rip = cpp_at.add 77 →
      Z.cpu.gpr.rcx + 4#64 = g₀.rdi → K1 g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m + 1 = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem (Sl V s j) →
      X.cpu.rip = cpp_at.add 66 → X.cpu.gpr.rcx = s.add (4 * j) → BitVec.setWidth 32 X.cpu.gpr.rsi = el V s j →
      K1 g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hrc hsi hk
    refine step66 c hin (by omega) hw hK hA hrip hrc hsi ?_
    intro Y t₁ hKY hAY hrY hgY
    have hjn : j + 1 = n := by omega
    rw [hjn] at hAY
    refine k Y t₁ hKY hAY hrY ?_ (by rw [hgY]; exact hk)
    rw [hgY, hrc, p4, hjn, hd]
  | succ m ih =>
    intro j hj X t hK hA hrip hrc hsi hk
    refine step66 c hin (by omega) hw hK hA hrip hrc hsi ?_
    intro Y t₁ hKY hAY hrY hgY
    have hkY : K1 g₀ Y.cpu.gpr := by rw [hgY]; exact hk
    have hrcY : Y.cpu.gpr.rcx + 4#64 = s.add (4 * (j + 1)) := by rw [hgY, hrc, p4]
    have hdY : Y.cpu.gpr.rdi = s.add (4 * n) := hkY.2.2.1.trans hd
    have he : Y.cpu.gpr.rcx + 4#64 ≠ Y.cpu.gpr.rdi := by
      rw [hrcY, hdY]
      exact add_ne' s (by omega) (by omega) (by omega)
    have hf1 : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rcx + 4#64) i) := fun i hi => by
      rw [hrcY]
      exact hf (j + 1) (by omega) i hi
    refine (c_77 prof).run c hin _ hKY hAY hrY (vc_77c he hf1) ?_
    rintro j' g fl V' ⟨rfl, rfl, hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
    subst V'
    refine ih (j + 1) (by omega) Z t₂ hKZ hAZ hrZ ?_ ?_ ?_
    · rw [hgZ]
      all_goals exact hrcY
    · rw [hgZ]
      show BitVec.setWidth 32 (BitVec.setWidth 64 rdd(Sl V s (j + 1), Y.cpu.gpr.rcx + 4#64)) = _
      rw [sw32, hrcY]
      exact Sl_self V s (Nat.le_refl _) (by omega)
    · rw [hgZ]
      all_goals exact hkY

/-- From 130 at the `i`-th character (`rax`): '.' or ' ' to 112, the registers as they were but `rcx`; else to the
`ret` at 142. -/
theorem step130 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpp_at cpp) {W : Addr → Byte} {s : Addr} {i : Nat}
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hrip : X.cpu.rip = cpp_at.add 130)
    (hra : X.cpu.gpr.rax = s.add (4 * i)) (hf : ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (kd : (el W s i = 46#32 ∨ el W s i = 32#32) → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem W → Y.cpu.rip = cpp_at.add 112 → Y.cpu.gpr.rax = X.cpu.gpr.rax →
      Y.cpu.gpr.rdx = X.cpu.gpr.rdx → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kr : ¬(el W s i = 46#32 ∨ el W s i = 32#32) → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem W → Y.cpu.rip = cpp_at.add 142 → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hb : rdd(W, X.cpu.gpr.rax) = el W s i := by
    show rdd(W, X.cpu.gpr.rax) = rdd(W, s.add (4 * i))
    rw [hra]
  have hf1 : ∀ b < 4, Foot F.data (Addr.add X.cpu.gpr.rax b) := fun b hb' => by
    rw [hra]
    exact hf b hb'
  by_cases hc : el W s i = 46#32 ∨ el W s i = 32#32
  · refine (c_130 prof).run c hin _ hK hA hrip (vc_130d (by rw [hb]; exact hc) hf1) ?_
    rintro j' g fl V' ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    exact kd hc Y t₁ hKY hAY hrY (by rw [hgY]; all_goals rfl) (by rw [hgY]; all_goals rfl) (kp_w hgY)
  · refine (c_130 prof).run c hin _ hK hA hrip
      (vc_130r (by rw [hb]; exact fun h => hc (Or.inl h)) (by rw [hb]; exact fun h => hc (Or.inr h)) hf1) ?_
    rintro j' g fl V' ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    exact kr hc Y t₁ hKY hAY hrY (kp_w hgY)

/-- The second loop from 130 at the `i`-th character (`rax`), `rdx` the first, the bytes `W` with `Tr s i W = R`: on
to a `ret` (101 or 142) with the bytes `R`, the registers a call keeps as at `g₀`. By induction on `i`. -/
theorem loop2 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpp_at cpp) {s : Addr} {R : Addr → Byte} {g₀ : Gprs}
    {N : Nat} (hN : N < 2 ^ 61) (hf : ∀ i, i ≤ N → ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i, i ≤ N → ∀ b < 4, Foot Wl ((s.add (4 * i)).add b))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem R →
      (Z.cpu.rip = cpp_at.add 101 ∨ Z.cpu.rip = cpp_at.add 142) → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (i : Nat), i ≤ N → ∀ (W : Addr → Byte) (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = cpp_at.add 130 → X.cpu.gpr.rax = s.add (4 * i) → X.cpu.gpr.rdx = s → Kp g₀ X.cpu.gpr →
      Tr s i W = R → GoG prof L o gev gP gE X t := by
  intro i
  induction i with
  | zero =>
    intro hi W X t hK hA hrip hra hdx hkp hT
    refine step130 c hin hK hA hrip hra (hf 0 hi) ?_ ?_
    · intro hc Y t₁ hKY hAY hrY hYa hYd hkY
      have hYa' : Y.cpu.gpr.rax = s.add (4 * 0) := hYa.trans hra
      have he : Y.cpu.gpr.rdx = Y.cpu.gpr.rax := by
        rw [hYd, hdx, hYa', Nat.mul_zero, addr_add_zero]
      have hw1 : ∀ b < 4, Foot Wl (Addr.add Y.cpu.gpr.rax b) := fun b hb => by
        rw [hYa']
        exact hw 0 hi b hb
      refine (c_112 prof).run c hin _ hKY hAY hrY (vc_112e he hw1) ?_
      rintro j' g fl V' ⟨rfl, hkp', hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
      subst V'
      refine k Z t₂ hKZ ?_ (Or.inl hrZ) (hkp.trans (hkY.trans (Kp.of_eq hgZ hkp')))
      rw [← hT, Tr_zero, if_pos hc, ← hYa']
      exact hAZ
    · intro hc Y t₁ hKY hAY hrY hkY
      refine k Y t₁ hKY ?_ (Or.inr hrY) (hkp.trans hkY)
      rw [← hT, Tr_zero, if_neg hc]
      exact hAY
  | succ i ih =>
    intro hi W X t hK hA hrip hra hdx hkp hT
    refine step130 c hin hK hA hrip hra (hf (i + 1) hi) ?_ ?_
    · intro hc Y t₁ hKY hAY hrY hYa hYd hkY
      have hYa' : Y.cpu.gpr.rax = s.add (4 * (i + 1)) := hYa.trans hra
      have he : Y.cpu.gpr.rdx ≠ Y.cpu.gpr.rax := by
        rw [hYd, hdx, hYa']
        have h := add_ne' s (i := 0) (j := 4 * (i + 1)) (by omega) (by omega) (by omega)
        rw [addr_add_zero] at h
        exact h
      have hw1 : ∀ b < 4, Foot Wl (Addr.add Y.cpu.gpr.rax b) := fun b hb => by
        rw [hYa']
        exact hw (i + 1) hi b hb
      refine (c_112 prof).run c hin _ hKY hAY hrY (vc_112n he hw1) ?_
      rintro j' g fl V' ⟨rfl, rfl, hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
      subst V'
      rw [hYa'] at hAZ
      refine ih (by omega) _ Z t₂ hKZ hAZ hrZ ?_ ?_ (hkp.trans (hkY.trans (kp_w hgZ))) ?_
      · rw [hgZ]
        show Y.cpu.gpr.rax + 18446744073709551612#64 = _
        rw [hYa', m4s]
      · rw [hgZ]
        show Y.cpu.gpr.rdx = _
        rw [hYd, hdx]
      · rw [← hT, Tr_succ, if_pos hc]
    · intro hc Y t₁ hKY hAY hrY hkY
      refine k Y t₁ hKY ?_ (Or.inr hrY) (hkp.trans hkY)
      rw [← hT, Tr_succ, if_neg hc]
      exact hAY

/-! ## The function -/

/-- `Correct_PathPart (s)` from its entry: `rdi` the `UString`, its characters at `s` (`hs`), its length `n`
(`hn`, `n < 2 ^ 61`) and the `n`-th character 0 (`hz`), their bytes and the byte at `0x79eda0` data of the
footprint, those of the `n` characters and of the length writable, apart from the return address: at the return
address with the bytes `Res`, the registers a call keeps (`Str.Back`). -/
theorem cpp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpp_at cpp) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = cpp_at) {s : Addr} {n : Nat}
    (hs : rdq(V, X.cpu.gpr.rdi) = s) (hn : (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat = n) (hn61 : n < 2 ^ 61)
    (hz : el V s n = 0#32)
    (hp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hpl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hpw : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hf : ∀ i, i ≤ n → ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b))
    (hfl : ∀ i < 1, Foot F.data (Addr.add 7990688#64 i))
    (hsf : ∀ b' < 1, ∀ i < n, ∀ b < 4, Addr.add 7990688#64 b' ≠ (s.add (4 * i)).add b)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hsr : ∀ b' < 8, ∀ i < n, ∀ b < 4, Addr.add X.cpu.gpr.rsp b' ≠ (s.add (4 * i)).add b)
    (hsd : ∀ b' < 8, ∀ b < 4, Addr.add X.cpu.gpr.rsp b' ≠ (X.cpu.gpr.rdi + 8#64).add b ∧
      Addr.add X.cpu.gpr.rsp b' ≠ s.add b)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Res V X.cpu.gpr.rdi s n) →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hra' : rdq(Res V X.cpu.gpr.rdi s n, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [res_rd V _ _ _ hsr hsd]
    exact hra
  have kr : ∀ jr, jr < 156 → (∀ feat, Dec feat cpp jr (FV7z.mk .ret 64 [] 1)) → ∀ (Z : State) (t' : Nat),
      KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Res V X.cpu.gpr.rdi s n) → Z.cpu.rip = cpp_at.add jr →
      Kp X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t' :=
    fun jr hj hd Z t' hKZ hAZ hrZ hkp =>
      ret_back c hin (lt_len hj) (hd _) hKZ hAZ hrZ hkp hl hin₂ h₂ hra'
        fun Z' t'' hK' hA' hr' hb _ => k Z' t'' hK' hA' hr' hb
  have f0 : ∀ i < 4, Foot F.data (Addr.add s i) := fun b hb => by
    have h := hf 0 (Nat.zero_le _) b hb
    rw [Nat.mul_zero, addr_add_zero] at h
    exact h
  have e0 : el V s 0 = rdd(V, s) := by
    show rdd(V, s.add (4 * 0)) = _
    rw [Nat.mul_zero, addr_add_zero]
  -- "." or "..": both 0
  have k17 : Dot V s → ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = cpp_at.add 17 → Y.cpu.gpr.rdx = s → Y.cpu.gpr.rdi = X.cpu.gpr.rdi → Kp X.cpu.gpr Y.cpu.gpr →
      GoG prof L o gev gP gE Y t₁ := by
    intro hD Y t₁ hKY hAY hrY hYd hYi hkp
    have hn1 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exact absurd (hD.1.symm.trans hz) (by decide)
      · exact h
    have hw8 : ∀ i < 4, Foot Wl (Addr.add (Y.cpu.gpr.rdi + 8#64) i) := fun i hi => by
      rw [hYi]
      exact hpw i hi
    have hw0 : ∀ i < 4, Foot Wl (Addr.add Y.cpu.gpr.rdx i) := fun b hb => by
      have h := hw 0 hn1 b hb
      rw [Nat.mul_zero, addr_add_zero] at h
      rw [hYd]
      exact h
    refine (c_17 prof).run c hin _ hKY hAY hrY (vc_17 hw8 hw0) ?_
    rintro j' g fl V' ⟨rfl, rfl, hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
    subst V'
    refine kr 30 (by decide) ret_30 Z t₂ hKZ ?_ hrZ (hkp.trans (Kp.of_eq hgZ (Kp.refl _)))
    rw [res_dot hD, ← hYi, ← hYd]
    exact hAZ
  -- otherwise: the length
  have k37 : ¬Dot V s → ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = cpp_at.add 37 → Y.cpu.gpr.rdx = s → Y.cpu.gpr.rsi = BitVec.setWidth 64 rdd(V, s) →
      Y.cpu.gpr.rdi = X.cpu.gpr.rdi → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t₁ := by
    intro hD Y t₁ hKY hAY hrY hYd hYs hYi hkp
    have fl : ∀ i < 4, Foot F.data (Addr.add (Y.cpu.gpr.rdi + 8#64) i) := fun i hi => by
      rw [hYi]
      exact hpl i hi
    by_cases hn0 : n = 0
    · have h0 : rdd(V, Y.cpu.gpr.rdi + 8#64) = 0#32 := by
        rw [hYi]
        exact BitVec.eq_of_toNat_eq (by rw [hn, hn0]; all_goals rfl)
      refine (c_37 prof).run c hin _ hKY hAY hrY (vc_37z fl h0) ?_
      rintro j' g fl' V' ⟨rfl, hkp', hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
      subst V'
      subst hn0
      refine kr 101 (by decide) ret_101 Z t₂ hKZ ?_ hrZ (hkp.trans (Kp.of_eq hgZ hkp'))
      rw [res_empty hD]
      exact hAZ
    have hc : (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat ≠ 0 := by rw [hn]; exact hn0
    have h0 : rdd(V, Y.cpu.gpr.rdi + 8#64) ≠ 0#32 := by
      rw [hYi]
      intro h
      exact hc (by rw [h]; all_goals rfl)
    refine (c_37 prof).run c hin _ hKY hAY hrY (vc_37n fl h0) ?_
    rintro j' g fl' V' ⟨rfl, hax, hcx, hdx, hsi, hdi, hkp', hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
    subst V'
    subst hgZ
    rw [hYi] at hax hdi
    rw [hYd] at hcx hdx hdi
    have hdZ : Z.cpu.gpr.rdi = s.add (4 * n) := by rw [hdi, endC_eq s _ hc, hn]
    have hf' : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b) := fun i hi => hf i (by omega)
    -- after the first loop
    have k77 : ∀ (W : State) (t' : Nat), KeptW Wl s₀ W → Agree F W.proc.mm.mem (Sl V s n) →
        W.cpu.rip = cpp_at.add 77 → W.cpu.gpr.rcx + 4#64 = Z.cpu.gpr.rdi → K1 Z.cpu.gpr W.cpu.gpr →
        GoG prof L o gev gP gE W t' := by
      intro W t₃ hKW hAW hrW hrc hk1
      have he : W.cpu.gpr.rcx + 4#64 = W.cpu.gpr.rdi := hrc.trans hk1.2.2.1.symm
      have hflg : flg (Sl V s n) = flg V := congrArg (ofBytesLE 8) (Sl_far V s hsf)
      have hkW : Kp X.cpu.gpr W.cpu.gpr := hkp.trans (hkp'.trans hk1.2.2.2)
      by_cases hfz : flg V = 0#8
      · refine (c_77 prof).run c hin _ hKW hAW hrW (vc_77z he (hflg.trans hfz) hfl) ?_
        rintro j' g fl'' V' ⟨rfl, hkp'', hV⟩ U t₄ hKU hAU hrU hgU -
        subst V'
        refine kr 101 (by decide) ret_101 U t₄ hKU ?_ hrU (hkW.trans (Kp.of_eq hgU hkp''))
        rw [res_flag0 hD hn0 hfz]
        exact hAU
      · refine (c_77 prof).run c hin _ hKW hAW hrW (vc_77f he (fun h => hfz (hflg.symm.trans h)) hfl) ?_
        rintro j' g fl'' V' ⟨rfl, hax', hdx', hkp'', hV⟩ U t₄ hKU hAU hrU hgU -
        subst V'
        subst hgU
        have hUa : U.cpu.gpr.rax = s.add (4 * (n - 1)) := by
          rw [hax', hk1.1, hk1.2.1, hax, hdx, lst_add s _ hc, hn]
        have hUd : U.cpu.gpr.rdx = s := by rw [hdx', hk1.2.1, hdx]
        refine loop2 c hin (N := n - 1) (R := Res V X.cpu.gpr.rdi s n) (g₀ := U.cpu.gpr) (by omega)
          (fun i hi => hf i (by omega)) (fun i hi => hw i (by omega)) ?_ (n - 1) (Nat.le_refl _) _ U t₄ hKU hAU hrU
          hUa hUd (Kp.refl _) (res_tail hD hn0 hfz).symm
        intro Z' t' hK' hA' hr' hkp₃
        rcases hr' with hr' | hr'
        · exact kr 101 (by decide) ret_101 Z' t' hK' hA' hr' (hkW.trans (hkp''.trans hkp₃))
        · exact kr 142 (by decide) ret_142 Z' t' hK' hA' hr' (hkW.trans (hkp''.trans hkp₃))
    refine loop1 c hin hn61 hdZ hf' hw k77 (n - 1) 0 (by omega) Z t₂ hKZ hAZ hrZ ?_ ?_ ⟨rfl, rfl, rfl, Kp.refl _⟩
    · rw [hcx, Nat.mul_zero, addr_add_zero]
    · rw [hsi, hYs, e0, sw32]
  -- the entry
  have hrip' : X.cpu.rip = cpp_at.add 0 := by rw [addr_add_zero]; exact hrip
  have run0 : ∀ N, W_0 F Wl (Q0 V X.cpu.gpr s N) X.cpu.gpr X.cpu.rflags V →
      (N = 17 → Dot V s) → (N = 37 → ¬Dot V s) → (N = 17 ∨ N = 37) → GoG prof L o gev gP gE X t := by
    intro N hvc hd17 hd37 hN
    refine (c_0 prof).run c hin _ hK hA hrip' hvc ?_
    rintro j' g fl V' ⟨rfl, hYd, hYs, hYi, hkp, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    subst hgY
    rcases hN with rfl | rfl
    · exact k17 (hd17 rfl) Y t₁ hKY hAY hrY hYd hYi hkp
    · exact k37 (hd37 rfl) Y t₁ hKY hAY hrY hYd hYs hYi hkp
  by_cases h0 : el V s 0 = 46#32
  · have h0' : rdd(V, s) = 46#32 := e0.symm.trans h0
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h
        exact absurd (h0.symm.trans hz) (by decide)
      · exact h
    have f4 : ∀ i < 4, Foot F.data (Addr.add (s + 4#64) i) := fun b hb => hf 1 hn1 b hb
    by_cases h1z : el V s 1 = 0#32
    · exact run0 17 (vc_0b hs hp f0 f4 h0' h1z) (fun _ => ⟨h0, Or.inl h1z⟩) (fun h => absurd h (by decide))
        (Or.inl rfl)
    by_cases h1d : el V s 1 = 46#32
    · have hn2 : 2 ≤ n := by
        rcases Nat.lt_or_ge n 2 with h | h
        · obtain rfl : n = 1 := by omega
          exact absurd hz h1z
        · exact h
      have f8 : ∀ i < 4, Foot F.data (Addr.add (s + 8#64) i) := fun b hb => hf 2 hn2 b hb
      by_cases h2z : el V s 2 = 0#32
      · exact run0 17 (vc_0d hs hp f0 f4 f8 h0' h1d h2z) (fun _ => ⟨h0, Or.inr ⟨h1d, h2z⟩⟩)
          (fun h => absurd h (by decide))
          (Or.inl rfl)
      · exact run0 37 (vc_0e hs hp f0 f4 f8 h0' h1d h2z) (fun h => absurd h (by decide))
          (fun _ hD => hD.2.elim h1z fun h => h2z h.2) (Or.inr rfl)
    · exact run0 37 (vc_0c hs hp f0 f4 h0' h1z h1d) (fun h => absurd h (by decide))
        (fun _ hD => hD.2.elim h1z fun h => h1d h.1) (Or.inr rfl)
  · exact run0 37 (vc_0a hs hp f0 fun h => h0 (e0.trans h)) (fun h => absurd h (by decide)) (fun _ hD => h0 hD.1)
      (Or.inr rfl)

end FV7z.Cpp
