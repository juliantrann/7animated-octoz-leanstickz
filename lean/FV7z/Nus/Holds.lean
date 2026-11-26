import FV7z.Nus.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Env
import FV7z.Lemmas.Signed
/-!
# `CStdOutStream::Normalize_UString (UString &s)` (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::Normalize_UString (s)` at `0x5a15e0` in `7zzs` (`CPP/Common/StdOutStream.cpp`;
`objdump -d`).
`rdi` is the stream: its flag byte at `[rdi + 8]`; `rsi` the `UString`: its characters' pointer at `[rsi]` (`s` here),
its length (32 bits) at `[rsi + 8]`; a character is a `wchar_t` (4 bytes). With the flag set, each character `bad`
(below ' ', from 0x7f to 0x9f, from 0x202a to 0x202e or from 0x2066 to 0x2069, as signed numbers) is made '_' (the
loop from 89, `rax` at the character, `rcx` at the end, `ret` at 111); with it 0, each '\n' (the loop from 128, `rdx`
at the end, `ret` at 148). The length 0: `ret` at 148.

- `Mk P V s k`: the first `k` characters with those `P` made '_'; `Res`: what the function leaves.
- `vc_*`: the verification conditions of the pieces; `step89`, `loopA`: the first loop; `step128`, `loopB`: the
  second.
- `nus_ok`: from the entry to the return address, the bytes `Res`, the registers a call keeps (`Str.Back`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Nus

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_111 : pret <+: nus.drop 111 := by decide +kernel
theorem w_148 : pret <+: nus.drop 148 := by decide +kernel
theorem ret_111 (feat : Features) : Dec feat nus 111 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 111) (k := 0) (pret_0 feat) w_111 (Nat.zero_le _)
theorem ret_148 (feat : Features) : Dec feat nus 148 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 148) (k := 0) (pret_0 feat) w_148 (Nat.zero_le _)

/-! ## What the function does -/

/-- The `i`-th character of the string at `s`. -/
abbrev el (V : Addr → Byte) (s : Addr) (i : Nat) : BitVec 32 := rdd(V, s.add (4 * i))
/-- '_', as stored. -/
abbrev u95 : List Byte := toBytesLE 95#32 4
/-- The stream's flag byte, the stream at `p`. -/
abbrev flg (V : Addr → Byte) (p : Addr) : BitVec 8 := ofBytesLE 8 ((byteAddrs (p + 8#64) 1).map V)

/-- A character the flag makes '_' (the code's comparisons, signed). -/
def bad (c : BitVec 32) : Prop :=
  c.toInt ≤ 31 ∨ (126 < c.toInt ∧ c.toInt ≤ 159) ∨ (8233 < c.toInt ∧ c.toInt ≤ 8238) ∨
    (8238 < c.toInt ∧ (c - 8294#32).toNat ≤ 3)
instance : DecidablePred bad := fun c => by unfold bad; exact inferInstance

/-- '\n'. -/
abbrev nl (c : BitVec 32) : Prop := c = 10#32

/-- The first `k` characters at `s` with each `P` made '_', one by one as the code stores them. -/
def Mk (P : BitVec 32 → Prop) [DecidablePred P] (V : Addr → Byte) (s : Addr) : Nat → Addr → Byte
  | 0 => V
  | k + 1 => if P (el V s k) then Vst (Mk P V s k) (s.add (4 * k)) u95 else Mk P V s k

/-- The bytes after `Normalize_UString`, the stream at `p`, the characters at `s`, the length `n`. -/
def Res (V : Addr → Byte) (p s : Addr) (n : Nat) : Addr → Byte :=
  if flg V p = 0#8 then Mk nl V s n else Mk bad V s n

theorem Mk_succ (P : BitVec 32 → Prop) [DecidablePred P] (V : Addr → Byte) (s : Addr) (k : Nat) :
    Mk P V s (k + 1) = if P (el V s k) then Vst (Mk P V s k) (s.add (4 * k)) u95 else Mk P V s k := rfl

/-- A byte not of the first `k` characters: as it was. -/
theorem Mk_out (P : BitVec 32 → Prop) [DecidablePred P] (V : Addr → Byte) (s : Addr) :
    ∀ (k : Nat) (x : Addr), (∀ i < k, ∀ b < 4, x ≠ (s.add (4 * i)).add b) → Mk P V s k x = V x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    have h4 : u95.length = 4 := toBytesLE_length _ _
    rw [Mk_succ]
    by_cases hc : P (el V s k)
    · rw [if_pos hc, Vst_apart u95 _ (s.add (4 * k)) x fun b hb => h k (by omega) b (by omega)]
      exact Mk_out P V s k x fun i hi => h i (by omega)
    · rw [if_neg hc]
      exact Mk_out P V s k x fun i hi => h i (by omega)

/-- Bytes apart from the first `k` characters: as they were. -/
theorem Mk_far (P : BitVec 32 → Prop) [DecidablePred P] (V : Addr → Byte) (s : Addr) {k : Nat} {a : Addr}
    {m : Nat} (h : ∀ b' < m, ∀ i < k, ∀ b < 4, a.add b' ≠ (s.add (4 * i)).add b) :
    (byteAddrs a m).map (Mk P V s k) = (byteAddrs a m).map V :=
  List.map_congr_left fun y hy => by
    obtain ⟨b', hb', rfl⟩ := mem_byteAddrs.1 hy
    exact Mk_out P V s k _ fun i hi b hb => h b' hb' i hi b hb

/-- The `j`-th character while the first `k ≤ j` are being done: as it was. -/
theorem Mk_self (P : BitVec 32 → Prop) [DecidablePred P] (V : Addr → Byte) (s : Addr) {k j : Nat} (hk : k ≤ j)
    (hj : 4 * j + 4 ≤ 2 ^ 64) : el (Mk P V s k) s j = el V s j := by
  have h : ∀ b' < 4, ∀ i < k, ∀ b < 4, (s.add (4 * j)).add b' ≠ (s.add (4 * i)).add b := fun b' hb' i hi b hb e => by
    rw [addr_add_add, addr_add_add] at e
    exact add_ne' s (by omega) (by omega) (by omega) e
  exact congrArg (ofBytesLE 32) (Mk_far P V s h)

theorem res_zero (V : Addr → Byte) (p s : Addr) : Res V p s 0 = V := by
  unfold Res
  split <;> rfl

theorem res_nl {V : Addr → Byte} {p s : Addr} {n : Nat} (h : flg V p = 0#8) : Res V p s n = Mk nl V s n := by
  unfold Res
  rw [if_pos h]

theorem res_bad {V : Addr → Byte} {p s : Addr} {n : Nat} (h : ¬flg V p = 0#8) : Res V p s n = Mk bad V s n := by
  unfold Res
  rw [if_neg h]

/-- Bytes apart from the `n` characters: as they were. -/
theorem res_rd (V : Addr → Byte) (p s : Addr) (n : Nat) {a : Addr} {m : Nat}
    (hx : ∀ b' < m, ∀ i < n, ∀ b < 4, a.add b' ≠ (s.add (4 * i)).add b) :
    (byteAddrs a m).map (Res V p s n) = (byteAddrs a m).map V := by
  unfold Res
  split
  · exact Mk_far nl V s hx
  · exact Mk_far bad V s hx

/-! ## Pointers and comparisons -/

/-- `rcx` (or `rdx`) after `sub edx, 1; lea r, [rax + rdx*4 + 4]`: the end. -/
abbrev endN (p : Addr) (c : BitVec 32) : Addr := p + BitVec.setWidth 64 (c - 1#32) * 4#64 + 4#64

theorem endN_eq (p : Addr) (c : BitVec 32) (hc : c.toNat ≠ 0) : endN p c = p.add (4 * c.toNat) := by
  have h : BitVec.setWidth 64 (c - 1#32) * 4#64 = BitVec.ofNat 64 (4 * (c.toNat - 1)) := by
    apply BitVec.eq_of_toNat_eq
    have h2 := c.isLt
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at h2 ⊢
    omega
  show p + BitVec.setWidth 64 (c - 1#32) * 4#64 + BitVec.ofNat 64 4 = _
  rw [h, ptr_step, show 4 * (c.toNat - 1) + 4 = 4 * c.toNat by omega]
  all_goals exact ptr_add _ _

theorem add4j (s : Addr) (j : Nat) : s.add (4 * j) + 4#64 = s.add (4 * (j + 1)) := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega]
  exact ptr_step s (4 * j) 4

/-- `jle` after `cmp x, y` (32 bits): signed not greater. -/
theorem subF_le32 (f : Rflags) (x y : BitVec 32) : (subF f x y).cond 14 = decide (x.toInt ≤ y.toInt) := by
  have h := subF_g32 f x y
  rw [cond_15] at h
  show ((subF f x y).zf || ((subF f x y).sf != (subF f x y).of)) = _
  rw [← Bool.not_not ((subF f x y).zf || ((subF f x y).sf != (subF f x y).of)), h]
  by_cases hlt : y.toInt < x.toInt <;> simp [hlt] <;> omega

theorem t31 : (31#32 : BitVec 32).toInt = 31 := by decide
theorem t126 : (126#32 : BitVec 32).toInt = 126 := by decide
theorem t159 : (159#32 : BitVec 32).toInt = 159 := by decide
theorem t8233 : (8233#32 : BitVec 32).toInt = 8233 := by decide
theorem t8238 : (8238#32 : BitVec 32).toInt = 8238 := by decide

/-- Closes what `wpx` leaves: equalities by `rfl`, footprints from the hypotheses. -/
macro "nuc" : tactic => `(tactic| (
  all_goals repeat'
    (first
      | exact rfl
      | exact trivial
      | assumption
      | apply And.intro
      | intro _)))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- The length 0: to the `ret` (148), the flag either way. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} (fp : ∀ i < 8, Foot F.data (Addr.add g.rsi i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) (ff : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (h0 : rdd(V, g.rsi + 8#64) = 0#32) :
    W_0 F Wl (fun j' g' _ V' => j' = 148 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fp fl ff h0 ⊢
  have hz : (rdd(V, rsi + 8#64) == 0) = true := by rw [h0]; rfl
  wpx [W_0, W_16, W_24, W_112, W_116, o0, o1, o2, o11, Op.cmpmi, Kp, hz, BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  nuc

/-- The flag set, the length not 0: `rax` the first character, `rcx` the end, to 89. -/
theorem vc_0s {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rsi) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsi i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) (ff : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hfz : ¬flg V g.rdi = 0#8) (h0 : rdd(V, g.rsi + 8#64) ≠ 0#32) :
    W_0 F Wl (fun j' g' _ V' => j' = 89 ∧ g'.rax = s ∧ g'.rcx = endN s rdd(V, g.rsi + 8#64) ∧ Kp g g' ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [flg, endN] at hs fp fl ff hfz h0 ⊢
  have hz : (rdd(V, rsi + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h0
  have hf' : decide (ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) = 0#8) = false := decide_eq_false hfz
  wpx [W_0, W_16, W_24, W_112, W_116, o0, o1, o2, o11, Op.cmpmi, Kp, hs, hz, hf', BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  nuc
  all_goals (rename_i h; simp [hfz] at h)

/-- The flag 0, the length not 0: `rax` the first character, `rdx` the end, to 128. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rsi) = s)
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rsi i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) (ff : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (hfz : flg V g.rdi = 0#8) (h0 : rdd(V, g.rsi + 8#64) ≠ 0#32) :
    W_0 F Wl (fun j' g' _ V' => j' = 128 ∧ g'.rax = s ∧ g'.rdx = endN s rdd(V, g.rsi + 8#64) ∧ Kp g g' ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [flg, endN] at hs fp fl ff hfz h0 ⊢
  have hz : (rdd(V, rsi + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h0
  have hf' : decide (ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) = 0#8) = true := decide_eq_true hfz
  wpx [W_0, W_16, W_24, W_112, W_116, o0, o1, o2, o11, Op.cmpmi, Kp, hs, hz, hf', BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  nuc
  all_goals (rename_i h; simp [hfz] at h)

/-- The piece from 89 in one of its eight ways, then the leftover goals by `omega` on `bad`. -/
local macro "w89" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  wpx [W_89, W_40, W_45, W_53, W_61, W_69, o3, o4, o5, o6, o7, o9, Kp, subF_g32, subF_le32, t31, t126, t159, t8233,
    t8238, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, Bool.true_or, Bool.false_or,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, $ls,*]
  nuc
  all_goals (exfalso; simp only [bad] at *; omega)))

/-- From 89: a `bad` character to 96 (to be made '_'), else to 80. -/
theorem vc_89 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) :
    W_89 F Wl (fun j' g' _ V' => (bad rdd(V, g.rax) → j' = 96) ∧ (¬bad rdd(V, g.rax) → j' = 80) ∧
      g'.rax = g.rax ∧ g'.rcx = g.rcx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf ⊢
  by_cases h1 : (31 : Int) < (rdd(V, rax)).toInt
  · have e1 : decide ((31 : Int) < (rdd(V, rax)).toInt) = true := decide_eq_true h1
    by_cases h2 : (rdd(V, rax)).toInt ≤ 126
    · have e2 : decide ((rdd(V, rax)).toInt ≤ 126) = true := decide_eq_true h2
      w89 [e1, e2]
    have e2 : decide ((rdd(V, rax)).toInt ≤ 126) = false := decide_eq_false h2
    by_cases h3 : (rdd(V, rax)).toInt ≤ 159
    · have e3 : decide ((rdd(V, rax)).toInt ≤ 159) = true := decide_eq_true h3
      w89 [e1, e2, e3]
    have e3 : decide ((rdd(V, rax)).toInt ≤ 159) = false := decide_eq_false h3
    by_cases h4 : (rdd(V, rax)).toInt ≤ 8233
    · have e4 : decide ((rdd(V, rax)).toInt ≤ 8233) = true := decide_eq_true h4
      w89 [e1, e2, e3, e4]
    have e4 : decide ((rdd(V, rax)).toInt ≤ 8233) = false := decide_eq_false h4
    by_cases h5 : (rdd(V, rax)).toInt ≤ 8238
    · have e5 : decide ((rdd(V, rax)).toInt ≤ 8238) = true := decide_eq_true h5
      w89 [e1, e2, e3, e4, e5]
    have e5 : decide ((rdd(V, rax)).toInt ≤ 8238) = false := decide_eq_false h5
    by_cases h6 : (rdd(V, rax) - 8294#32).toNat < 3
    · have e6 : decide ((rdd(V, rax) - 8294#32).toNat < 3) = true := decide_eq_true h6
      w89 [e1, e2, e3, e4, e5, e6]
    have e6 : decide ((rdd(V, rax) - 8294#32).toNat < 3) = false := decide_eq_false h6
    by_cases h7 : rdd(V, rax) - 8294#32 = 3#32
    · have e7 : decide (rdd(V, rax) - 8294#32 = 3#32) = true := decide_eq_true h7
      have h7n : (rdd(V, rax) - 8294#32).toNat = 3 := by rw [h7]; all_goals rfl
      w89 [e1, e2, e3, e4, e5, e6, e7]
    have e7 : decide (rdd(V, rax) - 8294#32 = 3#32) = false := decide_eq_false h7
    have h7n : (rdd(V, rax) - 8294#32).toNat ≠ 3 := fun h => h7 (BitVec.eq_of_toNat_eq h)
    w89 [e1, e2, e3, e4, e5, e6, e7]
  · have e1 : decide ((31 : Int) < (rdd(V, rax)).toInt) = false := decide_eq_false h1
    w89 [e1]

/-- From 80 (kept), not at the end: to 89. -/
theorem vc_80c {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 ≠ g.rcx) :
    W_80 F Wl (fun j' g' _ V' => j' = 89 ∧ g'.rax = g.rax + 4#64 ∧ g'.rcx = g.rcx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rcx) = false := decide_eq_false he
  wpx [W_80, o8, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-- From 80 (kept), at the end: to the `ret` (111). -/
theorem vc_80e {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 = g.rcx) :
    W_80 F Wl (fun j' g' _ V' => j' = 111 ∧ g'.rax = g.rax + 4#64 ∧ g'.rcx = g.rcx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rcx) = true := decide_eq_true he
  wpx [W_80, o8, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-- From 96 (made '_'), not at the end: to 89. -/
theorem vc_96c {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 ≠ g.rcx)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_96 F Wl (fun j' g' _ V' => j' = 89 ∧ g'.rax = g.rax + 4#64 ∧ g'.rcx = g.rcx ∧ Kp g g' ∧
      V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hw ⊢
  have he' : decide (rax + 4#64 = rcx) = false := decide_eq_false he
  wpx [W_96, o10, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-- From 96 (made '_'), at the end: to the `ret` (111). -/
theorem vc_96e {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 = g.rcx)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_96 F Wl (fun j' g' _ V' => j' = 111 ∧ g'.rax = g.rax + 4#64 ∧ g'.rcx = g.rcx ∧ Kp g g' ∧
      V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hw ⊢
  have he' : decide (rax + 4#64 = rcx) = true := decide_eq_true he
  wpx [W_96, o10, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-- From 128, a '\n': made '_', to 139. -/
theorem vc_128n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rax) = 10#32)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_128 F Wl (fun j' g' _ V' => j' = 139 ∧ g' = g ∧ V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf hw ⊢
  have h' : decide (rdd(V, rax) = 10#32) = true := decide_eq_true h
  wpx [W_128, W_133, o12, o13, Op.cmpmi, h', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-- From 128, not a '\n': to 139. -/
theorem vc_128o {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rax) ≠ 10#32)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) :
    W_128 F Wl (fun j' g' _ V' => j' = 139 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf ⊢
  have h' : decide (rdd(V, rax) = 10#32) = false := decide_eq_false h
  wpx [W_128, W_133, o12, o13, Op.cmpmi, h', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-- From 139, not at the end: to 128. -/
theorem vc_139c {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 ≠ g.rdx) :
    W_139 F Wl (fun j' g' _ V' => j' = 128 ∧ g'.rax = g.rax + 4#64 ∧ g'.rdx = g.rdx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rdx) = false := decide_eq_false he
  wpx [W_139, o14, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-- From 139, at the end: to the `ret` (148). -/
theorem vc_139e {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 = g.rdx) :
    W_139 F Wl (fun j' g' _ V' => j' = 148 ∧ g'.rax = g.rax + 4#64 ∧ g'.rdx = g.rdx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rdx) = true := decide_eq_true he
  wpx [W_139, o14, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nuc

/-! ## The loops -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 96 at the `j`-th of the `n` characters (`rax`), `rcx` the end: made '_', on to 89 or, at the end, 111. -/
theorem t96 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {s : Addr} {n j : Nat} (hj : j < n)
    (hn : n < 2 ^ 61) {W : Addr → Byte} {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = nus_at.add 96) (hra : Y.cpu.gpr.rax = s.add (4 * j)) (hrc : Y.cpu.gpr.rcx = s.add (4 * n))
    (hw : ∀ b < 4, Foot Wl ((s.add (4 * j)).add b))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vst W (s.add (4 * j)) u95) →
      Z.cpu.gpr.rax = s.add (4 * (j + 1)) → Z.cpu.gpr.rcx = Y.cpu.gpr.rcx → Kp Y.cpu.gpr Z.cpu.gpr →
      (j + 1 < n → Z.cpu.rip = nus_at.add 89) → (j + 1 = n → Z.cpu.rip = nus_at.add 111) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have hw1 : ∀ i < 4, Foot Wl (Addr.add Y.cpu.gpr.rax i) := fun i hi => by rw [hra]; exact hw i hi
  have h4 : Y.cpu.gpr.rax + 4#64 = s.add (4 * (j + 1)) := by rw [hra, add4j]
  by_cases he : j + 1 = n
  · have he' : Y.cpu.gpr.rax + 4#64 = Y.cpu.gpr.rcx := by rw [h4, hrc, he]
    refine (c_96 prof).run c hin _ hK hA hrip (vc_96e he' hw1) ?_
    rintro j' g fl V' ⟨rfl, hax, hcx, hkp, hV⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst V'
    rw [hra] at hAZ
    exact k Z t₁ hKZ hAZ (by rw [hgZ, hax, h4]) (by rw [hgZ, hcx]) (Kp.of_eq hgZ hkp)
      (fun h => absurd he (by omega)) fun _ => hrZ
  · have he' : Y.cpu.gpr.rax + 4#64 ≠ Y.cpu.gpr.rcx := by
      rw [h4, hrc]
      exact add_ne' s (by omega) (by omega) (by omega)
    refine (c_96 prof).run c hin _ hK hA hrip (vc_96c he' hw1) ?_
    rintro j' g fl V' ⟨rfl, hax, hcx, hkp, hV⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst V'
    rw [hra] at hAZ
    exact k Z t₁ hKZ hAZ (by rw [hgZ, hax, h4]) (by rw [hgZ, hcx]) (Kp.of_eq hgZ hkp) (fun _ => hrZ)
      fun h => absurd h he

/-- From 80 at the `j`-th of the `n` characters (`rax`), `rcx` the end: on to 89 or, at the end, 111. -/
theorem t80 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {s : Addr} {n j : Nat} (hj : j < n)
    (hn : n < 2 ^ 61) {W : Addr → Byte} {Y : State} {t : Nat} (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hrip : Y.cpu.rip = nus_at.add 80) (hra : Y.cpu.gpr.rax = s.add (4 * j)) (hrc : Y.cpu.gpr.rcx = s.add (4 * n))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      Z.cpu.gpr.rax = s.add (4 * (j + 1)) → Z.cpu.gpr.rcx = Y.cpu.gpr.rcx → Kp Y.cpu.gpr Z.cpu.gpr →
      (j + 1 < n → Z.cpu.rip = nus_at.add 89) → (j + 1 = n → Z.cpu.rip = nus_at.add 111) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  have h4 : Y.cpu.gpr.rax + 4#64 = s.add (4 * (j + 1)) := by rw [hra, add4j]
  by_cases he : j + 1 = n
  · have he' : Y.cpu.gpr.rax + 4#64 = Y.cpu.gpr.rcx := by rw [h4, hrc, he]
    refine (c_80 prof).run c hin _ hK hA hrip (vc_80e he') ?_
    rintro j' g fl V' ⟨rfl, hax, hcx, hkp, hV⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst V'
    exact k Z t₁ hKZ hAZ (by rw [hgZ, hax, h4]) (by rw [hgZ, hcx]) (Kp.of_eq hgZ hkp)
      (fun h => absurd he (by omega)) fun _ => hrZ
  · have he' : Y.cpu.gpr.rax + 4#64 ≠ Y.cpu.gpr.rcx := by
      rw [h4, hrc]
      exact add_ne' s (by omega) (by omega) (by omega)
    refine (c_80 prof).run c hin _ hK hA hrip (vc_80c he') ?_
    rintro j' g fl V' ⟨rfl, hax, hcx, hkp, hV⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst V'
    exact k Z t₁ hKZ hAZ (by rw [hgZ, hax, h4]) (by rw [hgZ, hcx]) (Kp.of_eq hgZ hkp) (fun _ => hrZ)
      fun h => absurd h he

/-- From 89 at the `j`-th of the `n` characters (`rax`), `rcx` the end, the first `j` done: the `j`-th done, on to
89 or, at the end, 111. -/
theorem step89 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n j : Nat}
    (hj : j < n) (hn : n < 2 ^ 61) (hf : ∀ b < 4, Foot F.data ((s.add (4 * j)).add b))
    (hw : ∀ b < 4, Foot Wl ((s.add (4 * j)).add b)) {X : State} {t : Nat} (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem (Mk bad V s j)) (hrip : X.cpu.rip = nus_at.add 89)
    (hra : X.cpu.gpr.rax = s.add (4 * j)) (hrc : X.cpu.gpr.rcx = s.add (4 * n))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mk bad V s (j + 1)) →
      Z.cpu.gpr.rax = s.add (4 * (j + 1)) → Z.cpu.gpr.rcx = X.cpu.gpr.rcx → Kp X.cpu.gpr Z.cpu.gpr →
      (j + 1 < n → Z.cpu.rip = nus_at.add 89) → (j + 1 = n → Z.cpu.rip = nus_at.add 111) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hb : rdd(Mk bad V s j, X.cpu.gpr.rax) = el V s j := by
    rw [hra]
    exact Mk_self bad V s (Nat.le_refl _) (by omega)
  have hf1 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rax i) := fun i hi => by rw [hra]; exact hf i hi
  refine (c_89 prof).run c hin _ hK hA hrip (vc_89 hf1) ?_
  rintro j' g fl V' ⟨hbt, hbf, hax, hcx, hkp, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst V'
  have hYa : Y.cpu.gpr.rax = s.add (4 * j) := by rw [hgY, hax, hra]
  have hYc : Y.cpu.gpr.rcx = s.add (4 * n) := by rw [hgY, hcx, hrc]
  have hkY : Kp X.cpu.gpr Y.cpu.gpr := Kp.of_eq hgY hkp
  by_cases hc : bad (el V s j)
  · rw [hbt (by rw [hb]; exact hc)] at hrY
    refine t96 c hin hj hn hKY hAY hrY hYa hYc hw ?_
    intro Z t₂ hKZ hAZ hZa hZc hkZ h1 h2
    refine k Z t₂ hKZ ?_ hZa (hZc.trans (hYc.trans hrc.symm)) (hkY.trans hkZ) h1 h2
    rw [Mk_succ, if_pos hc]
    exact hAZ
  · rw [hbf (by rw [hb]; exact hc)] at hrY
    refine t80 c hin hj hn hKY hAY hrY hYa hYc ?_
    intro Z t₂ hKZ hAZ hZa hZc hkZ h1 h2
    refine k Z t₂ hKZ ?_ hZa (hZc.trans (hYc.trans hrc.symm)) (hkY.trans hkZ) h1 h2
    rw [Mk_succ, if_neg hc]
    exact hAZ

/-- The first loop from 89 at the `j`-th of the `n` characters at `s`, the first `j` done: on to the `ret` (111)
with all `n` done, the registers a call keeps as at `g₀`. By induction on the characters left. -/
theorem loopA (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 61) (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mk bad V s n) →
      Z.cpu.rip = nus_at.add 111 → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m + 1 = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem (Mk bad V s j) →
      X.cpu.rip = nus_at.add 89 → X.cpu.gpr.rax = s.add (4 * j) → X.cpu.gpr.rcx = s.add (4 * n) →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hra hrc hkp
    refine step89 c hin (by omega) hn (hf j (by omega)) (hw j (by omega)) hK hA hrip hra hrc ?_
    intro Y t₁ hKY hAY _ _ hkY _ hend
    have hjn : j + 1 = n := by omega
    rw [hjn] at hAY
    exact k Y t₁ hKY hAY (hend hjn) (hkp.trans hkY)
  | succ m ih =>
    intro j hj X t hK hA hrip hra hrc hkp
    refine step89 c hin (by omega) hn (hf j (by omega)) (hw j (by omega)) hK hA hrip hra hrc ?_
    intro Y t₁ hKY hAY hYa hYc hkY hnext _
    exact ih (j + 1) (by omega) Y t₁ hKY hAY (hnext (by omega)) hYa (hYc.trans hrc) (hkp.trans hkY)

/-- From 128 at the `j`-th of the `n` characters (`rax`), `rdx` the end, the first `j` done: the `j`-th done, on to
128 or, at the end, 148. -/
theorem step128 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n j : Nat}
    (hj : j < n) (hn : n < 2 ^ 61) (hf : ∀ b < 4, Foot F.data ((s.add (4 * j)).add b))
    (hw : ∀ b < 4, Foot Wl ((s.add (4 * j)).add b)) {X : State} {t : Nat} (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem (Mk nl V s j)) (hrip : X.cpu.rip = nus_at.add 128)
    (hra : X.cpu.gpr.rax = s.add (4 * j)) (hrd : X.cpu.gpr.rdx = s.add (4 * n))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mk nl V s (j + 1)) →
      Z.cpu.gpr.rax = s.add (4 * (j + 1)) → Z.cpu.gpr.rdx = X.cpu.gpr.rdx → Kp X.cpu.gpr Z.cpu.gpr →
      (j + 1 < n → Z.cpu.rip = nus_at.add 128) → (j + 1 = n → Z.cpu.rip = nus_at.add 148) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hb : rdd(Mk nl V s j, X.cpu.gpr.rax) = el V s j := by
    rw [hra]
    exact Mk_self nl V s (Nat.le_refl _) (by omega)
  have hf1 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rax i) := fun i hi => by rw [hra]; exact hf i hi
  have hw1 : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rax i) := fun i hi => by rw [hra]; exact hw i hi
  have k139 : ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Mk nl V s (j + 1)) →
      Y.cpu.rip = nus_at.add 139 → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t₁ := by
    intro Y t₁ hKY hAY hrY hgY
    have h4 : Y.cpu.gpr.rax + 4#64 = s.add (4 * (j + 1)) := by rw [hgY, hra, add4j]
    have hkY : Kp X.cpu.gpr Y.cpu.gpr := Kp.of_eq hgY (Kp.refl _)
    by_cases he : j + 1 = n
    · have he' : Y.cpu.gpr.rax + 4#64 = Y.cpu.gpr.rdx := by rw [h4, hgY, hrd, he]
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139e he') ?_
      rintro j' g fl V' ⟨rfl, hax, hdx, hkp, hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
      subst V'
      exact k Z t₂ hKZ hAZ (by rw [hgZ, hax, h4]) (by rw [hgZ, hdx, hgY]) (hkY.trans (Kp.of_eq hgZ hkp))
        (fun h => absurd he (by omega)) fun _ => hrZ
    · have he' : Y.cpu.gpr.rax + 4#64 ≠ Y.cpu.gpr.rdx := by
        rw [h4, hgY, hrd]
        exact add_ne' s (by omega) (by omega) (by omega)
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139c he') ?_
      rintro j' g fl V' ⟨rfl, hax, hdx, hkp, hV⟩ Z t₂ hKZ hAZ hrZ hgZ -
      subst V'
      exact k Z t₂ hKZ hAZ (by rw [hgZ, hax, h4]) (by rw [hgZ, hdx, hgY]) (hkY.trans (Kp.of_eq hgZ hkp))
        (fun _ => hrZ) fun h => absurd h he
  by_cases hc : nl (el V s j)
  · refine (c_128 prof).run c hin _ hK hA hrip (vc_128n (by rw [hb]; exact hc) hf1 hw1) ?_
    rintro j' g fl V' ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine k139 Y t₁ hKY ?_ hrY (hgY.trans hg)
    rw [Mk_succ, if_pos hc, ← hra]
    exact hAY
  · refine (c_128 prof).run c hin _ hK hA hrip (vc_128o (by rw [hb]; exact hc) hf1) ?_
    rintro j' g fl V' ⟨rfl, hg, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine k139 Y t₁ hKY ?_ hrY (hgY.trans hg)
    rw [Mk_succ, if_neg hc]
    exact hAY

/-- The second loop from 128 at the `j`-th of the `n` characters at `s`, the first `j` done: on to the `ret` (148)
with all `n` done, the registers a call keeps as at `g₀`. By induction on the characters left. -/
theorem loopB (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 61) (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Mk nl V s n) →
      Z.cpu.rip = nus_at.add 148 → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m + 1 = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem (Mk nl V s j) →
      X.cpu.rip = nus_at.add 128 → X.cpu.gpr.rax = s.add (4 * j) → X.cpu.gpr.rdx = s.add (4 * n) →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hra hrd hkp
    refine step128 c hin (by omega) hn (hf j (by omega)) (hw j (by omega)) hK hA hrip hra hrd ?_
    intro Y t₁ hKY hAY _ _ hkY _ hend
    have hjn : j + 1 = n := by omega
    rw [hjn] at hAY
    exact k Y t₁ hKY hAY (hend hjn) (hkp.trans hkY)
  | succ m ih =>
    intro j hj X t hK hA hrip hra hrd hkp
    refine step128 c hin (by omega) hn (hf j (by omega)) (hw j (by omega)) hK hA hrip hra hrd ?_
    intro Y t₁ hKY hAY hYa hYd hkY hnext _
    exact ih (j + 1) (by omega) Y t₁ hKY hAY (hnext (by omega)) hYa (hYd.trans hrd) (hkp.trans hkY)

/-! ## The function -/

/-- `Normalize_UString (s)` from its entry: `rdi` the stream, its flag byte data of the footprint; `rsi` the
`UString`, its characters at `s` (`hs`), its length `n` (`hn`), their bytes data of the footprint and writable, apart
from the return address: at the return address with the bytes `Res`, the registers a call keeps (`Str.Back`). -/
theorem nus_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nus_at) {s : Addr} {n : Nat}
    (hs : rdq(V, X.cpu.gpr.rsi) = s) (hn : (rdd(V, X.cpu.gpr.rsi + 8#64)).toNat = n)
    (hp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hpl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
    (hfl : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hsr : ∀ b' < 8, ∀ i < n, ∀ b < 4, Addr.add X.cpu.gpr.rsp b' ≠ (s.add (4 * i)).add b)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Res V X.cpu.gpr.rdi s n) →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hn32 : n < 2 ^ 32 := by
    rw [← hn]
    exact (rdd(V, X.cpu.gpr.rsi + 8#64)).isLt
  have hn61 : n < 2 ^ 61 := by omega
  have hra' : rdq(Res V X.cpu.gpr.rdi s n, X.cpu.gpr.rsp) = e₂.add j₂ := by
    rw [res_rd V _ _ _ hsr]
    exact hra
  have kr : ∀ jr, jr < 149 → (∀ feat, Dec feat nus jr (FV7z.mk .ret 64 [] 1)) → ∀ (Z : State) (t' : Nat),
      KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Res V X.cpu.gpr.rdi s n) → Z.cpu.rip = nus_at.add jr →
      Kp X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t' :=
    fun jr hj hd Z t' hKZ hAZ hrZ hkp =>
      ret_back c hin (lt_len hj) (hd _) hKZ hAZ hrZ hkp hl hin₂ h₂ hra'
        fun Z' t'' hK' hA' hr' hb _ => k Z' t'' hK' hA' hr' hb
  by_cases hn0 : n = 0
  · have h0 : rdd(V, X.cpu.gpr.rsi + 8#64) = 0#32 := BitVec.eq_of_toNat_eq (by rw [hn, hn0]; all_goals rfl)
    refine (c_0 prof).run c hin _ hK hA hrip (vc_0e hp hpl hfl h0) ?_
    rintro j' g fl V' ⟨rfl, hkp, hV⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst V'
    subst hn0
    refine kr 148 (by decide) ret_148 Z t₁ hKZ ?_ hrZ (Kp.of_eq hgZ hkp)
    rw [res_zero]
    exact hAZ
  have hc : (rdd(V, X.cpu.gpr.rsi + 8#64)).toNat ≠ 0 := by rw [hn]; exact hn0
  have h0 : rdd(V, X.cpu.gpr.rsi + 8#64) ≠ 0#32 := fun h => hc (by rw [h]; all_goals rfl)
  have hend : endN s rdd(V, X.cpu.gpr.rsi + 8#64) = s.add (4 * n) := by rw [endN_eq s _ hc, hn]
  by_cases hfz : flg V X.cpu.gpr.rdi = 0#8
  · refine (c_0 prof).run c hin _ hK hA hrip (vc_0z hs hp hpl hfl hfz h0) ?_
    rintro j' g fl V' ⟨rfl, hax, hdx, hkp, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine loopB c hin (V := V) (g₀ := X.cpu.gpr) hn61 hf hw ?_ (n - 1) 0 (by omega) Y t₁ hKY hAY hrY ?_ ?_
      (Kp.of_eq hgY hkp)
    · intro Z t' hKZ hAZ hrZ hkZ
      refine kr 148 (by decide) ret_148 Z t' hKZ ?_ hrZ hkZ
      rw [res_nl hfz]
      exact hAZ
    · rw [hgY, hax, Nat.mul_zero, addr_add_zero]
    · rw [hgY, hdx, hend]
  · refine (c_0 prof).run c hin _ hK hA hrip (vc_0s hs hp hpl hfl hfz h0) ?_
    rintro j' g fl V' ⟨rfl, hax, hcx, hkp, hV⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine loopA c hin (V := V) (g₀ := X.cpu.gpr) hn61 hf hw ?_ (n - 1) 0 (by omega) Y t₁ hKY hAY hrY ?_ ?_
      (Kp.of_eq hgY hkp)
    · intro Z t' hKZ hAZ hrZ hkZ
      refine kr 111 (by decide) ret_111 Z t' hKZ ?_ hrZ hkZ
      rw [res_bad hfz]
      exact hAZ
    · rw [hgY, hax, Nat.mul_zero, addr_add_zero]
    · rw [hgY, hcx, hend]

end FV7z.Nus
