import FV7z.Nus.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Env
import FV7z.Lemmas.Signed
import FV7z.Lemmas.CmpImm
/-!
# `CStdOutStream::Normalize_UString (UString &s)` (PLAN.md §M, M1)

7-Zip 26.06's `CStdOutStream::Normalize_UString (s)` at `0x5a15e0` in `7zzs` (`CPP/Common/StdOutStream.cpp`;
`objdump -d`). A leaf: no calls, no frame.
`rdi` is the stream: the byte at `[rdi + 8]` says terminal mode. `rsi` is the `UString`: its characters' pointer at
`[rsi]` (`s` here), its length (32 bits) at `[rsi + 8]`; a character is a `wchar_t` (4 bytes). The length 0: the
`ret` at 148. Else, in terminal mode (the byte not 0), each character below 0x20 (signed), in 0x7f..0x9f,
0x202a..0x202e or 0x2066..0x2069 made '_' (the loop from 89, `rax` at the character, `rcx` at the end; `ret` at 111);
else each '\n' made '_' (the loop from 128, `rdx` at the end; `ret` at 148).

- `bT`, `bN`: the two tests; `Nm p V s k`: the first `k` characters with those `p` holds of made '_', one by one as
  the code stores them; `Res`: what the function leaves.
- `vc_*`: the verification conditions of the pieces; `step89`, `loop1`: the terminal-mode loop; `step128`, `loop2`:
  the other.
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
/-- The byte at `d + 8`: terminal mode when not 0. -/
abbrev tmB (V : Addr → Byte) (d : Addr) : BitVec 8 := ofBytesLE 8 ((byteAddrs (d + 8#64) 1).map V)

/-- Terminal mode: the character made '_' (below 0x20 signed, 0x7f..0x9f, 0x202a..0x202e, 0x2066..0x2069), tested
in the code's order. -/
def bT (c : BitVec 32) : Bool :=
  if 31 < c.toInt then
    (if c.toInt ≤ 126 then false else if c.toInt ≤ 159 then true else if c.toInt ≤ 8233 then false
      else if c.toInt ≤ 8238 then true else decide ((c - 8294#32).toNat ≤ 3))
  else true

/-- Otherwise: '\n' made '_'. -/
def bN (c : BitVec 32) : Bool := decide (c = 10#32)

/-- The first `k` characters at `s` with each one `p` holds of made '_', one by one as the code stores them. -/
def Nm (p : BitVec 32 → Bool) (V : Addr → Byte) (s : Addr) : Nat → Addr → Byte
  | 0 => V
  | k + 1 => if p (el V s k) = true then Vst (Nm p V s k) (s.add (4 * k)) u95 else Nm p V s k

/-- The bytes after `Normalize_UString`, the stream at `d`, the characters at `s`, the length `n`. -/
def Res (V : Addr → Byte) (d s : Addr) (n : Nat) : Addr → Byte :=
  if tmB V d = 0#8 then Nm bN V s n else Nm bT V s n

theorem Nm_succ (p : BitVec 32 → Bool) (V : Addr → Byte) (s : Addr) (k : Nat) :
    Nm p V s (k + 1) = if p (el V s k) = true then Vst (Nm p V s k) (s.add (4 * k)) u95 else Nm p V s k := rfl

/-- A byte not of the first `k` characters: as it was. -/
theorem Nm_out (p : BitVec 32 → Bool) (V : Addr → Byte) (s : Addr) :
    ∀ (k : Nat) (x : Addr), (∀ i < k, ∀ b < 4, x ≠ (s.add (4 * i)).add b) → Nm p V s k x = V x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    have h4 : u95.length = 4 := toBytesLE_length _ _
    rw [Nm_succ]
    by_cases hc : p (el V s k) = true
    · rw [if_pos hc, Vst_apart u95 _ (s.add (4 * k)) x fun b hb => h k (by omega) b (by omega)]
      exact Nm_out p V s k x fun i hi => h i (by omega)
    · rw [if_neg hc]
      exact Nm_out p V s k x fun i hi => h i (by omega)

/-- Bytes apart from the first `k` characters: as they were. -/
theorem Nm_far (p : BitVec 32 → Bool) (V : Addr → Byte) (s : Addr) {k : Nat} {a : Addr} {m : Nat}
    (h : ∀ b' < m, ∀ i < k, ∀ b < 4, a.add b' ≠ (s.add (4 * i)).add b) :
    (byteAddrs a m).map (Nm p V s k) = (byteAddrs a m).map V :=
  List.map_congr_left fun y hy => by
    obtain ⟨b', hb', rfl⟩ := mem_byteAddrs.1 hy
    exact Nm_out p V s k _ fun i hi b hb => h b' hb' i hi b hb

/-- The `j`-th character while the first `k ≤ j` are being done: as it was. -/
theorem Nm_self (p : BitVec 32 → Bool) (V : Addr → Byte) (s : Addr) {k j : Nat} (hk : k ≤ j)
    (hj : 4 * j + 4 ≤ 2 ^ 64) : el (Nm p V s k) s j = el V s j := by
  have h : ∀ b' < 4, ∀ i < k, ∀ b < 4, (s.add (4 * j)).add b' ≠ (s.add (4 * i)).add b :=
    fun b' hb' i hi b hb e => by
      rw [addr_add_add, addr_add_add] at e
      exact add_ne' s (by omega) (by omega) (by omega) e
  exact congrArg (ofBytesLE 32) (Nm_far p V s h)

theorem res_n {V : Addr → Byte} {d s : Addr} {n : Nat} (h : tmB V d = 0#8) : Res V d s n = Nm bN V s n := by
  unfold Res
  rw [if_pos h]

theorem res_t {V : Addr → Byte} {d s : Addr} {n : Nat} (h : ¬tmB V d = 0#8) : Res V d s n = Nm bT V s n := by
  unfold Res
  rw [if_neg h]

theorem res_zero (V : Addr → Byte) (d s : Addr) : Res V d s 0 = V := by
  unfold Res
  split <;> rfl

/-! ## Arithmetic -/

/-- `jle` after `cmp x, y` (32 bits): signed not greater (as `Sen.subF_le32`). -/
theorem nus_le32 (f : Rflags) (x y : BitVec 32) : (subF f x y).cond 14 = decide (x.toInt ≤ y.toInt) := by
  have e : (subF f x y).cond 14 = !((subF f x y).cond 15) := by simp only [Rflags.cond, Bool.not_not]
  rw [e, subF_g32]
  by_cases h : x.toInt ≤ y.toInt
  · rw [decide_eq_true h, decide_eq_false (Int.not_lt.mpr h)]
    rfl
  · rw [decide_eq_false h, decide_eq_true (Int.lt_of_not_ge h)]
    rfl

theorem i31 : (31#32 : BitVec 32).toInt = 31 := by decide
theorem i126 : (126#32 : BitVec 32).toInt = 126 := by decide
theorem i159 : (159#32 : BitVec 32).toInt = 159 := by decide
theorem i8233 : (8233#32 : BitVec 32).toInt = 8233 := by decide
theorem i8238 : (8238#32 : BitVec 32).toInt = 8238 := by decide

/-- `jbe` after `cmp x, 3`. -/
theorem be3 (x : BitVec 32) : (decide (x.toNat < 3) || decide (x = 3#32)) = decide (x.toNat ≤ 3) :=
  be_imm x 3 (by decide)

/-- `rcx` (`rdx`) at 89 (128): `lea rcx, [rax + rdx * 4 + 4]`, `rdx` the length less one. -/
abbrev endT (p : Addr) (c : BitVec 32) : Addr := p + BitVec.setWidth 64 (c - 1#32) * 4#64 + 4#64

theorem mul4_eq (c : BitVec 32) (hc : c.toNat ≠ 0) :
    BitVec.setWidth 64 (c - 1#32) * 4#64 = BitVec.ofNat 64 (4 * (c.toNat - 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h2 := c.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceSub] at h2 ⊢
  omega

theorem endT_eq (p : Addr) (c : BitVec 32) (hc : c.toNat ≠ 0) : endT p c = p.add (4 * c.toNat) := by
  show p + BitVec.setWidth 64 (c - 1#32) * 4#64 + BitVec.ofNat 64 4 = _
  rw [mul4_eq c hc, ptr_step, show 4 * (c.toNat - 1) + 4 = 4 * c.toNat by omega]
  all_goals exact ptr_add _ _

theorem add4j (s : Addr) (j : Nat) : s.add (4 * j) + 4#64 = s.add (4 * (j + 1)) := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega]
  exact ptr_step s (4 * j) 4

/-- Closes what `wpx` leaves: equalities by `rfl`, footprints from the hypotheses. -/
macro "nusx" : tactic => `(tactic| (
  all_goals repeat'
    (first
      | exact rfl
      | exact trivial
      | assumption
      | apply And.intro
      | intro _)))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- The length 0: to the `ret` (148). -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (fp1 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add g.rsi i)) (fl : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h0 : rdd(V, g.rsi + 8#64) = 0#32) :
    W_0 F Wl (fun j' g' _ V' => j' = 148 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fp1 fs fl h0 ⊢
  have hz : (rdd(V, rsi + 8#64) == 0) = true := by rw [h0]; rfl
  by_cases ht : tmB V rdi = 0#8
  · have ht' : decide (ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) = 0#8) = true := decide_eq_true ht
    wpx [W_0, W_16, W_24, W_112, W_116, o0, o1, o2, o11, Op.cmpmi, Kp, hz, ht', BitVec.and_self, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
      eq_self_iff_true, and_self]
    nusx
  · have ht' : decide (ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) = 0#8) = false := decide_eq_false ht
    wpx [W_0, W_16, W_24, W_112, W_116, o0, o1, o2, o11, Op.cmpmi, Kp, hz, ht', BitVec.and_self, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
      eq_self_iff_true, and_self]
    nusx

/-- Terminal mode, the length not 0: `rax` the first character, `rcx` the end, to 89. -/
theorem vc_0t {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rsi) = s)
    (fp1 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add g.rsi i)) (fl : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h0 : rdd(V, g.rsi + 8#64) ≠ 0#32) (ht : ¬tmB V g.rdi = 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 89 ∧ g'.rax = s ∧ g'.rcx = endT s rdd(V, g.rsi + 8#64) ∧ Kp g g' ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fp1 fs fl h0 ht ⊢
  have hz : (rdd(V, rsi + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h0
  have ht' : decide (ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) = 0#8) = false := decide_eq_false ht
  wpx [W_0, W_16, W_24, W_112, W_116, o0, o1, o2, o11, Op.cmpmi, Kp, hs, hz, ht', BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  nusx

/-- The other mode, the length not 0: `rax` the first character, `rdx` the end, to 128. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} {s : Addr} (hs : rdq(V, g.rsi) = s)
    (fp1 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (fs : ∀ i < 8, Foot F.data (Addr.add g.rsi i)) (fl : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h0 : rdd(V, g.rsi + 8#64) ≠ 0#32) (ht : tmB V g.rdi = 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 128 ∧ g'.rax = s ∧ g'.rdx = endT s rdd(V, g.rsi + 8#64) ∧ Kp g g' ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs fp1 fs fl h0 ht ⊢
  have hz : (rdd(V, rsi + 8#64) == 0) = false := beq_eq_false_iff_ne.2 h0
  have ht' : decide (ofBytesLE 8 ((byteAddrs (rdi + 8#64) 1).map V) = 0#8) = true := decide_eq_true ht
  wpx [W_0, W_16, W_24, W_112, W_116, o0, o1, o2, o11, Op.cmpmi, Kp, hs, hz, ht', BitVec.and_self, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self]
  nusx

/-- From 89: the character's test, to 96 (made '_') or 80 (kept). -/
abbrev P89 (V : Addr → Byte) (g : Gprs) : Nat → Gprs → Rflags → (Addr → Byte) → Prop :=
  fun j' g' _ V' => V' = V ∧ g'.rax = g.rax ∧ g'.rcx = g.rcx ∧ Kp g g' ∧
    (j' = 96 ∧ bT rdd(V, g.rax) = true ∨ j' = 80 ∧ bT rdd(V, g.rax) = false)

/-- `wpx` over the tests from 89, and what it leaves closed. -/
macro "w89" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  wpx [W_89, W_40, W_45, W_53, W_61, W_69, o9, o3, o4, o5, o6, o7, P89, Kp, subF_g32, nus_le32, be3, i31, i126,
    i159, i8233, i8238, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self, $ls,*]
  all_goals repeat'
    (first
      | assumption
      | exact Or.inl (by assumption)
      | exact Or.inr (by assumption)
      | exact Or.inl ⟨rfl, by assumption⟩
      | exact Or.inr ⟨rfl, by assumption⟩
      | exact rfl
      | exact trivial
      | apply And.intro
      | intro _)))

theorem vc_89 {g : Gprs} {f : Rflags} {V : Addr → Byte} (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) :
    W_89 F Wl (P89 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf ⊢
  by_cases h1 : 31 < (rdd(V, rax)).toInt
  swap
  · have hb : bT rdd(V, rax) = true := by
      unfold bT
      rw [if_neg h1]
    have d1 : decide (31 < (rdd(V, rax)).toInt) = false := decide_eq_false h1
    w89 [d1]
  have d1 : decide (31 < (rdd(V, rax)).toInt) = true := decide_eq_true h1
  by_cases h2 : (rdd(V, rax)).toInt ≤ 126
  · have hb : bT rdd(V, rax) = false := by
      unfold bT
      rw [if_pos h1, if_pos h2]
    have d2 : decide ((rdd(V, rax)).toInt ≤ 126) = true := decide_eq_true h2
    w89 [d1, d2]
  have d2 : decide ((rdd(V, rax)).toInt ≤ 126) = false := decide_eq_false h2
  by_cases h3 : (rdd(V, rax)).toInt ≤ 159
  · have hb : bT rdd(V, rax) = true := by
      unfold bT
      rw [if_pos h1, if_neg h2, if_pos h3]
    have d3 : decide ((rdd(V, rax)).toInt ≤ 159) = true := decide_eq_true h3
    w89 [d1, d2, d3]
  have d3 : decide ((rdd(V, rax)).toInt ≤ 159) = false := decide_eq_false h3
  by_cases h4 : (rdd(V, rax)).toInt ≤ 8233
  · have hb : bT rdd(V, rax) = false := by
      unfold bT
      rw [if_pos h1, if_neg h2, if_neg h3, if_pos h4]
    have d4 : decide ((rdd(V, rax)).toInt ≤ 8233) = true := decide_eq_true h4
    w89 [d1, d2, d3, d4]
  have d4 : decide ((rdd(V, rax)).toInt ≤ 8233) = false := decide_eq_false h4
  by_cases h5 : (rdd(V, rax)).toInt ≤ 8238
  · have hb : bT rdd(V, rax) = true := by
      unfold bT
      rw [if_pos h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]
    have d5 : decide ((rdd(V, rax)).toInt ≤ 8238) = true := decide_eq_true h5
    w89 [d1, d2, d3, d4, d5]
  have d5 : decide ((rdd(V, rax)).toInt ≤ 8238) = false := decide_eq_false h5
  by_cases h6 : (rdd(V, rax) - 8294#32).toNat ≤ 3
  · have hb : bT rdd(V, rax) = true := by
      unfold bT
      rw [if_pos h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
      exact decide_eq_true h6
    have d6 : decide ((rdd(V, rax) - 8294#32).toNat ≤ 3) = true := decide_eq_true h6
    w89 [d1, d2, d3, d4, d5, d6]
  · have hb : bT rdd(V, rax) = false := by
      unfold bT
      rw [if_pos h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
      exact decide_eq_false h6
    have d6 : decide ((rdd(V, rax) - 8294#32).toNat ≤ 3) = false := decide_eq_false h6
    w89 [d1, d2, d3, d4, d5, d6]

/-- From 96, not the end: made '_', `rax` the next, back to 89. -/
theorem vc_96c {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 ≠ g.rcx)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_96 F Wl (fun j' g' _ V' => j' = 89 ∧ g' = { g with rax := g.rax + 4#64 } ∧ V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hw ⊢
  have he' : decide (rax + 4#64 = rcx) = false := decide_eq_false he
  wpx [W_96, o10, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-- From 96 at the last: made '_', to the `ret` (111). -/
theorem vc_96e {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 = g.rcx)
    (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_96 F Wl (fun j' g' _ V' => j' = 111 ∧ Kp g g' ∧ V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he hw ⊢
  have he' : decide (rax + 4#64 = rcx) = true := decide_eq_true he
  wpx [W_96, o10, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-- From 80, not the end: `rax` the next, back to 89. -/
theorem vc_80c {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 ≠ g.rcx) :
    W_80 F Wl (fun j' g' _ V' => j' = 89 ∧ g' = { g with rax := g.rax + 4#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rcx) = false := decide_eq_false he
  wpx [W_80, o8, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-- From 80 at the last: to the `ret` (111). -/
theorem vc_80e {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 = g.rcx) :
    W_80 F Wl (fun j' g' _ V' => j' = 111 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rcx) = true := decide_eq_true he
  wpx [W_80, o8, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-- From 128, a '\n': made '_', to 139. -/
theorem vc_128s {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : rdd(V, g.rax) = 10#32)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) (hw : ∀ i < 4, Foot Wl (Addr.add g.rax i)) :
    W_128 F Wl (fun j' g' _ V' => j' = 139 ∧ g' = g ∧ V' = Vst V g.rax u95) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc hf hw ⊢
  have hc' : decide (rdd(V, rax) = 10#32) = true := decide_eq_true hc
  wpx [W_128, W_133, o12, o13, Op.cmpmi, hc', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-- From 128, not a '\n': to 139. -/
theorem vc_128n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : rdd(V, g.rax) ≠ 10#32)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rax i)) :
    W_128 F Wl (fun j' g' _ V' => j' = 139 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc hf ⊢
  have hc' : decide (rdd(V, rax) = 10#32) = false := decide_eq_false hc
  wpx [W_128, W_133, o12, o13, Op.cmpmi, hc', Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-- From 139, not the end: `rax` the next, back to 128. -/
theorem vc_139c {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 ≠ g.rdx) :
    W_139 F Wl (fun j' g' _ V' => j' = 128 ∧ g' = { g with rax := g.rax + 4#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rdx) = false := decide_eq_false he
  wpx [W_139, o14, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-- From 139 at the last: to the `ret` (148). -/
theorem vc_139e {g : Gprs} {f : Rflags} {V : Addr → Byte} (he : g.rax + 4#64 = g.rdx) :
    W_139 F Wl (fun j' g' _ V' => j' = 148 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at he ⊢
  have he' : decide (rax + 4#64 = rdx) = true := decide_eq_true he
  wpx [W_139, o14, Kp, he', Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self]
  nusx

/-! ## The loops -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 89 at the `j`-th of the `n` characters at `s` (`rax`), `rcx` the end, the first `j` done: on to 89 at the
next or to the `ret` at 111 after the last, the first `j + 1` done. -/
theorem step89 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n j : Nat}
    (hn : n < 2 ^ 32) (hj : j < n) (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b)) {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem (Nm bT V s j)) (hrip : X.cpu.rip = nus_at.add 89)
    (hra : X.cpu.gpr.rax = s.add (4 * j)) (hrc : X.cpu.gpr.rcx = s.add (4 * n))
    (kc : j + 1 < n → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Nm bT V s (j + 1)) →
      Y.cpu.rip = nus_at.add 89 → Y.cpu.gpr.rax = s.add (4 * (j + 1)) → Y.cpu.gpr.rcx = X.cpu.gpr.rcx →
      Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (ke : j + 1 = n → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Nm bT V s (j + 1)) →
      Y.cpu.rip = nus_at.add 111 → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hel : rdd(Nm bT V s j, X.cpu.gpr.rax) = el V s j := by
    rw [hra]
    exact Nm_self bT V s (Nat.le_refl _) (by omega)
  have hf1 : ∀ b < 4, Foot F.data (Addr.add X.cpu.gpr.rax b) := fun b hb => by
    rw [hra]
    exact hf j hj b hb
  refine (c_89 prof).run c hin _ hK hA hrip (vc_89 hf1) ?_
  rintro j' g fl V' ⟨rfl, hga, hgc, hkp, hj'⟩ Y t₁ hKY hAY hrY hgY -
  subst hgY
  rw [hel] at hj'
  have hra' : Y.cpu.gpr.rax = s.add (4 * j) := hga.trans hra
  have hrc' : Y.cpu.gpr.rcx = s.add (4 * n) := hgc.trans hrc
  have a4 : Y.cpu.gpr.rax + 4#64 = s.add (4 * (j + 1)) := by rw [hra', add4j]
  rcases hj' with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
  · have hw1 : ∀ b < 4, Foot Wl (Addr.add Y.cpu.gpr.rax b) := fun b hb' => by
      rw [hra']
      exact hw j hj b hb'
    have hN : Nm bT V s (j + 1) = Vst (Nm bT V s j) Y.cpu.gpr.rax u95 := by rw [Nm_succ, if_pos hb, hra']
    by_cases hl : j + 1 = n
    · have he : Y.cpu.gpr.rax + 4#64 = Y.cpu.gpr.rcx := by rw [a4, hrc', hl]
      refine (c_96 prof).run c hin _ hKY hAY hrY (vc_96e he hw1) ?_
      rintro j' g fl' V' ⟨rfl, hkp', rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      exact ke hl Z t₂ hKZ (by rw [hN]; exact hAZ) hrZ (hkp.trans (Kp.of_eq hgZ hkp'))
    · have he : Y.cpu.gpr.rax + 4#64 ≠ Y.cpu.gpr.rcx := by
        rw [a4, hrc']
        exact add_ne' s (by omega) (by omega) (by omega)
      refine (c_96 prof).run c hin _ hKY hAY hrY (vc_96c he hw1) ?_
      rintro j' g fl' V' ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      refine kc (by omega) Z t₂ hKZ (by rw [hN]; exact hAZ) hrZ ?_ ?_ (hkp.trans (kp_w hgZ))
      · rw [hgZ]
        exact a4
      · rw [hgZ]
        exact hgc
  · have hnb : ¬bT (el V s j) = true := by
      rw [hb]
      exact Bool.false_ne_true
    have hN : Nm bT V s (j + 1) = Nm bT V s j := by rw [Nm_succ, if_neg hnb]
    by_cases hl : j + 1 = n
    · have he : Y.cpu.gpr.rax + 4#64 = Y.cpu.gpr.rcx := by rw [a4, hrc', hl]
      refine (c_80 prof).run c hin _ hKY hAY hrY (vc_80e he) ?_
      rintro j' g fl' V' ⟨rfl, hkp', rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      exact ke hl Z t₂ hKZ (by rw [hN]; exact hAZ) hrZ (hkp.trans (Kp.of_eq hgZ hkp'))
    · have he : Y.cpu.gpr.rax + 4#64 ≠ Y.cpu.gpr.rcx := by
        rw [a4, hrc']
        exact add_ne' s (by omega) (by omega) (by omega)
      refine (c_80 prof).run c hin _ hKY hAY hrY (vc_80c he) ?_
      rintro j' g fl' V' ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      refine kc (by omega) Z t₂ hKZ (by rw [hN]; exact hAZ) hrZ ?_ ?_ (hkp.trans (kp_w hgZ))
      · rw [hgZ]
        exact a4
      · rw [hgZ]
        exact hgc

/-- The terminal-mode loop from 89 at the `j`-th of the `n` characters at `s`, the first `j` done, `rcx` the end as
at `g₀`: on to the `ret` at 111 with all `n` done (`Nm bT V s n`). By induction on the characters left. -/
theorem loop1 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n : Nat}
    (hn : n < 2 ^ 32) (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b)) {g₀ : Gprs} (hrc : g₀.rcx = s.add (4 * n))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Nm bT V s n) →
      Z.cpu.rip = nus_at.add 111 → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m + 1 = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Nm bT V s j) →
      X.cpu.rip = nus_at.add 89 → X.cpu.gpr.rax = s.add (4 * j) → X.cpu.gpr.rcx = g₀.rcx → Kp g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hra hrc' hkp
    refine step89 c hin hn (by omega) hf hw hK hA hrip hra (hrc'.trans hrc) (fun h => absurd h (by omega)) ?_
    intro hl Y t₁ hKY hAY hrY hkY
    rw [hl] at hAY
    exact k Y t₁ hKY hAY hrY (hkp.trans hkY)
  | succ m ih =>
    intro j hj X t hK hA hrip hra hrc' hkp
    refine step89 c hin hn (by omega) hf hw hK hA hrip hra (hrc'.trans hrc) ?_ (fun h => absurd h (by omega))
    intro hl Y t₁ hKY hAY hrY hYa hYc hkY
    exact ih (j + 1) (by omega) Y t₁ hKY hAY hrY hYa (hYc.trans hrc') (hkp.trans hkY)

/-- From 128 at the `j`-th of the `n` characters at `s` (`rax`), `rdx` the end, the first `j` done: on to 128 at the
next or to the `ret` at 148 after the last, the first `j + 1` done. -/
theorem step128 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n j : Nat}
    (hn : n < 2 ^ 32) (hj : j < n) (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b)) {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem (Nm bN V s j)) (hrip : X.cpu.rip = nus_at.add 128)
    (hra : X.cpu.gpr.rax = s.add (4 * j)) (hrd : X.cpu.gpr.rdx = s.add (4 * n))
    (kc : j + 1 < n → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Nm bN V s (j + 1)) →
      Y.cpu.rip = nus_at.add 128 → Y.cpu.gpr.rax = s.add (4 * (j + 1)) → Y.cpu.gpr.rdx = X.cpu.gpr.rdx →
      Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (ke : j + 1 = n → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Nm bN V s (j + 1)) →
      Y.cpu.rip = nus_at.add 148 → Kp X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have hel : rdd(Nm bN V s j, X.cpu.gpr.rax) = el V s j := by
    rw [hra]
    exact Nm_self bN V s (Nat.le_refl _) (by omega)
  have hf1 : ∀ b < 4, Foot F.data (Addr.add X.cpu.gpr.rax b) := fun b hb => by
    rw [hra]
    exact hf j hj b hb
  have hw1 : ∀ b < 4, Foot Wl (Addr.add X.cpu.gpr.rax b) := fun b hb => by
    rw [hra]
    exact hw j hj b hb
  have a4 : X.cpu.gpr.rax + 4#64 = s.add (4 * (j + 1)) := by rw [hra, add4j]
  have k139 : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Nm bN V s (j + 1)) →
      Y.cpu.rip = nus_at.add 139 → Y.cpu.gpr = X.cpu.gpr → GoG prof L o gev gP gE Y t' := by
    intro Y t₁ hKY hAY hrY hgY
    have hkY : Kp X.cpu.gpr Y.cpu.gpr := Kp.of_eq hgY (Kp.refl _)
    by_cases hl : j + 1 = n
    · have he : Y.cpu.gpr.rax + 4#64 = Y.cpu.gpr.rdx := by rw [hgY, a4, hrd, hl]
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139e he) ?_
      rintro j' g fl' V' ⟨rfl, hkp', rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      exact ke hl Z t₂ hKZ hAZ hrZ (hkY.trans (Kp.of_eq hgZ hkp'))
    · have he : Y.cpu.gpr.rax + 4#64 ≠ Y.cpu.gpr.rdx := by
        rw [hgY, a4, hrd]
        exact add_ne' s (by omega) (by omega) (by omega)
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139c he) ?_
      rintro j' g fl' V' ⟨rfl, rfl, rfl⟩ Z t₂ hKZ hAZ hrZ hgZ -
      refine kc (by omega) Z t₂ hKZ hAZ hrZ ?_ ?_ (hkY.trans (kp_w hgZ))
      · rw [hgZ]
        show Y.cpu.gpr.rax + 4#64 = _
        rw [hgY]
        exact a4
      · rw [hgZ]
        show Y.cpu.gpr.rdx = _
        rw [hgY]
  by_cases hc : el V s j = 10#32
  · have hb : bN (el V s j) = true := decide_eq_true hc
    refine (c_128 prof).run c hin _ hK hA hrip (vc_128s (hel.trans hc) hf1 hw1) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine k139 Y t₁ hKY ?_ hrY hgY
    rw [Nm_succ, if_pos hb, ← hra]
    exact hAY
  · have hb : ¬bN (el V s j) = true := fun h => hc (of_decide_eq_true h)
    refine (c_128 prof).run c hin _ hK hA hrip (vc_128n (fun h => hc (hel.symm.trans h)) hf1) ?_
    rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine k139 Y t₁ hKY ?_ hrY hgY
    rw [Nm_succ, if_neg hb]
    exact hAY

/-- The other loop from 128 at the `j`-th of the `n` characters at `s`, the first `j` done, `rdx` the end as at
`g₀`: on to the `ret` at 148 with all `n` done (`Nm bN V s n`). By induction on the characters left. -/
theorem loop2 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {V : Addr → Byte} {s : Addr} {n : Nat}
    (hn : n < 2 ^ 32) (hf : ∀ i < n, ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b)) {g₀ : Gprs} (hrd : g₀.rdx = s.add (4 * n))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Nm bN V s n) →
      Z.cpu.rip = nus_at.add 148 → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m + 1 = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Nm bN V s j) →
      X.cpu.rip = nus_at.add 128 → X.cpu.gpr.rax = s.add (4 * j) → X.cpu.gpr.rdx = g₀.rdx →
      Kp g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hra hrd' hkp
    refine step128 c hin hn (by omega) hf hw hK hA hrip hra (hrd'.trans hrd) (fun h => absurd h (by omega)) ?_
    intro hl Y t₁ hKY hAY hrY hkY
    rw [hl] at hAY
    exact k Y t₁ hKY hAY hrY (hkp.trans hkY)
  | succ m ih =>
    intro j hj X t hK hA hrip hra hrd' hkp
    refine step128 c hin hn (by omega) hf hw hK hA hrip hra (hrd'.trans hrd) ?_ (fun h => absurd h (by omega))
    intro hl Y t₁ hKY hAY hrY hYa hYd hkY
    exact ih (j + 1) (by omega) Y t₁ hKY hAY hrY hYa (hYd.trans hrd') (hkp.trans hkY)

/-! ## The function -/

/-- `CStdOutStream::Normalize_UString (s)` from its entry: `rdi` the stream, `rsi` the `UString`, its characters at
`s` (`hs`), its length `n` (`hn`), the byte at `rdi + 8`, the pointer, the length and the characters data of the
footprint, the characters writable, apart from the return address: at the return address with the bytes `Res`, the
registers a call keeps (`Str.Back`). -/
theorem nus_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L nus_at nus) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = nus_at) {s : Addr} {n : Nat}
    (hs : rdq(V, X.cpu.gpr.rsi) = s) (hn : (rdd(V, X.cpu.gpr.rsi + 8#64)).toNat = n)
    (hp1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hps : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hpl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsi + 8#64) i))
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
    exact BitVec.isLt _
  have hra' : rdq(Res V X.cpu.gpr.rdi s n, X.cpu.gpr.rsp) = e₂.add j₂ := by
    by_cases ht : tmB V X.cpu.gpr.rdi = 0#8
    · rw [res_n ht, Nm_far bN V s hsr]
      exact hra
    · rw [res_t ht, Nm_far bT V s hsr]
      exact hra
  have kr : ∀ jr, jr < 149 → (∀ feat, Dec feat nus jr (FV7z.mk .ret 64 [] 1)) → ∀ (Z : State) (t' : Nat),
      KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Res V X.cpu.gpr.rdi s n) → Z.cpu.rip = nus_at.add jr →
      Kp X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t' :=
    fun jr hj hd Z t' hKZ hAZ hrZ hkp =>
      ret_back c hin (lt_len hj) (hd _) hKZ hAZ hrZ hkp hl hin₂ h₂ hra'
        fun Z' t'' hK' hA' hr' hb _ => k Z' t'' hK' hA' hr' hb
  have hrip' : X.cpu.rip = nus_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : rdd(V, X.cpu.gpr.rsi + 8#64) = 0#32 := BitVec.eq_of_toNat_eq (by rw [hn]; all_goals rfl)
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0z hp1 hps hpl h0) ?_
    rintro j' g fl V' ⟨rfl, hkp, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    exact kr 148 (by decide) ret_148 Z t₁ hKZ (by rw [res_zero]; exact hAZ) hrZ (Kp.of_eq hgZ hkp)
  have hc : (rdd(V, X.cpu.gpr.rsi + 8#64)).toNat ≠ 0 := by rw [hn]; exact hn0
  have h0 : rdd(V, X.cpu.gpr.rsi + 8#64) ≠ 0#32 := fun h => hc (by rw [h]; all_goals rfl)
  have hend : endT s rdd(V, X.cpu.gpr.rsi + 8#64) = s.add (4 * n) := by rw [endT_eq s _ hc, hn]
  by_cases ht : tmB V X.cpu.gpr.rdi = 0#8
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0n hs hp1 hps hpl h0 ht) ?_
    rintro j' g fl V' ⟨rfl, hga, hgd, hkp, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst hgZ
    refine loop2 c hin hn32 hf hw (g₀ := Z.cpu.gpr) (hgd.trans hend) ?_ (n - 1) 0 (by omega) Z t₁ hKZ hAZ hrZ
      (by rw [hga, Nat.mul_zero, addr_add_zero]) rfl (Kp.refl _)
    intro Z' t' hK' hA' hr' hkp'
    exact kr 148 (by decide) ret_148 Z' t' hK' (by rw [res_n ht]; exact hA') hr' (hkp.trans hkp')
  · refine (c_0 prof).run c hin _ hK hA hrip' (vc_0t hs hp1 hps hpl h0 ht) ?_
    rintro j' g fl V' ⟨rfl, hga, hgc, hkp, rfl⟩ Z t₁ hKZ hAZ hrZ hgZ -
    subst hgZ
    refine loop1 c hin hn32 hf hw (g₀ := Z.cpu.gpr) (hgc.trans hend) ?_ (n - 1) 0 (by omega) Z t₁ hKZ hAZ hrZ
      (by rw [hga, Nat.mul_zero, addr_add_zero]) rfl (Kp.refl _)
    intro Z' t' hK' hA' hr' hkp'
    exact kr 111 (by decide) ret_111 Z' t' hK' (by rw [res_t ht]; exact hA') hr' (hkp.trans hkp')

end FV7z.Nus
