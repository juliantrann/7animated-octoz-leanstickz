import FV7z.Dnw.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `DoesNameContainWildcard`: a `*` or `?` in a `UString` (PLAN.md §M, M1)

7-Zip's `DoesNameContainWildcard (const UString &path)` at `0x452940` in `7zzs` (`Common/Wildcard.cpp`;
`objdump -d`): the `UString` at `rdi` has its characters' pointer at `[rdi]` and its length (32 bits) at `[rdi + 8]`;
the characters are `wchar_t`s (32 bits). The code returns 0 at once (`xor eax, eax; ret` at 65) for the empty string;
else it puts the end (`p + 4·(len - 1) + 4`) in `rsi` and loops from 41: a `*` (42) or a `?` (63) returns with
`al` 1 (`ret` at 59); else one character on (32), and at the end the `ret` at 64 with `al` 0.

- `wcA V a`: the `wchar_t` at `a`; `isW`: `*` or `?`; `anyW V p n`: one of the `n` characters at `p` is.
- `vc_*`: the pieces from the cut points; `loop`: from 41 to a `ret` by induction on the characters left;
  `dnw_ok`: from the entry to the return address, `al` 1 if one of the characters is a wildcard, else 0.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Dnw

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_59 : pret <+: dnw.drop 59 := by decide +kernel
theorem w_64 : pret <+: dnw.drop 64 := by decide +kernel
theorem w_67 : pret <+: dnw.drop 67 := by decide +kernel
theorem ret_59 (feat : Features) : Dec feat dnw 59 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 59) (k := 0) (pret_0 feat) w_59 (Nat.zero_le _)
theorem ret_64 (feat : Features) : Dec feat dnw 64 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 64) (k := 0) (pret_0 feat) w_64 (Nat.zero_le _)
theorem ret_67 (feat : Features) : Dec feat dnw 67 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 67) (k := 0) (pret_0 feat) w_67 (Nat.zero_le _)

/-- The `wchar_t` at `a`, as the code loads it. -/
abbrev wcA (V : Addr → Byte) (a : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs a 4).map V)
/-- The string's length, at `s + 8`. -/
abbrev lenA (V : Addr → Byte) (s : Addr) : BitVec 32 := ofBytesLE 32 ((byteAddrs (s + 8#64) 4).map V)
/-- The characters' pointer, at `s`. -/
abbrev ptrA (V : Addr → Byte) (s : Addr) : Addr := ofBytesLE 64 ((byteAddrs s 8).map V)
/-- The end the code computes: `lea rsi, [rdx + rax·4 + 4]`, `eax` the length less 1. -/
abbrev endA (p : Addr) (c : BitVec 32) : Addr := p + (c - 1#32).setWidth 64 * 4#64 + 4#64

/-- A wildcard: `*` or `?`. -/
def isW (w : BitVec 32) : Bool := decide (w = 42#32) || decide (w = 63#32)
/-- One of the `n` characters at `p` is a wildcard. -/
def anyW (V : Addr → Byte) (p : Addr) : Nat → Bool
  | 0 => false
  | k + 1 => anyW V p k || isW (wcA V (p + BitVec.ofNat 64 (4 * k)))

theorem isW_true {w : BitVec 32} (h : isW w = true) : w = 42#32 ∨ w = 63#32 := by
  simpa [isW] using h

theorem isW_false {w : BitVec 32} (h : isW w = false) : w ≠ 42#32 ∧ w ≠ 63#32 := by
  simpa [isW] using h

theorem anyW_mono {V : Addr → Byte} {p : Addr} {k : Nat} (h : anyW V p k = true) :
    ∀ n, k ≤ n → anyW V p n = true := by
  intro n
  induction n with
  | zero =>
    intro hk
    obtain rfl : k = 0 := by omega
    exact h
  | succ n ih =>
    intro hk
    by_cases e : k = n + 1
    · subst e
      exact h
    · simp only [anyW, Bool.or_eq_true]
      exact Or.inl (ih (by omega))

/-- The end is `4·len` on. -/
theorem endA_eq (p : Addr) (c : BitVec 32) (hc : c ≠ 0#32) :
    endA p c = p + BitVec.ofNat 64 (4 * c.toNat) := by
  have h1 : c.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
  have h2 := c.isLt
  unfold endA
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.reducePow] at h2 ⊢
  omega

/-- One character on: `add rdx, 4`. -/
theorem adv4 (p : Addr) (k : Nat) : p + BitVec.ofNat 64 (4 * k) + 4#64 = p + BitVec.ofNat 64 (4 * (k + 1)) := by
  have e : 4 * (k + 1) = 4 * k + 4 := by omega
  rw [e, BitVec.ofNat_add, BitVec.add_assoc]

/-- The end is reached after the last character, not before. -/
theorem atEnd (p : Addr) (c : BitVec 32) (hc : c ≠ 0#32) {k : Nat} (hk : k < c.toNat) :
    p + BitVec.ofNat 64 (4 * k) + 4#64 = endA p c ↔ k + 1 = c.toNat := by
  have h2 := c.isLt
  rw [endA_eq p c hc, adv4, BitVec.add_right_inj]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.reducePow] at h' h2
    omega
  · intro h
    rw [h]

theorem z0 (p : Addr) : p + BitVec.ofNat 64 (4 * 0) = p := BitVec.add_zero p

/-- A low byte made of `wrLo`s (`setcc`, `or r8`), bit by bit: equal to a literal. -/
macro "lob" : tactic => `(tactic| (apply BitVec.eq_of_getLsbD_eq; intro i hi;
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i <;>
    simp (config := { decide := true }) [BitVec.getLsbD_ofNat, BitVec.shiftLeft_zero, *] at hi ⊢))

/-- `al ||| cl` with a 1 in `al` or `cl` is not 0: its bit 0. -/
macro "lo_ne" : tactic => `(tactic| (exfalso;
  have h0 := congrArg (fun x : BitVec 8 => x.getLsbD 0) (eq_of_beq ‹((_ : BitVec 8) == 0) = true›);
  simp (config := { decide := true }) [BitVec.getLsbD_ofNat, BitVec.shiftLeft_zero] at h0))

/-- `al ||| cl` with 0 in both is 0. -/
macro "lo_eq" : tactic => `(tactic| (exfalso; apply (beq_eq_false_iff_ne.1 ‹((_ : BitVec 8) == 0) = false›); lob))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry, the length 0: `eax` 0, to the `ret` (67). -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (h0 : lenA V g.rdi = 0#32) :
    W_0 F Wl (fun j' g' _ V' => j' = 67 ∧ g' = { g with rax := 0#64 } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [lenA] at fl h0 ⊢
  have hz : (ofBytesLE 32 ((byteAddrs (rdi + 8#64) 4).map V) == 0) = true := by rw [h0]; rfl
  wpx [W_0, W_11, W_65, o0, o1, o4, BitVec.and_self, hz, BitVec.xor_self, BitVec.reduceSetWidth,
    Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals repeat' (first | exact fl | exact rfl | exact trivial | apply And.intro | intro _)

/-- From the entry, the length not 0: the characters' pointer in `rdx`, the end in `rsi`, to the loop (41). -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (fl : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add g.rdi i)) (h0 : lenA V g.rdi ≠ 0#32) :
    W_0 F Wl (fun j' g' _ V' => j' = 41 ∧
      g' = { g with
        rax := (lenA V g.rdi - 1#32).setWidth 64, rdx := ptrA V g.rdi,
        rsi := endA (ptrA V g.rdi) (lenA V g.rdi) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [lenA, ptrA, endA] at fl fp h0 ⊢
  have hz : (ofBytesLE 32 ((byteAddrs (rdi + 8#64) 4).map V) == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_0, W_11, W_65, o0, o1, o4, BitVec.and_self, hz, BitVec.reduceSetWidth,
    Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true, Bool.not_false]
  all_goals repeat' (first | exact fl | exact fp | exact rfl | exact trivial | apply And.intro | intro _)

/-- From 41, the character a wildcard: to the `ret` at 59, `al` 1. -/
theorem vc_41w {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdx i))
    (h : wcA V g.rdx = 42#32 ∨ wcA V g.rdx = 63#32) :
    W_41 F Wl (fun j' g' _ V' => j' = 59 ∧
      (∃ ra rc, g' = { g with rax := ra, rcx := rc } ∧ ra.setWidth 8 = 1#8) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [wcA] at fa h ⊢
  have hb : (decide (ofBytesLE 32 ((byteAddrs rdx 4).map V) = 42#32) = true ∧
      decide (ofBytesLE 32 ((byteAddrs rdx 4).map V) = 63#32) = false) ∨
      (decide (ofBytesLE 32 ((byteAddrs rdx 4).map V) = 42#32) = false ∧
      decide (ofBytesLE 32 ((byteAddrs rdx 4).map V) = 63#32) = true) := by
    rcases h with h | h <;> rw [h] <;> decide
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  · wpx [W_41, W_32, o2, o3, Op.setcc, Op.or8, h1, h2, BitVec.ofBool_true, BitVec.ofBool_false,
      BitVec.reduceSetWidth, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true,
      Bool.not_false]
    all_goals repeat' (first | exact fa | exact rfl | exact trivial | apply And.intro | intro _)
    all_goals first
      | exact ⟨_, _, rfl, by lob⟩
      | lo_ne
      | (exfalso; simp_all)

/-- From 41, the character not a wildcard and the last: to the `ret` at 64, `al` 0, `rdx` one on. -/
theorem vc_41e {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdx i))
    (h : wcA V g.rdx ≠ 42#32 ∧ wcA V g.rdx ≠ 63#32) (he : g.rdx + 4#64 = g.rsi) :
    W_41 F Wl (fun j' g' _ V' => j' = 64 ∧
      (∃ ra rc, g' = { g with rax := ra, rcx := rc, rdx := g.rdx + 4#64 } ∧ ra.setWidth 8 = 0#8) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [wcA] at fa h he ⊢
  have h1 := decide_eq_false h.1
  have h2 := decide_eq_false h.2
  have h3 : decide (rdx + 4#64 = rsi) = true := decide_eq_true he
  wpx [W_41, W_32, o2, o3, Op.setcc, Op.or8, h1, h2, h3, BitVec.ofBool_true, BitVec.ofBool_false,
    BitVec.reduceSetWidth, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true,
    Bool.not_false]
  all_goals repeat' (first | exact fa | exact rfl | exact trivial | apply And.intro | intro _)
  all_goals first
    | exact ⟨_, _, rfl, by lob⟩
    | lo_eq
    | (exfalso; simp_all)

/-- From 41, the character not a wildcard and not the last: back to 41, `rdx` one on. -/
theorem vc_41c {g : Gprs} {f : Rflags} {V : Addr → Byte} (fa : ∀ i < 4, Foot F.data (Addr.add g.rdx i))
    (h : wcA V g.rdx ≠ 42#32 ∧ wcA V g.rdx ≠ 63#32) (he : g.rdx + 4#64 ≠ g.rsi) :
    W_41 F Wl (fun j' g' _ V' => j' = 41 ∧
      (∃ ra rc, g' = { g with rax := ra, rcx := rc, rdx := g.rdx + 4#64 }) ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [wcA] at fa h he ⊢
  have h1 := decide_eq_false h.1
  have h2 := decide_eq_false h.2
  have h3 : decide (rdx + 4#64 = rsi) = false := decide_eq_false he
  wpx [W_41, W_32, o2, o3, Op.setcc, Op.or8, h1, h2, h3, BitVec.ofBool_true, BitVec.ofBool_false,
    BitVec.reduceSetWidth, Bool.true_eq_false, Bool.false_eq_true, false_implies, implies_true, Bool.not_true,
    Bool.not_false]
  all_goals repeat' (first | exact fa | exact rfl | exact trivial | apply And.intro | intro _)
  all_goals first
    | exact ⟨_, _, rfl⟩
    | lo_eq
    | (exfalso; simp_all)

/-! ## The loop and the function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The registers at the `ret`s, from `g₀` at the entry: `rax`, `rcx`, `rdx` some values, `rsi` the end, `al` the
answer. -/
abbrev AtRet (g₀ : Gprs) (E : Addr) (b : Bool) (G : Gprs) : Prop :=
  ∃ ra rc rd, G = { g₀ with rax := ra, rcx := rc, rdx := rd, rsi := E } ∧ ra.setWidth 8 = if b then 1#8 else 0#8

/-- From 41 with `kk` characters seen (none a wildcard) and `m + 1` left: to the `ret` at 59 or 64 with the answer for
the `n` characters. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dnw_at dnw) {V : Addr → Byte} {p E : Addr} {n : Nat}
    {g₀ : Gprs} (fa : ∀ k < n, ∀ i < 4, Foot F.data (Addr.add (p + BitVec.ofNat 64 (4 * k)) i))
    (hE : ∀ k < n, p + BitVec.ofNat 64 (4 * k) + 4#64 = E ↔ k + 1 = n)
    (kx : ∀ (j : Nat), (j = 59 ∨ j = 64) → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = dnw_at.add j → AtRet g₀ E (anyW V p n) Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m kk : Nat), kk + m + 1 = n → anyW V p kk = false → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = dnw_at.add 41 →
      (∃ ra rc, X.cpu.gpr = { g₀ with rax := ra, rcx := rc, rdx := p + BitVec.ofNat 64 (4 * kk), rsi := E }) →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro kk hkk hno X t hK hA hrip ⟨ra, rc, hX⟩
    have hd : X.cpu.gpr.rdx = p + BitVec.ofNat 64 (4 * kk) := by rw [hX] <;> rfl
    have hs : X.cpu.gpr.rsi = E := by rw [hX] <;> rfl
    have fk : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdx i) := by rw [hd]; exact fa kk (by omega)
    cases hw : isW (wcA V (p + BitVec.ofNat 64 (4 * kk)))
    · have hnw := isW_false hw
      refine (c_41 prof).run c hin _ hK hA hrip
        (vc_41e fk (by rw [hd]; exact hnw) (by rw [hd, hs]; exact (hE kk (by omega)).2 (by omega))) ?_
      rintro j' g fl V' ⟨rfl, ⟨ra', rc', hg, h8⟩, hV'⟩ Y t₁ hKY hAY hrY hgY -
      subst V'
      refine kx 64 (Or.inr rfl) Y t₁ hKY hAY hrY ⟨ra', rc', X.cpu.gpr.rdx + 4#64, by rw [hgY, hg, hX] <;> rfl, ?_⟩
      have hn : anyW V p n = false := by
        rw [← show kk + 1 = n by omega]
        simp only [anyW, hno, hw, Bool.or_false]
      rw [hn, h8] <;> rfl
    · refine (c_41 prof).run c hin _ hK hA hrip (vc_41w fk (by rw [hd]; exact isW_true hw)) ?_
      rintro j' g fl V' ⟨rfl, ⟨ra', rc', hg, h8⟩, hV'⟩ Y t₁ hKY hAY hrY hgY -
      subst V'
      refine kx 59 (Or.inl rfl) Y t₁ hKY hAY hrY ⟨ra', rc', X.cpu.gpr.rdx, by rw [hgY, hg, hX] <;> rfl, ?_⟩
      have hn : anyW V p n = true := anyW_mono (k := kk + 1) (by simp only [anyW, hw, Bool.or_true]) n (by omega)
      rw [hn, h8] <;> rfl
  | succ m ih =>
    intro kk hkk hno X t hK hA hrip ⟨ra, rc, hX⟩
    have hd : X.cpu.gpr.rdx = p + BitVec.ofNat 64 (4 * kk) := by rw [hX] <;> rfl
    have hs : X.cpu.gpr.rsi = E := by rw [hX] <;> rfl
    have fk : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdx i) := by rw [hd]; exact fa kk (by omega)
    cases hw : isW (wcA V (p + BitVec.ofNat 64 (4 * kk)))
    · have hnw := isW_false hw
      have hne : X.cpu.gpr.rdx + 4#64 ≠ X.cpu.gpr.rsi := by
        rw [hd, hs]
        intro h
        have := (hE kk (by omega)).1 h
        omega
      refine (c_41 prof).run c hin _ hK hA hrip (vc_41c fk (by rw [hd]; exact hnw) hne) ?_
      rintro j' g fl V' ⟨rfl, ⟨ra', rc', hg⟩, hV'⟩ Y t₁ hKY hAY hrY hgY -
      subst V'
      refine ih (kk + 1) (by omega) (by simp only [anyW, hno, hw, Bool.or_false]) Y t₁ hKY hAY hrY
        ⟨ra', rc', ?_⟩
      rw [hgY, hg, hd, adv4, hX] <;> rfl
    · refine (c_41 prof).run c hin _ hK hA hrip (vc_41w fk (by rw [hd]; exact isW_true hw)) ?_
      rintro j' g fl V' ⟨rfl, ⟨ra', rc', hg, h8⟩, hV'⟩ Y t₁ hKY hAY hrY hgY -
      subst V'
      refine kx 59 (Or.inl rfl) Y t₁ hKY hAY hrY ⟨ra', rc', X.cpu.gpr.rdx, by rw [hgY, hg, hX] <;> rfl, ?_⟩
      have hn : anyW V p n = true := anyW_mono (k := kk + 1) (by simp only [anyW, hw, Bool.or_true]) n (by omega)
      rw [hn, h8] <;> rfl

/-- The `ret`s: from `Y` at a `ret` with the registers `G` (`rsp` as at the entry) to the return address. -/
theorem ret_k (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dnw_at dnw) {V : Addr → Byte} {X : State} {j : Nat}
    (hj : j < 68) (hd : Dec prof.feat dnw j (FV7z.mk .ret 64 [] 1)) {Y : State} {t' : Nat} (hKY : KeptW Wl s₀ Y)
    (hAY : Agree F Y.proc.mm.mem V) (hrY : Y.cpu.rip = dnw_at.add j) {G : Gprs} (hgY : Y.cpu.gpr = G)
    (hsp : G.rsp = X.cpu.gpr.rsp) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = G.set 4 (X.cpu.gpr.rsp + 8) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t' := by
  refine c.s_ret hKY hAY hin (lt_len hj) hrY hd (fun i hi => by rw [hgY, hsp]; exact hl i hi) hin₂ h₂
    (by rw [hgY, hsp]; exact hra) ?_
  rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₂ hKZ hAZ hrZ (by rw [hgZ, hgY, hsp])

/-- `DoesNameContainWildcard (path)` from its entry, the `UString` at `rdi` with its `n` characters at `p`: at the
return address, the return address popped, `al` 1 if one of the characters is `*` or `?` (`anyW`), else 0; the upper
bits of `rax`, `rcx`, `rdx`, `rsi` some values, the rest and the memory kept. -/
theorem dnw_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L dnw_at dnw) {V : Addr → Byte} {X : State} {t : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = dnw_at)
    (fl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fa : ∀ k < (lenA V X.cpu.gpr.rdi).toNat, ∀ i < 4,
      Foot F.data (Addr.add (ptrA V X.cpu.gpr.rdi + BitVec.ofNat 64 (4 * k)) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : ofBytesLE 64 ((byteAddrs X.cpu.gpr.rsp 8).map V) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ ra rc rd si, Z.cpu.gpr = Gprs.set { X.cpu.gpr with
        rax := ra, rcx := rc, rdx := rd, rsi := si } 4 (X.cpu.gpr.rsp + 8) ∧
        ra.setWidth 8 = if anyW V (ptrA V X.cpu.gpr.rdi) (lenA V X.cpu.gpr.rdi).toNat then 1#8 else 0#8) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hrip' : X.cpu.rip = dnw_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h0 : lenA V X.cpu.gpr.rdi = 0#32
  · -- the empty string
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0z fl h0) ?_
    rintro j' g fl' V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    refine ret_k c hin (by decide) (ret_67 _) hKY hAY hrY (hgY.trans hg) rfl hl hin₂ h₂ hra
      fun Z t₂ hKZ hAZ hrZ hgZ => k Z t₂ hKZ hAZ hrZ ⟨0#64, X.cpu.gpr.rcx, X.cpu.gpr.rdx, X.cpu.gpr.rsi, hgZ, ?_⟩
    rw [h0] <;> rfl
  · -- the loop
    refine (c_0 prof).run c hin _ hK hA hrip' (vc_0n fl fp h0) ?_
    rintro j' g fl' V' ⟨rfl, hg, hV'⟩ Y t₁ hKY hAY hrY hgY -
    subst V'
    have hn : 0 < (lenA V X.cpu.gpr.rdi).toNat := by
      rcases Nat.eq_zero_or_pos (lenA V X.cpu.gpr.rdi).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
      · exact h
    refine loop c hin fa (fun kk hk => atEnd _ _ h0 hk) (g₀ := X.cpu.gpr) ?_
      ((lenA V X.cpu.gpr.rdi).toNat - 1) 0 (by omega) rfl Y t₁ hKY hAY hrY
      ⟨(lenA V X.cpu.gpr.rdi - 1#32).setWidth 64, X.cpu.gpr.rcx, ?_⟩
    · intro j hj Z t₂ hKZ hAZ hrZ ⟨ra, rc, rd, hgZ, h8⟩
      have hd : Dec prof.feat dnw j (FV7z.mk .ret 64 [] 1) := by
        rcases hj with rfl | rfl
        · exact ret_59 _
        · exact ret_64 _
      have hj' : j < 68 := by omega
      exact ret_k c hin hj' hd hKZ hAZ hrZ hgZ rfl hl hin₂ h₂ hra
        fun Z' t₃ hKZ' hAZ' hrZ' hgZ' => k Z' t₃ hKZ' hAZ' hrZ' ⟨ra, rc, rd, _, hgZ', h8⟩
    · rw [z0, hgY, hg] <;> rfl

end FV7z.Dnw
