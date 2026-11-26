import FV7z.Rfp.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
/-!
# `AString::ReverseFind_PathSepar () const` (PLAN.md §M, M1)

7-Zip 26.06's `AString::ReverseFind_PathSepar () const` at `0x44cb50` in `7zzs` (`CPP/Common/MyString.cpp`): the
index of the last `'/'` (47) among the `_len` bytes at `_chars`, else -1; `_chars` is at `this + 0` (8 bytes) and
`_len` at `this + 8` (4 bytes). The loop's head is the cut point 41 (`cmp rdx, rax`), `rax` one past the byte to look
at next, `rdx` `_chars`. The `ret`s are at 51 (`eax` -1, after 46) and 58 (`eax = p - _chars`, after 56).

- `RPos`: the answer for `n` bytes at `c`.
- `vc_0z`, `vc_0e`, `vc_0n`: from the entry, `_len` 0 (to 46), the last byte `'/'` (to 56) or not (to 41);
  `vc_41z`, `vc_41e`, `vc_41n`: the loop, at `_chars` (to 46), the byte before `'/'` (to 56) or not (back to 41);
  `vc_46`, `vc_56`.
- `loop`: from 41, by induction on the index; `rfp_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Rfp

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_51 : pret <+: rfp.drop 51 := by decide +kernel
theorem w_58 : pret <+: rfp.drop 58 := by decide +kernel
theorem ret_at (feat : Features) {jr : Nat} (h : jr = 51 ∨ jr = 58) : Dec feat rfp jr (FV7z.mk .ret 64 [] 1) := by
  rcases h with rfl | rfl
  · exact Dec.shift (j := 51) (k := 0) (pret_0 feat) w_51 (Nat.zero_le _)
  · exact Dec.shift (j := 58) (k := 0) (pret_0 feat) w_58 (Nat.zero_le _)
theorem ret_lt {jr : Nat} (h : jr = 51 ∨ jr = 58) : jr < rfp.length :=
  lt_len (by rcases h with rfl | rfl <;> decide)

/-- The answer for the `n` bytes at `c`: the index of the last `'/'`, or -1 (as `rax` has it) if there is none. -/
def RPos (V : Addr → Byte) (c : Addr) (n : Nat) (r : BitVec 64) : Prop :=
  (∃ k, k < n ∧ V (c.add k) = 47#8 ∧ (∀ j, k < j → j < n → V (c.add j) ≠ 47#8) ∧ r = BitVec.ofNat 64 k) ∨
    ((∀ j < n, V (c.add j) ≠ 47#8) ∧ r = 4294967295#64)

/-- The last byte's address `_chars + _len - 1`. -/
theorem p_last (c : Addr) (len : BitVec 32) (h : len.toNat ≠ 0) :
    c + BitVec.setWidth 64 len + 18446744073709551615#64 = c.add (len.toNat - 1) := by
  have hl : len.toNat < 4294967296 := len.isLt
  have e : BitVec.setWidth 64 len = BitVec.ofNat 64 (len.toNat - 1) + 1#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  rw [e, BitVec.add_assoc, BitVec.add_assoc, show (1#64 : BitVec 64) + 18446744073709551615#64 = 0#64 by decide,
    BitVec.add_zero]
  all_goals exact ptr_add _ _

/-- The step back: `(c + (i + 1)) - 1 = c + i`. -/
theorem p_dec (c : Addr) (i : Nat) : c.add (i + 1) - 1#64 = c.add i := by
  show c + BitVec.ofNat 64 (i + 1) - 1#64 = c + BitVec.ofNat 64 i
  rw [← ptr_step c i 1]
  exact BitVec.add_sub_cancel _ _

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `_len` 0, to 46. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rdd(V, g.rdi + 8#64) == 0) = true)
    (hh4 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 46 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hh4 ⊢
  wpx [W_0, W_11, W_24, o0, o1, Tun.rd1, BitVec.and_self, hz, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | exact hh4 | exact ⟨hh4, fun _ => trivial⟩ | done

/-- The last byte's address, as the code has it. -/
abbrev plast (V : Addr → Byte) (r : BitVec 64) : Addr :=
  rdq(V, r) + BitVec.setWidth 64 rdd(V, r + 8#64) + 18446744073709551615#64

/-- From the entry: the last byte `'/'`, to 56 with `rax` at it and `rdx` `_chars`. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rdd(V, g.rdi + 8#64) == 0) = false)
    (hh4 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (hh8 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hp : ∀ i < 1, Foot F.data (Addr.add (plast V g.rdi) i)) (h : V (plast V g.rdi) = 47#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 56 ∧ g'.rax = plast V g.rdi ∧ g'.rdx = rdq(V, g.rdi) ∧ Kp g g' ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [plast] at hz hh4 hh8 hp h ⊢
  have d := decide_eq_true h
  wpx [W_0, W_11, W_24, o0, o1, Tun.rd1, BitVec.and_self, hz, d, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | exact ⟨hh4, fun _ => ⟨hh8, hp⟩⟩ | exact ⟨hh4, fun _ => ⟨hh8, hp, trivial⟩⟩ | done

/-- From the entry: the last byte not `'/'`, to 41 with `rax` at it and `rdx` `_chars`. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rdd(V, g.rdi + 8#64) == 0) = false)
    (hh4 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i)) (hh8 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hp : ∀ i < 1, Foot F.data (Addr.add (plast V g.rdi) i)) (h : ¬ V (plast V g.rdi) = 47#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 41 ∧ g'.rax = plast V g.rdi ∧ g'.rdx = rdq(V, g.rdi) ∧ Kp g g' ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [plast] at hz hh4 hh8 hp h ⊢
  have d := decide_eq_false h
  wpx [W_0, W_11, W_24, o0, o1, Tun.rd1, BitVec.and_self, hz, d, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | exact ⟨hh4, fun _ => ⟨hh8, hp⟩⟩ | exact ⟨hh4, fun _ => ⟨hh8, hp, trivial⟩⟩ | done

/-- The loop at `_chars`: to 46. -/
theorem vc_41z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : g.rdx = g.rax) :
    W_41 F Wl (fun j' g' _ V' => j' = 46 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  have d := decide_eq_true h
  wpx [W_41, W_32, o2, o3, Tun.rd1, d, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals first | trivial | exact fun _ => trivial | done

/-- The loop, the byte before `'/'`: to 56 with `rax` one back. -/
theorem vc_41e {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rdx = g.rax)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rax - 1#64) i)) (hs : V (g.rax - 1#64) = 47#8) :
    W_41 F Wl (fun j' g' _ V' => j' = 56 ∧ g'.rax = g.rax - 1#64 ∧ g'.rdx = g.rdx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf hs ⊢
  have d := decide_eq_false h
  have ds := decide_eq_true hs
  wpx [W_41, W_32, o2, o3, Tun.rd1, d, ds, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals first | exact hf | exact fun _ => hf | exact ⟨hf, trivial⟩ | done

/-- The loop, the byte before not `'/'`: back to 41 with `rax` one back. -/
theorem vc_41n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ g.rdx = g.rax)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rax - 1#64) i)) (hs : ¬ V (g.rax - 1#64) = 47#8) :
    W_41 F Wl (fun j' g' _ V' => j' = 41 ∧ g'.rax = g.rax - 1#64 ∧ g'.rdx = g.rdx ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf hs ⊢
  have d := decide_eq_false h
  have ds := decide_eq_false hs
  wpx [W_41, W_32, o2, o3, Tun.rd1, d, ds, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals first | exact hf | exact fun _ => hf | exact ⟨hf, trivial⟩ | done

/-- At 46: `eax` -1, to the `ret` at 51. -/
theorem vc_46 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_46 F Wl (fun j' g' _ V' => j' = 51 ∧ g'.rax = 4294967295#64 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_46, o4, m1_64, Kp, eq_self_iff_true, and_self, and_true, implies_true]
  all_goals first | trivial | exact fun _ => trivial | done

/-- At 56: `eax = rax - rdx` (32 bits), to the `ret` at 58. -/
theorem vc_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_56 F Wl (fun j' g' _ V' => j' = 58 ∧
      g'.rax = BitVec.setWidth 64 (BitVec.setWidth 32 g.rax - BitVec.setWidth 32 g.rdx) ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_56, o5, Kp, eq_self_iff_true, and_self, and_true, implies_true]
  all_goals first | trivial | exact fun _ => trivial | done

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 46 to the `ret` at 51 with `rax` -1. -/
theorem at46 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rfp_at rfp) {V : Addr → Byte} {g₀ : Gprs} {X : State}
    {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rfp_at.add 46)
    (hkp : Kp g₀ X.cpu.gpr)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = rfp_at.add 51 →
      Kp g₀ Z.cpu.gpr → Z.cpu.gpr.rax = 4294967295#64 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_46 prof).run c hin _ hK hA hrip vc_46 ?_
  rintro j' g fl V₁ ⟨rfl, hax, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp')) (by rw [hgY]; exact hax)

/-- From 56, `rax` at the index `i` of `c` and `rdx` `c`, to the `ret` at 58 with `rax` `i`. -/
theorem at56 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rfp_at rfp) {V : Addr → Byte} {g₀ : Gprs} {X : State}
    {t : Nat} {ch : Addr} {i : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = rfp_at.add 56) (hax : X.cpu.gpr.rax = ch.add i) (hdx : X.cpu.gpr.rdx = ch)
    (hi : i < 2 ^ 32) (hkp : Kp g₀ X.cpu.gpr)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = rfp_at.add 58 →
      Kp g₀ Z.cpu.gpr → Z.cpu.gpr.rax = BitVec.ofNat 64 i → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_56 prof).run c hin _ hK hA hrip vc_56 ?_
  rintro j' g fl V₁ ⟨rfl, hax', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
  refine k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp')) ?_
  rw [hgY, hax', hax, hdx]
  exact sub32_add ch hi

/-- The loop from 41, `rax` at the index `i + 1`... of the `n` bytes at `ch` (`i < n`), `rdx` `ch`, none of those
from `i` on `'/'`: on to a `ret` (51 or 58) with `rax` the answer (`RPos`), the registers a call keeps as at `g₀`.
By induction on `i`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rfp_at rfp) {V : Addr → Byte} {ch : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 32) (hf : ∀ i < n, Foot F.data (ch.add i))
    (k : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = rfp_at.add jr →
      (jr = 51 ∨ jr = 58) → Kp g₀ Z.cpu.gpr → RPos V ch n Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') :
    ∀ (i : Nat) (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = rfp_at.add 41 →
      X.cpu.gpr.rax = ch.add i → X.cpu.gpr.rdx = ch → i < n → (∀ j, i ≤ j → j < n → V (ch.add j) ≠ 47#8) →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro i
  induction i with
  | zero =>
    intro X t hK hA hrip hax hdx hin' hne hkp
    have h : X.cpu.gpr.rdx = X.cpu.gpr.rax := by rw [hdx, hax, addr_add_zero]
    refine (c_41 prof).run c hin _ hK hA hrip (vc_41z h) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact at46 c hin hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp')) fun Z t₂ hKZ hAZ hrZ hkZ hax₀ =>
      k Z t₂ 51 hKZ hAZ hrZ (.inl rfl) hkZ (.inr ⟨fun j hj => hne j (Nat.zero_le _) hj, hax₀⟩)
  | succ i ih =>
    intro X t hK hA hrip hax hdx hin' hne hkp
    have h : ¬ X.cpu.gpr.rdx = X.cpu.gpr.rax := by
      rw [hdx, hax]
      exact fun e => add_ne' ch (Nat.succ_ne_zero i) (by omega) (by omega) (by rw [addr_add_zero]; exact e.symm)
    have ea : X.cpu.gpr.rax - 1#64 = ch.add i := by rw [hax]; exact p_dec ch i
    have hf1 : ∀ j < 1, Foot F.data (Addr.add (X.cpu.gpr.rax - 1#64) j) := fun j hj => by
      obtain rfl : j = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf i (by omega)
    by_cases hs : V (ch.add i) = 47#8
    · refine (c_41 prof).run c hin _ hK hA hrip (vc_41e h hf1 (by rw [ea]; exact hs)) ?_
      rintro j' g fl V₁ ⟨rfl, hax', hdx', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
      exact at56 c hin hKY hAY hrY (by rw [hgY, hax', ea]) (by rw [hgY, hdx', hdx]) (by omega)
        (hkp.trans (Kp.of_eq hgY hkp')) fun Z t₂ hKZ hAZ hrZ hkZ hax₀ =>
          k Z t₂ 58 hKZ hAZ hrZ (.inr rfl) hkZ
            (.inl ⟨i, by omega, hs, fun j hij hjn => hne j (by omega) hjn, hax₀⟩)
    · refine (c_41 prof).run c hin _ hK hA hrip (vc_41n h hf1 (by rw [ea]; exact hs)) ?_
      rintro j' g fl V₁ ⟨rfl, hax', hdx', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ih Y t₁ hKY hAY hrY (by rw [hgY, hax', ea]) (by rw [hgY, hdx', hdx]) (by omega) (fun j h1 h2 => ?_)
        (hkp.trans (Kp.of_eq hgY hkp'))
      rcases Nat.lt_or_ge i j with h3 | h3
      · exact hne j (by omega) h2
      · obtain rfl : j = i := by omega
        exact hs

/-- `AString::ReverseFind_PathSepar ()` from its entry, `this` (`rdi`) with `_chars` (`rdq` at `this`) and `_len`
(`rdd` at `this + 8`), those and the `_len` bytes at `_chars` data of the footprint: at the return address with `rax`
the answer (`RPos`), the registers a call keeps (`Str.Back`), the bytes as they were. -/
theorem rfp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rfp_at rfp) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rfp_at)
    (hh8 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hh4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (hf : ∀ i < (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat, Foot F.data (Addr.add rdq(V, X.cpu.gpr.rdi) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Str.Back X.cpu.gpr Z.cpu.gpr →
      RPos V rdq(V, X.cpu.gpr.rdi) (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat Z.cpu.gpr.rax →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have kr : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = rfp_at.add jr → (jr = 51 ∨ jr = 58) → Kp X.cpu.gpr Z.cpu.gpr →
      RPos V rdq(V, X.cpu.gpr.rdi) (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat Z.cpu.gpr.rax →
      GoG prof L o gev gP gE Z t' :=
    fun Z t' jr hKZ hAZ hrZ hjr hkp hr =>
      ret_back c hin (ret_lt hjr) (ret_at _ hjr) hKZ hAZ hrZ hkp hl hin₂ h₂ hra fun Z' t'' hK' hA' hr' hb hax =>
        k Z' t'' hK' hA' hr' hb (by rw [hax]; exact hr)
  have hrip0 : X.cpu.rip = rfp_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hn : (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat < 2 ^ 32 := (rdd(V, X.cpu.gpr.rdi + 8#64)).isLt
  by_cases hz : rdd(V, X.cpu.gpr.rdi + 8#64) = 0
  · have hz' : (rdd(V, X.cpu.gpr.rdi + 8#64) == 0) = true := by rw [hz]; all_goals decide
    refine (c_0 prof).run c hin _ hK hA hrip0 (vc_0z hz' hh4) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact at46 c hin hKY hAY hrY (Kp.of_eq hgY hkp') fun Z t₂ hKZ hAZ hrZ hkZ hax₀ =>
      kr Z t₂ 51 hKZ hAZ hrZ (.inl rfl) hkZ (.inr ⟨fun j hj => by rw [hz] at hj; simp at hj, hax₀⟩)
  · have hz' : (rdd(V, X.cpu.gpr.rdi + 8#64) == 0) = false := beq_eq_false_iff_ne.2 hz
    have hn0 : (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat ≠ 0 := fun e => hz (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    have ep : plast V X.cpu.gpr.rdi = Addr.add rdq(V, X.cpu.gpr.rdi) ((rdd(V, X.cpu.gpr.rdi + 8#64)).toNat - 1) :=
      p_last _ _ hn0
    have hp : ∀ i < 1, Foot F.data (Addr.add (plast V X.cpu.gpr.rdi) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ep]
      exact hf _ (by omega)
    by_cases hs : V (Addr.add rdq(V, X.cpu.gpr.rdi) ((rdd(V, X.cpu.gpr.rdi + 8#64)).toNat - 1)) = 47#8
    · refine (c_0 prof).run c hin _ hK hA hrip0 (vc_0e hz' hh4 hh8 hp (by rw [ep]; exact hs)) ?_
      rintro j' g fl V₁ ⟨rfl, hax', hdx', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
      exact at56 c hin hKY hAY hrY (by rw [hgY, hax', ep]) (by rw [hgY, hdx']) (by omega) (Kp.of_eq hgY hkp')
        fun Z t₂ hKZ hAZ hrZ hkZ hax₀ => kr Z t₂ 58 hKZ hAZ hrZ (.inr rfl) hkZ
          (.inl ⟨_, by omega, hs, fun j h1 h2 => absurd h2 (by omega), hax₀⟩)
    · refine (c_0 prof).run c hin _ hK hA hrip0 (vc_0n hz' hh4 hh8 hp (by rw [ep]; exact hs)) ?_
      rintro j' g fl V₁ ⟨rfl, hax', hdx', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine loop c hin hn hf kr _ Y t₁ hKY hAY hrY (by rw [hgY, hax', ep]) (by rw [hgY, hdx']) (by omega)
        (fun j h1 h2 => ?_) (Kp.of_eq hgY hkp')
      obtain rfl : j = (rdd(V, X.cpu.gpr.rdi + 8#64)).toNat - 1 := by omega
      exact hs

end FV7z.Rfp
