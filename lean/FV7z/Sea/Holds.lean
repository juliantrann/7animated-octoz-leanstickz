import FV7z.Sea.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
/-!
# `StringsAreEqual_Ascii (const wchar_t *u, const char *a)` (PLAN.md §M, M1)

7-Zip 26.06's `StringsAreEqual_Ascii (const wchar_t *u, const char *a)` at `0x44bb60` in `7zzs`
(`CPP/Common/MyString.cpp`): 1 if each element of `u` is the byte of `a` at its index, zero-extended, up to and with
the 0 of `a`; else 0, at the first index where they differ. The loop's head is the cut point 40 (`test dl, dl`), `rax`
the index, `dl` the byte of `a` there; the `ret`s are at 49 (`eax` 1) and, after `xor eax, eax` at 56, at 58.

- `Eqs`: the answer for the `na` bytes not 0 and a 0 of `a`.
- `vc_0e`, `vc_0n`: from the entry, `u[0] = a[0]` (to 40 with index 0) or not (to 56); `vc_40z`, `vc_40e`,
  `vc_40n`: the loop, at the 0 of `a` (to the `ret` at 49), the next ones equal (back to 40) or not (to 56); `vc_56`.
- `loop`: from 40, by induction on the bytes left; `sea_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Sea

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_49 : pret <+: sea.drop 49 := by decide +kernel
theorem w_58 : pret <+: sea.drop 58 := by decide +kernel
theorem ret_at (feat : Features) {jr : Nat} (h : jr = 49 ∨ jr = 58) : Dec feat sea jr (FV7z.mk .ret 64 [] 1) := by
  rcases h with rfl | rfl
  · exact Dec.shift (j := 49) (k := 0) (pret_0 feat) w_49 (Nat.zero_le _)
  · exact Dec.shift (j := 58) (k := 0) (pret_0 feat) w_58 (Nat.zero_le _)
theorem ret_lt {jr : Nat} (h : jr = 49 ∨ jr = 58) : jr < sea.length :=
  lt_len (by rcases h with rfl | rfl <;> decide)

/-- The `i`-th element of the `wchar_t` string at `u`. -/
abbrev el (V : Addr → Byte) (u : Addr) (i : Nat) : BitVec 32 := rdd(V, u.add (4 * i))

/-- The answer for `a` (`na` bytes not 0 and a 0) and `u`: 1 if the elements of `u` up to `na` are the bytes of `a`
zero-extended, else 0. -/
def Eqs (V : Addr → Byte) (u a : Addr) (na : Nat) (r : BitVec 64) : Prop :=
  ((∀ i, i ≤ na → el V u i = BitVec.setWidth 32 (V (a.add i))) ∧ r = 1#64) ∨
    ((∃ i, i ≤ na ∧ el V u i ≠ BitVec.setWidth 32 (V (a.add i))) ∧ r = 0)

/-- `eax = 1`, zero-extended. -/
theorem one_64 : BitVec.setWidth 64 1#32 = 1#64 := by decide

/-- The element's address `rdi + (rax + 1) * 4` at the index `i`: `u + 4 (i + 1)`. -/
theorem idx4 (u : Addr) (i : Nat) : u + (BitVec.ofNat 64 i + 1#64) * 4#64 = u.add (4 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow]
  omega

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `u[0] = a[0]`, to 40 with `eax` 0 and `edx` `a[0]`. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 32 (V g.rsi) = rdd(V, g.rdi))
    (hf1 : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) (hf4 : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧
      g'.rax = BitVec.setWidth 64 (BitVec.setWidth 32 (V g.rsi) ^^^ BitVec.setWidth 32 (V g.rsi)) ∧
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (V g.rsi)) ∧ g'.rsi = g.rsi ∧ g'.rdi = g.rdi ∧ Kp g g' ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf1 hf4 ⊢
  have d := decide_eq_true h
  wpx [W_0, W_13, o0, o1, Tun.rd1, d, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals first | exact ⟨hf1, hf4⟩ | exact ⟨hf1, hf4, trivial⟩ | exact ⟨hf1, hf4, fun _ => trivial⟩ | done

/-- From the entry: `u[0] ≠ a[0]`, to 56. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ BitVec.setWidth 32 (V g.rsi) = rdd(V, g.rdi))
    (hf1 : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) (hf4 : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 56 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf1 hf4 ⊢
  have d := decide_eq_false h
  wpx [W_0, W_13, o0, o1, Tun.rd1, d, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals first | exact ⟨hf1, hf4⟩ | exact ⟨hf1, hf4, trivial⟩ | done

/-- The loop at the 0 of `a`: to the `ret` at 49 with `eax` 1. -/
theorem vc_40z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 8 g.rdx == 0) = true) :
    W_40 F Wl (fun j' g' _ V' => j' = 49 ∧ g'.rax = 1#64 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  wpx [W_40, W_24, W_44, o2, o3, o4, Tun.rd1, BitVec.and_self, hz, Kp, one_64, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | trivial | exact fun _ => trivial | done

/-- The loop, the next ones equal: back to 40 with the index one on. -/
theorem vc_40e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 8 g.rdx == 0) = false)
    (hf1 : ∀ i < 1, Foot F.data (Addr.add (g.rsi + g.rax + 1#64) i))
    (hf4 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + (g.rax + 1#64) * 4#64) i))
    (h : BitVec.setWidth 32 (V (g.rsi + g.rax + 1#64)) = rdd(V, g.rdi + (g.rax + 1#64) * 4#64)) :
    W_40 F Wl (fun j' g' _ V' => j' = 40 ∧ g'.rax = g.rax + 1#64 ∧
      g'.rdx = BitVec.setWidth 64 (BitVec.setWidth 32 (V (g.rsi + g.rax + 1#64))) ∧ g'.rsi = g.rsi ∧
      g'.rdi = g.rdi ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf1 hf4 h ⊢
  have d := decide_eq_true h
  wpx [W_40, W_24, W_44, o2, o3, o4, Tun.rd1, BitVec.and_self, hz, d, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | exact fun _ => ⟨hf1, hf4⟩ | exact ⟨hf1, hf4⟩ | exact fun _ => ⟨hf1, hf4, trivial⟩ | done

/-- The loop, the next ones not equal: to 56. -/
theorem vc_40n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 8 g.rdx == 0) = false)
    (hf1 : ∀ i < 1, Foot F.data (Addr.add (g.rsi + g.rax + 1#64) i))
    (hf4 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + (g.rax + 1#64) * 4#64) i))
    (h : ¬ BitVec.setWidth 32 (V (g.rsi + g.rax + 1#64)) = rdd(V, g.rdi + (g.rax + 1#64) * 4#64)) :
    W_40 F Wl (fun j' g' _ V' => j' = 56 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf1 hf4 h ⊢
  have d := decide_eq_false h
  wpx [W_40, W_24, W_44, o2, o3, o4, Tun.rd1, BitVec.and_self, hz, d, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | exact fun _ => ⟨hf1, hf4⟩ | exact ⟨hf1, hf4⟩ | exact fun _ => ⟨hf1, hf4, trivial⟩ | done

/-- At 56: `eax` 0, to the `ret` at 58. -/
theorem vc_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_56 F Wl (fun j' g' _ V' => j' = 58 ∧ g'.rax = 0 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_56, o1, lf_xz, Kp, eq_self_iff_true, and_self, and_true, implies_true]
  all_goals first | trivial | exact fun _ => trivial | done

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 56 to the `ret` at 58 with `rax` 0. -/
theorem at56 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sea_at sea) {V : Addr → Byte} {g₀ : Gprs} {X : State}
    {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sea_at.add 56)
    (hkp : Kp g₀ X.cpu.gpr)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = sea_at.add 58 →
      Kp g₀ Z.cpu.gpr → Z.cpu.gpr.rax = 0 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_56 prof).run c hin _ hK hA hrip vc_56 ?_
  rintro j' g fl V₁ ⟨rfl, hax, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp')) (by rw [hgY]; exact hax)

/-- The loop from 40 at the index `j` of `a` (`na` bytes not 0 and a 0), the elements of `u` up to `j` its bytes,
`dl` the byte at `j`: on to a `ret` (49 or 58) with `rax` the answer (`Eqs`), the registers a call keeps as at
`g₀`. By induction on `na - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sea_at sea) {V : Addr → Byte} {u a : Addr} {na : Nat}
    {g₀ : Gprs} (hna : na < 2 ^ 61) (hnz : ∀ i < na, V (a.add i) ≠ 0) (hz : V (a.add na) = 0)
    (hf : ∀ i, i ≤ na → (∀ j < i, el V u j = BitVec.setWidth 32 (V (a.add j))) →
      Foot F.data (a.add i) ∧ ∀ b < 4, Foot F.data ((u.add (4 * i)).add b))
    (k : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = sea_at.add jr →
      (jr = 49 ∨ jr = 58) → Kp g₀ Z.cpu.gpr → Eqs V u a na Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = na → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = sea_at.add 40 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rsi = a → X.cpu.gpr.rdi = u →
      BitVec.setWidth 8 X.cpu.gpr.rdx = V (a.add j) →
      (∀ i, i ≤ j → el V u i = BitVec.setWidth 32 (V (a.add i))) → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hsi hdi hdx hm hkp
    have hjn : j = na := by omega
    subst hjn
    have hz' : (BitVec.setWidth 8 X.cpu.gpr.rdx == 0) = true := by rw [hdx, hz]; all_goals decide
    refine (c_40 prof).run c hin _ hK hA hrip (vc_40z hz') ?_
    rintro j' g fl V₁ ⟨rfl, hax', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact k Y t₁ 49 hKY hAY hrY (.inl rfl) (hkp.trans (Kp.of_eq hgY hkp')) (.inl ⟨hm, by rw [hgY]; exact hax'⟩)
  | succ m ih =>
    intro j hj X t hK hA hrip hax hsi hdi hdx hm hkp
    have hz' : (BitVec.setWidth 8 X.cpu.gpr.rdx == 0) = false := by
      rw [hdx]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have ea1 : X.cpu.gpr.rsi + X.cpu.gpr.rax + 1#64 = a.add (j + 1) := by rw [hsi, hax]; exact ptr_step a j 1
    have ea4 : X.cpu.gpr.rdi + (X.cpu.gpr.rax + 1#64) * 4#64 = u.add (4 * (j + 1)) := by
      rw [hdi, hax]; exact idx4 u j
    obtain ⟨fa, fu⟩ := hf (j + 1) (by omega) fun i hi => hm i (by omega)
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rax + 1#64) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea1]
      exact fa
    have hf4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + (X.cpu.gpr.rax + 1#64) * 4#64) i) := fun i hi => by
      rw [ea4]
      exact fu i hi
    by_cases he : el V u (j + 1) = BitVec.setWidth 32 (V (a.add (j + 1)))
    · refine (c_40 prof).run c hin _ hK hA hrip (vc_40e hz' hf1 hf4 (by rw [ea1, ea4]; exact he.symm)) ?_
      rintro j' g fl V₁ ⟨rfl, hax', hdx', hsi', hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (by rw [hgY, hsi', hsi]) (by rw [hgY, hdi', hdi]) ?_
        (fun i hi => ?_) (hkp.trans (Kp.of_eq hgY hkp'))
      · rw [hgY, hax', hax]
        exact (BitVec.ofNat_add j 1).symm
      · rw [hgY, hdx', ea1, sw8b]
      · rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hm i (by omega)
        · obtain rfl : i = j + 1 := by omega
          exact he
    · refine (c_40 prof).run c hin _ hK hA hrip
        (vc_40n hz' hf1 hf4 (fun e => he (by rw [ea1, ea4] at e; exact e.symm))) ?_
      rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
      exact at56 c hin hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp')) fun Z t₂ hKZ hAZ hrZ hkZ hax₀ =>
        k Z t₂ 58 hKZ hAZ hrZ (.inr rfl) hkZ (.inr ⟨⟨j + 1, by omega, he⟩, hax₀⟩)

/-- `StringsAreEqual_Ascii (u, a)` from its entry, `u` (`rdi`) and `a` (`rsi`, `na` bytes not 0 and a 0,
`na < 2 ^ 61`), the bytes of both at an index readable while those before are equal: at the return address with
`rax` the answer (`Eqs`), the registers a call keeps (`Str.Back`), the bytes as they were. -/
theorem sea_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sea_at sea) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sea_at) {na : Nat} (hna : na < 2 ^ 61)
    (hnz : ∀ i < na, V (Addr.add X.cpu.gpr.rsi i) ≠ 0) (hz : V (Addr.add X.cpu.gpr.rsi na) = 0)
    (hf : ∀ i, i ≤ na →
      (∀ j < i, el V X.cpu.gpr.rdi j = BitVec.setWidth 32 (V (Addr.add X.cpu.gpr.rsi j))) →
      Foot F.data (Addr.add X.cpu.gpr.rsi i) ∧ ∀ b < 4, Foot F.data ((Addr.add X.cpu.gpr.rdi (4 * i)).add b))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Str.Back X.cpu.gpr Z.cpu.gpr → Eqs V X.cpu.gpr.rdi X.cpu.gpr.rsi na Z.cpu.gpr.rax →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have kr : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = sea_at.add jr → (jr = 49 ∨ jr = 58) → Kp X.cpu.gpr Z.cpu.gpr →
      Eqs V X.cpu.gpr.rdi X.cpu.gpr.rsi na Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t' :=
    fun Z t' jr hKZ hAZ hrZ hjr hkp hr =>
      ret_back c hin (ret_lt hjr) (ret_at _ hjr) hKZ hAZ hrZ hkp hl hin₂ h₂ hra fun Z' t'' hK' hA' hr' hb hax =>
        k Z' t'' hK' hA' hr' hb (by rw [hax]; exact hr)
  obtain ⟨fa, fu⟩ := hf 0 (Nat.zero_le _) fun j hj => absurd hj (Nat.not_lt_zero _)
  have e0 : el V X.cpu.gpr.rdi 0 = rdd(V, X.cpu.gpr.rdi) := by
    show rdd(V, Addr.add X.cpu.gpr.rdi (4 * 0)) = _
    rw [Nat.mul_zero, addr_add_zero]
  have a0 : Addr.add X.cpu.gpr.rsi 0 = X.cpu.gpr.rsi := addr_add_zero _
  have hf1 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => by
    obtain rfl : i = 0 := by omega
    exact fa
  have hf4 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
    have h := fu i hi
    rwa [Nat.mul_zero, addr_add_zero] at h
  have hrip0 : X.cpu.rip = sea_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases he0 : rdd(V, X.cpu.gpr.rdi) = BitVec.setWidth 32 (V X.cpu.gpr.rsi)
  · refine (c_0 prof).run c hin _ hK hA hrip0 (vc_0e he0.symm hf1 hf4) ?_
    rintro j' g fl V₁ ⟨rfl, hax', hdx', hsi', hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine loop c hin hna hnz hz hf kr na 0 (Nat.zero_add na) Y t₁ hKY hAY hrY ?_ (by rw [hgY, hsi'])
      (by rw [hgY, hdi']) ?_ (fun i hi => ?_) (Kp.of_eq hgY hkp')
    · rw [hgY, hax', lf_xz]
      all_goals rfl
    · rw [hgY, hdx', sw8b, a0]
    · obtain rfl : i = 0 := by omega
      rw [e0, a0]
      exact he0
  · refine (c_0 prof).run c hin _ hK hA hrip0 (vc_0n (fun e => he0 e.symm) hf1 hf4) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact at56 c hin hKY hAY hrY (Kp.of_eq hgY hkp') fun Z t₂ hKZ hAZ hrZ hkZ hax₀ =>
      kr Z t₂ 58 hKZ hAZ hrZ (.inr rfl) hkZ (.inr ⟨⟨0, Nat.zero_le _, fun e => he0 (by rw [← e0, e, a0])⟩, hax₀⟩)

end FV7z.Sea
