import FV7z.Fcw.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
/-!
# `FindCharPosInString (s, c)` for `wchar_t` (PLAN.md §M, M1)

7-Zip 26.06's `FindCharPosInString (const wchar_t *s, wchar_t c)` at `0x44b9a0` in `7zzs`
(`CPP/Common/MyString.cpp`): the index of the first `c` (4 bytes) in `s`, its 0 included, else -1. The loop's head
is the cut point 27 (`test edx, edx`), with `rax` at the element, `edx` that element and `esi` the character.

- `Pos`: the answer for a string of `n` elements not 0 and a 0.
- `vc_0e`, `vc_0n`: from the entry, `s[0] = c` (to the `ret` at 50 with 0) or not (to the loop at 27);
  `vc_27z`, `vc_27e`, `vc_27n`: the loop, at the 0 (to the `ret` at 36 with -1), the next element `c` (to the `ret`
  at 47 with its index, `(p - s) >> 2`), or not (back to 27).
- `loop`: from 27, by induction on the elements left; `fcw_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Fcw

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_36 : pret <+: fcw.drop 36 := by decide +kernel
theorem w_47 : pret <+: fcw.drop 47 := by decide +kernel
theorem w_50 : pret <+: fcw.drop 50 := by decide +kernel
theorem ret_at (feat : Features) {jr : Nat} (h : jr = 36 ∨ jr = 47 ∨ jr = 50) :
    Dec feat fcw jr (FV7z.mk .ret 64 [] 1) := by
  rcases h with rfl | rfl | rfl
  · exact Dec.shift (j := 36) (k := 0) (pret_0 feat) w_36 (Nat.zero_le _)
  · exact Dec.shift (j := 47) (k := 0) (pret_0 feat) w_47 (Nat.zero_le _)
  · exact Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)
theorem ret_lt {jr : Nat} (h : jr = 36 ∨ jr = 47 ∨ jr = 50) : jr < fcw.length :=
  lt_len (by rcases h with rfl | rfl | rfl <;> decide)

/-- The `i`-th element of the `wchar_t` string at `s`. -/
abbrev el (V : Addr → Byte) (s : Addr) (i : Nat) : BitVec 32 := rdd(V, s.add (4 * i))

/-- The answer for the `n` elements not 0 and a 0 at `s` and the character `c`: the index of the first `c`, the 0
included, or -1 (as `rax` has it) if there is none. -/
def Pos (V : Addr → Byte) (s : Addr) (c : BitVec 32) (n : Nat) (r : BitVec 64) : Prop :=
  (∃ k, k ≤ n ∧ (∀ i < k, el V s i ≠ c) ∧ el V s k = c ∧ r = BitVec.ofNat 64 k) ∨
    ((∀ i, i ≤ n → el V s i ≠ c) ∧ r = 4294967295#64)

/-- The step of the pointer: `(s + 4j) + 4 = s + 4(j + 1)`. -/
theorem step4 (s : Addr) (j : Nat) : s.add (4 * j) + 4#64 = s.add (4 * (j + 1)) := by
  rw [show 4 * (j + 1) = 4 * j + 4 by omega]
  exact ptr_step s (4 * j) 4

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `s[0] = c`, to the `ret` at 50 with `eax` 0. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 32 g.rsi = rdd(V, g.rdi))
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 50 ∧
      g' = { g with rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi ^^^ BitVec.setWidth 32 g.rdi),
                    rdx := BitVec.setWidth 64 rdd(V, g.rdi) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf ⊢
  have d := decide_eq_true h
  wpx [W_0, W_13, W_48, o0, o5, d, Bool.not_true, Bool.not_false, Bool.false_eq_true, false_implies,
    true_implies, implies_true, eq_self_iff_true]
  all_goals first | exact hf | exact ⟨hf, fun _ => trivial⟩ | exact ⟨hf, trivial⟩ |
    exact ⟨hf, fun _ => ⟨rfl, rfl, rfl⟩⟩ | done

/-- From the entry: `s[0] ≠ c`, to the loop's head with `rax = s`, `edx = s[0]`. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬ BitVec.setWidth 32 g.rsi = rdd(V, g.rdi))
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 27 ∧
      g' = { g with rax := g.rdi, rdx := BitVec.setWidth 64 rdd(V, g.rdi) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf ⊢
  have d := decide_eq_false h
  wpx [W_0, W_13, W_48, o0, o5, d, Bool.not_true, Bool.not_false, Bool.false_eq_true, false_implies,
    true_implies, implies_true, eq_self_iff_true]
  all_goals first | exact hf | exact ⟨hf, trivial⟩ | exact ⟨hf, ⟨rfl, rfl, rfl⟩⟩ | exact ⟨hf, rfl, rfl, rfl⟩ | done

/-- The loop at the 0: to the `ret` at 36 with `eax` -1. -/
theorem vc_27z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 32 g.rdx == 0) = true) :
    W_27 F Wl (fun j' g' _ V' => j' = 36 ∧ g' = { g with rax := BitVec.setWidth 64 4294967295#32 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  wpx [W_27, W_16, W_40, W_31, o1, o2, o3, o4, Op.sar64, BitVec.and_self, hz, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, false_implies, true_implies, implies_true, eq_self_iff_true]
  all_goals first | trivial | exact fun _ => trivial | exact fun _ => ⟨rfl, rfl, rfl⟩ | done

/-- The loop, the next element `c`: to the `ret` at 47 with its index. -/
theorem vc_27e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 32 g.rdx == 0) = false)
    (hf : ∀ i < 4, Foot F.data (Addr.add (g.rax + 4#64) i))
    (h : rdd(V, g.rax + 4#64) = BitVec.setWidth 32 g.rsi) :
    W_27 F Wl (fun j' g' _ V' => j' = 47 ∧
      g' = { g with rax := (g.rax + 4#64 - g.rdi).sshiftRight 2,
                    rdx := BitVec.setWidth 64 rdd(V, g.rax + 4#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf h ⊢
  have d := decide_eq_true h
  wpx [W_27, W_16, W_40, W_31, o1, o2, o3, o4, Op.sar64, BitVec.and_self, hz, d, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, false_implies, true_implies, implies_true, eq_self_iff_true]
  all_goals first | exact fun _ => hf | exact fun _ => ⟨hf, trivial⟩ | exact hf |
    exact fun _ => ⟨hf, fun _ => trivial⟩ | exact fun _ => ⟨hf, fun _ _ => ⟨rfl, rfl, rfl⟩⟩ |
    exact ⟨hf, fun _ _ => ⟨rfl, rfl, rfl⟩⟩ | done

/-- The loop, the next element not `c`: back to 27 with `rax` one on. -/
theorem vc_27n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 32 g.rdx == 0) = false)
    (hf : ∀ i < 4, Foot F.data (Addr.add (g.rax + 4#64) i))
    (h : ¬ rdd(V, g.rax + 4#64) = BitVec.setWidth 32 g.rsi) :
    W_27 F Wl (fun j' g' _ V' => j' = 27 ∧
      g' = { g with rax := g.rax + 4#64, rdx := BitVec.setWidth 64 rdd(V, g.rax + 4#64) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf h ⊢
  have d := decide_eq_false h
  wpx [W_27, W_16, W_40, W_31, o1, o2, o3, o4, Op.sar64, BitVec.and_self, hz, d, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, false_implies, true_implies, implies_true, eq_self_iff_true]
  all_goals first | exact fun _ => hf | exact fun _ => ⟨hf, trivial⟩ | exact hf |
    exact fun _ => ⟨hf, fun _ => trivial⟩ | exact fun _ => ⟨hf, ⟨rfl, rfl, rfl⟩⟩ | done

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The loop from 27 at the index `j` of the `n` elements not 0 and a 0 at `s`, none of the elements up to `j` the
character `ch` (`esi`), `edx` the element at `j`, `rax` its address: on to a `ret` (36, 47 or 50) with `rax` the
answer (`Pos`), the registers a call keeps as at `g₀`. By induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fcw_at fcw) {V : Addr → Byte} {s : Addr} {ch : BitVec 32}
    {n : Nat} {g₀ : Gprs} (hn : n < 2 ^ 31) (hnz : ∀ i < n, el V s i ≠ 0) (hz : el V s n = 0)
    (hf : ∀ i, i ≤ n → ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (k : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = fcw_at.add jr →
      (jr = 36 ∨ jr = 47 ∨ jr = 50) → Kp g₀ Z.cpu.gpr → Pos V s ch n Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = fcw_at.add 27 → X.cpu.gpr.rax = s.add (4 * j) → X.cpu.gpr.rdi = s →
      BitVec.setWidth 32 X.cpu.gpr.rdx = el V s j → BitVec.setWidth 32 X.cpu.gpr.rsi = ch →
      (∀ i, i ≤ j → el V s i ≠ ch) → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hdi hdx hsi hne hkp
    obtain rfl : j = n := by omega
    have hz' : (BitVec.setWidth 32 X.cpu.gpr.rdx == 0) = true := by rw [hdx, hz]; all_goals decide
    refine (c_27 prof).run c hin _ hK hA hrip (vc_27z hz') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine k Y t₁ 36 hKY hAY hrY (.inl rfl) (hkp.trans (kp_w hgY)) (.inr ⟨hne, ?_⟩)
    rw [hgY]
    exact m1_64
  | succ m ih =>
    intro j hj X t hK hA hrip hax hdi hdx hsi hne hkp
    have hj0 : el V s j ≠ 0 := hnz j (by omega)
    have hz' : (BitVec.setWidth 32 X.cpu.gpr.rdx == 0) = false := by rw [hdx]; exact beq_eq_false_iff_ne.2 hj0
    have ea : X.cpu.gpr.rax + 4#64 = s.add (4 * (j + 1)) := by rw [hax]; exact step4 s j
    have hf1 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rax + 4#64) i) := fun i hi => by
      rw [ea]
      exact hf (j + 1) (by omega) i hi
    have hb : rdd(V, X.cpu.gpr.rax + 4#64) = el V s (j + 1) := by rw [ea]
    by_cases he : el V s (j + 1) = ch
    · refine (c_27 prof).run c hin _ hK hA hrip (vc_27e hz' hf1 (by rw [hb, hsi]; exact he)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine k Y t₁ 47 hKY hAY hrY (.inr (.inl rfl)) (hkp.trans (kp_w hgY))
        (.inl ⟨j + 1, by omega, fun i hi => hne i (by omega), he, ?_⟩)
      rw [hgY]
      show (X.cpu.gpr.rax + 4#64 - X.cpu.gpr.rdi).sshiftRight 2 = _
      rw [ea, hdi]
      exact sar_sub4 s (by omega)
    · refine (c_27 prof).run c hin _ hK hA hrip (vc_27n hz' hf1 (by rw [hb, hsi]; exact he)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY (by rw [hgY]; exact ea) (by rw [hgY]; exact hdi) ?_
        (by rw [hgY]; exact hsi) (fun i hi => ?_) (hkp.trans (kp_w hgY))
      · rw [hgY]
        show BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rax + 4#64)) = _
        rw [sw32, hb]
      · rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hne i (by omega)
        · obtain rfl : i = j + 1 := by omega
          exact he

/-- `FindCharPosInString (s, c)` from its entry, `s` (`rdi`) `n` elements not 0 and a 0 (`n < 2 ^ 31`), their bytes
data of the footprint: at the return address with `rax` the answer (`Pos`, `c` the low 32 bits of `rsi`), the
registers a call keeps (`Str.Back`), the bytes as they were. -/
theorem fcw_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fcw_at fcw) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fcw_at) {n : Nat} (hn : n < 2 ^ 31)
    (hnz : ∀ i < n, el V X.cpu.gpr.rdi i ≠ 0) (hz : el V X.cpu.gpr.rdi n = 0)
    (hf : ∀ i, i ≤ n → ∀ b < 4, Foot F.data ((X.cpu.gpr.rdi.add (4 * i)).add b))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Str.Back X.cpu.gpr Z.cpu.gpr → Pos V X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) n Z.cpu.gpr.rax →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have kr : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = fcw_at.add jr → (jr = 36 ∨ jr = 47 ∨ jr = 50) → Kp X.cpu.gpr Z.cpu.gpr →
      Pos V X.cpu.gpr.rdi (BitVec.setWidth 32 X.cpu.gpr.rsi) n Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t' :=
    fun Z t' jr hKZ hAZ hrZ hjr hkp hpos =>
      ret_back c hin (ret_lt hjr) (ret_at _ hjr) hKZ hAZ hrZ hkp hl hin₂ h₂ hra fun Z' t'' hK' hA' hr' hb hax =>
        k Z' t'' hK' hA' hr' hb (by rw [hax]; exact hpos)
  have hf0 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
    have h := hf 0 (Nat.zero_le _) i hi
    rwa [Nat.mul_zero, addr_add_zero] at h
  have hb0 : rdd(V, X.cpu.gpr.rdi) = el V X.cpu.gpr.rdi 0 := by
    show _ = rdd(V, X.cpu.gpr.rdi.add (4 * 0))
    rw [Nat.mul_zero, addr_add_zero]
  by_cases he : el V X.cpu.gpr.rdi 0 = BitVec.setWidth 32 X.cpu.gpr.rsi
  · refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0e (by rw [hb0, he]) hf0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine kr Y t₁ 50 hKY hAY hrY (.inr (.inr rfl)) (kp_w hgY)
      (.inl ⟨0, Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _), he, ?_⟩)
    rw [hgY]
    exact lf_xz _
  · refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0n (fun h => he (by rw [← hb0, ← h])) hf0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine loop c hin hn hnz hz hf kr n 0 (Nat.zero_add n) Y t₁ hKY hAY hrY ?_ (by rw [hgY]; try rfl) ?_
      (by rw [hgY]; try rfl) (fun i hi => ?_) (kp_w hgY)
    · rw [hgY]
      show X.cpu.gpr.rdi = X.cpu.gpr.rdi.add (4 * 0)
      rw [Nat.mul_zero, addr_add_zero]
    · rw [hgY]
      show BitVec.setWidth 32 (BitVec.setWidth 64 rdd(V, X.cpu.gpr.rdi)) = _
      rw [sw32, hb0]
    · obtain rfl : i = 0 := by omega
      exact he

end FV7z.Fcw
