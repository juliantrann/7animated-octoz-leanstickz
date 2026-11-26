import FV7z.Fcp.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
/-!
# `FindCharPosInString (s, c)` for `char` (PLAN.md §M, M1)

7-Zip 26.06's `FindCharPosInString (const char *s, char c)` at `0x44b960` in `7zzs` (`CPP/Common/MyString.cpp`):
the index of the first `c` in `s`, its 0 included, else -1 (`for (p = s;; p++) { if (*p == c) return p - s;
if (*p == 0) return -1; }`). The loop's head is the cut point 36 (`test dl, dl`), with `rax` at the byte, `dl` that
byte and `cl` the character.

- `Pos`: the answer for a string of `n` bytes not 0 and a 0.
- `vc_0e`, `vc_0n`: from the entry, `s[0] = c` (to the `ret` at 53 with 0) or not (to the loop at 36);
  `vc_36z`, `vc_36e`, `vc_36n`: the loop, at the 0 (to the `ret` at 45 with -1), the next byte `c` (to the `ret` at
  50 with its index), or not (back to 36).
- `loop`: from 36, by induction on the bytes left; `fcp_ok`: from the entry to the return address, `rax` with `Pos`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Fcp

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_45 : pret <+: fcp.drop 45 := by decide +kernel
theorem w_50 : pret <+: fcp.drop 50 := by decide +kernel
theorem w_53 : pret <+: fcp.drop 53 := by decide +kernel
theorem ret_at (feat : Features) {jr : Nat} (h : jr = 45 ∨ jr = 50 ∨ jr = 53) :
    Dec feat fcp jr (FV7z.mk .ret 64 [] 1) := by
  rcases h with rfl | rfl | rfl
  · exact Dec.shift (j := 45) (k := 0) (pret_0 feat) w_45 (Nat.zero_le _)
  · exact Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)
  · exact Dec.shift (j := 53) (k := 0) (pret_0 feat) w_53 (Nat.zero_le _)
theorem ret_lt {jr : Nat} (h : jr = 45 ∨ jr = 50 ∨ jr = 53) : jr < fcp.length :=
  lt_len (by rcases h with rfl | rfl | rfl <;> decide)

/-- The answer for the `n` bytes not 0 and a 0 at `s` and the character `c`: the index of the first `c`, the 0
included, or -1 (as `rax` has it) if there is none. -/
def Pos (V : Addr → Byte) (s : Addr) (c : Byte) (n : Nat) (r : BitVec 64) : Prop :=
  (∃ k, k ≤ n ∧ (∀ i < k, V (s.add i) ≠ c) ∧ V (s.add k) = c ∧ r = BitVec.ofNat 64 k) ∨
    ((∀ i, i ≤ n → V (s.add i) ≠ c) ∧ r = 4294967295#64)

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `s[0] = c`, to the `ret` at 53 with `eax` 0. -/
theorem vc_0e {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : BitVec.setWidth 8 g.rsi = BitVec.setWidth 8 (BitVec.setWidth 32 (V g.rdi)))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 53 ∧
      g' = { g with rax := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi ^^^ BitVec.setWidth 32 g.rdi),
                    rcx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi),
                    rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (V g.rdi)) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf ⊢
  have d := decide_eq_true h
  wpx [W_0, W_17, W_51, o0, o5, Tun.rd1, d, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals first | exact hf | exact ⟨hf, fun _ => trivial⟩ | exact ⟨hf, trivial⟩ |
    exact ⟨hf, fun _ => ⟨rfl, rfl, rfl⟩⟩ | done

/-- From the entry: `s[0] ≠ c`, to the loop's head with `rax = s`, `dl = s[0]`, `cl = c`. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : ¬ BitVec.setWidth 8 g.rsi = BitVec.setWidth 8 (BitVec.setWidth 32 (V g.rdi)))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rdi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 36 ∧
      g' = { g with rax := g.rdi, rcx := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi),
                    rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (V g.rdi)) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h hf ⊢
  have d := decide_eq_false h
  wpx [W_0, W_17, W_51, o0, o5, Tun.rd1, d, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals first | exact hf | exact ⟨hf, trivial⟩ | exact ⟨hf, ⟨rfl, rfl, rfl⟩⟩ | exact ⟨hf, rfl, rfl, rfl⟩ | done

/-- The loop at the 0: to the `ret` at 45 with `eax` -1. -/
theorem vc_36z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 8 g.rdx == 0) = true) :
    W_36 F Wl (fun j' g' _ V' => j' = 45 ∧ g' = { g with rax := BitVec.setWidth 64 4294967295#32 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  wpx [W_36, W_24, W_48, W_40, o1, o2, o3, o4, Tun.rd1, BitVec.and_self, hz, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals first | trivial | exact fun _ => trivial | exact fun _ => ⟨rfl, rfl, rfl⟩ | done

/-- The loop, the next byte `c`: to the `ret` at 50 with its index. -/
theorem vc_36e {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 8 g.rdx == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rax + 1#64) i))
    (h : BitVec.setWidth 8 (BitVec.setWidth 32 (V (g.rax + 1#64))) = BitVec.setWidth 8 g.rcx) :
    W_36 F Wl (fun j' g' _ V' => j' = 50 ∧
      g' = { g with rax := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rax + 1#64) - BitVec.setWidth 32 g.rdi),
                    rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (V (g.rax + 1#64))) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf h ⊢
  have d := decide_eq_true h
  wpx [W_36, W_24, W_48, W_40, o1, o2, o3, o4, Tun.rd1, BitVec.and_self, hz, d, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals first | exact fun _ => hf | exact fun _ => ⟨hf, trivial⟩ | exact hf |
    exact fun _ => ⟨hf, fun _ => trivial⟩ |
    exact fun _ => ⟨hf, ⟨rfl, rfl, rfl⟩⟩ | done

/-- The loop, the next byte not `c`: back to 36 with `rax` one on. -/
theorem vc_36n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (BitVec.setWidth 8 g.rdx == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rax + 1#64) i))
    (h : ¬ BitVec.setWidth 8 (BitVec.setWidth 32 (V (g.rax + 1#64))) = BitVec.setWidth 8 g.rcx) :
    W_36 F Wl (fun j' g' _ V' => j' = 36 ∧
      g' = { g with rax := g.rax + 1#64, rdx := BitVec.setWidth 64 (BitVec.setWidth 32 (V (g.rax + 1#64))) } ∧
        V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf h ⊢
  have d := decide_eq_false h
  wpx [W_36, W_24, W_48, W_40, o1, o2, o3, o4, Tun.rd1, BitVec.and_self, hz, d, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_true]
  all_goals first | exact fun _ => hf | exact fun _ => ⟨hf, trivial⟩ | exact hf |
    exact fun _ => ⟨hf, fun _ => trivial⟩ |
    exact fun _ => ⟨hf, ⟨rfl, rfl, rfl⟩⟩ | done

/-- `test dl, dl` on a byte `b` zero-extended. -/
theorem tz (b : Byte) : (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 b)) == 0) = (b == 0) := by
  rw [sw8b]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The loop from 36 at the index `k` of the `n` bytes not 0 and a 0 at `s`, none of the bytes up to `k` the
character `ch` (`cl`), `dl` the byte at `k`, `rax` its address: on to a `ret` (45, 50 or 53) with `rax` the answer
(`Pos`), the registers a call keeps as at `g₀`. By induction on `n - k`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fcp_at fcp) {V : Addr → Byte} {s : Addr} {ch : Byte}
    {n : Nat} {g₀ : Gprs} (hn : n < 2 ^ 31) (hnz : ∀ i < n, V (s.add i) ≠ 0) (hz : V (s.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (s.add i))
    (k : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = fcp_at.add jr →
      (jr = 45 ∨ jr = 50 ∨ jr = 53) → Kp g₀ Z.cpu.gpr → Pos V s ch n Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = fcp_at.add 36 → X.cpu.gpr.rax = s.add j → X.cpu.gpr.rdi = s →
      BitVec.setWidth 8 X.cpu.gpr.rdx = V (s.add j) → BitVec.setWidth 8 X.cpu.gpr.rcx = ch →
      (∀ i, i ≤ j → V (s.add i) ≠ ch) → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hdi hdx hcx hne hkp
    have hjn : j = n := by omega
    subst hjn
    have hz' : (BitVec.setWidth 8 X.cpu.gpr.rdx == 0) = true := by rw [hdx, hz]; all_goals decide
    refine (c_36 prof).run c hin _ hK hA hrip (vc_36z hz') ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine k Y t₁ 45 hKY hAY hrY (.inl rfl) (hkp.trans (kp_w hgY)) (.inr ⟨hne, ?_⟩)
    rw [hgY]
    exact m1_64
  | succ m ih =>
    intro j hj X t hK hA hrip hax hdi hdx hcx hne hkp
    have hj0 : V (s.add j) ≠ 0 := hnz j (by omega)
    have hz' : (BitVec.setWidth 8 X.cpu.gpr.rdx == 0) = false := by rw [hdx]; exact beq_eq_false_iff_ne.2 hj0
    have ea : X.cpu.gpr.rax + 1#64 = s.add (j + 1) := by rw [hax]; exact ptr_step s j 1
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rax + 1#64) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (by omega)
    have hb : BitVec.setWidth 8 (BitVec.setWidth 32 (V (X.cpu.gpr.rax + 1#64))) = V (s.add (j + 1)) := by
      rw [sw8a, ea]
    by_cases he : V (s.add (j + 1)) = ch
    · refine (c_36 prof).run c hin _ hK hA hrip (vc_36e hz' hf1 (by rw [hb, hcx]; exact he)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine k Y t₁ 50 hKY hAY hrY (.inr (.inl rfl)) (hkp.trans (kp_w hgY))
        (.inl ⟨j + 1, by omega, fun i hi => hne i (by omega), he, ?_⟩)
      rw [hgY]
      show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rax + 1#64) - BitVec.setWidth 32 X.cpu.gpr.rdi) = _
      rw [ea, hdi]
      exact sub32_add s (by omega)
    · refine (c_36 prof).run c hin _ hK hA hrip (vc_36n hz' hf1 (by rw [hb, hcx]; exact he)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY (by rw [hgY]; exact ea) (by rw [hgY]; exact hdi) ?_
        (by rw [hgY]; exact hcx) (fun i hi => ?_) (hkp.trans (kp_w hgY))
      · rw [hgY]
        show BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (_ (X.cpu.gpr.rax + 1#64)))) = _
        rw [sw8b, ea]
      · rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact hne i (by omega)
        · obtain rfl : i = j + 1 := by omega
          exact he

/-- `FindCharPosInString (s, c)` from its entry, `s` (`rdi`) `n` bytes not 0 and a 0 (`n < 2 ^ 31`, an `int`), those
bytes data of the footprint: at the return address with `rax` the answer (`Pos`, `c` the low byte of `rsi`), the
registers a call keeps (`Str.Back`), the bytes as they were. -/
theorem fcp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fcp_at fcp) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fcp_at) {n : Nat} (hn : n < 2 ^ 31)
    (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rdi i) ≠ 0) (hz : V (Addr.add X.cpu.gpr.rdi n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Str.Back X.cpu.gpr Z.cpu.gpr → Pos V X.cpu.gpr.rdi (BitVec.setWidth 8 X.cpu.gpr.rsi) n Z.cpu.gpr.rax →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have kr : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = fcp_at.add jr → (jr = 45 ∨ jr = 50 ∨ jr = 53) → Kp X.cpu.gpr Z.cpu.gpr →
      Pos V X.cpu.gpr.rdi (BitVec.setWidth 8 X.cpu.gpr.rsi) n Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t' :=
    fun Z t' jr hKZ hAZ hrZ hjr hkp hpos =>
      ret_back c hin (ret_lt hjr) (ret_at _ hjr) hKZ hAZ hrZ hkp hl hin₂ h₂ hra fun Z' t'' hK' hA' hr' hb hax =>
        k Z' t'' hK' hA' hr' hb (by rw [hax]; exact hpos)
  have hf0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
    obtain rfl : i = 0 := by omega
    exact hf 0 (Nat.zero_le _)
  have hb0 : BitVec.setWidth 8 (BitVec.setWidth 32 (V X.cpu.gpr.rdi)) = V (Addr.add X.cpu.gpr.rdi 0) := by
    rw [sw8a, addr_add_zero]
  by_cases he : V (Addr.add X.cpu.gpr.rdi 0) = BitVec.setWidth 8 X.cpu.gpr.rsi
  · refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) (vc_0e (by rw [hb0, he]) hf0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine kr Y t₁ 53 hKY hAY hrY (.inr (.inr rfl)) (kp_w hgY)
      (.inl ⟨0, Nat.zero_le _, fun i hi => absurd hi (Nat.not_lt_zero _), he, ?_⟩)
    rw [hgY]
    exact lf_xz _
  · refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
      (vc_0n (fun h => he (by rw [← hb0, ← h])) hf0) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine loop c hin hn hnz hz hf kr n 0 (Nat.zero_add n) Y t₁ hKY hAY hrY
      (by rw [hgY]; exact (addr_add_zero _).symm) (by rw [hgY]; try rfl) ?_ (by rw [hgY]; exact sw8x _) (fun i hi => ?_)
      (kp_w hgY)
    · rw [hgY]
      show BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (_ X.cpu.gpr.rdi))) = _
      rw [sw8b, addr_add_zero]
    · obtain rfl : i = 0 := by omega
      exact he

end FV7z.Fcp
