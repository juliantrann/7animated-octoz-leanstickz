import FV7z.Lwa.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.RepStosb
import FV7z.Lemmas.Env
/-!
# `MyStringLower_Ascii (char *s)` (PLAN.md §M, M1)

7-Zip 26.06's `MyStringLower_Ascii (char *s)` at `0x44b9e0` in `7zzs` (`CPP/Common/MyString.cpp`): each byte of `s`
before its 0 from `'A'` to `'Z'` made lower case, in place. The loop's head is the cut point 35 (`movzx eax, [rdi]`,
`test al, al`), `rdi` at the byte; the body stores the byte back at `rdi - 1` after `rdi += 1`.

- `lo8`: a byte made lower case as the code has it (`b - 'A' < 26` unsigned, then `b + 32`); `Lw V s k`: the bytes
  `V` after the first `k` bytes at `s` were; `Lw_out`, `Lw_at`: its bytes.
- `vc_0`, `vc_35z`, `vc_35n`: the entry (to 35), the loop at the 0 (to the `ret` at 42) and at a byte not 0 (the
  store, back to 35).
- `loop`: from 35, by induction on the bytes left; `lwa_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Lwa

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_42 : pret <+: lwa.drop 42 := by decide +kernel
theorem ret_42 (feat : Features) : Dec feat lwa 42 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 42) (k := 0) (pret_0 feat) w_42 (Nat.zero_le _)

/-- A byte made lower case as the code has it: `b - 'A'` below 26 (unsigned), then `b + 32`. -/
def lo8 (b : Byte) : Byte := if (b + 191#8).toNat < 26 then b + 32#8 else b

/-- The byte the code stores (`lea ecx, [rax-0x41]; lea edx, [rax+0x20]; cmp cl, 26; cmovb eax, edx`): `lo8`. -/
theorem lwa_byte (b : Byte) :
    BitVec.setWidth 8
      (if decide ((BitVec.setWidth 8 (BitVec.setWidth 32
            (BitVec.setWidth 64 (BitVec.setWidth 32 b) + 18446744073709551551#64))).toNat < 26) = true then
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) + 32#64)
      else BitVec.setWidth 32 b) = lo8 b := by
  have hb := b.isLt
  have hc : (BitVec.setWidth 8 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 b) + 18446744073709551551#64))).toNat = (b + 191#8).toNat := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  have ha : BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) + 32#64)) =
      b + 32#8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
    omega
  unfold lo8
  rw [hc]
  by_cases h : (b + 191#8).toNat < 26
  · rw [if_pos (decide_eq_true h), if_pos h]
    exact ha
  · rw [if_neg (fun e => h (of_decide_eq_true e)), if_neg h]
    exact sw8a b

/-- `rdi + 1 - 1`. -/
theorem p1m1 (x : BitVec 64) : x + 1#64 + 18446744073709551615#64 = x := by
  have hx : x.toNat < 18446744073709551616 := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- The bytes `V` after the first `k` bytes at `s` were made lower case (`lo8`), one by one as the code stores
them. -/
def Lw (V : Addr → Byte) (s : Addr) : Nat → Addr → Byte
  | 0 => V
  | k + 1 => Vst (Lw V s k) (s.add k) [lo8 (V (s.add k))]

/-- A byte not among the first `k`: as it was. -/
theorem Lw_out (V : Addr → Byte) (s : Addr) : ∀ (k : Nat) (x : Addr), (∀ i < k, x ≠ s.add i) → Lw V s k x = V x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    show Vst (Lw V s k) (s.add k) [lo8 (V (s.add k))] x = V x
    rw [Vst_apart _ _ _ x fun i hi => by
      obtain rfl : i = 0 := by simp at hi; omega
      rw [addr_add_zero]
      exact h k (by omega)]
    exact Lw_out V s k x fun i hi => h i (by omega)

/-- The `k`-th byte while the first `k` are being made lower case: as it was. -/
theorem Lw_self (V : Addr → Byte) (s : Addr) {k : Nat} (hk : k < 2 ^ 64) : Lw V s k (s.add k) = V (s.add k) :=
  Lw_out V s k _ fun i hi => add_ne' s (by omega) (by omega) hk

/-- One of the first `k` bytes: made lower case. -/
theorem Lw_at (V : Addr → Byte) (s : Addr) : ∀ (k : Nat), k ≤ 2 ^ 64 → ∀ i < k, Lw V s k (s.add i) = lo8 (V (s.add i))
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, i, hi => by
    show Vst (Lw V s k) (s.add k) [lo8 (V (s.add k))] (s.add i) = _
    rcases Nat.lt_or_ge i k with h | h
    · rw [Vst_apart _ _ _ _ fun j hj => by
        obtain rfl : j = 0 := by simp at hj; omega
        rw [addr_add_zero]
        exact add_ne' s (by omega) (by omega) (by omega)]
      exact Lw_at V s k (by omega) i h
    · obtain rfl : i = k := by omega
      show upd1 (Lw V s i) (s.add i) (lo8 (V (s.add i))) (s.add i) = _
      simp [upd1]

/-- Bytes apart from the first `k` of the string: as they were. -/
theorem rd_far (V : Addr → Byte) (s : Addr) {k : Nat} {a : Addr} {m : Nat} (h : ∀ b < m, ∀ i < k, a.add b ≠ s.add i) :
    (byteAddrs a m).map (Lw V s k) = (byteAddrs a m).map V :=
  List.map_congr_left fun y hy => by
    obtain ⟨b, hb, rfl⟩ := mem_byteAddrs.1 hy
    exact Lw_out V s k _ fun i hi => h b hb i hi

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: on to 35. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 35 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, eq_self_iff_true, and_self]
  all_goals first | trivial | exact ⟨rfl, rfl, rfl⟩ | done

/-- The loop at the 0: to the `ret` at 42. -/
theorem vc_35z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (BitVec.setWidth 8 (BitVec.setWidth 32 (V g.rdi)) == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rdi i)) :
    W_35 F Wl (fun j' g' _ V' => j' = 42 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf ⊢
  wpx [W_35, W_16, o1, o2, Tun.rd1, BitVec.and_self, hz, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals first | exact hf | exact ⟨hf, fun _ => trivial⟩ | exact ⟨hf, fun _ => ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩, rfl⟩⟩ | done

/-- The loop at a byte not 0: the byte stored back made lower case, `rdi` one on, back to 35. -/
theorem vc_35n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (BitVec.setWidth 8 (BitVec.setWidth 32 (V g.rdi)) == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rdi i)) (hw : ∀ i < 1, Foot Wl (Addr.add g.rdi i)) :
    W_35 F Wl (fun j' g' _ V' => j' = 35 ∧ g'.rdi = g.rdi + 1#64 ∧ Kp g g' ∧
      V' = Vst V g.rdi [lo8 (V g.rdi)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_35, W_16, o1, o2, Tun.rd1, BitVec.and_self, hz, Kp, p1m1, lwa_byte, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | exact ⟨hf, fun _ => hw⟩ | exact ⟨hf, fun _ => ⟨hw, trivial⟩⟩ |
    exact ⟨hf, fun _ => ⟨hw, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩ | done

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The loop from 35 at the index `j` of the `n` bytes not 0 and a 0 at `s`, the first `j` made lower case: on to the
`ret` at 42 with all `n` made lower case, the registers a call keeps as at `g₀`. By induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lwa_at lwa) {V : Addr → Byte} {s : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 63) (hnz : ∀ i < n, V (s.add i) ≠ 0) (hz : V (s.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (s.add i)) (hw : ∀ i < n, Foot Wl (s.add i))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Lw V s n) → Z.cpu.rip = lwa_at.add 42 →
      Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem (Lw V s j) →
      X.cpu.rip = lwa_at.add 35 → X.cpu.gpr.rdi = s.add j → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdi hkp
    have hjn : j = n := by omega
    subst hjn
    have hb : Lw V s j X.cpu.gpr.rdi = V (s.add j) := by rw [hdi]; exact Lw_self V s (by omega)
    have hz' : (BitVec.setWidth 8 (BitVec.setWidth 32 (Lw V s j X.cpu.gpr.rdi)) == 0) = true := by
      rw [hb, sw8a, hz]; all_goals decide
    have hf1 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, hdi]
      exact hf j (Nat.le_refl _)
    refine (c_35 prof).run c hin _ hK hA hrip (vc_35z hz' hf1) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp'))
  | succ m ih =>
    intro j hj X t hK hA hrip hdi hkp
    have hb : Lw V s j X.cpu.gpr.rdi = V (s.add j) := by rw [hdi]; exact Lw_self V s (by omega)
    have hz' : (BitVec.setWidth 8 (BitVec.setWidth 32 (Lw V s j X.cpu.gpr.rdi)) == 0) = false := by
      rw [hb, sw8a]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, hdi]
      exact hf j (by omega)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, hdi]
      exact hw j (by omega)
    refine (c_35 prof).run c hin _ hK hA hrip (vc_35n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine ih (j + 1) (by omega) Y t₁ hKY ?_ hrY ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    · rw [hb, hdi] at hAY
      exact hAY
    · rw [hgY, hdi', hdi]
      exact ptr_step s j 1

/-- `MyStringLower_Ascii (s)` from its entry, `s` (`rdi`) `n` bytes not 0 and a 0 (`n < 2 ^ 63`), those bytes data
of the footprint and the `n` writable, apart from the return address: at the return address with the `n` bytes made
lower case (`Lw`, `Lw_at`), the registers a call keeps (`Str.Back`). -/
theorem lwa_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lwa_at lwa) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lwa_at) {n : Nat} (hn : n < 2 ^ 63)
    (hnz : ∀ i < n, V (Addr.add X.cpu.gpr.rdi i) ≠ 0) (hz : V (Addr.add X.cpu.gpr.rdi n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (Addr.add X.cpu.gpr.rdi i)) (hw : ∀ i < n, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hsep : ∀ b < 8, ∀ i < n, Addr.add X.cpu.gpr.rsp b ≠ Addr.add X.cpu.gpr.rdi i)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Lw V X.cpu.gpr.rdi n) →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hra' : rdq(Lw V X.cpu.gpr.rdi n, X.cpu.gpr.rsp) = e₂.add j₂ := by rw [rd_far V _ hsep]; exact hra
  have kr : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Lw V X.cpu.gpr.rdi n) →
      Z.cpu.rip = lwa_at.add 42 → Kp X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t' :=
    fun Z t' hKZ hAZ hrZ hkp =>
      ret_back c hin (lt_len (by decide)) (ret_42 _) hKZ hAZ hrZ hkp hl hin₂ h₂ hra'
        fun Z' t'' hK' hA' hr' hb _ => k Z' t'' hK' hA' hr' hb
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact loop c hin hn hnz hz hf hw kr n 0 (Nat.zero_add n) Y t₁ hKY hAY hrY (by rw [hgY, addr_add_zero])
    (Kp.of_eq hgY (Kp.refl _))

end FV7z.Lwa
