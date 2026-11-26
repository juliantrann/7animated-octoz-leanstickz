import FV7z.Lww.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Env
/-!
# `MyStringLower_Ascii (wchar_t *s)` (PLAN.md §M, M1)

7-Zip 26.06's `MyStringLower_Ascii (wchar_t *s)` at `0x44ba10` in `7zzs` (`CPP/Common/MyString.cpp`): each element
(4 bytes) of `s` before its 0 from `'A'` to `'Z'` made lower case, in place. The loop's head is the cut point 35
(`mov eax, [rdi]`, `test eax, eax`), `rdi` at the element; the body stores it back at `rdi - 4` after `rdi += 4`.

- `lo32`: an element made lower case as the code has it; `Lw V s k`: the bytes `V` after the first `k` elements at
  `s` were; `Lw_out`, `rd_self`: its bytes.
- `vc_0`, `vc_35z`, `vc_35n`: the entry (to 35), the loop at the 0 (to the `ret` at 41) and at an element not 0
  (the store, back to 35).
- `loop`: from 35, by induction on the elements left; `lww_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Lww

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_41 : pret <+: lww.drop 41 := by decide +kernel
theorem ret_41 (feat : Features) : Dec feat lww 41 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 41) (k := 0) (pret_0 feat) w_41 (Nat.zero_le _)

/-- The `i`-th element of the `wchar_t` string at `s`. -/
abbrev el (V : Addr → Byte) (s : Addr) (i : Nat) : BitVec 32 := rdd(V, s.add (4 * i))

/-- An element made lower case as the code has it: `w - 'A'` below 26 (unsigned), then `w + 32`. -/
def lo32 (w : BitVec 32) : BitVec 32 := if (w + 4294967231#32).toNat < 26 then w + 32#32 else w

/-- The element the code stores (`lea ecx, [rax-0x41]; lea edx, [rax+0x20]; cmp ecx, 26; cmovb eax, edx`):
`lo32`. -/
theorem lww_val (w : BitVec 32) :
    (if decide ((BitVec.setWidth 32 (BitVec.setWidth 64 w + 18446744073709551551#64)).toNat < 26) = true then
        BitVec.setWidth 32 (BitVec.setWidth 64 w + 32#64)
      else w) = lo32 w := by
  have sa : ∀ x y : BitVec 64, BitVec.setWidth 32 (x + y) = BitVec.setWidth 32 x + BitVec.setWidth 32 y :=
    fun x y => BitVec.setWidth_add x y (by decide)
  have k1 : BitVec.setWidth 32 18446744073709551551#64 = 4294967231#32 := by decide
  have k2 : BitVec.setWidth 32 32#64 = 32#32 := by decide
  have hc : BitVec.setWidth 32 (BitVec.setWidth 64 w + 18446744073709551551#64) = w + 4294967231#32 := by
    rw [sa, k1, sw32]
  have ha : BitVec.setWidth 32 (BitVec.setWidth 64 w + 32#64) = w + 32#32 := by
    rw [sa, k2, sw32]
  unfold lo32
  rw [hc]
  by_cases h : (w + 4294967231#32).toNat < 26
  · rw [if_pos (decide_eq_true h), if_pos h]
    exact ha
  · rw [if_neg (fun e => h (of_decide_eq_true e)), if_neg h]

/-- `rdi + 4 - 4`. -/
theorem p4m4 (x : BitVec 64) : x + 4#64 + 18446744073709551612#64 = x := by
  rw [BitVec.add_assoc, show (4#64 : BitVec 64) + 18446744073709551612#64 = 0#64 by decide, BitVec.add_zero]

/-- The bytes `V` after the first `k` elements at `s` were made lower case (`lo32`), one by one as the code stores
them. -/
def Lw (V : Addr → Byte) (s : Addr) : Nat → Addr → Byte
  | 0 => V
  | k + 1 => Vst (Lw V s k) (s.add (4 * k)) (toBytesLE (lo32 (el V s k)) 4)

/-- A byte not of the first `k` elements: as it was. -/
theorem Lw_out (V : Addr → Byte) (s : Addr) :
    ∀ (k : Nat) (x : Addr), (∀ i < k, ∀ b < 4, x ≠ (s.add (4 * i)).add b) → Lw V s k x = V x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    show Vst (Lw V s k) (s.add (4 * k)) (toBytesLE (lo32 (el V s k)) 4) x = V x
    have h4 : (toBytesLE (lo32 (el V s k)) 4).length = 4 := toBytesLE_length _ _
    rw [Vst_apart _ _ _ x fun b hb => h k (by omega) b (by omega)]
    exact Lw_out V s k x fun i hi => h i (by omega)

/-- Bytes apart from the first `k` elements of the string: as they were. -/
theorem rd_far (V : Addr → Byte) (s : Addr) {k : Nat} {a : Addr} {m : Nat}
    (h : ∀ b' < m, ∀ i < k, ∀ b < 4, a.add b' ≠ (s.add (4 * i)).add b) :
    (byteAddrs a m).map (Lw V s k) = (byteAddrs a m).map V :=
  List.map_congr_left fun y hy => by
    obtain ⟨b', hb', rfl⟩ := mem_byteAddrs.1 hy
    exact Lw_out V s k _ fun i hi b hb => h b' hb' i hi b hb

/-- The `k`-th element while the first `k` are being made lower case: as it was. -/
theorem rd_self (V : Addr → Byte) (s : Addr) {k : Nat} (hk : 4 * k + 4 ≤ 2 ^ 64) :
    rdd(Lw V s k, s.add (4 * k)) = el V s k := by
  have h : ∀ b' < 4, ∀ i < k, ∀ b < 4, (s.add (4 * k)).add b' ≠ (s.add (4 * i)).add b := fun b' hb' i hi b hb e => by
    rw [addr_add_add, addr_add_add] at e
    exact add_ne' s (by omega) (by omega) (by omega) e
  exact congrArg (ofBytesLE 32) (rd_far V s h)

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: on to 35. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_0 F Wl (fun j' g' _ V' => j' = 35 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0, eq_self_iff_true, and_self]
  all_goals first | trivial | exact ⟨rfl, rfl, rfl⟩ | done

/-- The loop at the 0: to the `ret` at 41. -/
theorem vc_35z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rdd(V, g.rdi) == 0) = true)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) :
    W_35 F Wl (fun j' g' _ V' => j' = 41 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf ⊢
  wpx [W_35, W_16, o1, o2, BitVec.and_self, hz, Kp, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals first | exact hf | exact ⟨hf, fun _ => trivial⟩ |
    exact ⟨hf, fun _ => ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩ | done

/-- The loop at an element not 0: the element stored back made lower case, `rdi` four on, back to 35. -/
theorem vc_35n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (rdd(V, g.rdi) == 0) = false)
    (hf : ∀ i < 4, Foot F.data (Addr.add g.rdi i)) (hw : ∀ i < 4, Foot Wl (Addr.add g.rdi i)) :
    W_35 F Wl (fun j' g' _ V' => j' = 35 ∧ g'.rdi = g.rdi + 4#64 ∧ Kp g g' ∧
      V' = Vst V g.rdi (toBytesLE (lo32 rdd(V, g.rdi)) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_35, W_16, o1, o2, BitVec.and_self, hz, Kp, p4m4, lww_val, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals first | exact ⟨hf, fun _ => hw⟩ | exact ⟨hf, fun _ => ⟨hw, trivial⟩⟩ | exact ⟨hf, rfl, hw⟩ |
    exact ⟨hf, fun _ => ⟨rfl, hw⟩⟩ |
    exact ⟨hf, fun _ => ⟨hw, rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩⟩ | done

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The loop from 35 at the index `j` of the `n` elements not 0 and a 0 at `s`, the first `j` made lower case: on to
the `ret` at 41 with all `n` made lower case, the registers a call keeps as at `g₀`. By induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lww_at lww) {V : Addr → Byte} {s : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 61) (hnz : ∀ i < n, el V s i ≠ 0) (hz : el V s n = 0)
    (hf : ∀ i, i ≤ n → ∀ b < 4, Foot F.data ((s.add (4 * i)).add b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl ((s.add (4 * i)).add b))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Lw V s n) → Z.cpu.rip = lww_at.add 41 →
      Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem (Lw V s j) →
      X.cpu.rip = lww_at.add 35 → X.cpu.gpr.rdi = s.add (4 * j) → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdi hkp
    have hjn : j = n := by omega
    subst hjn
    have hb : rdd(Lw V s j, X.cpu.gpr.rdi) = el V s j := by rw [hdi]; exact rd_self V s (by omega)
    have hz' : (rdd(Lw V s j, X.cpu.gpr.rdi) == 0) = true := by rw [hb, hz]; all_goals decide
    have hf1 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
      rw [hdi]
      exact hf j (Nat.le_refl _) i hi
    refine (c_35 prof).run c hin _ hK hA hrip (vc_35z hz' hf1) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp'))
  | succ m ih =>
    intro j hj X t hK hA hrip hdi hkp
    have hb : rdd(Lw V s j, X.cpu.gpr.rdi) = el V s j := by rw [hdi]; exact rd_self V s (by omega)
    have hz' : (rdd(Lw V s j, X.cpu.gpr.rdi) == 0) = false := by
      rw [hb]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
      rw [hdi]
      exact hf j (by omega) i hi
    have hw1 : ∀ i < 4, Foot Wl (Addr.add X.cpu.gpr.rdi i) := fun i hi => by
      rw [hdi]
      exact hw j (by omega) i hi
    refine (c_35 prof).run c hin _ hK hA hrip (vc_35n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine ih (j + 1) (by omega) Y t₁ hKY ?_ hrY ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    · rw [hb, hdi] at hAY
      exact hAY
    · rw [hgY, hdi', hdi, show 4 * (j + 1) = 4 * j + 4 by omega]
      exact ptr_step s (4 * j) 4

/-- `MyStringLower_Ascii (s)` for `wchar_t` from its entry, `s` (`rdi`) `n` elements not 0 and a 0 (`n < 2 ^ 61`),
their bytes data of the footprint and those of the `n` writable, apart from the return address: at the return address
with the `n` elements made lower case (`Lw`), the registers a call keeps (`Str.Back`). -/
theorem lww_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lww_at lww) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lww_at) {n : Nat} (hn : n < 2 ^ 61)
    (hnz : ∀ i < n, el V X.cpu.gpr.rdi i ≠ 0) (hz : el V X.cpu.gpr.rdi n = 0)
    (hf : ∀ i, i ≤ n → ∀ b < 4, Foot F.data (Addr.add (Addr.add X.cpu.gpr.rdi (4 * i)) b))
    (hw : ∀ i < n, ∀ b < 4, Foot Wl (Addr.add (Addr.add X.cpu.gpr.rdi (4 * i)) b))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hsep : ∀ b' < 8, ∀ i < n, ∀ b < 4, Addr.add X.cpu.gpr.rsp b' ≠ Addr.add (Addr.add X.cpu.gpr.rdi (4 * i)) b)
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Lw V X.cpu.gpr.rdi n) →
      Z.cpu.rip = e₂.add j₂ → Str.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hra' : rdq(Lw V X.cpu.gpr.rdi n, X.cpu.gpr.rsp) = e₂.add j₂ := by rw [rd_far V _ hsep]; exact hra
  have kr : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Lw V X.cpu.gpr.rdi n) →
      Z.cpu.rip = lww_at.add 41 → Kp X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t' :=
    fun Z t' hKZ hAZ hrZ hkp =>
      ret_back c hin (lt_len (by decide)) (ret_41 _) hKZ hAZ hrZ hkp hl hin₂ h₂ hra'
        fun Z' t'' hK' hA' hr' hb _ => k Z' t'' hK' hA' hr' hb
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip) vc_0 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact loop c hin hn hnz hz hf hw kr n 0 (Nat.zero_add n) Y t₁ hKY hAY hrY
    (by rw [hgY, Nat.mul_zero, addr_add_zero]) (Kp.of_eq hgY (Kp.refl _))

end FV7z.Lww
