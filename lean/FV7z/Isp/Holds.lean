import FV7z.Isp.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
/-!
# `IsString1PrefixedByString2_NoCase_Ascii (const wchar_t *s1, const char *s2)` (PLAN.md §M, M1)

7-Zip 26.06's `IsString1PrefixedByString2_NoCase_Ascii` at `0x44bde0` in `7zzs` (`CPP/Common/MyString.cpp`): over the
bytes of `s2` (`rsi`) up to its 0, the index in `rdx`, each against the element of `s1` (`rdi`) at the index, equal
or equal as ASCII lower case; at the 0 of `s2`, `return true` (`mov eax, 1` at 88, `ret` at 93); at the first index
where they differ, `return false` (`xor eax, eax` at 96, `ret` at 98). The loop's head is the cut point 46 (the load
of the element); the next byte is loaded at 34. The contract: it reads, stores nothing, and answers 0 or 1.

- `vc_0z`, `vc_0n`: from the entry, `s2` empty (to 88) or not (to 46 with index 0); `vc_46`, `vc_22`, `vc_29`: the
  comparisons, to 22, 29, 34 or 96 with the index kept; `vc_34z`, `vc_34n`: the next byte 0 (to 88) or not (back to
  46 with the index one on); `vc_88`, `vc_96`: `eax` 1 and 0.
- `loop`: from 46, by induction on the bytes left; `isp_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Isp

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_93 : pret <+: isp.drop 93 := by decide +kernel
theorem w_98 : pret <+: isp.drop 98 := by decide +kernel
theorem ret_at (feat : Features) {jr : Nat} (h : jr = 93 ∨ jr = 98) : Dec feat isp jr (FV7z.mk .ret 64 [] 1) := by
  rcases h with rfl | rfl
  · exact Dec.shift (j := 93) (k := 0) (pret_0 feat) w_93 (Nat.zero_le _)
  · exact Dec.shift (j := 98) (k := 0) (pret_0 feat) w_98 (Nat.zero_le _)
theorem ret_lt {jr : Nat} (h : jr = 93 ∨ jr = 98) : jr < isp.length :=
  lt_len (by rcases h with rfl | rfl <;> decide)

/-- The element's address `rdi + rdx * 4` at the index `j`: `s1 + 4 j`. -/
theorem idx4 (u : Addr) (j : Nat) : u + BitVec.ofNat 64 j * 4#64 = u.add (4 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- The next byte's address `rsi + (rdx + 1)` at the index `j`: `s2 + (j + 1)`. -/
theorem idx1 (a : Addr) (j : Nat) : a + (BitVec.ofNat 64 j + 1#64) = a.add (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  omega

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry: `s2` empty, to 88. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (V g.rsi == 0) = true)
    (hf1 : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 88 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf1 ⊢
  wpx [W_0, W_11, o0, o1, Tun.rd1, sw8a, sw8b, BitVec.and_self, hz, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- From the entry: `s2` not empty, to 46 with the index 0. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (V g.rsi == 0) = false)
    (hf1 : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 46 ∧ g'.rdx = 0#64 ∧ g'.rsi = g.rsi ∧ g'.rdi = g.rdi ∧ Kp g g' ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf1 ⊢
  wpx [W_0, W_11, o0, o1, Tun.rd1, sw8a, sw8b, BitVec.and_self, hz, lf_xz, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- From the loop's head: the element against the byte, to 34, 22, 29 or 96, the index kept. -/
theorem vc_46 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf4 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + g.rdx * 4#64) i)) :
    W_46 F Wl (fun j' g' _ V' => (j' = 34 ∨ j' = 22 ∨ j' = 29 ∨ j' = 96) ∧ g'.rdx = g.rdx ∧ g'.rsi = g.rsi ∧
      g'.rdi = g.rdi ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf4 ⊢
  wpx [W_46, W_58, W_16, W_72, W_81, o6, o7, o2, o8, Op.zxr, Kp, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true, true_or, false_or, or_true, or_false]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _
    | decide

/-- At 22: `add eax, 0x20; movzx r8d, al`, to 29. -/
theorem vc_22 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_22 F Wl (fun j' g' _ V' => j' = 29 ∧ g'.rdx = g.rdx ∧ g'.rsi = g.rsi ∧ g'.rdi = g.rdi ∧ Kp g g' ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_22, o3, Op.zxr, Kp, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _

/-- At 29: `cmp r8d, ecx; jne`, to 96 or 34. -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_29 F Wl (fun j' g' _ V' => (j' = 96 ∨ j' = 34) ∧ g'.rdx = g.rdx ∧ g'.rsi = g.rsi ∧ g'.rdi = g.rdi ∧
      Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_29, o4, Kp, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true, true_or,
    false_or, or_true, or_false]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _
    | decide

/-- At 34, the next byte 0: to 88. -/
theorem vc_34z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (V (g.rsi + (g.rdx + 1#64)) == 0) = true)
    (hf1 : ∀ i < 1, Foot F.data (Addr.add (g.rsi + (g.rdx + 1#64)) i)) :
    W_34 F Wl (fun j' g' _ V' => j' = 88 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf1 ⊢
  wpx [W_34, o5, Tun.rd1, sw8a, sw8b, BitVec.and_self, hz, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- At 34, the next byte not 0: back to 46 with the index one on. -/
theorem vc_34n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : (V (g.rsi + (g.rdx + 1#64)) == 0) = false)
    (hf1 : ∀ i < 1, Foot F.data (Addr.add (g.rsi + (g.rdx + 1#64)) i)) :
    W_34 F Wl (fun j' g' _ V' => j' = 46 ∧ g'.rdx = g.rdx + 1#64 ∧ g'.rsi = g.rsi ∧ g'.rdi = g.rdi ∧ Kp g g' ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf1 ⊢
  wpx [W_34, o5, Tun.rd1, sw8a, sw8b, BitVec.and_self, hz, Kp, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- At 88: `eax` 1, to the `ret` at 93. -/
theorem vc_88 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_88 F Wl (fun j' g' _ V' => j' = 93 ∧ g'.rax = 1#64 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_88, o9, Kp, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _
    | decide

/-- At 96: `eax` 0, to the `ret` at 98. -/
theorem vc_96 {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_96 F Wl (fun j' g' _ V' => j' = 98 ∧ g'.rax = 0#64 ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_96, o10, lf_xz, Kp, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | exact trivial
    | apply And.intro
    | intro _
    | decide

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The answers. -/
abbrev Ans (r : BitVec 64) : Prop := r = 1#64 ∨ r = 0#64

section
variable (c : Seg prof F Wl L s₀ o) (hin : CodeIn L isp_at isp) {V : Addr → Byte} {g₀ : Gprs}
  (k : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
    Z.cpu.rip = isp_at.add jr → (jr = 93 ∨ jr = 98) → Kp g₀ Z.cpu.gpr → Ans Z.cpu.gpr.rax →
    GoG prof L o gev gP gE Z t')
include c hin k

/-- From 88 to the `ret` at 93 with `rax` 1. -/
theorem at88 {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = isp_at.add 88) (hkp : Kp g₀ X.cpu.gpr) : GoG prof L o gev gP gE X t := by
  refine (c_88 prof).run c hin _ hK hA hrip vc_88 ?_
  rintro j' g fl V₁ ⟨rfl, hax, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ 93 hKY hAY hrY (.inl rfl) (hkp.trans (Kp.of_eq hgY hkp')) (.inl (by rw [hgY]; exact hax))

/-- From 96 to the `ret` at 98 with `rax` 0. -/
theorem at96 {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = isp_at.add 96) (hkp : Kp g₀ X.cpu.gpr) : GoG prof L o gev gP gE X t := by
  refine (c_96 prof).run c hin _ hK hA hrip vc_96 ?_
  rintro j' g fl V₁ ⟨rfl, hax, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact k Y t₁ 98 hKY hAY hrY (.inr rfl) (hkp.trans (Kp.of_eq hgY hkp')) (.inr (by rw [hgY]; exact hax))

variable {u a : Addr} {na : Nat} (hz : V (a.add na) = 0) (hf : ∀ i, i ≤ na → Foot F.data (a.add i))
include hz hf

/-- From 34 at the index `j < na`: to 88 at the 0 of `s2`, else to 46 with the index `j + 1` (`k46`). -/
theorem at34 {j : Nat} (hj : j < na)
    (k46 : j + 1 < na → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = isp_at.add 46 → X.cpu.gpr.rdx = BitVec.ofNat 64 (j + 1) → X.cpu.gpr.rsi = a →
      X.cpu.gpr.rdi = u → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = isp_at.add 34)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 j) (hsi : X.cpu.gpr.rsi = a) (hdi : X.cpu.gpr.rdi = u)
    (hkp : Kp g₀ X.cpu.gpr) : GoG prof L o gev gP gE X t := by
  have ea : X.cpu.gpr.rsi + (X.cpu.gpr.rdx + 1#64) = a.add (j + 1) := by rw [hsi, hdx]; exact idx1 a j
  have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rsi + (X.cpu.gpr.rdx + 1#64)) i) := fun i hi => by
    obtain rfl : i = 0 := by omega
    rw [addr_add_zero, ea]
    exact hf (j + 1) (by omega)
  by_cases h0 : V (a.add (j + 1)) = 0
  · have hz' : (V (X.cpu.gpr.rsi + (X.cpu.gpr.rdx + 1#64)) == 0) = true := by rw [ea, h0]; all_goals decide
    refine (c_34 prof).run c hin _ hK hA hrip (vc_34z hz' hf1) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact at88 c hin k hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp'))
  · have hz' : (V (X.cpu.gpr.rsi + (X.cpu.gpr.rdx + 1#64)) == 0) = false := by
      rw [ea]; exact beq_eq_false_iff_ne.2 h0
    have hj1 : j + 1 < na := by
      rcases Nat.lt_or_ge (j + 1) na with h | h
      · exact h
      · obtain rfl : j + 1 = na := by omega
        exact absurd hz h0
    refine (c_34 prof).run c hin _ hK hA hrip (vc_34n hz' hf1) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hsi', hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine k46 hj1 Y t₁ hKY hAY hrY ?_ (by rw [hgY, hsi', hsi]) (by rw [hgY, hdi', hdi])
      (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hdx', hdx]
    exact (BitVec.ofNat_add j 1).symm

/-- From 29 at the index `j < na`: to 96, or on from 34 (`at34`). -/
theorem at29 {j : Nat} (hj : j < na)
    (k46 : j + 1 < na → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = isp_at.add 46 → X.cpu.gpr.rdx = BitVec.ofNat 64 (j + 1) → X.cpu.gpr.rsi = a →
      X.cpu.gpr.rdi = u → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = isp_at.add 29)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 j) (hsi : X.cpu.gpr.rsi = a) (hdi : X.cpu.gpr.rdi = u)
    (hkp : Kp g₀ X.cpu.gpr) : GoG prof L o gev gP gE X t := by
  refine (c_29 prof).run c hin _ hK hA hrip vc_29 ?_
  rintro j' g fl V₁ ⟨hj', hdx', hsi', hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hkY := hkp.trans (Kp.of_eq hgY hkp')
  rcases hj' with rfl | rfl
  · exact at96 c hin k hKY hAY hrY hkY
  · exact at34 c hin k hz hf hj k46 hKY hAY hrY (by rw [hgY, hdx', hdx]) (by rw [hgY, hsi', hsi])
      (by rw [hgY, hdi', hdi]) hkY

/-- From 22 at the index `j < na`: on from 29 (`at29`). -/
theorem at22 {j : Nat} (hj : j < na)
    (k46 : j + 1 < na → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
      X.cpu.rip = isp_at.add 46 → X.cpu.gpr.rdx = BitVec.ofNat 64 (j + 1) → X.cpu.gpr.rsi = a →
      X.cpu.gpr.rdi = u → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t)
    {X : State} {t : Nat} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = isp_at.add 22)
    (hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 j) (hsi : X.cpu.gpr.rsi = a) (hdi : X.cpu.gpr.rdi = u)
    (hkp : Kp g₀ X.cpu.gpr) : GoG prof L o gev gP gE X t := by
  refine (c_22 prof).run c hin _ hK hA hrip vc_22 ?_
  rintro j' g fl V₁ ⟨rfl, hdx', hsi', hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
  exact at29 c hin k hz hf hj k46 hKY hAY hrY (by rw [hgY, hdx', hdx]) (by rw [hgY, hsi', hsi])
    (by rw [hgY, hdi', hdi]) (hkp.trans (Kp.of_eq hgY hkp'))

/-- The loop from 46 at the index `j < na` of `s2` (`na` bytes up to its 0), the elements of `s1` below `na`
readable: on to a `ret` (93 or 98) with `rax` 0 or 1. By induction on `na - j`. -/
theorem loop (hu : ∀ i < na, ∀ b < 4, Foot F.data ((u.add (4 * i)).add b)) :
    ∀ (m j : Nat), j + m = na → j < na → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V → X.cpu.rip = isp_at.add 46 → X.cpu.gpr.rdx = BitVec.ofNat 64 j →
      X.cpu.gpr.rsi = a → X.cpu.gpr.rdi = u → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero => intro j hj hjn; exfalso; omega
  | succ m ih =>
    intro j hjm hj X t hK hA hrip hdx hsi hdi hkp
    have k46 : j + 1 < na → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem V →
        X.cpu.rip = isp_at.add 46 → X.cpu.gpr.rdx = BitVec.ofNat 64 (j + 1) → X.cpu.gpr.rsi = a →
        X.cpu.gpr.rdi = u → Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t :=
      fun h1 => ih (j + 1) (by omega) h1
    have hf4 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + X.cpu.gpr.rdx * 4#64) i) := fun i hi => by
      rw [hdi, hdx, idx4]
      exact hu j hj i hi
    refine (c_46 prof).run c hin _ hK hA hrip (vc_46 hf4) ?_
    rintro j' g fl V₁ ⟨hj', hdx', hsi', hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    have hkY := hkp.trans (Kp.of_eq hgY hkp')
    have hdY : Y.cpu.gpr.rdx = BitVec.ofNat 64 j := by rw [hgY, hdx', hdx]
    have hsY : Y.cpu.gpr.rsi = a := by rw [hgY, hsi', hsi]
    have hiY : Y.cpu.gpr.rdi = u := by rw [hgY, hdi', hdi]
    rcases hj' with rfl | rfl | rfl | rfl
    · exact at34 c hin k hz hf hj k46 hKY hAY hrY hdY hsY hiY hkY
    · exact at22 c hin k hz hf hj k46 hKY hAY hrY hdY hsY hiY hkY
    · exact at29 c hin k hz hf hj k46 hKY hAY hrY hdY hsY hiY hkY
    · exact at96 c hin k hKY hAY hrY hkY

end

/-- `IsString1PrefixedByString2_NoCase_Ascii (s1, s2)` from its entry, `s1` (`rdi`) and `s2` (`rsi`, `na` bytes up to
its 0), the bytes of `s2` up to its 0 and the elements of `s1` below `na` readable: at the return address with `rax`
0 or 1 (`Ans`), the registers a call keeps (`Str.Back`), the bytes as they were. -/
theorem isp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L isp_at isp) {X : State} {t : Nat} {V : Addr → Byte}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = isp_at) {na : Nat}
    (hz : V (Addr.add X.cpu.gpr.rsi na) = 0) (hf : ∀ i, i ≤ na → Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (hu : ∀ i < na, ∀ b < 4, Foot F.data ((Addr.add X.cpu.gpr.rdi (4 * i)).add b))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Str.Back X.cpu.gpr Z.cpu.gpr → Ans Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have kr : ∀ (Z : State) (t' : Nat) (jr : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V →
      Z.cpu.rip = isp_at.add jr → (jr = 93 ∨ jr = 98) → Kp X.cpu.gpr Z.cpu.gpr → Ans Z.cpu.gpr.rax →
      GoG prof L o gev gP gE Z t' :=
    fun Z t' jr hKZ hAZ hrZ hjr hkp hr =>
      ret_back c hin (ret_lt hjr) (ret_at _ hjr) hKZ hAZ hrZ hkp hl hin₂ h₂ hra fun Z' t'' hK' hA' hr' hb hax =>
        k Z' t'' hK' hA' hr' hb (by rw [hax]; exact hr)
  have a0 : Addr.add X.cpu.gpr.rsi 0 = X.cpu.gpr.rsi := addr_add_zero _
  have hf1 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsi i) := fun i hi => by
    obtain rfl : i = 0 := by omega
    exact hf 0 (Nat.zero_le _)
  have hrip0 : X.cpu.rip = isp_at.add 0 := by rw [addr_add_zero]; exact hrip
  by_cases h0 : V X.cpu.gpr.rsi = 0
  · have hz' : (V X.cpu.gpr.rsi == 0) = true := by rw [h0]; all_goals decide
    refine (c_0 prof).run c hin _ hK hA hrip0 (vc_0z hz' hf1) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact at88 c hin kr hKY hAY hrY (Kp.of_eq hgY hkp')
  · have hz' : (V X.cpu.gpr.rsi == 0) = false := beq_eq_false_iff_ne.2 h0
    have hn : 0 < na := by
      rcases Nat.eq_zero_or_pos na with e | e
      · subst e
        exact absurd (a0 ▸ hz) h0
      · exact e
    refine (c_0 prof).run c hin _ hK hA hrip0 (vc_0n hz' hf1) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hsi', hdi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact loop c hin kr hz hf hu na 0 (Nat.zero_add na) hn Y t₁ hKY hAY hrY (by rw [hgY, hdx']; all_goals rfl)
      (by rw [hgY, hsi']) (by rw [hgY, hdi']) (Kp.of_eq hgY hkp')

end FV7z.Isp
