import FV7z.Acc.Cuts
import FV7z.Acp.Loop
/-!
# The loops of `AString::AString (const char *)` (PLAN.md §M, M1)

The two loops of `AString (const char *s)` at `0x44c3c0` in `7zzs`:

- the length: at 0 `cmp byte [rsi], 0; mov esi, 0; je 44`, then at 32 `lea eax, [rsi + 1]; cmp byte [rbx + rax], 0;
  mov rsi, rax; jne 32`, `rbx` = `s`, `esi` the length so far;
- the copy at 64: `movzx edx, byte [rbx + rax]; mov [rcx + rax], dl; add rax, 1; test dl, dl; jne 64`, `rcx` the new
  buffer, `rax` the index; at the 0 (stored too) on to `add rsp, 8; pop rbx; pop rbp` and the `ret` at 85.

The bytes copied are `Acp.Cp`, as in `AString (const AString &)` (`FV7z/Acp/Loop.lean`).

- `gS`, `V0`: the registers and the bytes after the pushes; `nx`: `esi + 1`, zero-extended.
- `vc_0z`, `vc_0n`: from the entry at an empty and a non-empty string; `vc_32z`, `vc_32n`: the length loop at the 0
  and at a byte not 0; `slen`: the length loop by induction.
- `vc_64n`, `vc_64z`, `loop`: the copy loop.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Acc

/-- The registers after `push rbp; mov rbp, rdi; push rbx; mov rbx, rsi; sub rsp, 8; mov esi, 0`. -/
abbrev gS (g : Gprs) : Gprs :=
  { g with rbp := g.rdi, rbx := g.rsi, rsi := 0#64, rsp := g.rsp - 8 - 8 - 8 }

/-- The bytes after `push rbp; push rbx`. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- `lea eax, [rsi + 1]`. -/
abbrev nx (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rsi + 1#64))

/-- `nx` at a length `j` with `j + 1` in 32 bits. -/
theorem nx_ofNat (j : Nat) (h : j + 1 < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 j + 1#64)) = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry at an empty string: to 44. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i))
    (hz : Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8) g.rsi = 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 44 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hf hz ⊢
  wpx [W_0, W_26, o0, o1, Op.cmpmi, Tun.rd1, BitVec.sub_zero, hz, gS, V0, decide_true, decide_false,
    Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- From the entry at a string not empty: to 32. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i))
    (hz : Vst (Vst V (g.rsp - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8) g.rsi ≠ 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 32 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hf hz ⊢
  wpx [W_0, W_26, o0, o1, Op.cmpmi, Tun.rd1, BitVec.sub_zero, hz, gS, V0, decide_true, decide_false,
    Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The length loop at the 0: to 44, `rsi` = `nx`. -/
theorem vc_32z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbx + nx g) i)) (hz : V (g.rbx + nx g) = 0#8) :
    W_32 F Wl (fun j' g' _ V' => j' = 44 ∧ g'.rsi = nx g ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz ⊢
  wpx [W_32, o2, Op.cmpmi, Tun.rd1, BitVec.sub_zero, hz, Kp, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The length loop at a byte not 0: back to 32, `rsi` = `nx`. -/
theorem vc_32n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbx + nx g) i)) (hz : V (g.rbx + nx g) ≠ 0#8) :
    W_32 F Wl (fun j' g' _ V' => j' = 32 ∧ g'.rsi = nx g ∧ Kp g g' ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz ⊢
  wpx [W_32, o2, Op.cmpmi, Tun.rd1, BitVec.sub_zero, hz, Kp, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The copy loop at a byte not 0: the byte stored, `rax` one on, back to 64. -/
theorem vc_64n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rbx + g.rax) == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbx + g.rax) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rcx + g.rax) i)) :
    W_64 F Wl (fun j' g' _ V' => j' = 64 ∧ g'.rax = g.rax + 1#64 ∧ g'.rcx = g.rcx ∧ Kp g g' ∧
      V' = Vst V (g.rcx + g.rax) [V (g.rbx + g.rax)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_64, W_79, o5, o6, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at the 0: the 0 stored, then `add rsp, 8; pop rbx; pop rbp` to the `ret` at 85. -/
theorem vc_64z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rbx + g.rax) == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbx + g.rax) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rcx + g.rax) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i)) :
    W_64 F Wl (fun j' g' _ V' => j' = 85 ∧ g'.rbx = rdq(V', g.rsp + 8#64) ∧ g'.rbp = rdq(V', g.rsp + 8#64 + 8) ∧
      g'.rsp = g.rsp + 8#64 + 8 + 8 ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
      V' = Vst V (g.rcx + g.rax) [V (g.rbx + g.rax)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw l1 l2 ⊢
  wpx [W_64, W_79, o5, o6, Tun.rd1, BitVec.and_self, hz, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The length loop from 32 at the length `j` so far (`j + 1 ≤ n`) of the `n` bytes not 0 and a 0 at `p` (in `W`,
`rbx` = `p`): on to 44 with `rsi` = `n`, the registers a call keeps as at `g₀`. By induction on `n - j - 1`. -/
theorem slen (c : Seg prof F Wl L s₀ o) (hin : CodeIn L acc_at acc) {W : Addr → Byte} {p : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 32) (hnz : ∀ i < n, W (p.add i) ≠ 0#8) (hz : W (p.add n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hp : g₀.rbx = p)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = acc_at.add 44 →
      Z.cpu.gpr.rsi = BitVec.ofNat 64 n → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + 1 + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = acc_at.add 32 → X.cpu.gpr.rsi = BitVec.ofNat 64 j → Kp g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hsi hkp
    have ea : X.cpu.gpr.rbx + nx X.cpu.gpr = p.add (j + 1) := by
      show X.cpu.gpr.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rsi + 1#64)) = _
      rw [hkp.2.1, hp, hsi, nx_ofNat j (by omega)]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbx + nx X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (by omega)
    refine (c_32 prof).run c hin _ hK hA hrip (vc_32z hf1 (by rw [ea]; obtain rfl : j + 1 = n := (by omega); exact hz))
      ?_
    rintro j' g fl V₁ ⟨rfl, hsi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine k Y t₁ hKY hAY hrY ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hsi']
    show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rsi + 1#64)) = _
    rw [hsi, nx_ofNat j (by omega)]
    congr 1 <;> omega
  | succ m ih =>
    intro j hj X t hK hA hrip hsi hkp
    have ea : X.cpu.gpr.rbx + nx X.cpu.gpr = p.add (j + 1) := by
      show X.cpu.gpr.rbx + BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rsi + 1#64)) = _
      rw [hkp.2.1, hp, hsi, nx_ofNat j (by omega)]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbx + nx X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (by omega)
    refine (c_32 prof).run c hin _ hK hA hrip (vc_32n hf1 (by rw [ea]; exact hnz (j + 1) (by omega))) ?_
    rintro j' g fl V₁ ⟨rfl, hsi', hkp', rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hsi']
    show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rsi + 1#64)) = _
    rw [hsi, nx_ofNat j (by omega)]

/-- The copy loop from 64 at the index `j` of the `n` bytes not 0 and a 0 at `p` (in `W`, `rbx` = `p`), the first `j`
stored at `d`: on to the `ret` at 85 with all `n + 1` stored, `rbx`, `rbp` popped and `r12` … `r15` as at `g₀`. By
induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L acc_at acc) {W : Addr → Byte} {p d : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 63) (hnz : ∀ i < n, W (p.add i) ≠ 0) (hz : W (p.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hw : ∀ i, i ≤ n → Foot Wl (d.add i))
    (hsep : ∀ i, i ≤ n → ∀ j, j ≤ n → p.add i ≠ d.add j) (hp : g₀.rbx = p)
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64 + 8) i))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Acp.Cp W p d (n + 1)) →
      Z.cpu.rip = acc_at.add 85 → Z.cpu.gpr.rbx = rdq(Acp.Cp W p d (n + 1), g₀.rsp + 8#64) →
      Z.cpu.gpr.rbp = rdq(Acp.Cp W p d (n + 1), g₀.rsp + 8#64 + 8) → Z.cpu.gpr.rsp = g₀.rsp + 8#64 + 8 + 8 →
      Z.cpu.gpr.r12 = g₀.r12 → Z.cpu.gpr.r13 = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 →
      Z.cpu.gpr.r15 = g₀.r15 → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Acp.Cp W p d j) →
      X.cpu.rip = acc_at.add 64 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rcx = d →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hci hkp
    have hjn : j = n := by omega
    subst hjn
    have es : X.cpu.gpr.rbx + X.cpu.gpr.rax = p.add j := by rw [hkp.2.1, hp, hax]; rfl
    have ed : X.cpu.gpr.rcx + X.cpu.gpr.rax = d.add j := by rw [hci, hax]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (Nat.le_refl _) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rbx + X.cpu.gpr.rax) == 0) = true := by
      rw [es, hb]; exact beq_iff_eq.2 hz
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbx + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (Nat.le_refl _)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rcx + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (Nat.le_refl _)
    have hsp : X.cpu.gpr.rsp = g₀.rsp := hkp.1
    refine (c_64 prof).run c hin _ hK hA hrip
      (vc_64z hz' hf1 hw1 (by rw [hsp]; exact l1) (by rw [hsp]; exact l2)) ?_
    rintro j' g fl V₁ ⟨rfl, hbx, hbp, hs', h12, h13, h14, h15, hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    obtain ⟨-, -, -, k12, k13, k14, k15⟩ := hkp
    refine k Y t₁ hKY hAY hrY ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hgY, hbx, hsp]; rfl
    · rw [hgY, hbp, hsp]; rfl
    · rw [hgY, hs', hsp]
    · rw [hgY, h12, k12]
    · rw [hgY, h13, k13]
    · rw [hgY, h14, k14]
    · rw [hgY, h15, k15]
  | succ m ih =>
    intro j hj X t hK hA hrip hax hci hkp
    have es : X.cpu.gpr.rbx + X.cpu.gpr.rax = p.add j := by rw [hkp.2.1, hp, hax]; rfl
    have ed : X.cpu.gpr.rcx + X.cpu.gpr.rax = d.add j := by rw [hci, hax]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (by omega) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rbx + X.cpu.gpr.rax) == 0) = false := by
      rw [es, hb]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbx + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rcx + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (by omega)
    refine (c_64 prof).run c hin _ hK hA hrip (vc_64n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hax', hci', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (by rw [hgY, hci', hci])
      (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hax', hax]
    exact (BitVec.ofNat_add j 1).symm

end FV7z.Acc
