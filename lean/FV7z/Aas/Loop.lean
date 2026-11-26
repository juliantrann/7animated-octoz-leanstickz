import FV7z.Aas.Cuts
import FV7z.Aac.Loop
/-!
# The pieces and the copy loop of `AString::operator= (const AString &)` (PLAN.md §M, M1)

7-Zip's `AString::operator= (const AString &s)` at `0x44c550` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`,
`&s` in `rsi`:

- at 0 `push r13; push r12; mov r12, rdi; push rbp; push rbx; sub rsp, 8; cmp rsi, rdi; je 71` (`&s == this`), at 22
  `mov r13d, [rsi + 8]` (`s._len`); `mov rbp, rsi; cmp [rdi + 12], r13d; jb 88` (`_limit` below it), at 35
  `mov rbx, [rdi]` (`_chars`);
- at 38 `mov [r12 + 8], r13d` (`_len`); `mov rax, [rbp]` (`s._chars`); `xor edx, edx`;
- the copy at 56: `movzx ecx, byte [rax + rdx]; mov [rbx + rdx], cl; add rdx, 1; test cl, cl; jne 56`;
- at 71 `add rsp, 8; mov rax, r12; pop rbx; pop rbp; pop r12; pop r13` and the `ret` at 84;
- at 88 `mov edi, r13d; add rdi, 1` to the `call` of `operator new []` at 95; at 100 `mov rdi, [r12]; mov rbx, rax;
  test rdi, rdi; je 117` and the `call` of `operator delete []` at 112; at 117 `mov [r12], rbx; mov [r12 + 12], r13d;
  jmp 38`.

The bytes copied are `Acp.Cp`, as in `AString (const AString &)` (`FV7z/Acp/Loop.lean`); the bytes after the pushes
are `Aac.V0`.

- `gS`: the registers after the pushes.
- `vc_0s`, `vc_0c`, `vc_0b`: from the entry at `&s == this` (to 71), else at `_limit` not below `s._len` (to 38) or
  below it (to the `call` at 95); `vc_38`, `vc_56n`, `vc_56z`, `vc_71`, `vc_100`, `vc_117`: the other pieces.
- `loop`: the copy loop by induction.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Aas

/-- The registers after `push r13; push r12; mov r12, rdi; push rbp; push rbx; sub rsp, 8`. -/
abbrev gS (g : Gprs) : Gprs :=
  { g with r12 := g.rdi, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry at `&s == this`: to 71. -/
theorem vc_0s {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)) (he : g.rsi = g.rdi) :
    W_0 F Wl (fun j' g' _ V' => j' = 71 ∧ g' = gS g ∧ V' = Aac.V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 he ⊢
  subst he
  wpx [W_0, o0, gS, Aac.V0, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- From the entry at `&s != this`, `_limit` (`M`) not below `s._len` (`L`): `_chars` (`T`) into `rbx`, to 38. -/
theorem vc_0c {g : Gprs} {f : Rflags} {V : Addr → Byte} {L M : BitVec 32} {T : BitVec 64}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)) (he : g.rsi ≠ g.rdi)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hLd : rdd(Aac.V0 V g, g.rsi + 8#64) = L) (hMd : rdd(Aac.V0 V g, g.rdi + 12#64) = M)
    (hTd : rdq(Aac.V0 V g, g.rdi) = T) (hL : ¬ M.toNat < L.toNat) :
    W_0 F Wl (fun j' g' _ V' => j' = 38 ∧
      g' = { gS g with r13 := BitVec.setWidth 64 L, rbp := g.rsi, rbx := T } ∧ V' = Aac.V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Aac.V0] at hs1 hs2 hs3 hs4 he f8 f12 f0 hLd hMd hTd ⊢
  wpx [W_0, W_22, W_35, o0, o1, o2, Op.cmpmr, he, hLd, hMd, hTd, hL, gS, Aac.V0, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- From the entry at `&s != this`, `_limit` (`M`) below `s._len` (`L`): `rdi` = `L + 1`, to the `call` at 95. -/
theorem vc_0b {g : Gprs} {f : Rflags} {V : Addr → Byte} {L M : BitVec 32}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)) (he : g.rsi ≠ g.rdi)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i)) (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i))
    (hLd : rdd(Aac.V0 V g, g.rsi + 8#64) = L) (hMd : rdd(Aac.V0 V g, g.rdi + 12#64) = M)
    (hL : M.toNat < L.toNat) :
    W_0 F Wl (fun j' g' _ V' => j' = 95 ∧
      g' = { gS g with r13 := BitVec.setWidth 64 L, rbp := g.rsi, rdi := BitVec.setWidth 64 L + 1#64 } ∧
      V' = Aac.V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Aac.V0] at hs1 hs2 hs3 hs4 he f8 f12 hLd hMd ⊢
  wpx [W_0, W_22, W_88, o0, o1, o6, Op.cmpmr, he, hLd, hMd, hL, gS, Aac.V0, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- `mov [r12 + 8], r13d; mov rax, [rbp]; xor edx, edx`, to the copy loop at 56. -/
theorem vc_38 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) :
    W_38 F Wl (fun j' g' _ V' => j' = 56 ∧
      g' = { g with
        rax := rdq(Vst V (g.r12 + 8#64) (toBytesLE (BitVec.setWidth 32 g.r13) 4), g.rbp), rdx := 0#64 } ∧
      V' = Vst V (g.r12 + 8#64) (toBytesLE (BitVec.setWidth 32 g.r13) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw f0 ⊢
  wpx [W_38, o3, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at a byte not 0: the byte stored, `rdx` one on, back to 56. -/
theorem vc_56n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rax + g.rdx) == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rax + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rbx + g.rdx) i)) :
    W_56 F Wl (fun j' g' _ V' => j' = 56 ∧ g'.rdx = g.rdx + 1#64 ∧ g'.rax = g.rax ∧ Kp g g' ∧
      V' = Vst V (g.rbx + g.rdx) [V (g.rax + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_56, o4, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at the 0: the 0 stored, to 71. -/
theorem vc_56z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rax + g.rdx) == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rax + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rbx + g.rdx) i)) :
    W_56 F Wl (fun j' g' _ V' => j' = 71 ∧ Kp g g' ∧ V' = Vst V (g.rbx + g.rdx) [V (g.rax + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_56, o4, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `add rsp, 8; mov rax, r12; pop rbx; pop rbp; pop r12; pop r13`, to the `ret` at 84. -/
theorem vc_71 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i)) :
    W_71 F Wl (fun j' g' _ V' => j' = 84 ∧ g'.rbx = rdq(V, g.rsp + 8#64) ∧ g'.rbp = rdq(V, g.rsp + 8#64 + 8) ∧
      g'.r12 = rdq(V, g.rsp + 8#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8) ∧
      g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 ∧ g'.rax = g.r12 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l1 l2 l3 l4 ⊢
  wpx [W_71, o5, eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new []`: `mov rdi, [r12]; mov rbx, rax; test rdi, rdi; je 117`, else to the `call` at 112. -/
theorem vc_100 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (h117 : rdq(V, g.r12) = 0 → ∀ fl, Q 117 { g with rdi := rdq(V, g.r12), rbx := g.rax } fl V)
    (h112 : rdq(V, g.r12) ≠ 0 → ∀ fl, Q 112 { g with rdi := rdq(V, g.r12), rbx := g.rax } fl V) :
    W_100 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h117 h112 ⊢
  by_cases h0 : rdq(V, r12) = 0
  · have hb : (rdq(V, r12) == 0) = true := beq_iff_eq.2 h0
    wpx [W_100, o7, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h117 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hb : (rdq(V, r12) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_100, o7, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h112 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- `mov [r12], rbx; mov [r12 + 12], r13d; jmp 38`. -/
theorem vc_117 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.r12 i)) (hw12 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 12#64) i)) :
    W_117 F Wl (fun j' g' _ V' => j' = 38 ∧ g' = g ∧
      V' = Vst (Vst V g.r12 (toBytesLE g.rbx 8)) (g.r12 + 12#64) (toBytesLE (BitVec.setWidth 32 g.r13) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw0 hw12 ⊢
  wpx [W_117, o8]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The copy loop from 56 at the index `j` of the `n` bytes not 0 and a 0 at `p` (in `W`, `rax` = `p`), the first `j`
stored at `d` (`rbx`): on to 71 with all `n + 1` stored and the registers a call keeps as at `g₀`. By induction on
`n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aas_at aas) {W : Addr → Byte} {p d : Addr} {n : Nat}
    {g₀ : Gprs} (hnz : ∀ i < n, W (p.add i) ≠ 0) (hz : W (p.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hw : ∀ i, i ≤ n → Foot Wl (d.add i))
    (hsep : ∀ i, i ≤ n → ∀ j, j ≤ n → p.add i ≠ d.add j) (hd : g₀.rbx = d)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Acp.Cp W p d (n + 1)) →
      Z.cpu.rip = aas_at.add 71 → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Acp.Cp W p d j) →
      X.cpu.rip = aas_at.add 56 → X.cpu.gpr.rdx = BitVec.ofNat 64 j → X.cpu.gpr.rax = p → Kp g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdx hax hkp
    have hjn : j = n := by omega
    subst hjn
    have es : X.cpu.gpr.rax + X.cpu.gpr.rdx = p.add j := by rw [hax, hdx]; rfl
    have ed : X.cpu.gpr.rbx + X.cpu.gpr.rdx = d.add j := by rw [hkp.2.1, hd, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (Nat.le_refl _) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rax + X.cpu.gpr.rdx) == 0) = true := by
      rw [es, hb]; exact beq_iff_eq.2 hz
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rax + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, es]
      exact hf j (Nat.le_refl _)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rbx + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, ed]
      exact hw j (Nat.le_refl _)
    refine (c_56 prof).run c hin _ hK hA hrip (vc_56z hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    exact k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp'))
  | succ m ih =>
    intro j hj X t hK hA hrip hdx hax hkp
    have es : X.cpu.gpr.rax + X.cpu.gpr.rdx = p.add j := by rw [hax, hdx]; rfl
    have ed : X.cpu.gpr.rbx + X.cpu.gpr.rdx = d.add j := by rw [hkp.2.1, hd, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (by omega) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rax + X.cpu.gpr.rdx) == 0) = false := by
      rw [es, hb]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rax + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rbx + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := (by omega)
      rw [addr_add_zero, ed]
      exact hw j (by omega)
    refine (c_56 prof).run c hin _ hK hA hrip (vc_56n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hax', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    · rw [hgY, hdx', hdx]
      exact (BitVec.ofNat_add j 1).symm
    · rw [hgY, hax', hax]

end FV7z.Aas
