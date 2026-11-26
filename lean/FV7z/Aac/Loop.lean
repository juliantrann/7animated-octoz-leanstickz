import FV7z.Aac.Cuts
import FV7z.Acc.Loop
/-!
# The loops of `AString::operator= (const char *)` (PLAN.md §M, M1)

The two loops of `AString::operator= (const char *s)` at `0x44c4c0` in `7zzs`:

- the length: at 0 `push r13; mov r13, rdi; push r12; push rbp; mov rbp, rsi; push rbx; xor ebx, ebx; sub rsp, 8;
  cmp byte [rsi], 0; je 51`, then at 32 `lea edi, [rbx + 1]; cmp byte [rbp + rdi], 0; mov rbx, rdi; jne 32`, `rbp` =
  `s`, `ebx` the length so far; at the 0 `cmp [r13 + 12], edi; jb 96` (`_limit` below the length) and at 96
  `add rdi, 1` to the `call` of `operator new []` at 100, else to 51;
- the copy at 64: `movzx ecx, byte [rbp + rdx]; mov [r12 + rdx], cl; add rdx, 1; test cl, cl; jne 64`, `r12` the
  buffer, `rdx` the index; at the 0 (stored too) on to `add rsp, 8; mov rax, r13; pop rbx; pop rbp; pop r12; pop r13`
  and the `ret` at 94.

The bytes copied are `Acp.Cp`, as in `AString (const AString &)` (`FV7z/Acp/Loop.lean`).

- `gS`, `V0`: the registers and the bytes after the pushes; `nx`: `ebx + 1`, zero-extended; `Ks`: the registers the
  length loop keeps.
- `vc_0z`, `vc_0n`: from the entry at an empty and a non-empty string; `vc_32n`, `vc_32zb`, `vc_32zs`: the length
  loop at a byte not 0, and at the 0 with `_limit` below the length or not; `slen`: the length loop by induction.
- `vc_64n`, `vc_64z`, `loop`: the copy loop.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Aac

/-- The registers after `push r13; mov r13, rdi; push r12; push rbp; mov rbp, rsi; push rbx; xor ebx, ebx;
`sub rsp, 8`. -/
abbrev gS (g : Gprs) : Gprs :=
  { g with r13 := g.rdi, rbp := g.rsi, rbx := 0#64, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 }

/-- The bytes after the four pushes. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- `lea edi, [rbx + 1]`. -/
abbrev nx (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rbx + 1#64))

/-- The registers the length loop keeps. -/
def Ks (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry at an empty string: to 51. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i))
    (hz : Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
      (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8) g.rsi = 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 51 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 hf hz ⊢
  wpx [W_0, W_27, o0, o1, Op.cmpmi, Tun.rd1, BitVec.sub_zero, BitVec.xor_self, BitVec.setWidth_zero, hz, gS, V0,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
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
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i))
    (hz : Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
      (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8) g.rsi ≠ 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 32 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 hf hz ⊢
  wpx [W_0, W_27, o0, o1, Op.cmpmi, Tun.rd1, BitVec.sub_zero, BitVec.xor_self, BitVec.setWidth_zero, hz, gS, V0,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The length loop at a byte not 0: back to 32, `rbx` = `rdi` = `nx`. -/
theorem vc_32n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nx g) i)) (hz : V (g.rbp + nx g) ≠ 0#8) :
    W_32 F Wl (fun j' g' _ V' => j' = 32 ∧ g' = { g with rdi := nx g, rbx := nx g } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz ⊢
  wpx [W_32, W_45, W_96, o2, o3, o8, Op.cmpmi, Tun.rd1, BitVec.sub_zero, hz, decide_true, decide_false,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies,
    implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The length loop at the 0, `_limit` below the length: `add rdi, 1`, to the `call` at 100. -/
theorem vc_32zb {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nx g) i)) (hz : V (g.rbp + nx g) = 0#8)
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 12#64) i))
    (hL : rdd(V, g.r13 + 12#64).toNat < (BitVec.setWidth 32 (g.rbx + 1#64)).toNat) :
    W_32 F Wl (fun j' g' _ V' => j' = 100 ∧ g' = { g with rdi := nx g + 1#64, rbx := nx g } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz hl4 hL ⊢
  wpx [W_32, W_45, W_96, o2, o3, o8, Op.cmpmi, Op.cmpmr, Tun.rd1, BitVec.sub_zero, hz, cond_2, subF_cf, hL,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The length loop at the 0, `_limit` not below the length: to 51. -/
theorem vc_32zs {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nx g) i)) (hz : V (g.rbp + nx g) = 0#8)
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 12#64) i))
    (hL : ¬ rdd(V, g.r13 + 12#64).toNat < (BitVec.setWidth 32 (g.rbx + 1#64)).toNat) :
    W_32 F Wl (fun j' g' _ V' => j' = 51 ∧ g' = { g with rdi := nx g, rbx := nx g } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz hl4 hL ⊢
  wpx [W_32, W_45, W_96, o2, o3, o8, Op.cmpmi, Op.cmpmr, Tun.rd1, BitVec.sub_zero, hz, cond_2, subF_cf, hL,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- The copy loop at a byte not 0: the byte stored, `rdx` one on, back to 64. -/
theorem vc_64n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rbp + g.rdx) == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.r12 + g.rdx) i)) :
    W_64 F Wl (fun j' g' _ V' => j' = 64 ∧ g'.rdx = g.rdx + 1#64 ∧ Kp g g' ∧
      V' = Vst V (g.r12 + g.rdx) [V (g.rbp + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_64, W_81, o6, o7, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The copy loop at the 0: the 0 stored, then `add rsp, 8; mov rax, r13; pop rbx; pop rbp; pop r12; pop r13` to the
`ret` at 94. -/
theorem vc_64z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (V (g.rbp + g.rdx) == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.r12 + g.rdx) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i)) :
    W_64 F Wl (fun j' g' _ V' => j' = 94 ∧ g'.rbx = rdq(V', g.rsp + 8#64) ∧ g'.rbp = rdq(V', g.rsp + 8#64 + 8) ∧
      g'.r12 = rdq(V', g.rsp + 8#64 + 8 + 8) ∧ g'.r13 = rdq(V', g.rsp + 8#64 + 8 + 8 + 8) ∧
      g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 ∧ g'.rax = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
      V' = Vst V (g.r12 + g.rdx) [V (g.rbp + g.rdx)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw l1 l2 l3 l4 ⊢
  wpx [W_64, W_81, o6, o7, Tun.rd1, BitVec.and_self, hz, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The length loop from 32 at the length `j` so far (`j + 1 ≤ n`) of the `n` bytes not 0 and a 0 at `p` (in `W`,
`rbp` = `p`): with `_limit` (the 4 bytes at `r13 + 12`) below `n` on to the `call` at 100 with `rbx` = `n`, `rdi` =
`n + 1` (`kb`), else to 51 with `rbx` = `n` (`ks`), the registers `Ks` keeps as at `g₀`. By induction on
`n - j - 1`. -/
theorem slen (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aac_at aac) {W : Addr → Byte} {p : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 32) (hnz : ∀ i < n, W (p.add i) ≠ 0#8) (hz : W (p.add n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hp : g₀.rbp = p)
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g₀.r13 + 12#64) i))
    (kb : rdd(W, g₀.r13 + 12#64).toNat < n → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem W → Z.cpu.rip = aac_at.add 100 → Z.cpu.gpr.rbx = BitVec.ofNat 64 n →
      Z.cpu.gpr.rdi = BitVec.ofNat 64 (n + 1) → Ks g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t')
    (ks : ¬ rdd(W, g₀.r13 + 12#64).toNat < n → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem W → Z.cpu.rip = aac_at.add 51 → Z.cpu.gpr.rbx = BitVec.ofNat 64 n →
      Ks g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + 1 + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = aac_at.add 32 → X.cpu.gpr.rbx = BitVec.ofNat 64 j → Ks g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hbx hks
    obtain rfl : n = j + 1 := by omega
    have enx : nx X.cpu.gpr = BitVec.ofNat 64 (j + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)) = _
      rw [hbx, Acc.nx_ofNat j hn]
    have ea : X.cpu.gpr.rbp + nx X.cpu.gpr = p.add (j + 1) := by
      rw [enx, hks.2.1, hp]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + nx X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (Nat.le_refl _)
    have h13 : X.cpu.gpr.r13 = g₀.r13 := hks.2.2.2.1
    have hl4' : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.r13 + 12#64) i) := by rw [h13]; exact hl4
    have hw32 : (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)).toNat = j + 1 := by
      rw [hbx]
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hz1 : W (X.cpu.gpr.rbp + nx X.cpu.gpr) = 0#8 := by rw [ea]; exact hz
    by_cases hL : rdd(W, g₀.r13 + 12#64).toNat < j + 1
    · have hL' : rdd(W, X.cpu.gpr.r13 + 12#64).toNat < (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)).toNat := by
        rw [hw32, h13]; exact hL
      refine (c_32 prof).run c hin _ hK hA hrip (vc_32zb hf1 hz1 hl4' hL') ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine kb hL Y t₁ hKY hAY hrY ?_ ?_ (by rw [hgY]; exact hks)
      · rw [hgY]; exact enx
      · rw [hgY]
        show nx X.cpu.gpr + 1#64 = _
        rw [enx]
        exact (BitVec.ofNat_add (j + 1) 1).symm
    · have hL' : ¬ rdd(W, X.cpu.gpr.r13 + 12#64).toNat < (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)).toNat := by
        rw [hw32, h13]; exact hL
      refine (c_32 prof).run c hin _ hK hA hrip (vc_32zs hf1 hz1 hl4' hL') ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ks hL Y t₁ hKY hAY hrY ?_ (by rw [hgY]; exact hks)
      rw [hgY]; exact enx
  | succ m ih =>
    intro j hj X t hK hA hrip hbx hks
    have enx : nx X.cpu.gpr = BitVec.ofNat 64 (j + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)) = _
      rw [hbx, Acc.nx_ofNat j (by omega)]
    have ea : X.cpu.gpr.rbp + nx X.cpu.gpr = p.add (j + 1) := by
      rw [enx, hks.2.1, hp]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + nx X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (by omega)
    refine (c_32 prof).run c hin _ hK hA hrip (vc_32n hf1 (by rw [ea]; exact hnz (j + 1) (by omega))) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (by rw [hgY]; exact hks)
    rw [hgY]; exact enx

/-- The copy loop from 64 at the index `j` of the `n` bytes not 0 and a 0 at `p` (in `W`, `rbp` = `p`), the first `j`
stored at `d` (`r12`): on to the `ret` at 94 with all `n + 1` stored, `rbx`, `rbp`, `r12`, `r13` popped, `rax` = the
`r13` of `g₀` and `r14`, `r15` as at `g₀`. By induction on `n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L aac_at aac) {W : Addr → Byte} {p d : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 63) (hnz : ∀ i < n, W (p.add i) ≠ 0) (hz : W (p.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hw : ∀ i, i ≤ n → Foot Wl (d.add i))
    (hsep : ∀ i, i ≤ n → ∀ j, j ≤ n → p.add i ≠ d.add j) (hp : g₀.rbp = p) (hd : g₀.r12 = d)
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64 + 8 + 8 + 8) i))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Acp.Cp W p d (n + 1)) →
      Z.cpu.rip = aac_at.add 94 → Z.cpu.gpr.rbx = rdq(Acp.Cp W p d (n + 1), g₀.rsp + 8#64) →
      Z.cpu.gpr.rbp = rdq(Acp.Cp W p d (n + 1), g₀.rsp + 8#64 + 8) →
      Z.cpu.gpr.r12 = rdq(Acp.Cp W p d (n + 1), g₀.rsp + 8#64 + 8 + 8) →
      Z.cpu.gpr.r13 = rdq(Acp.Cp W p d (n + 1), g₀.rsp + 8#64 + 8 + 8 + 8) →
      Z.cpu.gpr.rsp = g₀.rsp + 8#64 + 8 + 8 + 8 + 8 → Z.cpu.gpr.rax = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 →
      Z.cpu.gpr.r15 = g₀.r15 → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Acp.Cp W p d j) →
      X.cpu.rip = aac_at.add 64 → X.cpu.gpr.rdx = BitVec.ofNat 64 j → Kp g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdx hkp
    have hjn : j = n := by omega
    subst hjn
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rdx = p.add j := by rw [hkp.2.2.1, hp, hdx]; rfl
    have ed : X.cpu.gpr.r12 + X.cpu.gpr.rdx = d.add j := by rw [hkp.2.2.2.1, hd, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (Nat.le_refl _) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rbp + X.cpu.gpr.rdx) == 0) = true := by
      rw [es, hb]; exact beq_iff_eq.2 hz
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (Nat.le_refl _)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.r12 + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (Nat.le_refl _)
    have hsp : X.cpu.gpr.rsp = g₀.rsp := hkp.1
    refine (c_64 prof).run c hin _ hK hA hrip
      (vc_64z hz' hf1 hw1 (by rw [hsp]; exact l1) (by rw [hsp]; exact l2) (by rw [hsp]; exact l3)
        (by rw [hsp]; exact l4)) ?_
    rintro j' g fl V₁ ⟨rfl, hbx, hbp, h12, h13, hs', hax, h14, h15, hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    obtain ⟨-, -, -, -, k13, k14, k15⟩ := hkp
    refine k Y t₁ hKY hAY hrY ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hgY, hbx, hsp]; rfl
    · rw [hgY, hbp, hsp]; rfl
    · rw [hgY, h12, hsp]; rfl
    · rw [hgY, h13, hsp]; rfl
    · rw [hgY, hs', hsp]
    · rw [hgY, hax, k13]
    · rw [hgY, h14, k14]
    · rw [hgY, h15, k15]
  | succ m ih =>
    intro j hj X t hK hA hrip hdx hkp
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rdx = p.add j := by rw [hkp.2.2.1, hp, hdx]; rfl
    have ed : X.cpu.gpr.r12 + X.cpu.gpr.rdx = d.add j := by rw [hkp.2.2.2.1, hd, hdx]; rfl
    have hb : Acp.Cp W p d j (p.add j) = W (p.add j) :=
      Acp.Cp_out W p d j _ fun i hi => hsep j (by omega) i (by omega)
    have hz' : (Acp.Cp W p d j (X.cpu.gpr.rbp + X.cpu.gpr.rdx) == 0) = false := by
      rw [es, hb]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.r12 + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (by omega)
    refine (c_64 prof).run c hin _ hK hA hrip (vc_64n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hdx', hdx]
    exact (BitVec.ofNat_add j 1).symm

end FV7z.Aac
