import FV7z.Uac.Cuts
import FV7z.Uca.Holds
/-!
# The loops of `UString::operator= (const char *)` (PLAN.md §M, M1)

The two loops of `UString::operator= (const char *s)` at `0x44d8a0` in `7zzs` (`CPP/Common/MyString.cpp`):

- the length: at 0 `push r15; mov r15, rdi; push r14; push r13; push r12; push rbp; mov rbp, rsi; push rbx;
  xor ebx, ebx; sub rsp, 8; cmp byte [rsi], 0; je 176` (176: `mov r14, [rdi]; xor r12d, r12d; jmp 101`), then at 40
  `lea eax, [rbx + 1]; mov r13d, ebx; cmp byte [rbp + rax], 0; mov rbx, rax; jne 40`, `rbp` = `s`, `ebx` the length
  so far; at the 0 `lea r12, [rax * 4]; cmp [r15 + 12], eax; jb 136` (`_limit` below the length; 136:
  `lea rdi, [r12 + 4]` to the `call` of `operator new []` at 141), else `mov r14, [r15]` to 73;
- the copy at 80 (from 73: `xor edx, edx; test ebx, ebx; je 101`): `movzx ecx, byte [rbp + rdx];
  mov [r14 + rdx * 4], ecx; mov rcx, rdx; add rdx, 1; cmp r13, rcx; jne 80`, `r14` the buffer, `rdx` the index,
  `r13` = `n - 1`; on to 101.

The bytes copied, each widened to 4, are `Uca.Cw`, as in `UString (const char *)` (`FV7z/Uca/Holds.lean`).

- `gS`, `V0`: the registers and the bytes after the pushes; `nx`: `ebx + 1`, zero-extended; `Ks`: the registers the
  length loop keeps; `Ex`: the registers at its exits.
- `vc_0z`, `vc_0n`: from the entry at an empty and a non-empty string; `vc_40n`, `vc_40zb`, `vc_40zs`: the length
  loop at a byte not 0, and at the 0 with `_limit` below the length or not; `slen`: the length loop by induction.
- `vc_73`, `vc_80n`, `vc_80z`, `loop`: the copy loop.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Uac
open FV7z.Uca (Cw)

/-- The registers after the pushes, `mov r15, rdi; mov rbp, rsi; xor ebx, ebx; sub rsp, 8`. -/
abbrev gS (g : Gprs) : Gprs :=
  { g with r15 := g.rdi, rbp := g.rsi, rbx := 0#64, rsp := g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 8 }

/-- The bytes after the six pushes. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- `lea eax, [rbx + 1]`. -/
abbrev nx (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 (g.rbx + 1#64))

/-- `mov r13d, ebx`. -/
abbrev lo (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx)

/-- The registers the length loop keeps. -/
def Ks (g₀ g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- The registers at the length loop's exits, for the length `n`. -/
def Ex (g₀ : Gprs) (n : Nat) (g : Gprs) : Prop :=
  g.rsp = g₀.rsp ∧ g.rbp = g₀.rbp ∧ g.r15 = g₀.r15 ∧ g.rbx = BitVec.ofNat 64 n ∧
    g.r13 = BitVec.ofNat 64 (n - 1) ∧ g.r12 = BitVec.ofNat 64 (4 * n)

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 2000000 in
/-- From the entry at an empty string: `mov r14, [rdi]; xor r12d, r12d`, to 101. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hz : V0 V g g.rsi = 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 101 ∧ g' = { gS g with r14 := rdq(V0 V g, g.rdi), r12 := 0#64 } ∧
      V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V0] at hs1 hs2 hs3 hs4 hs5 hs6 hf f0 hz ⊢
  wpx [W_0, W_176, W_35, o0, o1, o12, Op.cmpmi, Tun.rd1, BitVec.sub_zero, Ucw.xz, BitVec.xor_self,
    BitVec.setWidth_zero, hz, gS, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 2000000 in
/-- From the entry at a string not empty: to the loop's head at 40. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hf : ∀ i < 1, Foot F.data (Addr.add g.rsi i)) (hz : V0 V g g.rsi ≠ 0#8) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = gS g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [V0] at hs1 hs2 hs3 hs4 hs5 hs6 hf hz ⊢
  wpx [W_0, W_176, W_35, o0, o1, o12, Op.cmpmi, Tun.rd1, BitVec.sub_zero, Ucw.xz, BitVec.xor_self,
    BitVec.setWidth_zero, hz, gS, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The length loop at a byte not 0: back to 40, `rax` = `rbx` = `nx`, `r13` = `lo`. -/
theorem vc_40n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nx g) i)) (hz : V (g.rbp + nx g) ≠ 0#8) :
    W_40 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = { g with rax := nx g, r13 := lo g, rbx := nx g } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz ⊢
  wpx [W_40, W_56, W_136, W_70, o2, o3, o4, o9, Op.cmpmi, Op.cmpmr, Tun.rd1, BitVec.sub_zero, hz, decide_true,
    decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The length loop at the 0, `_limit` below the length: `lea r12, [rax * 4]; lea rdi, [r12 + 4]`, to the `call`
at 141. -/
theorem vc_40zb {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nx g) i)) (hz : V (g.rbp + nx g) = 0#8)
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g.r15 + 12#64) i))
    (hL : rdd(V, g.r15 + 12#64).toNat < (BitVec.setWidth 32 (g.rbx + 1#64)).toNat) :
    W_40 F Wl (fun j' g' _ V' => j' = 141 ∧
      g' = { g with rax := nx g, r13 := lo g, rbx := nx g, r12 := nx g * 4#64, rdi := nx g * 4#64 + 4#64 } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz hl4 hL ⊢
  wpx [W_40, W_56, W_136, W_70, o2, o3, o4, o9, Op.cmpmi, Op.cmpmr, Tun.rd1, BitVec.sub_zero, hz, cond_2, subF_cf,
    hL, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The length loop at the 0, `_limit` not below the length: `lea r12, [rax * 4]; mov r14, [r15]`, to 73. -/
theorem vc_40zs {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + nx g) i)) (hz : V (g.rbp + nx g) = 0#8)
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g.r15 + 12#64) i)) (f15 : ∀ i < 8, Foot F.data (Addr.add g.r15 i))
    (hL : ¬ rdd(V, g.r15 + 12#64).toNat < (BitVec.setWidth 32 (g.rbx + 1#64)).toNat) :
    W_40 F Wl (fun j' g' _ V' => j' = 73 ∧
      g' = { g with rax := nx g, r13 := lo g, rbx := nx g, r12 := nx g * 4#64, r14 := rdq(V, g.r15) } ∧
      V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hf hz hl4 f15 hL ⊢
  wpx [W_40, W_56, W_136, W_70, o2, o3, o4, o9, Op.cmpmi, Op.cmpmr, Tun.rd1, BitVec.sub_zero, hz, cond_2, subF_cf,
    hL, decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false,
    false_implies, true_implies, implies_true, eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- `xor edx, edx; test ebx, ebx; je 101` (not taken, `n > 0`), to the copy loop at 80. -/
theorem vc_73 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {n : Nat}
    (hb : g.rbx = BitVec.ofNat 64 n) (hn : 0 < n) (hn' : n < 2 ^ 32)
    (h : ∀ fl, Q 80 { g with rdx := 0#64 } fl V) : W_73 F Wl Q g f V := by
  have hX : (BitVec.setWidth 32 g.rbx == 0) = false := by
    rw [beq_eq_false_iff_ne, hb]
    intro e
    have := congrArg BitVec.toNat e
    simp at this <;> omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hX h ⊢
  wpx [W_73, W_79, o5, o6, Ucw.xz, BitVec.and_self, hX, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    true_implies, implies_true]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

set_option maxHeartbeats 1000000 in
/-- The copy loop at the index `rdx` short of the last (`r13`): the byte stored as 4, `rdx` one on, back to 80. -/
theorem vc_80n {g : Gprs} {f : Rflags} {V : Addr → Byte} (hX : g.r13 ≠ g.rdx)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.r14 + g.rdx * 4#64) i)) :
    W_80 F Wl (fun j' g' _ V' => j' = 80 ∧ g'.rdx = g.rdx + 1#64 ∧ Kp g g' ∧
      V' = Vst V (g.r14 + g.rdx * 4#64) (toBytesLE (BitVec.setWidth 32 (V (g.rbp + g.rdx))) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hX hf hw ⊢
  have hX' : rdx ≠ r13 := fun e => hX e.symm
  wpx [W_80, o7, Tun.rd1, hX, hX', Kp, decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true, true_and]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)
  all_goals (congr 2; uca_tn)

set_option maxHeartbeats 1000000 in
/-- The copy loop at the last index (`rdx` = `r13`): the byte stored as 4, on to 101. -/
theorem vc_80z {g : Gprs} {f : Rflags} {V : Addr → Byte} (hX : g.r13 = g.rdx)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rbp + g.rdx) i))
    (hw : ∀ i < 4, Foot Wl (Addr.add (g.r14 + g.rdx * 4#64) i)) :
    W_80 F Wl (fun j' g' _ V' => j' = 101 ∧ Kp g g' ∧
      V' = Vst V (g.r14 + g.rdx * 4#64) (toBytesLE (BitVec.setWidth 32 (V (g.rbp + g.rdx))) 4)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hX hf hw ⊢
  subst hX
  wpx [W_80, o7, Tun.rd1, Kp, decide_true, decide_false, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true, eq_self_iff_true, and_self,
    and_true, true_and]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)
  all_goals (congr 2; uca_tn)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The length loop from 40 at the length `j` so far (`j + 1 ≤ n`) of the `n` bytes not 0 and a 0 at `p` (in `W`,
`rbp` = `p`): with `_limit` (the 4 bytes at `r15 + 12`) below `n` on to the `call` at 141 with `rdi` = `4 n + 4`
(`kb`), else to 73 with `r14` = `_chars` (`ks`), the registers as `Ex`. By induction on `n - j - 1`. -/
theorem slen (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uac_at uac) {W : Addr → Byte} {p : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 32) (hnz : ∀ i < n, W (p.add i) ≠ 0#8) (hz : W (p.add n) = 0#8)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hp : g₀.rbp = p)
    (hl4 : ∀ i < 4, Foot F.data (Addr.add (g₀.r15 + 12#64) i)) (f15 : ∀ i < 8, Foot F.data (Addr.add g₀.r15 i))
    (kb : rdd(W, g₀.r15 + 12#64).toNat < n → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem W → Z.cpu.rip = uac_at.add 141 → Ex g₀ n Z.cpu.gpr → Z.cpu.gpr.r14 = g₀.r14 →
      Z.cpu.gpr.rdi = BitVec.ofNat 64 (4 * n + 4) → GoG prof L o gev gP gE Z t')
    (ks : ¬ rdd(W, g₀.r15 + 12#64).toNat < n → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem W → Z.cpu.rip = uac_at.add 73 → Ex g₀ n Z.cpu.gpr →
      Z.cpu.gpr.r14 = rdq(W, g₀.r15) → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + 1 + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem W →
      X.cpu.rip = uac_at.add 40 → X.cpu.gpr.rbx = BitVec.ofNat 64 j → Ks g₀ X.cpu.gpr →
      GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hbx hks
    obtain rfl : n = j + 1 := by omega
    have enx : nx X.cpu.gpr = BitVec.ofNat 64 (j + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)) = _
      rw [hbx, Ucw.sk1 (k := j) hn]
    have elo : lo X.cpu.gpr = BitVec.ofNat 64 (j + 1 - 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rbx) = _
      rw [hbx]
      uca_tn
    have e4 : nx X.cpu.gpr * 4#64 = BitVec.ofNat 64 (4 * (j + 1)) := by
      rw [enx]
      uca_tn
    have ea : X.cpu.gpr.rbp + nx X.cpu.gpr = p.add (j + 1) := by
      rw [enx, hks.2.1, hp]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + nx X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (Nat.le_refl _)
    have h15 : X.cpu.gpr.r15 = g₀.r15 := hks.2.2.2.2
    have hl4' : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.r15 + 12#64) i) := by rw [h15]; exact hl4
    have f15' : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.r15 i) := by rw [h15]; exact f15
    have hw32 : (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)).toNat = j + 1 := by
      rw [hbx]
      simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hz1 : W (X.cpu.gpr.rbp + nx X.cpu.gpr) = 0#8 := by rw [ea]; exact hz
    by_cases hL : rdd(W, g₀.r15 + 12#64).toNat < j + 1
    · have hL' : rdd(W, X.cpu.gpr.r15 + 12#64).toNat < (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)).toNat := by
        rw [hw32, h15]; exact hL
      refine (c_40 prof).run c hin _ hK hA hrip (vc_40zb hf1 hz1 hl4' hL') ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine kb hL Y t₁ hKY hAY hrY ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_
      · rw [hgY]; exact hks.1
      · rw [hgY]; exact hks.2.1
      · rw [hgY]; exact h15
      · rw [hgY]; exact enx
      · rw [hgY]; exact elo
      · rw [hgY]; exact e4
      · rw [hgY]; exact hks.2.2.2.1
      · rw [hgY]
        show nx X.cpu.gpr * 4#64 + 4#64 = _
        rw [e4]
        uca_tn
    · have hL' : ¬ rdd(W, X.cpu.gpr.r15 + 12#64).toNat < (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)).toNat := by
        rw [hw32, h15]; exact hL
      refine (c_40 prof).run c hin _ hK hA hrip (vc_40zs hf1 hz1 hl4' f15' hL') ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
      refine ks hL Y t₁ hKY hAY hrY ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
      · rw [hgY]; exact hks.1
      · rw [hgY]; exact hks.2.1
      · rw [hgY]; exact h15
      · rw [hgY]; exact enx
      · rw [hgY]; exact elo
      · rw [hgY]; exact e4
      · rw [hgY]
        show rdq(_, X.cpu.gpr.r15) = _
        rw [h15]
  | succ m ih =>
    intro j hj X t hK hA hrip hbx hks
    have enx : nx X.cpu.gpr = BitVec.ofNat 64 (j + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 (X.cpu.gpr.rbx + 1#64)) = _
      rw [hbx, Ucw.sk1 (k := j) (by omega)]
    have ea : X.cpu.gpr.rbp + nx X.cpu.gpr = p.add (j + 1) := by
      rw [enx, hks.2.1, hp]; rfl
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + nx X.cpu.gpr) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ea]
      exact hf (j + 1) (by omega)
    have hz1 : W (X.cpu.gpr.rbp + nx X.cpu.gpr) ≠ 0#8 := by rw [ea]; exact hnz (j + 1) (by omega)
    refine (c_40 prof).run c hin _ hK hA hrip (vc_40n hf1 hz1) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
    exact ih (j + 1) (by omega) Y t₁ hKY hAY hrY (by rw [hgY]; exact enx) (by rw [hgY]; exact hks)

/-- The copy loop from 80 at the index `j` (`j + 1 ≤ n`) of the `n` bytes at `s` (`rbp`) to `d` (`r14`), `r13` =
`n - 1`: on to 101 with all `n` stored and the registers `Kp` keeps as at `g₀`. By induction on `n - j - 1`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L uac_at uac) {W : Addr → Byte} {s d : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 32) (hf : ∀ i ≤ n, Foot F.data (Addr.add s i))
    (hw : ∀ i < 4 * n + 4, Foot Wl (Addr.add d i)) (hp : g₀.rbp = s) (hd : g₀.r14 = d)
    (h13 : g₀.r13 = BitVec.ofNat 64 (n - 1))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Cw W s d n) →
      Z.cpu.rip = uac_at.add 101 → Kp g₀ Z.cpu.gpr → GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + 1 + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X →
      Agree F X.proc.mm.mem (Cw W s d j) → X.cpu.rip = uac_at.add 80 → X.cpu.gpr.rdx = BitVec.ofNat 64 j →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hdx hkp
    obtain rfl : n = j + 1 := by omega
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rdx = Addr.add s j := by rw [hkp.2.2.1, hp, hdx]; rfl
    have ed : X.cpu.gpr.r14 + X.cpu.gpr.rdx * 4#64 = Addr.add d (4 * j) := by
      rw [hkp.2.2.2.2.2.1, hd, hdx]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    have hX : X.cpu.gpr.r13 = X.cpu.gpr.rdx := by
      rw [hkp.2.2.2.2.1, h13, hdx]
      congr 1
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.r14 + X.cpu.gpr.rdx * 4#64) i) := fun i hi => by
      rw [ed, addr_add_add]
      exact hw _ (by omega)
    refine (c_80 prof).run c hin _ hK hA hrip (vc_80z hX hf1 hw4) ?_
    rintro j' g fl V₁ ⟨rfl, hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed] at hV
    subst hV
    exact k Y t₁ hKY hAY hrY (hkp.trans (Kp.of_eq hgY hkp'))
  | succ m ih =>
    intro j hj X t hK hA hrip hdx hkp
    have es : X.cpu.gpr.rbp + X.cpu.gpr.rdx = Addr.add s j := by rw [hkp.2.2.1, hp, hdx]; rfl
    have ed : X.cpu.gpr.r14 + X.cpu.gpr.rdx * 4#64 = Addr.add d (4 * j) := by
      rw [hkp.2.2.2.2.2.1, hd, hdx]
      apply BitVec.eq_of_toNat_eq
      simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    have hX : X.cpu.gpr.r13 ≠ X.cpu.gpr.rdx := by
      rw [hkp.2.2.2.2.1, h13, hdx]
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rbp + X.cpu.gpr.rdx) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw4 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.r14 + X.cpu.gpr.rdx * 4#64) i) := fun i hi => by
      rw [ed, addr_add_add]
      exact hw _ (by omega)
    refine (c_80 prof).run c hin _ hK hA hrip (vc_80n hX hf1 hw4) ?_
    rintro j' g fl V₁ ⟨rfl, hdx', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hdx', hdx]
    exact (BitVec.ofNat_add j 1).symm

end FV7z.Uac
