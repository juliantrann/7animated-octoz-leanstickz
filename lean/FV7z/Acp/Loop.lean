import FV7z.Acp.Cuts
import FV7z.Mys.Lem
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.RepStosb
import FV7z.Lemmas.Env
/-!
# The copy loop of `AString::AString (const AString &)` (PLAN.md §M, M1)

The loop at 40 of `AString (const AString &s)` at `0x44c420` in `7zzs`: `movzx edx, byte [rsi + rax]; mov [rcx + rax],
dl; add rax, 1; test dl, dl; jne 40`, `rsi` the source's bytes, `rcx` the new buffer, `rax` the index; at the 0 (stored
too) on to `add rsp, 8; pop rbx; pop rbp` and the `ret` at 61.

- `Cp W p d k`: the bytes `W` after the first `k` bytes at `p` were stored at `d`, one by one as the code stores
  them; `Cp_out`, `Cp_at`, `rd_far`: its bytes.
- `vc_40n`, `vc_40z`: the loop at a byte not 0 (back to 40) and at the 0 (to the `ret` at 61).
- `loop`: from 40, by induction on the bytes left.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Mys
namespace FV7z.Acp

/-- The bytes `W` after the first `k` bytes at `p` were stored at `d`, one by one. -/
def Cp (W : Addr → Byte) (p d : Addr) : Nat → Addr → Byte
  | 0 => W
  | k + 1 => Vst (Cp W p d k) (d.add k) [W (p.add k)]

/-- A byte not among the first `k` at `d`: as it was. -/
theorem Cp_out (W : Addr → Byte) (p d : Addr) : ∀ (k : Nat) (x : Addr), (∀ i < k, x ≠ d.add i) → Cp W p d k x = W x
  | 0, _, _ => rfl
  | k + 1, x, h => by
    show Vst (Cp W p d k) (d.add k) [W (p.add k)] x = W x
    rw [Vst_apart _ _ _ x fun i hi => by
      obtain rfl : i = 0 := by simp at hi; omega
      rw [addr_add_zero]
      exact h k (by omega)]
    exact Cp_out W p d k x fun i hi => h i (by omega)

/-- One of the first `k` bytes at `d`: the byte of `p` at its index. -/
theorem Cp_at (W : Addr → Byte) (p d : Addr) :
    ∀ (k : Nat), k ≤ 2 ^ 64 → ∀ i < k, Cp W p d k (d.add i) = W (p.add i)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, i, hi => by
    show Vst (Cp W p d k) (d.add k) [W (p.add k)] (d.add i) = _
    rcases Nat.lt_or_ge i k with h | h
    · rw [Vst_apart _ _ _ _ fun j hj => by
        obtain rfl : j = 0 := by simp at hj; omega
        rw [addr_add_zero]
        exact add_ne' d (by omega) (by omega) (by omega)]
      exact Cp_at W p d k (by omega) i h
    · obtain rfl : i = k := by omega
      show upd1 (Cp W p d i) (d.add i) (W (p.add i)) (d.add i) = _
      simp [upd1]

/-- Bytes apart from the first `k` at `d`: as they were. -/
theorem rd_far (W : Addr → Byte) (p d : Addr) {k : Nat} {a : Addr} {m : Nat}
    (h : ∀ b < m, ∀ i < k, a.add b ≠ d.add i) : (byteAddrs a m).map (Cp W p d k) = (byteAddrs a m).map W :=
  List.map_congr_left fun y hy => by
    obtain ⟨b, hb, rfl⟩ := mem_byteAddrs.1 hy
    exact Cp_out W p d k _ fun i hi => h b hb i hi

variable {F : Footprint} {Wl : List Rgn}

/-- The loop at a byte not 0: the byte stored, `rax` one on, back to 40. -/
theorem vc_40n {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (BitVec.setWidth 8 (BitVec.setWidth 32 (V (g.rsi + g.rax))) == 0) = false)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rsi + g.rax) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rcx + g.rax) i)) :
    W_40 F Wl (fun j' g' _ V' => j' = 40 ∧ g'.rax = g.rax + 1#64 ∧ g'.rsi = g.rsi ∧ g'.rcx = g.rcx ∧ Kp g g' ∧
      V' = Vst V (g.rcx + g.rax) [V (g.rsi + g.rax)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw ⊢
  wpx [W_40, W_55, o2, o3, Tun.rd1, BitVec.and_self, hz, Kp, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

/-- The loop at the 0: the 0 stored, then `add rsp, 8; pop rbx; pop rbp` to the `ret` at 61. -/
theorem vc_40z {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hz : (BitVec.setWidth 8 (BitVec.setWidth 32 (V (g.rsi + g.rax))) == 0) = true)
    (hf : ∀ i < 1, Foot F.data (Addr.add (g.rsi + g.rax) i)) (hw : ∀ i < 1, Foot Wl (Addr.add (g.rcx + g.rax) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i)) :
    W_40 F Wl (fun j' g' _ V' => j' = 61 ∧ g'.rbx = rdq(V', g.rsp + 8#64) ∧ g'.rbp = rdq(V', g.rsp + 8#64 + 8) ∧
      g'.rsp = g.rsp + 8#64 + 8 + 8 ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15 ∧
      V' = Vst V (g.rcx + g.rax) [V (g.rsi + g.rax)]) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz hf hw l1 l2 ⊢
  wpx [W_40, W_55, o2, o3, Tun.rd1, BitVec.and_self, hz, sw8b, sw8a, toBytesLE_one8, Bool.not_true,
    Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, true_implies, implies_true,
    eq_self_iff_true, and_self, and_true]
  all_goals repeat' (first | exact rfl | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The loop from 40 at the index `j` of the `n` bytes not 0 and a 0 at `p` (in `W`), the first `j` stored at `d`:
on to the `ret` at 61 with all `n + 1` stored, `rbx`, `rbp` popped and `r12` … `r15` as at `g₀`. By induction on
`n - j`. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L acp_at acp) {W : Addr → Byte} {p d : Addr} {n : Nat}
    {g₀ : Gprs} (hn : n < 2 ^ 63) (hnz : ∀ i < n, W (p.add i) ≠ 0) (hz : W (p.add n) = 0)
    (hf : ∀ i, i ≤ n → Foot F.data (p.add i)) (hw : ∀ i, i ≤ n → Foot Wl (d.add i))
    (hsep : ∀ i, i ≤ n → ∀ j, j ≤ n → p.add i ≠ d.add j)
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g₀.rsp + 8#64 + 8) i))
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Cp W p d (n + 1)) →
      Z.cpu.rip = acp_at.add 61 → Z.cpu.gpr.rbx = rdq(Cp W p d (n + 1), g₀.rsp + 8#64) →
      Z.cpu.gpr.rbp = rdq(Cp W p d (n + 1), g₀.rsp + 8#64 + 8) → Z.cpu.gpr.rsp = g₀.rsp + 8#64 + 8 + 8 →
      Z.cpu.gpr.r12 = g₀.r12 → Z.cpu.gpr.r13 = g₀.r13 → Z.cpu.gpr.r14 = g₀.r14 → Z.cpu.gpr.r15 = g₀.r15 →
      GoG prof L o gev gP gE Z t') :
    ∀ (m j : Nat), j + m = n → ∀ (X : State) (t : Nat), KeptW Wl s₀ X → Agree F X.proc.mm.mem (Cp W p d j) →
      X.cpu.rip = acp_at.add 40 → X.cpu.gpr.rax = BitVec.ofNat 64 j → X.cpu.gpr.rsi = p → X.cpu.gpr.rcx = d →
      Kp g₀ X.cpu.gpr → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero =>
    intro j hj X t hK hA hrip hax hsi hci hkp
    have hjn : j = n := by omega
    subst hjn
    have es : X.cpu.gpr.rsi + X.cpu.gpr.rax = p.add j := by rw [hsi, hax]; rfl
    have ed : X.cpu.gpr.rcx + X.cpu.gpr.rax = d.add j := by rw [hci, hax]; rfl
    have hb : Cp W p d j (p.add j) = W (p.add j) :=
      Cp_out W p d j _ fun i hi => hsep j (Nat.le_refl _) i (by omega)
    have hz' : (BitVec.setWidth 8 (BitVec.setWidth 32 (Cp W p d j (X.cpu.gpr.rsi + X.cpu.gpr.rax))) == 0) = true := by
      rw [es, hb, sw8a, hz]; all_goals decide
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (Nat.le_refl _)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rcx + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (Nat.le_refl _)
    have hsp : X.cpu.gpr.rsp = g₀.rsp := hkp.1
    refine (c_40 prof).run c hin _ hK hA hrip
      (vc_40z hz' hf1 hw1 (by rw [hsp]; exact l1) (by rw [hsp]; exact l2)) ?_
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
    intro j hj X t hK hA hrip hax hsi hci hkp
    have es : X.cpu.gpr.rsi + X.cpu.gpr.rax = p.add j := by rw [hsi, hax]; rfl
    have ed : X.cpu.gpr.rcx + X.cpu.gpr.rax = d.add j := by rw [hci, hax]; rfl
    have hb : Cp W p d j (p.add j) = W (p.add j) :=
      Cp_out W p d j _ fun i hi => hsep j (by omega) i (by omega)
    have hz' : (BitVec.setWidth 8 (BitVec.setWidth 32 (Cp W p d j (X.cpu.gpr.rsi + X.cpu.gpr.rax))) == 0) =
        false := by
      rw [es, hb, sw8a]; exact beq_eq_false_iff_ne.2 (hnz j (by omega))
    have hf1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rsi + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, es]
      exact hf j (by omega)
    have hw1 : ∀ i < 1, Foot Wl (Addr.add (X.cpu.gpr.rcx + X.cpu.gpr.rax) i) := fun i hi => by
      obtain rfl : i = 0 := by omega
      rw [addr_add_zero, ed]
      exact hw j (by omega)
    refine (c_40 prof).run c hin _ hK hA hrip (vc_40n hz' hf1 hw1) ?_
    rintro j' g fl V₁ ⟨rfl, hax', hsi', hci', hkp', hV⟩ Y t₁ hKY hAY hrY hgY -
    rw [es, ed, hb] at hV
    subst hV
    refine ih (j + 1) (by omega) Y t₁ hKY hAY hrY ?_ (by rw [hgY, hsi', hsi]) (by rw [hgY, hci', hci])
      (hkp.trans (Kp.of_eq hgY hkp'))
    rw [hgY, hax', hax]
    exact (BitVec.ofNat_add j 1).symm

end FV7z.Acp
