import FV7z.Strncmp.AshrS
import FV7z.Strncmp.Ashr1
import FV7z.Strncmp.Ashr2
import FV7z.Strncmp.Ashr3
import FV7z.Strncmp.Ashr4
import FV7z.Strncmp.Ashr5
import FV7z.Strncmp.Ashr0
import FV7z.Strncmp.Align
import FV7z.Strncmp.Head
/-!
# `__strncmp_sse2` meets `Str.NcmpAt` (PLAN.md G3, `strncmp`)

The loop shifting by `k` starts at `400 + 384 (k - 1)` (`ashrC`: the fifteen `AshrC`s). From `128` (`go128`),
`align` goes on at `192` when the strings' offsets in their 16 bytes are equal (`ashr0`), else at the loop for
their difference, by the table (`entryS`). With `head`, a call at `0x63a420`, where the code of `__strncmp_sse2`
is, does what `Str.NcmpAt` says, for any `Pm` with the table's bytes (`ncmpAt_sse2`). The PLT stub at `0x401048`
jumping through the GOT to it is a separate step.
-/
namespace FV7z.Strncmp
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

/-- The loops shifting by `1` to `15`: at `400 + 384 (k - 1)`, the `jb` to `6160` `e ≤ 4` bytes on. -/
theorem ashrC (prof : Profile) : ∀ k, 1 ≤ k → k ≤ 15 → ∃ e, e ≤ 4 ∧ AshrC prof k (400 + 384 * (k - 1)) e
  | 1, _, _ => ⟨4, by decide, ashr1 prof⟩
  | 2, _, _ => ⟨4, by decide, ashr2 prof⟩
  | 3, _, _ => ⟨4, by decide, ashr3 prof⟩
  | 4, _, _ => ⟨4, by decide, ashr4 prof⟩
  | 5, _, _ => ⟨4, by decide, ashr5 prof⟩
  | 6, _, _ => ⟨4, by decide, ashr6 prof⟩
  | 7, _, _ => ⟨4, by decide, ashr7 prof⟩
  | 8, _, _ => ⟨4, by decide, ashr8 prof⟩
  | 9, _, _ => ⟨4, by decide, ashr9 prof⟩
  | 10, _, _ => ⟨4, by decide, ashr10 prof⟩
  | 11, _, _ => ⟨4, by decide, ashr11 prof⟩
  | 12, _, _ => ⟨4, by decide, ashr12 prof⟩
  | 13, _, _ => ⟨4, by decide, ashr13 prof⟩
  | 14, _, _ => ⟨4, by decide, ashr14 prof⟩
  | 15, _, _ => ⟨0, by decide, ashr15 prof⟩
  | 0, h, _ => absurd h (by decide)
  | k + 16, _, h => absurd h (by omega)

/-- The table's bytes, `[0x6f0df0, 0x6f0e30)`. -/
theorem tab_rng {i : Nat} (hi : i < 64) :
    0x6f0df0 ≤ ((0x6f0df0 : Addr).add i).toNat ∧ ((0x6f0df0 : Addr).add i).toNat < 0x6f0e30 := by
  have h0 : (0x6f0df0 : Addr).toNat = 7278064 := rfl
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, h0]
  omega

/-- The page of a string's first byte, when there is one to compare. -/
theorem pg0 {F : Footprint} {V : Addr → Byte} {a : Addr} {n : Nat} (hp : Str.StrPg F V a n) (h0 : 0 < n) :
    ∀ x : Addr, x.toNat / 4096 = a.toNat / 4096 → Foot F.data x := fun x hx =>
  (hp 0 h0 fun i hi => absurd hi (Nat.not_lt_zero _)).2 x (by rw [Nat.add_zero]; exact hx)

/-- What `Str.NcmpAt` asks of the `eax` returned, the first `m` bytes the same and not 0. -/
def NP (V : Addr → Byte) (a b : Addr) (n m : Nat) (r : BitVec 32) : Prop :=
  (m = n → r = 0) ∧ (m < n → V (Addr.add a m) = V (Addr.add b m) → V (Addr.add a m) = 0 → r = 0) ∧
    (m < n → V (Addr.add a m) ≠ V (Addr.add b m) → r ≠ 0)

section
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `128`: `align`, then `ashr0` or the loop for the difference of the offsets (`entryS`). -/
theorem go128 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' scm) (he : e' = 0x63a420) (hT : NcmpTabV V)
    (hTf : ∀ i < 64, Foot F.data ((0x6f0df0 : Addr).add i)) {g₀ : Gprs} {a b : Addr} {n : Nat}
    {P : BitVec 32 → Prop} (hn64 : n < 2 ^ 64) (hpa : Str.StrPg F V a n) (hpb : Str.StrPg F V b n)
    (hP : ∀ r, NRes V a b n r → P r) (hR : RetN prof F Wl L s₀ o gev gP gE V g₀ P) :
    Go128 prof F Wl L s₀ o gev gP gE V e' g₀ a b n := by
  intro Z t' q hK hA hrip hg hq hq01 hs
  refine align c hin he hT hTf hK hA hrip hg (by rcases hq01 with rfl | rfl <;> rfl) ?_ ?_
  · intro Z₁ t₁ hK₁ hA₁ hr₁ hab hL
    exact ashr0 c hin hK₁ hA₁ hr₁ hab hL hn64 hq hs hpa hpb hP hR
  · intro Z₁ t₁ sw x y hK₁ hA₁ hxy hlt hr₁ hL
    have hX : x.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have hY : y.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    obtain ⟨e, he4, A⟩ := ashrC prof (16 + x.toNat % 16 - y.toNat % 16) (by omega) (by omega)
    have hxy' : Str.StrPg F V x n ∧ Str.StrPg F V y n ∧ Same V x y q := by
      rcases hxy with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩
      · exact ⟨hpa, hpb, hs⟩
      · exact ⟨hpb, hpa, hs.comm⟩
    have hr₁' : Z₁.cpu.rip = e'.add (400 + 384 * (16 + x.toNat % 16 - y.toNat % 16 - 1)) := by
      rw [hr₁, show 16 + x.toNat % 16 - y.toNat % 16 - 1 = 15 + x.toNat % 16 - y.toNat % 16 by omega]
    exact entryS c hin A (by omega) he4 hK₁ hA₁ hr₁' hL hlt (by omega) hn64 hq hxy'.2.2 hxy hxy'.1 hxy'.2.1 hP hR

end

/-- A call at `0x63a420`, the code of `__strncmp_sse2` there, the bytes with the table: what `Str.NcmpAt` says. -/
theorem ncmpAt_sse2 {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {Pm : (Addr → Byte) → Prop}
    (hin : CodeIn L (0x63a420 : Addr) scm) (hPm : ∀ V, Pm V → NcmpTabV V) :
    Str.NcmpAt prof L o (0x63a420 : Addr) Pm := by
  intro F Wl s₀ gev gP gE X t V e' code j m c hG hK hA hrip hPV hin₂ hj hra hl hm _ _ hs hpa hpb K
  have hn64 := X.cpu.gpr.rdx.isLt
  have hkp : KpN X.cpu.gpr X.cpu.gpr := by
    unfold KpN
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hdx : X.cpu.gpr.rdx = BitVec.ofNat 64 X.cpu.gpr.rdx.toNat :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64])
  have hP : ∀ r, NRes V X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat r →
      NP V X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat m r := fun r hr => hr m hm hs
  have hR : RetN prof F Wl L s₀ o gev gP gE V X.cpu.gpr
      (NP V X.cpu.gpr.rdi X.cpu.gpr.rsi X.cpu.gpr.rdx.toNat m) :=
    ⟨hl, e', code, j, hin₂, hj, hra, fun Z t' hKZ hAZ hrZ hsp hp hbx hbp h12 h13 h14 h15 =>
      K Z t' hKZ hAZ hrZ hsp hp.1 hp.2.1 hp.2.2 hbx hbp h12 h13 h14 h15⟩
  exact head c hin hK hA (by rw [hrip, addr_add_zero]) hkp rfl rfl hdx hn64 (pg0 hpa) (pg0 hpb) hP hR
    (go128 c hin rfl (hPm V hPV) (fun i hi => hG.ntab _ (tab_rng hi).1 (tab_rng hi).2) hn64 hpa hpb hP hR)

end FV7z.Strncmp
