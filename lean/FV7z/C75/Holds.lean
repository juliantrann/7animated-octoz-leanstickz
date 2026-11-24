import FV7z.C75.Cuts
import FV7z.Ctor.StSpec
/-!
# `csuTg 75`: a table of reversed bytes (PLAN.md §M, constructors)

`csuTg 75`, at offset 1584 of `sti`, fills the 256 bytes at `0x79d340` (`wr75`), each its index with the bits
reversed, and returns. No later code takes those bytes as an address, so its spec says only where they lie
(`wrSpec wr75`).

- `Inv`: the invariant at the two cut points (`Cuts.lean`): the entry, and the loop's head with `rcx` the count of
  bytes done, `rsi` the table, the registers a call keeps, and the bytes outside the table as at the entry (`Out`).
- `vc_1584`, `vc_1600`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches the `ret`.
- `runs75`: `csuTg 75` is a function as `Csu.csu_ok` asks (`cfg_runs`), for an invariant that goes from `75` to `76`
  through `Out`; `runs75_jg`: for `Jg` (`jg_wr`).
-/
namespace FV7z.C75
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The table. -/
def wr75 : List (Nat × Nat) := [(7983936, 7984192)]

/-- The bytes outside the table as before. -/
def Out (V V' : Addr → Byte) : Prop := ∀ a : Addr, ¬ InR wr75 a.toNat → V' a = V a

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 1584 ∧ n = 257 ∧ g = g₀ ∧ V = V₀) ∨
  (ℓ = 1600 ∧ g.rcx.toNat < 256 ∧ n = 256 - g.rcx.toNat ∧ g.rsi = 7983936#64 ∧ Kp g₀ g ∧ Out V₀ V)

/-- A byte of the table is in `Wl`. -/
theorem ft75 (hw : ∀ i < 256, Foot Wl (Addr.add 7983936#64 i)) {a : Addr} (h1 : 7983936 ≤ a.toNat)
    (h2 : a.toNat < 7984192) : Foot Wl a := by
  have e : Addr.add 7983936#64 (a.toNat - 7983936) = a := by
    apply BitVec.eq_of_toNat_eq
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [← e]
  exact hw _ (by omega)

/-- A store of a byte into the table keeps `Out`. -/
theorem out_st {V₀ V : Addr → Byte} {e : Addr} {bs : List Byte} (hO : Out V₀ V) (hl : bs.length = 1)
    (h1 : 7983936 ≤ e.toNat) (h2 : e.toNat < 7984192) : Out V₀ (Vst V e bs) := fun a ha => by
  have h : ¬ (7983936 ≤ a.toNat ∧ a.toNat < 7984192) := by simpa only [wr75, InR, or_false] using ha
  rw [Tun.Vst_out V e bs a (by rw [hl]; omega) (by rw [hl]; omega)]
  exact hO a ha

/-- The count one more, not yet 256. -/
theorem inc_lt {x : BitVec 64} (h : x.toNat < 256) (hne : ¬ x + 1#64 = 256#64) :
    (x + 1#64).toNat < 256 ∧ 256 - (x + 1#64).toNat < 256 - x.toNat := by
  bv_omega

/-- The address of the loop's store lies in the table. -/
macro "ea75" : tactic => `(tactic| first
  | (simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_mul]; omega)
  | ((try simp only [Addr.add]) <;> bv_omega))

/-- From the entry to the loop's head: `rsi` the table, `rcx` 0. -/
theorem vc_1584 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post)
    (hQ : ∀ g' f' V', Inv g V 1600 256 g' f' V' → Q 1600 g' f' V') : W_1584 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1584, o0]
  intros
  apply hQ
  exact Or.inr ⟨rfl, by simp, by simp, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl⟩

/-- One round of the loop: the byte stored in the table, then back to the head with the count one more, or on to
the `ret` after the last. -/
theorem vc_1600 {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hw : ∀ i < 256, Foot Wl (Addr.add 7983936#64 i))
    (hr : g.rcx.toNat < 256) (hs : g.rsi = 7983936#64) (hK : Kp g₀ g) (hO : Out V₀ V) (Q : Post)
    (hQ1 : ∀ g' f' V', Inv g₀ V₀ 1600 (256 - g'.rcx.toNat) g' f' V' → 256 - g'.rcx.toNat < 256 - g.rcx.toNat →
      Q 1600 g' f' V')
    (hQ2 : ∀ g' f' V', Kp g₀ g' → Out V₀ V' → Q 1665 g' f' V') : W_1600 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr hs hQ1
  subst hs
  wpx [W_1600, o1]
  intros
  refine ⟨fun i hi => ft75 hw (by ea75) (by ea75), fun h => ?_, fun _ => ?_⟩
  · have hne : ¬ rcx + 1#64 = 256#64 := by simpa using h
    have hi := inc_lt hr hne
    apply hQ1
    · exact Or.inr ⟨rfl, hi.1, rfl, rfl, hK, out_st hO (by simp) (by ea75) (by ea75)⟩
    · exact hi.2
  · apply hQ2
    · exact hK
    · exact out_st hO (by simp) (by ea75) (by ea75)

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the table as at the entry. -/
theorem vc (hw : ∀ i < 256, Foot Wl (Addr.add 7983936#64 i)) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat)
    (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = 1665 ∧ Kp g₀ g' ∧ Out V₀ V'))
      g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, hr, rfl, hs, hK, hO⟩
  · show W_1584 F Wl _ _ _ _
    exact vc_1584 _ fun g' f' V' h => Or.inl ⟨256, by decide, h⟩
  · show W_1600 F Wl _ _ _ _
    exact vc_1600 hw hr hs hK hO _ (fun g' f' V' h hlt => Or.inl ⟨_, hlt, h⟩)
      fun g' f' V' hK' hO' => Or.inr ⟨rfl, hK', hO'⟩

/-- The `ret` at offset 1665 of `sti`. -/
def r1665 : List Byte := [0xc3]
theorem r1665_0 : ∀ feat, Dec feat r1665 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v1665 : r1665 <+: sti.drop 1665 := by decide +kernel
theorem tg75 : csuTg 75 = sti_at.add 1584 := by decide +kernel
theorem calls75 : calls 75 = [] := by decide +kernel
theorem wrT75 : ∀ x ∈ wr75, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- `csuTg 75` is a function as `Csu.csu_ok` asks, for an invariant that goes from `75` to `76` through `Out`. -/
theorem runs75 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hw : ∀ i < 256, Foot Wl (Addr.add 7983936#64 i)) (hsp : 7984192 + 64 ≤ sp.toNat)
    (hJ : ∀ V V', J 75 V → Out V V' → J 76 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 75 (csuTg 75) :=
  cfg_runs c hC hin tg75 (spAll prof) (Dec.shift (j := 1665) (k := 0) (r1665_0 _) v1665 (by decide))
    (lt_len (by decide)) Out Inv (fun _ _ _ => ⟨257, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩) (vc hw)
    (fun _ _ h a ha => h a (by simp only [wr75, InR, or_false]; omega)) hJ

/-- `csuTg 75` for `Jg`, its spec `wrSpec wr75`. -/
theorem runs75_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hw : ∀ i < 256, Foot Wl (Addr.add 7983936#64 i)) (hsp : 7984192 + 64 ≤ sp.toNat)
    (hspec : spec 75 = wrSpec wr75) (hD : ∀ k, (spec k).Dep)
    (hXw : ∀ k, 3 ≤ k → k < 75 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr75, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W', G 75 W → Out W W' → G 76 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 75 (csuTg 75) :=
  runs75 c hC hin hw hsp fun W W' hJ hO => jg_wr (by decide) calls75 hspec hD wrT75 hXw hO (hG W W' · hO) hJ

end FV7z.C75
