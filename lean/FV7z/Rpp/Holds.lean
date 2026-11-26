import FV7z.Rpp.Cuts
import FV7z.Rfw.Holds
/-!
# `UString::ReverseFind_PathSepar` (PLAN.md §M, M1)

7-Zip 26.06's `UString::ReverseFind_PathSepar () const` at `0x44dd80` in `7zzs` (`CPP/Common/MyString.cpp`;
`objdump -d`): `ReverseFind ('/')` (`FV7z.Rfw`) inlined, without the test for length 0: for the string at `p` = `rdi`,
the index of the last character `/` in `rax` (`ret` at 47), else -1 in `eax` (`ret` at 35). Cut points: the entry
and the loop's head (25).

- `Inv`, `Fin`, `Nx`: the invariant (the loop: the characters from `n` on not `/`), the end, and the post of
  `Seg.cfg`; `vc_*`: the cut points' conditions; `rpp_ok`: from the entry to the return address, `Res` of `rax`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Rfw (chs len ch Res Fp lea4 add4 ac4 ne4 m1 resF)
namespace FV7z.Rpp

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_35 : pret <+: rpp.drop 35 := by decide +kernel
theorem ret_35 (feat : Features) : Dec feat rpp 35 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 35) (k := 0) (pret_0 feat) w_35 (Nat.zero_le _)
theorem w_47 : pret <+: rpp.drop 47 := by decide +kernel
theorem ret_47 (feat : Features) : Dec feat rpp 47 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 47) (k := 0) (pret_0 feat) w_47 (Nat.zero_le _)

/-- The state at the loop's head, the characters from `n` on not `/`. -/
abbrev G25 (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Gprs :=
  { g₀ with rax := Addr.add (chs V₀ g₀.rdi) (4 * n), rdx := chs V₀ g₀.rdi }

/-- At the loop's head. -/
def I25 (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) (g : Gprs) : Prop :=
  n ≤ (len V₀ g₀.rdi).toNat ∧ (∀ j < (len V₀ g₀.rdi).toNat, n ≤ j → ch V₀ g₀.rdi j ≠ 47#32) ∧ g = G25 g₀ V₀ n
/-- The invariant at the cut points. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ ((ℓ = 0 ∧ n = (len V₀ g₀.rdi).toNat + 1 ∧ g = g₀) ∨ (ℓ = 25 ∧ I25 g₀ V₀ n g))
/-- At a `ret`: the result in `rax`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ (j = 35 ∨ j = 47) ∧ ∃ a d, g = { g₀ with rax := a, rdx := d } ∧ Res V₀ g₀.rdi 47#32 a
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n' < n, Inv g₀ V₀ j' n' g' V') ∨ Fin g₀ V₀ j' g' V'

variable {g₀ : Gprs} {V₀ : Addr → Byte}

theorem x25 {n m : Nat} (hm : m ≤ (len V₀ g₀.rdi).toNat)
    (hall : ∀ j < (len V₀ g₀.rdi).toNat, m ≤ j → ch V₀ g₀.rdi j ≠ 47#32) (hn : m < n) {g' : Gprs} {fl : Rflags}
    (hg : g' = G25 g₀ V₀ m) : Nx g₀ V₀ n 25 g' fl V₀ :=
  Or.inl ⟨m, hn, rfl, Or.inr ⟨rfl, hm, hall, hg⟩⟩

theorem xFin {n j : Nat} (hj : j = 35 ∨ j = 47) {a d : BitVec 64} (hr : Res V₀ g₀.rdi 47#32 a) {g' : Gprs}
    {fl : Rflags} (hg : g' = { g₀ with rax := a, rdx := d }) : Nx g₀ V₀ n j g' fl V₀ :=
  Or.inr ⟨rfl, hj, a, d, hg, hr⟩

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: to the loop's head past the last character. -/
theorem vc_0 {f : Rflags} (hF : Fp F V₀ g₀.rdi) :
    W_0 F Wl (Nx g₀ V₀ ((len V₀ g₀.rdi).toNat + 1)) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨f0, f8, -⟩ := hF
  dsimp only at f0 f8 ⊢
  wpx [W_0, o0]
  refine ⟨f0, f8, ?_⟩
  exact x25 (Nat.le_refl _) (fun _ hj h => absurd hj (Nat.not_lt.mpr h)) (Nat.lt_succ_self _) (by rw [lea4])

/-- The loop's head with no characters left: none is `/`, -1, the `ret` at 35. -/
theorem vc_25z {f : Rflags} (hall : ∀ j < (len V₀ g₀.rdi).toNat, 0 ≤ j → ch V₀ g₀.rdi j ≠ 47#32) :
    W_25 F Wl (Nx g₀ V₀ 0) (G25 g₀ V₀ 0) f V₀ := by
  rw [show G25 g₀ V₀ 0 = { g₀ with rax := chs V₀ g₀.rdi, rdx := chs V₀ g₀.rdi } by
    simp only [G25, Nat.mul_zero, addr_add_zero]]
  have hall' : ∀ k < (len V₀ g₀.rdi).toNat, ch V₀ g₀.rdi k ≠ 47#32 := fun k hk => hall k hk (Nat.zero_le _)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hall' ⊢
  wpx [W_25, W_16, W_40, W_30, o2, o1, o4, o3, Op.cmpmi, eq_self_iff_true, decide_true, Bool.not_true,
    Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
  all_goals repeat' (first
    | exact xFin (Or.inl rfl) (by exact Or.inl ⟨hall', m1⟩) rfl
    | apply And.intro
    | intro)

/-- The loop's head, character `m` a `/`: its index, the `ret` at 47. -/
theorem vc_25f {m : Nat} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hm : m + 1 ≤ (len V₀ g₀.rdi).toNat)
    (hall : ∀ j < (len V₀ g₀.rdi).toNat, m + 1 ≤ j → ch V₀ g₀.rdi j ≠ 47#32) (hch : ch V₀ g₀.rdi m = 47#32) :
    W_25 F Wl (Nx g₀ V₀ (m + 1)) (G25 g₀ V₀ (m + 1)) f V₀ := by
  rw [show G25 g₀ V₀ (m + 1) = { g₀ with rax := Addr.add (chs V₀ g₀.rdi) (4 * m) + 4#64, rdx := chs V₀ g₀.rdi }
    by rw [← add4]]
  have hr := resF hm hch hall
  have hm32 : m < 2 ^ 32 := by have := (len V₀ g₀.rdi).isLt; omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  have fm := fk m hm
  dsimp only at hch fm hr ⊢
  have hc := hch
  dsimp only [ch, chs] at hc
  have hne : rdq(V₀, rdi) ≠ Addr.add (rdq(V₀, rdi)) (4 * m) + 4#64 := by
    rw [← add4]
    exact ne4 _ hm32
  wpx [W_25, W_16, W_40, W_30, o2, o1, o4, o3, Op.cmpmi, Op.sar64, ac4, hc, hne, eq_self_iff_true, decide_true,
    decide_false, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies,
    true_implies, true_and, and_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fm
    | exact xFin (Or.inr rfl) (by exact hr) rfl
    | apply And.intro
    | intro)

/-- The loop's head, character `m` not a `/`: the one before. -/
theorem vc_25s {m : Nat} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hm : m + 1 ≤ (len V₀ g₀.rdi).toNat)
    (hall : ∀ j < (len V₀ g₀.rdi).toNat, m + 1 ≤ j → ch V₀ g₀.rdi j ≠ 47#32) (hch : ¬ ch V₀ g₀.rdi m = 47#32) :
    W_25 F Wl (Nx g₀ V₀ (m + 1)) (G25 g₀ V₀ (m + 1)) f V₀ := by
  rw [show G25 g₀ V₀ (m + 1) = { g₀ with rax := Addr.add (chs V₀ g₀.rdi) (4 * m) + 4#64, rdx := chs V₀ g₀.rdi }
    by rw [← add4]]
  have hall' : ∀ j < (len V₀ g₀.rdi).toNat, m ≤ j → ch V₀ g₀.rdi j ≠ 47#32 := fun j hj h => by
    by_cases e : j = m
    · subst e
      exact hch
    · exact hall j hj (by omega)
  have hm32 : m < 2 ^ 32 := by have := (len V₀ g₀.rdi).isLt; omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  have fm := fk m hm
  dsimp only at hch fm hall' hm ⊢
  have hc := hch
  dsimp only [ch, chs] at hc
  have hne : rdq(V₀, rdi) ≠ Addr.add (rdq(V₀, rdi)) (4 * m) + 4#64 := by
    rw [← add4]
    exact ne4 _ hm32
  wpx [W_25, W_16, W_40, W_30, o2, o1, o4, o3, Op.cmpmi, ac4, hc, hne, decide_false, Bool.not_false,
    Bool.true_eq_false, Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fm
    | exact x25 (by exact Nat.le_of_succ_le hm) (by exact hall') (by omega) rfl
    | apply And.intro
    | intro)

theorem vc_25 {n : Nat} {g : Gprs} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (h : I25 g₀ V₀ n g) :
    W_25 F Wl (Nx g₀ V₀ n) g f V₀ := by
  obtain ⟨hn, hall, rfl⟩ := h
  rcases n with _ | m
  · exact vc_25z hall
  · by_cases hch : ch V₀ g₀.rdi m = 47#32
    · exact vc_25f hF hn hall hch
    · exact vc_25s hF hn hall hch

theorem vcAll (hF : Fp F V₀ g₀.rdi) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ ℓ n g V) : Wt ℓ F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, h⟩⟩ := h
  · exact vc_0 hF
  · exact vc_25 hF h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::ReverseFind_PathSepar ()` from its entry to the return address: `rax` the result (`Res` for `/`),
`rdx` changed. -/
theorem rpp_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rpp_at rpp) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rpp_at) (hF : Fp F V X.cpu.gpr.rdi)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ a d, Z.cpu.gpr = { X.cpu.gpr with rax := a, rdx := d }.set 4 (X.cpu.gpr.rsp + 8) ∧
        Res V X.cpu.gpr.rdi 47#32 a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V' => Inv X.cpu.gpr V ℓ n g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hF ℓ n g f V' h) ?_
    ((len V X.cpu.gpr.rdi).toNat + 1) 0 hK hA (by rw [addr_add_zero]; exact hrip) ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rintro j g fl V' ⟨hV, hj, a, d, rfl, hr⟩ Y t' hKY hAY hrY hgY -
  subst hV
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  rcases hj with rfl | rfl
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_35 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨a, d, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_47 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨a, d, by rw [hgZ, hsY, hgY], hr⟩

end FV7z.Rpp
