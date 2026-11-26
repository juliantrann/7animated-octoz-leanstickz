import FV7z.Fcw.Cuts
import FV7z.Fcc.Holds
import FV7z.Rfw.Holds
/-!
# `FindCharPosInString (const wchar_t *s, wchar_t c)` (PLAN.md §M, M1)

7-Zip 26.06's `FindCharPosInString (const wchar_t *s, wchar_t c)` at `0x44b9a0` in `7zzs`
(`CPP/Common/MyString.cpp`; `objdump -d`): `s` = `rdi`, `c` = `esi` (`ch k`: the 4-byte character at `s + 4 k`). The
first character, if `c`, gives 0 (50); else the loop's head (27) with `rax` = `s + 4 i`, `edx` = `ch i` (not `c`):
`ch i` 0 gives -1 in `eax` (36), `ch (i + 1)` = `c` gives `i + 1` in `rax` (47, `sub rax, rdi; sar rax, 2`), else
`i + 1` next. So the result is the index of the first character that is `c` or 0, if `c`, else -1 (`Res`). Nothing
is stored; `rax`, `rdx` change.

- `Res`; `Inv`, `Fin`, `Nx`: as for the `char` version (`FV7z.Fcc`), with character `N` 0 (`N` < `2^32`);
  `vc_0`, `vc_27`: the cut points' conditions.
- `fcw_ok`: from the entry to the return address with `Res` of `rax`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Fcc (nb_t nb_f)
open FV7z.Rfw (add4 sar4)
namespace FV7z.Fcw

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_36 : pret <+: fcw.drop 36 := by decide +kernel
theorem ret_36 (feat : Features) : Dec feat fcw 36 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 36) (k := 0) (pret_0 feat) w_36 (Nat.zero_le _)
theorem w_47 : pret <+: fcw.drop 47 := by decide +kernel
theorem ret_47 (feat : Features) : Dec feat fcw 47 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 47) (k := 0) (pret_0 feat) w_47 (Nat.zero_le _)
theorem w_50 : pret <+: fcw.drop 50 := by decide +kernel
theorem ret_50 (feat : Features) : Dec feat fcw 50 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)

/-- The 4-byte character at `s + 4 k`. -/
abbrev ch (V : Addr → Byte) (s : Addr) (k : Nat) : BitVec 32 := rdd(V, Addr.add s (4 * k))

/-- The result `r`: the index of the first character that is `c` or 0, if it is `c`; else -1 in `eax`. -/
def Res (V : Addr → Byte) (s : Addr) (c : BitVec 32) (r : BitVec 64) : Prop :=
  ∃ i, (∀ k < i, ch V s k ≠ c ∧ ch V s k ≠ 0) ∧
    ((ch V s i = c ∧ r.toNat = i) ∨ (ch V s i ≠ c ∧ ch V s i = 0 ∧ r = BitVec.setWidth 64 4294967295#32))

theorem tz_t {b : BitVec 32} (h : (!(b == 0)) = true) : b ≠ 0 := fun e => by
  subst e
  revert h
  decide

theorem tz_f {b : BitVec 32} (h : (!(b == 0)) = false) : b = 0 := by
  cases hb : (b == 0) with
  | true => exact beq_iff_eq.mp hb
  | false =>
    rw [hb] at h
    exact absurd h (by decide)

theorem ok_succ {V : Addr → Byte} {s : Addr} {c : BitVec 32} {i : Nat} (hok : ∀ k < i, ch V s k ≠ c ∧ ch V s k ≠ 0)
    (hc : ch V s i ≠ c) (hz : ch V s i ≠ 0) : ∀ k < i + 1, ch V s k ≠ c ∧ ch V s k ≠ 0 := by
  intro k hk
  by_cases h : k < i
  · exact hok k h
  · obtain rfl : k = i := by omega
    exact ⟨hc, hz⟩

/-- The registers at the loop's head, character `i` in `edx`. -/
abbrev G27 (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) : Gprs :=
  { g₀ with rax := Addr.add g₀.rdi (4 * i), rdx := (ch V₀ g₀.rdi i).setWidth 64 }

/-- At the loop's head: character `i` not `c`, the characters before it neither `c` nor 0. -/
def I27 (g₀ : Gprs) (V₀ : Addr → Byte) (N n : Nat) (g : Gprs) : Prop :=
  ∃ i ≤ N, n = N + 1 - i ∧ ch V₀ g₀.rdi i ≠ g₀.rsi.setWidth 32 ∧
    (∀ k < i, ch V₀ g₀.rdi k ≠ g₀.rsi.setWidth 32 ∧ ch V₀ g₀.rdi k ≠ 0) ∧ g = G27 g₀ V₀ i
/-- The invariant at the cut points. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (N ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ ((ℓ = 0 ∧ n = N + 2 ∧ g = g₀) ∨ (ℓ = 27 ∧ I27 g₀ V₀ N n g))
/-- At a `ret`: the result in `rax`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ (j = 36 ∨ j = 47 ∨ j = 50) ∧ ∃ r d : BitVec 64,
    g = { g₀ with rax := r, rdx := d } ∧ Res V₀ g₀.rdi (g₀.rsi.setWidth 32) r
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (N n : Nat) : Post :=
  fun j' g' _ V' => (∃ n' < n, Inv g₀ V₀ N j' n' g' V') ∨ Fin g₀ V₀ j' g' V'

variable {g₀ : Gprs} {V₀ : Addr → Byte}

theorem eFin {N n j : Nat} (hj : j = 36 ∨ j = 47 ∨ j = 50) {r d : BitVec 64}
    (hr : Res V₀ g₀.rdi (g₀.rsi.setWidth 32) r) {g' : Gprs} {fl : Rflags}
    (hg : g' = { g₀ with rax := r, rdx := d }) : Nx g₀ V₀ N n j g' fl V₀ :=
  Or.inr ⟨rfl, hj, r, d, hg, hr⟩

theorem e27 {N n i : Nat} (hi : i ≤ N) (hn : N + 1 - i < n) (hc : ch V₀ g₀.rdi i ≠ g₀.rsi.setWidth 32)
    (hok : ∀ k < i, ch V₀ g₀.rdi k ≠ g₀.rsi.setWidth 32 ∧ ch V₀ g₀.rdi k ≠ 0) {g' : Gprs} {fl : Rflags}
    (hg : g' = G27 g₀ V₀ i) : Nx g₀ V₀ N n 27 g' fl V₀ :=
  Or.inl ⟨_, hn, rfl, Or.inr ⟨rfl, i, hi, rfl, hc, hok, hg⟩⟩

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: character 0 `c`, 0 at 50; else the loop's head with character 0. -/
theorem vc_0 {N : Nat} {f : Rflags} (hF : ∀ k ≤ N, ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j)) :
    W_0 F Wl (Nx g₀ V₀ N (N + 2)) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hF ⊢
  have h0 := hF 0 (Nat.zero_le _)
  rw [Nat.mul_zero, addr_add_zero] at h0
  wpx [W_0, W_13, W_48, o0, o5, BitVec.xor_self, sw_64_32]
  refine ⟨h0, fun h => ?_, fun h af => ?_⟩
  · refine e27 (i := 0) (Nat.zero_le _) (by omega) ?_ ?_ ?_
    · simp only [ch, Nat.mul_zero, addr_add_zero]
      exact fun e => nb_t h e.symm
    · exact fun k hk => absurd hk (Nat.not_lt_zero _)
    · simp only [G27, ch, Nat.mul_zero, addr_add_zero]
  · have hc : ch V₀ rdi 0 = rsi.setWidth 32 := by
      simp only [ch, Nat.mul_zero, addr_add_zero]
      exact (nb_f h).symm
    refine eFin (Or.inr (Or.inr rfl)) ?_ rfl
    exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _), Or.inl ⟨by simpa only using hc, by simp⟩⟩

set_option maxHeartbeats 1000000 in
/-- The loop's head, character `i`: 0, -1 at 36; else character `i + 1` `c`, `i + 1` at 47; else the head with
`i + 1`. -/
theorem vc_27 {N n : Nat} {g : Gprs} {f : Rflags} (hN32 : N < 2 ^ 32)
    (hF : ∀ k ≤ N, ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j))
    (hN : ch V₀ g₀.rdi N = 0) (h : I27 g₀ V₀ N n g) : W_27 F Wl (Nx g₀ V₀ N n) g f V₀ := by
  obtain ⟨i, hi, rfl, hne, hok, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G27] at hF hN hne hok ⊢
  wpx [W_27, W_16, W_40, W_31, o2, o1, o4, o3, Op.sar64, BitVec.and_self, sw_64_32]
  intro af
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hz : ch V₀ rdi i ≠ 0 := tz_t h1
    have hi1 : i + 1 ≤ N := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hi fun e => hz (by rw [e]; exact hN))
    have hok' := ok_succ hok hne hz
    have hF1 := hF (i + 1) hi1
    rw [add4] at hF1
    refine ⟨hF1, fun h2 => ?_, fun h2 => ?_⟩
    · have hc : ch V₀ rdi (i + 1) = rsi.setWidth 32 := by
        have e := of_decide_eq_true h2
        rw [← add4] at e
        exact e
      refine eFin (Or.inr (Or.inl rfl)) ?_ rfl
      rw [← add4]
      exact ⟨i + 1, by simpa only using hok', Or.inl ⟨by simpa only using hc, sar4 _ (by omega)⟩⟩
    · have hc : ch V₀ rdi (i + 1) ≠ rsi.setWidth 32 := by
        have e := of_decide_eq_false h2
        rw [← add4] at e
        exact e
      refine e27 (i := i + 1) hi1 (by omega) ?_ ?_ ?_
      · simpa only using hc
      · simpa only using hok'
      · simp only [G27, ch, add4]
  · have hz : ch V₀ rdi i = 0 := tz_f h1
    refine eFin (Or.inl rfl) ?_ rfl
    exact ⟨i, by simpa only using hok, Or.inr ⟨by simpa only using hne, by simpa only using hz, rfl⟩⟩

theorem vcAll {N : Nat} (hN32 : N < 2 ^ 32)
    (hF : ∀ k ≤ N, ∀ j < 4, Foot F.data (Addr.add (Addr.add g₀.rdi (4 * k)) j)) (hN : ch V₀ g₀.rdi N = 0)
    (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ N ℓ n g V) :
    Wt ℓ F Wl (Nx g₀ V₀ N n) g f V := by
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, h⟩⟩ := h
  · exact vc_0 (f := f) hF
  · exact vc_27 (f := f) hN32 hF hN h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `FindCharPosInString (s, c)` (`wchar_t`) from its entry to the return address, character `N` < `2^32` of `s` 0
and the characters up to it readable: `rax` the result (`Res`), `rdx` changed, nothing stored. -/
theorem fcw_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fcw_at fcw) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fcw_at) {N : Nat} (hN32 : N < 2 ^ 32)
    (hF : ∀ k ≤ N, ∀ j < 4, Foot F.data (Addr.add (Addr.add X.cpu.gpr.rdi (4 * k)) j))
    (hN : ch V X.cpu.gpr.rdi N = 0) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ r d : BitVec 64, Z.cpu.gpr = { X.cpu.gpr with rax := r, rdx := d }.set 4 (X.cpu.gpr.rsp + 8) ∧
        Res V X.cpu.gpr.rdi (X.cpu.gpr.rsi.setWidth 32) r) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V' => Inv X.cpu.gpr V N ℓ n g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hN32 hF hN ℓ n g f V' h) ?_
    (N + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rintro j g fl V' ⟨hV, hj, r, d, rfl, hr⟩ Y t' hKY hAY hrY hgY -
  rw [hV] at hAY
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  rcases hj with rfl | rfl | rfl
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_36 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, d, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_47 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, d, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_50 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, d, by rw [hgZ, hsY, hgY], hr⟩

end FV7z.Fcw
