import FV7z.Sea.Cuts
import FV7z.Fcc.Holds
/-!
# `StringsAreEqual_Ascii (const wchar_t *u, const char *a)` (PLAN.md §M, M1)

7-Zip 26.06's `StringsAreEqual_Ascii` at `0x44bb60` in `7zzs` (`CPP/Common/MyString.cpp`; `objdump -d`): `u` = `rdi`
(`cu k`: the 4-byte character at `u + 4 k`), `a` = `rsi` (`cb k`: the byte at `a + k`). Byte 0 zero-extended not
`cu 0` gives 0 (56, then 58); else the loop's head (40) with `rax` = `i`, `edx` = `cb i` (equal to `cu i`): `cb i` 0
gives 1 (49); else `cb (i + 1)` not `cu (i + 1)` gives 0 (56), else `i + 1` next. So the result is 1 if the
strings agree up to and with `a`'s 0, else 0 (`Res`). Nothing is stored; `rax`, `rcx`, `rdx` change.

- `Res`; `Inv`, `Fin`, `Nx`: the invariant at the cut points (0, 40, 56), at a `ret` and at an exit, `a`'s byte `N`
  0; `vc_0`, `vc_40`, `vc_56`: the cut points' conditions.
- `sea_ok`: from the entry to the return address with `Res` of `rax`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Fcc (nb_t nb_f tz_t tz_f)
open FV7z.Tun (sw_8_32_8)
namespace FV7z.Sea

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_49 : pret <+: sea.drop 49 := by decide +kernel
theorem ret_49 (feat : Features) : Dec feat sea 49 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 49) (k := 0) (pret_0 feat) w_49 (Nat.zero_le _)
theorem w_58 : pret <+: sea.drop 58 := by decide +kernel
theorem ret_58 (feat : Features) : Dec feat sea 58 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 58) (k := 0) (pret_0 feat) w_58 (Nat.zero_le _)

/-- Byte `k` of `a`. -/
abbrev cb (V : Addr → Byte) (a : Addr) (k : Nat) : BitVec 8 :=
  ofBytesLE 8 (List.map V (byteAddrs (a + BitVec.ofNat 64 k) 1))
/-- Character `k` of `u`. -/
abbrev cu (V : Addr → Byte) (u : Addr) (k : Nat) : BitVec 32 := rdd(V, u + BitVec.ofNat 64 k * 4#64)

/-- The characters before `i` agree and are not 0. -/
def Ok (V : Addr → Byte) (u a : Addr) (i : Nat) : Prop :=
  ∀ k < i, (cb V a k).setWidth 32 = cu V u k ∧ cb V a k ≠ 0

/-- The result `r`: 1 if the strings agree up to and with `a`'s 0, else 0. -/
def Res (V : Addr → Byte) (u a : Addr) (r : BitVec 64) : Prop :=
  ∃ i, Ok V u a i ∧ (((cb V a i).setWidth 32 = cu V u i ∧ cb V a i = 0 ∧ r = 1#64) ∨
    ((cb V a i).setWidth 32 ≠ cu V u i ∧ r = 0#64))

theorem u1 (i : Nat) : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem s1 (a : Addr) (i : Nat) : a + BitVec.ofNat 64 i + 1#64 = a + BitVec.ofNat 64 (i + 1) := by
  rw [BitVec.add_assoc, u1]

theorem z0 : BitVec.setWidth 64 0#32 = BitVec.ofNat 64 0 := by decide

theorem ok_succ {V : Addr → Byte} {u a : Addr} {i : Nat} (hok : Ok V u a i)
    (hc : (cb V a i).setWidth 32 = cu V u i) (hz : cb V a i ≠ 0) : Ok V u a (i + 1) := by
  intro k hk
  by_cases h : k < i
  · exact hok k h
  · obtain rfl : k = i := by omega
    exact ⟨hc, hz⟩

/-- The registers at the loop's head, index `i` in `rax`, byte `i` in `edx`. -/
abbrev G40 (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) (c : BitVec 64) : Gprs :=
  { g₀ with rax := BitVec.ofNat 64 i, rcx := c, rdx := ((cb V₀ g₀.rsi i).setWidth 32).setWidth 64 }

/-- At the loop's head: byte `i` agrees, the ones before agree and are not 0. -/
def I40 (g₀ : Gprs) (V₀ : Addr → Byte) (N n : Nat) (g : Gprs) : Prop :=
  ∃ i ≤ N, n = N + 1 - i ∧ (cb V₀ g₀.rsi i).setWidth 32 = cu V₀ g₀.rdi i ∧ Ok V₀ g₀.rdi g₀.rsi i ∧
    g = G40 g₀ V₀ i g.rcx
/-- Before the `xor` at 56: byte `i` disagrees, the ones before agree and are not 0. -/
def I56 (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) : Prop :=
  ∃ i, Ok V₀ g₀.rdi g₀.rsi i ∧ (cb V₀ g₀.rsi i).setWidth 32 ≠ cu V₀ g₀.rdi i ∧
    g = { g₀ with rax := g.rax, rcx := g.rcx, rdx := g.rdx }
/-- The invariant at the cut points. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (N ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ ((ℓ = 0 ∧ n = N + 2 ∧ g = g₀) ∨ (ℓ = 40 ∧ I40 g₀ V₀ N n g) ∨ (ℓ = 56 ∧ n = 0 ∧ I56 g₀ V₀ g))
/-- At a `ret`: the result in `rax`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ (j = 49 ∨ j = 58) ∧ ∃ r c d : BitVec 64,
    g = { g₀ with rax := r, rcx := c, rdx := d } ∧ Res V₀ g₀.rdi g₀.rsi r
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (N n : Nat) : Post :=
  fun j' g' _ V' => (∃ n' < n, Inv g₀ V₀ N j' n' g' V') ∨ Fin g₀ V₀ j' g' V'

variable {g₀ : Gprs} {V₀ : Addr → Byte}

theorem eFin {N n j : Nat} (hj : j = 49 ∨ j = 58) {r c d : BitVec 64} (hr : Res V₀ g₀.rdi g₀.rsi r) {g' : Gprs}
    {fl : Rflags} (hg : g' = { g₀ with rax := r, rcx := c, rdx := d }) : Nx g₀ V₀ N n j g' fl V₀ :=
  Or.inr ⟨rfl, hj, r, c, d, hg, hr⟩

theorem e40 {N n i : Nat} (hi : i ≤ N) (hn : N + 1 - i < n) (hc : (cb V₀ g₀.rsi i).setWidth 32 = cu V₀ g₀.rdi i)
    (hok : Ok V₀ g₀.rdi g₀.rsi i) {g' : Gprs} {fl : Rflags} (hg : g' = G40 g₀ V₀ i g'.rcx) :
    Nx g₀ V₀ N n 40 g' fl V₀ :=
  Or.inl ⟨_, hn, rfl, Or.inr (Or.inl ⟨rfl, i, hi, rfl, hc, hok, hg⟩)⟩

theorem e56 {N n i : Nat} (hn : 0 < n) (hok : Ok V₀ g₀.rdi g₀.rsi i)
    (hc : (cb V₀ g₀.rsi i).setWidth 32 ≠ cu V₀ g₀.rdi i) {g' : Gprs} {fl : Rflags}
    (hg : g' = { g₀ with rax := g'.rax, rcx := g'.rcx, rdx := g'.rdx }) : Nx g₀ V₀ N n 56 g' fl V₀ :=
  Or.inl ⟨0, hn, rfl, Or.inr (Or.inr ⟨rfl, rfl, i, hok, hc, hg⟩)⟩

variable {F : Footprint} {Wl : List Rgn}

theorem nok {V : Addr → Byte} {u a : Addr} : Ok V u a 0 := fun _ hk => absurd hk (Nat.not_lt_zero _)

set_option maxHeartbeats 1000000 in
/-- The entry: byte 0 not character 0, to 56; else the loop's head with index 0. -/
theorem vc_0 {N : Nat} {f : Rflags} (hFa : ∀ k ≤ N, ∀ j < 1, Foot F.data ((g₀.rsi + BitVec.ofNat 64 k).add j))
    (hFu : ∀ k ≤ N, ∀ j < 4, Foot F.data ((g₀.rdi + BitVec.ofNat 64 k * 4#64).add j)) :
    W_0 F Wl (Nx g₀ V₀ N (N + 2)) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hFa hFu ⊢
  have ha0 := hFa 0 (Nat.zero_le _)
  have hu0 := hFu 0 (Nat.zero_le _)
  rw [BitVec.add_zero] at ha0
  rw [BitVec.zero_mul, BitVec.add_zero] at hu0
  wpx [W_0, W_13, o0, o1, BitVec.xor_self, sw_64_32]
  refine ⟨ha0, hu0, fun h => ?_, fun h af => ?_⟩
  · have hc : (cb V₀ rsi 0).setWidth 32 ≠ cu V₀ rdi 0 := by
      simp only [cb, cu, BitVec.add_zero, BitVec.zero_mul]
      exact nb_t h
    exact e56 (by omega) nok hc rfl
  · have hc : (cb V₀ rsi 0).setWidth 32 = cu V₀ rdi 0 := by
      simp only [cb, cu, BitVec.add_zero, BitVec.zero_mul]
      exact nb_f h
    exact e40 (Nat.zero_le _) (by omega) hc nok (by simp only [G40, cb, BitVec.add_zero, z0])

set_option maxHeartbeats 1000000 in
/-- The loop's head, byte `i`: 0, 1 at 49; else byte `i + 1` not character `i + 1`, to 56; else the head with
`i + 1`. -/
theorem vc_40 {N n : Nat} {g : Gprs} {f : Rflags}
    (hFa : ∀ k ≤ N, ∀ j < 1, Foot F.data ((g₀.rsi + BitVec.ofNat 64 k).add j))
    (hFu : ∀ k ≤ N, ∀ j < 4, Foot F.data ((g₀.rdi + BitVec.ofNat 64 k * 4#64).add j))
    (hN : cb V₀ g₀.rsi N = 0) (h : I40 g₀ V₀ N n g) : W_40 F Wl (Nx g₀ V₀ N n) g f V₀ := by
  obtain ⟨i, hi, rfl, heq, hok, hg⟩ := h
  rw [hg]
  generalize g.rcx = c
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G40] at hFa hFu hN heq hok ⊢
  wpx [W_40, W_24, W_44, o3, o2, o4, BitVec.and_self, sw_8_32_8, sw_64_32, sw_64_8]
  intro af
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hz : cb V₀ rsi i ≠ 0 := tz_t h1
    have hi1 : i + 1 ≤ N := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hi fun e => hz (by rw [e]; exact hN))
    have hok' := ok_succ hok heq hz
    have ha1 := hFa (i + 1) hi1
    have hu1 := hFu (i + 1) hi1
    rw [← s1] at ha1
    rw [← u1] at hu1
    refine ⟨ha1, hu1, fun h2 => ?_, fun h2 => ?_⟩
    · have hc : (cb V₀ rsi (i + 1)).setWidth 32 ≠ cu V₀ rdi (i + 1) := by
        have e := nb_t h2
        rw [s1, u1] at e
        exact e
      exact e56 (by omega) hok' hc rfl
    · have hc : (cb V₀ rsi (i + 1)).setWidth 32 = cu V₀ rdi (i + 1) := by
        have e := nb_f h2
        rw [s1, u1] at e
        exact e
      exact e40 hi1 (by omega) hc hok' (by simp only [G40, cb, s1, u1])
  · have hz : cb V₀ rsi i = 0 := tz_f h1
    exact eFin (Or.inl rfl) (by exact ⟨i, hok, Or.inl ⟨heq, hz, by decide⟩⟩) rfl

/-- At 56: 0 at 58. -/
theorem vc_56 {N : Nat} {g : Gprs} {f : Rflags} (h : I56 g₀ V₀ g) : W_56 F Wl (Nx g₀ V₀ N 0) g f V₀ := by
  obtain ⟨i, hok, hne, hg⟩ := h
  rw [hg]
  generalize g.rax = a
  generalize g.rcx = c
  generalize g.rdx = d
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hok hne ⊢
  wpx [W_56, o1, BitVec.xor_self]
  intro af
  exact eFin (Or.inr rfl) (by exact ⟨i, hok, Or.inr ⟨hne, by decide⟩⟩) rfl

theorem vcAll {N : Nat} (hFa : ∀ k ≤ N, ∀ j < 1, Foot F.data ((g₀.rsi + BitVec.ofNat 64 k).add j))
    (hFu : ∀ k ≤ N, ∀ j < 4, Foot F.data ((g₀.rdi + BitVec.ofNat 64 k * 4#64).add j)) (hN : cb V₀ g₀.rsi N = 0)
    (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ N ℓ n g V) :
    Wt ℓ F Wl (Nx g₀ V₀ N n) g f V := by
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩⟩ := h
  · exact vc_0 (f := f) hFa hFu
  · exact vc_40 (f := f) hFa hFu hN h
  · exact vc_56 (f := f) h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `StringsAreEqual_Ascii (u, a)` from its entry to the return address, byte `N` of `a` 0 and the bytes and
characters up to it readable: `rax` the result (`Res`), `rcx`, `rdx` changed, nothing stored. -/
theorem sea_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L sea_at sea) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sea_at) {N : Nat}
    (hFa : ∀ k ≤ N, ∀ j < 1, Foot F.data ((X.cpu.gpr.rsi + BitVec.ofNat 64 k).add j))
    (hFu : ∀ k ≤ N, ∀ j < 4, Foot F.data ((X.cpu.gpr.rdi + BitVec.ofNat 64 k * 4#64).add j))
    (hN : cb V X.cpu.gpr.rsi N = 0) (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ r c d : BitVec 64, Z.cpu.gpr = { X.cpu.gpr with rax := r, rcx := c, rdx := d }.set 4 (X.cpu.gpr.rsp + 8) ∧
        Res V X.cpu.gpr.rdi X.cpu.gpr.rsi r) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V' => Inv X.cpu.gpr V N ℓ n g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hFa hFu hN ℓ n g f V' h) ?_
    (N + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rintro j g fl V' ⟨hV, hj, r, c', d, rfl, hr⟩ Y t' hKY hAY hrY hgY -
  rw [hV] at hAY
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  rcases hj with rfl | rfl
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_49 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, c', d, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_58 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, c', d, by rw [hgZ, hsY, hgY], hr⟩

end FV7z.Sea
