import FV7z.Fcc.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `FindCharPosInString (const char *s, char c)` (PLAN.md §M, M1)

7-Zip 26.06's `FindCharPosInString (const char *s, char c)` at `0x44b960` in `7zzs` (`CPP/Common/MyString.cpp`;
`objdump -d`): `s` = `rdi`, `c` = `sil` (`ch k`: the byte at `s + k`). The first byte, if `c`, gives 0 (53); else
the loop's head (36) with `rax` = `s + i`, `dl` = `ch i` (not `c`): `ch i` 0 gives -1 (45), `ch (i + 1)` = `c`
gives `i + 1` (50), else `i + 1` next. So the result is the index of the first byte that is `c` or 0, if `c`, else
-1 (`Res`). Nothing is stored; `rax`, `rcx`, `rdx` change.

- `Res`; `Inv`, `Fin`, `Nx`: the invariant (the loop: byte `i` in `dl`, the bytes before it neither `c` nor 0, byte
  `N` 0 bounds the loop), the end, the post of `Seg.cfg`; `vc_0`, `vc_36`: the cut points' conditions.
- `fcc_ok`: from the entry to the return address with `Res` of `eax`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (sw_8_32_8 sw_8_32_64_8)
namespace FV7z.Fcc

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_45 : pret <+: fcc.drop 45 := by decide +kernel
theorem ret_45 (feat : Features) : Dec feat fcc 45 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 45) (k := 0) (pret_0 feat) w_45 (Nat.zero_le _)
theorem w_50 : pret <+: fcc.drop 50 := by decide +kernel
theorem ret_50 (feat : Features) : Dec feat fcc 50 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 50) (k := 0) (pret_0 feat) w_50 (Nat.zero_le _)
theorem w_53 : pret <+: fcc.drop 53 := by decide +kernel
theorem ret_53 (feat : Features) : Dec feat fcc 53 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 53) (k := 0) (pret_0 feat) w_53 (Nat.zero_le _)

/-- The byte at `s + k`. -/
abbrev ch (V : Addr → Byte) (s : Addr) (k : Nat) : BitVec 8 := ofBytesLE 8 (List.map V (byteAddrs (Addr.add s k) 1))

/-- The result `r`: the index of the first byte that is `c` or 0, if it is `c`; else -1. -/
def Res (V : Addr → Byte) (s : Addr) (c : BitVec 8) (r : BitVec 32) : Prop :=
  ∃ i, (∀ k < i, ch V s k ≠ c ∧ ch V s k ≠ 0) ∧
    ((ch V s i = c ∧ r = BitVec.ofNat 32 i) ∨ (ch V s i ≠ c ∧ ch V s i = 0 ∧ r = 4294967295#32))

theorem step1 (a : Addr) (i : Nat) : Addr.add a i + 1#64 = Addr.add a (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `eax - edi` at 50: the index. -/
theorem idx (s : Addr) (i : Nat) : BitVec.setWidth 32 (Addr.add s i) - BitVec.setWidth 32 s = BitVec.ofNat 32 i := by
  apply BitVec.eq_of_toNat_eq
  have := s.isLt
  simp only [Addr.add, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem sw8r (x : BitVec 64) : ((x.setWidth 32).setWidth 64).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem sw32r (x : BitVec 64) : (x.setWidth 32).setWidth 8 = x.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem tz_t {b : BitVec 8} (h : (!(b == 0)) = true) : b ≠ 0 := fun e => by
  subst e
  revert h
  decide

theorem tz_f {b : BitVec 8} (h : (!(b == 0)) = false) : b = 0 := by
  cases hb : (b == 0) with
  | true => exact beq_iff_eq.mp hb
  | false =>
    rw [hb] at h
    exact absurd h (by decide)

theorem nb_t {p : Prop} [Decidable p] (h : (!decide p) = true) : ¬ p := fun hp => by
  rw [decide_eq_true hp] at h
  exact absurd h (by decide)

theorem nb_f {p : Prop} [Decidable p] (h : (!decide p) = false) : p := by
  cases hd : decide p with
  | true => exact of_decide_eq_true hd
  | false =>
    rw [hd] at h
    exact absurd h (by decide)

theorem ok_succ {V : Addr → Byte} {s : Addr} {c : BitVec 8} {i : Nat} (hok : ∀ k < i, ch V s k ≠ c ∧ ch V s k ≠ 0)
    (hc : ch V s i ≠ c) (hz : ch V s i ≠ 0) : ∀ k < i + 1, ch V s k ≠ c ∧ ch V s k ≠ 0 := by
  intro k hk
  by_cases h : k < i
  · exact hok k h
  · obtain rfl : k = i := by omega
    exact ⟨hc, hz⟩

theorem f0 {R : List Rgn} {s : Addr} (h : Foot R (Addr.add s 0)) : ∀ j < 1, Foot R (Addr.add s j) := fun j hj => by
  obtain rfl : j = 0 := by omega
  exact h

theorem f1 {R : List Rgn} {s : Addr} {i : Nat} (h : Foot R (Addr.add s (i + 1))) :
    ∀ j < 1, Foot R (Addr.add (Addr.add s i + 1#64) j) := fun j hj => by
  obtain rfl : j = 0 := by omega
  rw [addr_add_zero, step1]
  exact h

/-- `rax`, `rcx` at the loop's head. -/
abbrev G36a (g₀ : Gprs) (i : Nat) : Gprs :=
  { g₀ with rax := Addr.add g₀.rdi i, rcx := (g₀.rsi.setWidth 32).setWidth 64 }
/-- The registers at the loop's head, byte `i` in `dl`. -/
abbrev G36 (g₀ : Gprs) (V₀ : Addr → Byte) (i : Nat) : Gprs :=
  { G36a g₀ i with rdx := ((ch V₀ g₀.rdi i).setWidth 32).setWidth 64 }

/-- At the loop's head: byte `i` not `c`, the bytes before it neither `c` nor 0. -/
def I36 (g₀ : Gprs) (V₀ : Addr → Byte) (N n : Nat) (g : Gprs) : Prop :=
  ∃ i ≤ N, n = N + 1 - i ∧ ch V₀ g₀.rdi i ≠ g₀.rsi.setWidth 8 ∧
    (∀ k < i, ch V₀ g₀.rdi k ≠ g₀.rsi.setWidth 8 ∧ ch V₀ g₀.rdi k ≠ 0) ∧ g = G36 g₀ V₀ i
/-- The invariant at the cut points. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (N ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ ((ℓ = 0 ∧ n = N + 2 ∧ g = g₀) ∨ (ℓ = 36 ∧ I36 g₀ V₀ N n g))
/-- At a `ret`: the result in `eax`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ (j = 45 ∨ j = 50 ∨ j = 53) ∧ ∃ (r : BitVec 32) (c d : BitVec 64),
    g = { g₀ with rax := r.setWidth 64, rcx := c, rdx := d } ∧ Res V₀ g₀.rdi (g₀.rsi.setWidth 8) r
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (N n : Nat) : Post :=
  fun j' g' _ V' => (∃ n' < n, Inv g₀ V₀ N j' n' g' V') ∨ Fin g₀ V₀ j' g' V'

variable {g₀ : Gprs} {V₀ : Addr → Byte}

theorem eFin {N n j : Nat} (hj : j = 45 ∨ j = 50 ∨ j = 53) {r : BitVec 32} {c d : BitVec 64}
    (hr : Res V₀ g₀.rdi (g₀.rsi.setWidth 8) r) {g' : Gprs} {fl : Rflags}
    (hg : g' = { g₀ with rax := r.setWidth 64, rcx := c, rdx := d }) : Nx g₀ V₀ N n j g' fl V₀ :=
  Or.inr ⟨rfl, hj, r, c, d, hg, hr⟩

theorem e36 {N n i : Nat} (hi : i ≤ N) (hn : N + 1 - i < n) (hc : ch V₀ g₀.rdi i ≠ g₀.rsi.setWidth 8)
    (hok : ∀ k < i, ch V₀ g₀.rdi k ≠ g₀.rsi.setWidth 8 ∧ ch V₀ g₀.rdi k ≠ 0) {g' : Gprs} {fl : Rflags}
    (hg : g' = G36 g₀ V₀ i) : Nx g₀ V₀ N n 36 g' fl V₀ :=
  Or.inl ⟨_, hn, rfl, Or.inr ⟨rfl, i, hi, rfl, hc, hok, hg⟩⟩

variable {F : Footprint} {Wl : List Rgn}

set_option maxHeartbeats 1000000 in
/-- The entry: byte 0 `c`, 0 at 53; else the loop's head with byte 0. -/
theorem vc_0 {N : Nat} {f : Rflags} (hF : ∀ k ≤ N, Foot F.data (Addr.add g₀.rdi k)) :
    W_0 F Wl (Nx g₀ V₀ N (N + 2)) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hF ⊢
  wpx [W_0, W_17, W_51, o0, o5, sw_8_32_8, sw_8_32_64_8, sw8r, sw32r, BitVec.xor_self]
  refine ⟨f0 (hF 0 (Nat.zero_le _)), fun h => ?_, fun h af => ?_⟩
  · refine e36 (i := 0) (Nat.zero_le _) (by omega) ?_ (fun k hk => absurd hk (Nat.not_lt_zero _)) ?_
    · simp only [ch, addr_add_zero]
      exact fun e => nb_t h e.symm
    · simp only [G36, G36a, ch, addr_add_zero]
  · have hc : ch V₀ rdi 0 = rsi.setWidth 8 := by
      simp only [ch, addr_add_zero]
      exact (nb_f h).symm
    exact eFin (Or.inr (Or.inr rfl)) (by exact ⟨0, fun k hk => absurd hk (Nat.not_lt_zero _), Or.inl ⟨hc, rfl⟩⟩) rfl

set_option maxHeartbeats 3000000 in
/-- The loop's head, byte `i`: 0, -1 at 45; else byte `i + 1` `c`, `i + 1` at 50; else the head with `i + 1`. -/
theorem vc_36 {N n : Nat} {g : Gprs} {f : Rflags} (hF : ∀ k ≤ N, Foot F.data (Addr.add g₀.rdi k))
    (hN : ch V₀ g₀.rdi N = 0) (h : I36 g₀ V₀ N n g) : W_36 F Wl (Nx g₀ V₀ N n) g f V₀ := by
  obtain ⟨i, hi, rfl, hne, hok, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only [G36, G36a] at hF hN hne hok ⊢
  wpx [W_36, W_24, W_48, W_40, o2, o1, o4, o3, BitVec.and_self, sw_8_32_64_8, sw_8_32_8, sw8r, sw32r]
  intro af
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hz : ch V₀ rdi i ≠ 0 := tz_t h1
    have hi1 : i + 1 ≤ N := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hi fun e => hz (by rw [e]; exact hN))
    have hok' := ok_succ hok hne hz
    refine ⟨f1 (hF _ hi1), fun h2 => ?_, fun h2 => ?_⟩
    · have hc : ch V₀ rdi (i + 1) = rsi.setWidth 8 := by
        have e := of_decide_eq_true h2
        rw [step1] at e
        exact e
      exact eFin (Or.inr (Or.inl rfl))
        (by rw [step1, idx]; exact ⟨i + 1, hok', Or.inl ⟨hc, rfl⟩⟩) rfl
    · refine e36 (i := i + 1) hi1 (by omega) ?_ ?_ ?_
      · have e := of_decide_eq_false h2
        rw [step1] at e
        simpa only using e
      · simpa only using hok'
      · simp only [G36, G36a, step1]
  · have hz : ch V₀ rdi i = 0 := tz_f h1
    exact eFin (Or.inl rfl) (by exact ⟨i, hok, Or.inr ⟨hne, hz, rfl⟩⟩) rfl

theorem vcAll {N : Nat} (hF : ∀ k ≤ N, Foot F.data (Addr.add g₀.rdi k)) (hN : ch V₀ g₀.rdi N = 0)
    (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ N ℓ n g V) :
    Wt ℓ F Wl (Nx g₀ V₀ N n) g f V := by
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, h⟩⟩ := h
  · exact vc_0 (f := f) hF
  · exact vc_36 (f := f) hF hN h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `FindCharPosInString (s, c)` from its entry to the return address, byte `N` of `s` 0 and the bytes up to it
readable: `eax` the result (`Res`), `rcx`, `rdx` changed, nothing stored. -/
theorem fcc_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L fcc_at fcc) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = fcc_at) {N : Nat}
    (hF : ∀ k ≤ N, Foot F.data (Addr.add X.cpu.gpr.rdi k)) (hN : ch V X.cpu.gpr.rdi N = 0)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ (r : BitVec 32) (c d : BitVec 64),
        Z.cpu.gpr = { X.cpu.gpr with rax := r.setWidth 64, rcx := c, rdx := d }.set 4 (X.cpu.gpr.rsp + 8) ∧
        Res V X.cpu.gpr.rdi (X.cpu.gpr.rsi.setWidth 8) r) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V' => Inv X.cpu.gpr V N ℓ n g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hF hN ℓ n g f V' h) ?_
    (N + 2) 0 hK hA (by rw [addr_add_zero]; exact hrip) ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rintro j g fl V' ⟨hV, hj, r, c', d, rfl, hr⟩ Y t' hKY hAY hrY hgY -
  rw [hV] at hAY
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  rcases hj with rfl | rfl | rfl
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_45 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, c', d, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_50 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, c', d, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_53 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨r, c', d, by rw [hgZ, hsY, hgY], hr⟩

end FV7z.Fcc
