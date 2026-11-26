import FV7z.Rfw.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `UString::ReverseFind` (PLAN.md §M, M1)

7-Zip 26.06's `UString::ReverseFind (c) const` at `0x44dd40` in `7zzs` (`CPP/Common/MyString.cpp`; `objdump -d`):
for the string at `p` = `rdi` (`chs`: the characters, the 8 bytes at `p`; `len`: the length, the 4 bytes at `p + 8`;
`ch k`: the `k`-th 4-byte character), from the end back to the first, the index of the last character equal to `c`
(`esi`) in `rax` (`ret` at 44), else -1 in `eax` (`ret` at 53). Cut points: the entry, the loop's head (29) and 48.

- `Res`: the result, as a relation (shared with `ReverseFind_PathSepar`, `FV7z.Rpp`); `Fp`: the bytes read.
- `lea4`, `add4`, `ac4`, `ne4`, `sar4`: the address arithmetic (`lea`, `sub rax, 4`, `cmp rdx, rax`, `sar rax, 2`).
- `Inv`, `Fin`, `Nx`: the invariant (the loop: the characters from `n` on not `c`), the end, and the post of
  `Seg.cfg`; `vc_*`: the cut points' conditions; `rfw_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rfw

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_44 : pret <+: rfw.drop 44 := by decide +kernel
theorem ret_44 (feat : Features) : Dec feat rfw 44 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 44) (k := 0) (pret_0 feat) w_44 (Nat.zero_le _)
theorem w_53 : pret <+: rfw.drop 53 := by decide +kernel
theorem ret_53 (feat : Features) : Dec feat rfw 53 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 53) (k := 0) (pret_0 feat) w_53 (Nat.zero_le _)

/-- The characters. -/
abbrev chs (V : Addr → Byte) (p : Addr) : Addr := rdq(V, p)
/-- The length. -/
abbrev len (V : Addr → Byte) (p : Addr) : BitVec 32 := rdd(V, p + 8#64)
/-- The `k`-th character. -/
abbrev ch (V : Addr → Byte) (p : Addr) (k : Nat) : BitVec 32 := rdd(V, Addr.add (chs V p) (4 * k))

/-- The result `a` of the search for `c`: -1 (as `mov eax, -1` leaves `rax`) if no character is `c`, else the index
of the last one that is. -/
def Res (V : Addr → Byte) (p : Addr) (c : BitVec 32) (a : BitVec 64) : Prop :=
  ((∀ k < (len V p).toNat, ch V p k ≠ c) ∧ a = 4294967295#64) ∨
  ∃ k < (len V p).toNat, ch V p k = c ∧ (∀ j < (len V p).toNat, k < j → ch V p j ≠ c) ∧ a.toNat = k

/-- The bytes read: the pointer to the characters, the length and the characters. -/
def Fp (F : Footprint) (V : Addr → Byte) (p : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add p i)) ∧ (∀ i < 4, Foot F.data (Addr.add (p + 8#64) i)) ∧
  ∀ k < (len V p).toNat, ∀ i < 4, Foot F.data (Addr.add (Addr.add (chs V p) (4 * k)) i)

theorem lea4 (s : Addr) (x : BitVec 32) : s + BitVec.setWidth 64 x * 4#64 = Addr.add s (4 * x.toNat) := by
  have := x.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem add4 (s : Addr) (m : Nat) : Addr.add s (4 * (m + 1)) = Addr.add s (4 * m) + 4#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ac4 (a : Addr) : a + 4#64 - 4#64 = a := by
  have := a.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ne4 (s : Addr) {m : Nat} (h : m < 2 ^ 32) : s ≠ Addr.add s (4 * (m + 1)) := by
  have := s.isLt
  intro e
  have e' := congrArg BitVec.toNat e
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat] at e'
  omega

theorem sar4 (s : Addr) {k : Nat} (h : k < 2 ^ 32) : ((Addr.add s (4 * k) - s).sshiftRight 2).toNat = k := by
  have := s.isLt
  have e : Addr.add s (4 * k) - s = BitVec.ofNat 64 (4 * k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Addr.add, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hm : (BitVec.ofNat 64 (4 * k)).msb = false := by
    rw [BitVec.msb_eq_decide]
    exact decide_eq_false (by show ¬ (2 ^ 63 ≤ (BitVec.ofNat 64 (4 * k)).toNat); rw [BitVec.toNat_ofNat]; omega)
  rw [e, BitVec.sshiftRight_eq_of_msb_false hm, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega

theorem m1 : BitVec.setWidth 64 4294967295#32 = 4294967295#64 := by decide

/-- The character searched for. -/
abbrev cc (g : Gprs) : BitVec 32 := BitVec.setWidth 32 g.rsi
/-- The state at the loop's head, the characters from `n` on not `c`. -/
abbrev G29 (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Gprs :=
  { g₀ with rax := Addr.add (chs V₀ g₀.rdi) (4 * n), rdx := chs V₀ g₀.rdi }

/-- At the loop's head (`1 ≤ n`). -/
def I29 (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) (g : Gprs) : Prop :=
  1 ≤ n ∧ n ≤ (len V₀ g₀.rdi).toNat ∧ (∀ j < (len V₀ g₀.rdi).toNat, n ≤ j → ch V₀ g₀.rdi j ≠ cc g₀) ∧
    g = G29 g₀ V₀ n
/-- At 48: no character is `c`. -/
def I48 (g₀ : Gprs) (V₀ : Addr → Byte) (g : Gprs) : Prop :=
  (∀ k < (len V₀ g₀.rdi).toNat, ch V₀ g₀.rdi k ≠ cc g₀) ∧ ∃ a d, g = { g₀ with rax := a, rdx := d }
/-- The invariant at the cut points. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ ((ℓ = 0 ∧ n = (len V₀ g₀.rdi).toNat + 1 ∧ g = g₀) ∨ (ℓ = 29 ∧ I29 g₀ V₀ n g) ∨
    (ℓ = 48 ∧ n = 0 ∧ I48 g₀ V₀ g))
/-- At a `ret`: the result in `rax`. -/
def Fin (g₀ : Gprs) (V₀ : Addr → Byte) (j : Nat) (g : Gprs) (V : Addr → Byte) : Prop :=
  V = V₀ ∧ (j = 44 ∨ j = 53) ∧ ∃ a d, g = { g₀ with rax := a, rdx := d } ∧ Res V₀ g₀.rdi (cc g₀) a
/-- At an exit: a cut point's invariant with a smaller measure, or a `ret`. -/
def Nx (g₀ : Gprs) (V₀ : Addr → Byte) (n : Nat) : Post :=
  fun j' g' _ V' => (∃ n' < n, Inv g₀ V₀ j' n' g' V') ∨ Fin g₀ V₀ j' g' V'

variable {g₀ : Gprs} {V₀ : Addr → Byte}

theorem x29 {n m : Nat} (h1 : 1 ≤ m) (hm : m ≤ (len V₀ g₀.rdi).toNat)
    (hall : ∀ j < (len V₀ g₀.rdi).toNat, m ≤ j → ch V₀ g₀.rdi j ≠ cc g₀) (hn : m < n) {g' : Gprs} {fl : Rflags}
    (hg : g' = G29 g₀ V₀ m) : Nx g₀ V₀ n 29 g' fl V₀ :=
  Or.inl ⟨m, hn, rfl, Or.inr (Or.inl ⟨rfl, h1, hm, hall, hg⟩)⟩

theorem x48 {n : Nat} (hn : 0 < n) (hall : ∀ k < (len V₀ g₀.rdi).toNat, ch V₀ g₀.rdi k ≠ cc g₀) {a d : BitVec 64}
    {g' : Gprs} {fl : Rflags} (hg : g' = { g₀ with rax := a, rdx := d }) : Nx g₀ V₀ n 48 g' fl V₀ :=
  Or.inl ⟨0, hn, rfl, Or.inr (Or.inr ⟨rfl, rfl, hall, a, d, hg⟩)⟩

theorem xFin {n j : Nat} (hj : j = 44 ∨ j = 53) {a d : BitVec 64} (hr : Res V₀ g₀.rdi (cc g₀) a) {g' : Gprs}
    {fl : Rflags} (hg : g' = { g₀ with rax := a, rdx := d }) : Nx g₀ V₀ n j g' fl V₀ :=
  Or.inr ⟨rfl, hj, a, d, hg, hr⟩

theorem xe29 {n : Nat} (hL : 0 < (len V₀ g₀.rdi).toNat) (hn : (len V₀ g₀.rdi).toNat < n) {g' : Gprs}
    {fl : Rflags}
    (hg : g' = { g₀ with rax := chs V₀ g₀.rdi + BitVec.setWidth 64 (len V₀ g₀.rdi) * 4#64, rdx := chs V₀ g₀.rdi }) :
    Nx g₀ V₀ n 29 g' fl V₀ :=
  x29 hL (Nat.le_refl _) (fun _ hj h => absurd hj (Nat.not_lt.mpr h)) hn (by rw [hg, lea4])

/-- The found case: the index from `sar`. -/
theorem resF {V : Addr → Byte} {p : Addr} {c : BitVec 32} {m : Nat} (hm : m + 1 ≤ (len V p).toNat)
    (hch : ch V p m = c) (hall : ∀ j < (len V p).toNat, m + 1 ≤ j → ch V p j ≠ c) :
    Res V p c ((Addr.add (chs V p) (4 * m) - chs V p).sshiftRight 2) :=
  Or.inr ⟨m, hm, hch, hall, sar4 _ (by have := (len V p).isLt; omega)⟩

variable {F : Footprint} {Wl : List Rgn}

/-- The entry: length 0, to 48; else to the loop's head past the last character. -/
theorem vc_0 {f : Rflags} (hF : Fp F V₀ g₀.rdi) :
    W_0 F Wl (Nx g₀ V₀ ((len V₀ g₀.rdi).toNat + 1)) g₀ f V₀ := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨f0, f8, -⟩ := hF
  dsimp only at f0 f8 ⊢
  wpx [W_0, W_11, o0, o1, BitVec.and_self]
  refine ⟨f8, fun _ => ⟨fun hc => ?_, fun hc => ⟨f0, ?_⟩⟩⟩
  · have h0 : (len V₀ rdi).toNat = 0 := by
      have e : rdd(V₀, rdi + 8#64) = 0 := by simpa using hc
      simp [len, e]
    exact x48 (by omega) (by exact fun k hk => absurd (show k < (len V₀ rdi).toNat from hk) (by omega)) rfl
  · have hne : rdd(V₀, rdi + 8#64) ≠ 0 := by simpa using hc
    have hpos : 0 < (len V₀ rdi).toNat :=
      Nat.pos_of_ne_zero fun e => hne (BitVec.eq_of_toNat_eq (by simpa using e))
    exact xe29 (by exact hpos) (by dsimp only; omega) rfl

set_option maxHeartbeats 1000000 in
/-- The loop's head, character `m` equal to `c`: its index, the `ret` at 44. -/
theorem vc_29f {m : Nat} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hm : m + 1 ≤ (len V₀ g₀.rdi).toNat)
    (hall : ∀ j < (len V₀ g₀.rdi).toNat, m + 1 ≤ j → ch V₀ g₀.rdi j ≠ cc g₀) (hch : ch V₀ g₀.rdi m = cc g₀) :
    W_29 F Wl (Nx g₀ V₀ (m + 1)) (G29 g₀ V₀ (m + 1)) f V₀ := by
  have hr := resF hm hch hall
  rw [show G29 g₀ V₀ (m + 1) = { g₀ with rax := Addr.add (chs V₀ g₀.rdi) (4 * m) + 4#64, rdx := chs V₀ g₀.rdi }
    by rw [← add4]]
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  have fm := fk m hm
  dsimp only [cc] at hch fm hr ⊢
  have hc := hch
  dsimp only [ch, chs] at hc
  wpx [W_29, W_24, W_37, o3, o2, o4, Op.cmpmr, Op.sar64, ac4, hc, eq_self_iff_true, decide_true, Bool.not_true,
    Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fm
    | apply And.intro
    | intro)
  exact xFin (Or.inl rfl) (by exact hr) rfl

/-- The loop's head, the first character not `c`: no character is, 48. -/
theorem vc_29z {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hm : 1 ≤ (len V₀ g₀.rdi).toNat)
    (hall : ∀ j < (len V₀ g₀.rdi).toNat, 1 ≤ j → ch V₀ g₀.rdi j ≠ cc g₀) (hch : ¬ ch V₀ g₀.rdi 0 = cc g₀) :
    W_29 F Wl (Nx g₀ V₀ 1) (G29 g₀ V₀ 1) f V₀ := by
  rw [show G29 g₀ V₀ 1 = { g₀ with rax := Addr.add (chs V₀ g₀.rdi) (4 * 0) + 4#64, rdx := chs V₀ g₀.rdi }
    by rw [← add4]]
  have hall' : ∀ k < (len V₀ g₀.rdi).toNat, ch V₀ g₀.rdi k ≠ cc g₀ := fun k hk => by
    rcases k with _ | k
    · exact hch
    · exact hall _ hk (by omega)
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  have fm := fk 0 hm
  dsimp only [cc] at hch fm hall' ⊢
  have hc := hch
  dsimp only [ch, chs] at hc
  simp only [Nat.mul_zero, addr_add_zero] at hc fm
  wpx [W_29, W_24, W_37, o3, o2, o4, Op.cmpmr, ac4, Nat.mul_zero, addr_add_zero, hc, eq_self_iff_true,
    decide_true, decide_false, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true, false_implies,
    true_implies, true_and, and_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fm
    | exact x48 (by omega) (by exact hall') rfl
    | apply And.intro
    | intro)

/-- The loop's head, character `m + 1` not `c`: the next. -/
theorem vc_29s {m : Nat} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (hm : m + 1 + 1 ≤ (len V₀ g₀.rdi).toNat)
    (hall : ∀ j < (len V₀ g₀.rdi).toNat, m + 1 + 1 ≤ j → ch V₀ g₀.rdi j ≠ cc g₀)
    (hch : ¬ ch V₀ g₀.rdi (m + 1) = cc g₀) :
    W_29 F Wl (Nx g₀ V₀ (m + 1 + 1)) (G29 g₀ V₀ (m + 1 + 1)) f V₀ := by
  rw [show G29 g₀ V₀ (m + 1 + 1) =
      { g₀ with rax := Addr.add (chs V₀ g₀.rdi) (4 * (m + 1)) + 4#64, rdx := chs V₀ g₀.rdi }
    by rw [← add4]]
  have hall' : ∀ j < (len V₀ g₀.rdi).toNat, m + 1 ≤ j → ch V₀ g₀.rdi j ≠ cc g₀ := fun j hj h => by
    by_cases e : j = m + 1
    · subst e
      exact hch
    · exact hall j hj (by omega)
  have hm32 : m < 2 ^ 32 := by have := (len V₀ g₀.rdi).isLt; omega
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  obtain ⟨-, -, fk⟩ := hF
  have fm := fk (m + 1) (by omega)
  dsimp only [cc] at hch fm hall' hm ⊢
  have hc := hch
  dsimp only [ch, chs] at hc
  have hne := ne4 (rdq(V₀, rdi)) hm32
  wpx [W_29, W_24, W_37, o3, o2, o4, Op.cmpmr, ac4, hc, hne, decide_false, Bool.not_false, Bool.true_eq_false,
    Bool.false_eq_true, false_implies, true_implies, true_and, and_true, implies_true]
  all_goals repeat' (first
    | with_reducible exact fm
    | exact x29 (by omega) (by exact Nat.le_of_succ_le hm) (by exact hall') (by omega) rfl
    | apply And.intro
    | intro)

theorem vc_29 {n : Nat} {g : Gprs} {f : Rflags} (hF : Fp F V₀ g₀.rdi) (h : I29 g₀ V₀ n g) :
    W_29 F Wl (Nx g₀ V₀ n) g f V₀ := by
  obtain ⟨h1, hn, hall, rfl⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  by_cases hch : ch V₀ g₀.rdi m = cc g₀
  · exact vc_29f hF hn hall hch
  · rcases m with _ | m
    · exact vc_29z hF hn hall hch
    · exact vc_29s hF hn hall hch

/-- 48: -1 in `eax`, the `ret` at 53. -/
theorem vc_48 {g : Gprs} {f : Rflags} (h : I48 g₀ V₀ g) : W_48 F Wl (Nx g₀ V₀ 0) g f V₀ := by
  obtain ⟨hall, a, d, rfl⟩ := h
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g₀
  dsimp only at hall ⊢
  wpx [W_48, o5]
  exact xFin (Or.inr rfl) (by exact Or.inl ⟨hall, m1⟩) rfl

theorem vcAll (hF : Fp F V₀ g₀.rdi) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ ℓ n g V) : Wt ℓ F Wl (Nx g₀ V₀ n) g f V := by
  obtain ⟨rfl, ⟨rfl, rfl, rfl⟩ | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩⟩ := h
  · exact vc_0 hF
  · exact vc_29 hF h
  · exact vc_48 h

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::ReverseFind (c)` from its entry to the return address: `rax` the result (`Res`), `rdx` changed. -/
theorem rfw_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rfw_at rfw) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rfw_at) (hF : Fp F V X.cpu.gpr.rdi)
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      (∃ a d, Z.cpu.gpr = { X.cpu.gpr with rax := a, rdx := d }.set 4 (X.cpu.gpr.rsp + 8) ∧
        Res V X.cpu.gpr.rdi (cc X.cpu.gpr) a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine c.cfg hin (fun ℓ => spAll prof ℓ) (fun ℓ n g _ V' => Inv X.cpu.gpr V ℓ n g V')
    (fun j g _ V' => Fin X.cpu.gpr V j g V') (fun ℓ n g f V' h => vcAll hF ℓ n g f V' h) ?_
    ((len V X.cpu.gpr.rdi).toNat + 1) 0 hK hA (by rw [addr_add_zero]; exact hrip) ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  rintro j g fl V' ⟨hV, hj, a, d, rfl, hr⟩ Y t' hKY hAY hrY hgY -
  subst hV
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgY]
  rcases hj with rfl | rfl
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_44 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨a, d, by rw [hgZ, hsY, hgY], hr⟩
  · refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (ret_53 _) (by rw [hsY]; exact hl) hin₂ h₂
      (by rw [hsY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    exact k Z t₂ hKZ hAZ hrZ ⟨a, d, by rw [hgZ, hsY, hgY], hr⟩

end FV7z.Rfw
