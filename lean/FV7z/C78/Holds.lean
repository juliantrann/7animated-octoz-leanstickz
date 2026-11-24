import FV7z.C78.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
/-!
# `csuTg 78`: the CRC-32 table of bzip2 (PLAN.md §M, constructors)

`csuTg 78`, at offset 1824 of `sti`, is `endbr64; jmp c78_at`. The function there (`CBZip2Crc::InitTable` by its
shape) fills the 1024 bytes at `0x79d440` (`wr78`) with 256 words, the CRC-32 (MSB first, the polynomial
`0x04c11db7`) of each index, and returns. The outer loop walks `rsi` through the table four bytes at a time, up to
`r8`; the inner loop takes eight steps for each word, `rdx` the count left. No later code takes those bytes as an
address, so its spec says only where they lie (`wrSpec wr78`).

- `Inv`: the invariant at the three cut points (`Cuts.lean`): the entry; the outer loop's head with `rsi` at word `k`
  of the table; the inner loop's head, the same and `rdx` from 1 to 8 (the measure as in `C70.Inv`).
- `step4`: `rsi` one word on, and the outer loop's test (the inner count by `dec32`).
- `vc_0`, `vc_24`, `vc_32`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches the `ret`.
  `vc_24` and `vc_32` are for the table at a variable `b`.
- `runsF`: the function is one as `Csu.csu_ok` asks (`cfg_runs`); `runs78`: so is `csuTg 78` (`jmp_runs`), for an
  invariant that goes from `78` to `79` through `Out`; `runs78_jg`: for `Jg` (`jg_wr`).
-/
namespace FV7z.C78
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The table. -/
def wr78 : List (Nat × Nat) := [(7984192, 7985216)]

/-- The bytes outside the table as before. -/
abbrev Out (V V' : Addr → Byte) : Prop := Raf.Out 7984192 (7984192 + 1024) V V'

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ n = 2561 ∧ g = g₀ ∧ V = V₀) ∨
  ∃ k < 256, g.rsi.toNat = 7984192 + 4 * k ∧ g.r8 = BitVec.ofNat 64 (7984192 + 1024) ∧ Kp g₀ g ∧ Out V₀ V ∧
    ((ℓ = 24 ∧ n = 10 * (256 - k)) ∨
      (ℓ = 32 ∧ 1 ≤ g.rdx.toNat ∧ g.rdx.toNat ≤ 8 ∧ n = 10 * (256 - k) - 9 + g.rdx.toNat))

/-- `rsi` one word on, and the outer loop's test `cmp r8, rsi`: not the end means another word. -/
theorem step4 {r s : BitVec 64} {b k : Nat} (hb : b + 1024 < 2 ^ 64) (hr : r = BitVec.ofNat 64 (b + 1024))
    (hs : s.toNat = b + 4 * k) (hk : k < 256) :
    (s + 4#64).toNat = b + 4 * (k + 1) ∧ (¬ r = s + 4#64 → k + 1 < 256) := by
  subst hr
  refine ⟨?_, fun h => Nat.lt_of_le_of_ne (by omega) fun e => h ?_⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- From the entry to the outer loop's head: `rsi` the table, `r8` its end. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post)
    (hQ : ∀ g' f' V', Inv g V 24 2560 g' f' V' → Q 24 g' f' V') : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  intros
  apply hQ
  exact Or.inr ⟨0, by decide, by simp, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- From the outer loop's head to the inner one's: `rdx` 8. -/
theorem vc_24 {b k : Nat} {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.rsi.toNat = b + 4 * k)
    (hK : Kp g₀ g) (Q : Post)
    (hQ : ∀ g' f', g'.rsi.toNat = b + 4 * k → g'.r8 = g.r8 → Kp g₀ g' → g'.rdx.toNat = 8 → Q 32 g' f' V) :
    W_24 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hQ
  wpx [W_24, o1]
  intros
  exact hQ _ _ hs rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) (by simp)

/-- One inner step, for the table at a variable `b`: back to the inner head with `rdx` one less; or, after the
eighth, the word stored at `rsi` and on to the next word, or to the `ret` after the last. -/
theorem vc_32 {b k : Nat} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hb : b + 1024 < 2 ^ 64)
    (hw : ∀ i < 1024, Foot Wl (Addr.add (BitVec.ofNat 64 b) i)) (hk : k < 256) (hs : g.rsi.toNat = b + 4 * k)
    (hr8 : g.r8 = BitVec.ofNat 64 (b + 1024)) (hK : Kp g₀ g) (hO : Raf.Out b (b + 1024) V₀ V)
    (hc1 : 1 ≤ g.rdx.toNat) (hc8 : g.rdx.toNat ≤ 8) (Q : Post)
    (hQ1 : ∀ g' f', g'.rsi.toNat = b + 4 * k → g'.r8 = BitVec.ofNat 64 (b + 1024) → Kp g₀ g' →
      g'.rdx.toNat + 1 = g.rdx.toNat → 1 ≤ g'.rdx.toNat → Q 32 g' f' V)
    (hQ2 : ∀ g' f' V', k + 1 < 256 → g'.rsi.toNat = b + 4 * (k + 1) → g'.r8 = BitVec.ofNat 64 (b + 1024) →
      Kp g₀ g' → Raf.Out b (b + 1024) V₀ V' → Q 24 g' f' V')
    (hQ3 : ∀ g' f' V', Kp g₀ g' → Raf.Out b (b + 1024) V₀ V' → Q 67 g' f' V') : W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hr8 hc1 hc8 hQ1
  wpx -implicitDefEqProofs [W_32, W_50, o2, o3]
  intros
  have h4 := step4 hb hr8 hs hk
  refine ⟨fun h => ?_, fun _ => ⟨ft_at hw (by omega) (by omega) (by omega), fun h => ?_, fun _ => ?_⟩⟩
  · have hne : ¬ rdx.setWidth 32 = 1#32 := by simpa using h
    have hd := dec32 hc1 hc8 hne
    exact hQ1 _ _ hs hr8 (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) hd.1 hd.2
  · have hne : ¬ r8 = rsi + 4#64 := by simpa using h
    exact hQ2 _ _ _ (h4.2 hne) h4.1 hr8 (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))
  · exact hQ3 _ _ _ (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the table as at the entry. -/
theorem vc (hw : ∀ i < 1024, Foot Wl (Addr.add 7984192#64 i)) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat)
    (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = 67 ∧ Kp g₀ g' ∧ Out V₀ V'))
      g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨k, hk, hs, hr8, hK, hO, ⟨rfl, rfl⟩ | ⟨rfl, hc1, hc8, rfl⟩⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    exact vc_0 _ fun g' f' V' h => Or.inl ⟨2560, by decide, h⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_24 hs hK
    intro g' f' h1 h2 h3 h4
    exact Or.inl ⟨10 * (256 - k) - 9 + g'.rdx.toNat, by omega,
      Or.inr ⟨k, hk, h1, h2.trans hr8, h3, hO, Or.inr ⟨rfl, by omega, by omega, rfl⟩⟩⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_32 (b := 7984192) (by decide) hw hk hs hr8 hK hO hc1 hc8
    · intro g' f' e1 e2 e3 e4 e5
      exact Or.inl ⟨10 * (256 - k) - 9 + g'.rdx.toNat, by omega,
        Or.inr ⟨k, hk, e1, e2, e3, hO, Or.inr ⟨rfl, e5, by omega, rfl⟩⟩⟩
    · intro g' f' V' e1 e2 e3 e4 e5
      exact Or.inl ⟨10 * (256 - (k + 1)), by omega, Or.inr ⟨k + 1, e1, e2, e3, e4, e5, Or.inl ⟨rfl, rfl⟩⟩⟩
    · intro g' f' V' e1 e2
      exact Or.inr ⟨rfl, e1, e2⟩

/-- `Out` says the bytes outside `wr78` are as before. -/
theorem out_wr {V V' : Addr → Byte} (h : Out V V') : ∀ a : Addr, ¬ InR wr78 a.toNat → V' a = V a := fun a ha =>
  h a fun h' => ha (by simp only [wr78, InR, or_false]; omega)

/-- The `ret` at offset 67 of `c78`. -/
def r67 : List Byte := [0xc3]
theorem r67_0 : ∀ feat, Dec feat r67 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v67 : r67 <+: c78.drop 67 := by decide +kernel

/-- `csuTg 78`, at offset 1824 of `sti`: `endbr64; jmp c78_at`. -/
def c1824 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x07, 0xfc, 0x14, 0x00]
theorem c1824_0 : ∀ feat, Dec feat c1824 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c1824_4 : ∀ feat, Dec feat c1824 4 (FV7z.mk .jmp 64 [.rel 1375239] 5) := by dec_rfl
theorem v1824 : c1824 <+: sti.drop 1824 := by decide +kernel
theorem tg78 : csuTg 78 = sti_at.add 1824 := by decide +kernel
theorem calls78 : calls 78 = [] := by decide +kernel
theorem wrT78 : ∀ x ∈ wr78, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- The function at `c78_at` is one as `Csu.csu_ok` asks, for an invariant that goes from `78` to `79` through
`Out`. -/
theorem runsF {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hinE : CodeIn L c78_at c78)
    (hw : ∀ i < 1024, Foot Wl (Addr.add 7984192#64 i)) (hsp : 7985216 + 64 ≤ sp.toNat)
    (hJ : ∀ V V', J 78 V → Out V V' → J 79 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 78 c78_at :=
  cfg_runs (j := 0) c hC hinE (addr_add_zero _).symm (spAll prof)
    (Dec.shift (j := 67) (k := 0) (r67_0 _) v67 (by decide)) (lt_len (by decide)) Out Inv
    (fun _ _ _ => ⟨2561, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩) (vc hw) (fun _ _ h a ha => h a (by omega)) hJ

/-- `csuTg 78` is a function as `Csu.csu_ok` asks, for an invariant that goes from `78` to `79` through `Out`. -/
theorem runs78 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hinE : CodeIn L c78_at c78) (hw : ∀ i < 1024, Foot Wl (Addr.add 7984192#64 i)) (hsp : 7985216 + 64 ≤ sp.toNat)
    (hJ : ∀ V V', J 78 V → Out V V' → J 79 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 78 (csuTg 78) :=
  jmp_runs (j := 1824) (rel := 1375239) c hin hinE (by decide) tg78
    (Dec.shift (j := 1824) (k := 0) (c1824_0 _) v1824 (by decide))
    (Dec.shift (j := 1824) (k := 4) (c1824_4 _) v1824 (by decide))
    (sti_lt (by decide)) (by decide) (runsF c hC hinE hw hsp hJ)

/-- `csuTg 78` for `Jg`, its spec `wrSpec wr78`. -/
theorem runs78_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hinE : CodeIn L c78_at c78) (hw : ∀ i < 1024, Foot Wl (Addr.add 7984192#64 i))
    (hsp : 7985216 + 64 ≤ sp.toNat) (hspec : spec 78 = wrSpec wr78) (hD : ∀ k, (spec k).Dep)
    (hXw : ∀ k, 3 ≤ k → k < 78 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr78, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W', G 78 W → Out W W' → G 79 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 78 (csuTg 78) :=
  runs78 c hC hin hinE hw hsp fun W W' hJ hO =>
    jg_wr (by decide) calls78 hspec hD wrT78 hXw (out_wr hO) (hG W W' · hO) hJ

end FV7z.C78
