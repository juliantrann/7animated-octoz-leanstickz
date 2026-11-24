import FV7z.C3.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
/-!
# `csuTg 3`: the CRC-32 tables of 7-Zip (PLAN.md §M, constructors)

`csuTg 3`, at offset 0 of `sti`, is `endbr64; jmp c3_at`. The function there (`CrcGenerateTable`) fills the 12288
bytes at `0x7a4e00` (`wr3`) and returns, in two loops:

- the first takes `rsi` through the 256 words of the first table, with an inner loop of eight steps for each, `rdx`
  the count left, and stores the word at `rdi + 4·rsi`;
- the second takes `rdx` through the words of the table from the first on, loads the word at `rdx` and the word
  of the first table its low byte picks, and stores at `rdx + 1024`, up to `rsi = rdi + 11264`.

No later code takes those bytes as an address, so its spec says only where they lie (`wrSpec wr3`).

- `Inv`: the invariant at the four cut points (`Cuts.lean`): the entry; the first loop's head and its inner loop's
  head (the measure as in `C78.Inv`, above that of the second loop); the second loop's head with `rdx` at word `j`.
- `inc_k`, `step80`, `toNat_1020`, `toNat_b0`: the loops' arithmetic.
- `vc_0`, `vc_16`, `vc_32`, `vc_80`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches
  the `ret`. `vc_32` and `vc_80` are for the table at a variable `b`; the second loop's loads need the table in the
  footprint's data (`Seg.hws`).
- `runsF`: the function is one as `Csu.csu_ok` asks (`cfg_runs`); `runs3`: so is `csuTg 3` (`jmp_runs`), for an
  invariant that goes from `3` to `4` through `Out`; `runs3_jg`: for `Jg` (`jg_wr`).
-/
namespace FV7z.C3
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The tables. -/
def wr3 : List (Nat × Nat) := [(8015360, 8027648)]

/-- The bytes outside the tables as before. -/
abbrev Out (V V' : Addr → Byte) : Prop := Raf.Out 8015360 (8015360 + 12288) V V'

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ n = 5378 ∧ g = g₀ ∧ V = V₀) ∨
  (∃ k < 256, g.rsi.toNat = k ∧ g.rdi = BitVec.ofNat 64 8015360 ∧ Kp g₀ g ∧ Out V₀ V ∧
    ((ℓ = 16 ∧ n = 2817 + 10 * (256 - k)) ∨
      (ℓ = 32 ∧ 1 ≤ g.rdx.toNat ∧ g.rdx.toNat ≤ 8 ∧ n = 2817 + 10 * (256 - k) - 9 + g.rdx.toNat))) ∨
  (ℓ = 80 ∧ ∃ j < 2816, g.rdx.toNat = 8015360 + 4 * j ∧ g.rdi = BitVec.ofNat 64 8015360 ∧
    g.rsi = BitVec.ofNat 64 8015360 + 11264#64 ∧ Kp g₀ g ∧ Out V₀ V ∧ n = 2816 - j)

/-- The first loop's index one more, and its test `cmp rsi, 256`: not the end means another word. -/
theorem inc_k {x : BitVec 64} {k : Nat} (hx : x.toNat = k) (hk : k < 256) :
    (x + 1#64).toNat = k + 1 ∧ (¬ x + 1#64 = 256#64 → k + 1 < 256) := by
  subst hx
  constructor
  · bv_omega
  · intro h
    bv_omega

/-- `rdx` one word on, and the second loop's test `cmp rsi, rdx`: not the end means another word. -/
theorem step80 {r : BitVec 64} {b j : Nat} (hb : b + 12288 < 2 ^ 64) (hr : r.toNat = b + 4 * j) (hj : j < 2816) :
    (r + 4#64).toNat = b + 4 * (j + 1) ∧ (¬ BitVec.ofNat 64 b + 11264#64 = r + 4#64 → j + 1 < 2816) := by
  have e : (r + 4#64).toNat = b + 4 * (j + 1) := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨e, fun h => Nat.lt_of_le_of_ne (by omega) fun e' => h ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [e]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The second loop's store goes to `[rdx + 1020]` after `rdx` is one word on: 1024 bytes past the load. -/
theorem toNat_1020 {x : BitVec 64} (h : x.toNat + 1024 < 2 ^ 64) : (x + 4#64 + 1020#64).toNat = x.toNat + 1024 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The second loop starts at word 0. -/
theorem toNat_b0 {b : Nat} (hb : b + 12288 < 2 ^ 64) : (BitVec.ofNat 64 b).toNat = b + 4 * 0 := by
  simp only [BitVec.toNat_ofNat]
  omega

/-- From the entry to the first loop's head: `rdi` the table, `rsi` 0. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post)
    (hQ : ∀ g' f' V', Inv g V 16 5377 g' f' V' → Q 16 g' f' V') : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  intros
  apply hQ
  exact Or.inr (Or.inl ⟨0, by decide, by simp, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl,
    Or.inl ⟨rfl, rfl⟩⟩)

/-- From the first loop's head to the inner one's: `rdx` 8. -/
theorem vc_16 {k : Nat} {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.rsi.toNat = k) (hK : Kp g₀ g)
    (Q : Post)
    (hQ : ∀ g' f', g'.rsi.toNat = k → g'.rdi = g.rdi → Kp g₀ g' → g'.rdx.toNat = 8 → Q 32 g' f' V) :
    W_16 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hQ
  wpx [W_16, o1]
  intros
  exact hQ _ _ hs rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) (by simp)

/-- One inner step of the first loop, for the table at a variable `b`: back to the inner head with `rdx` one less;
or, after the eighth, the word stored at `b + 4·rsi` and on to the next word, or to the second loop after the last. -/
theorem vc_32 {b k : Nat} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hb : b + 12288 < 2 ^ 64)
    (hw : ∀ i < 12288, Foot Wl (Addr.add (BitVec.ofNat 64 b) i)) (hk : k < 256) (hs : g.rsi.toNat = k)
    (hdi : g.rdi = BitVec.ofNat 64 b) (hK : Kp g₀ g) (hO : Raf.Out b (b + 12288) V₀ V)
    (hc1 : 1 ≤ g.rdx.toNat) (hc8 : g.rdx.toNat ≤ 8) (Q : Post)
    (hQ1 : ∀ g' f', g'.rsi.toNat = k → g'.rdi = BitVec.ofNat 64 b → Kp g₀ g' →
      g'.rdx.toNat + 1 = g.rdx.toNat → 1 ≤ g'.rdx.toNat → Q 32 g' f' V)
    (hQ2 : ∀ g' f' V', k + 1 < 256 → g'.rsi.toNat = k + 1 → g'.rdi = BitVec.ofNat 64 b → Kp g₀ g' →
      Raf.Out b (b + 12288) V₀ V' → Q 16 g' f' V')
    (hQ3 : ∀ g' f' V', g'.rdx.toNat = b + 4 * 0 → g'.rdi = BitVec.ofNat 64 b →
      g'.rsi = BitVec.ofNat 64 b + 11264#64 → Kp g₀ g' → Raf.Out b (b + 12288) V₀ V' → Q 80 g' f' V') :
    W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hdi hc1 hc8 hQ1
  subst hdi
  wpx -implicitDefEqProofs [W_32, W_53, W_69, o2, o3, o4]
  intros
  have hi := inc_k hs hk
  refine ⟨fun h => ?_, fun _ => ⟨ft_b4 hw hb (by omega), fun h => ?_, fun _ => ?_⟩⟩
  · have hne : ¬ rdx.setWidth 32 = 1#32 := by simpa using h
    have hd := dec32 hc1 hc8 hne
    exact hQ1 _ _ hs rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) hd.1 hd.2
  · have hne : ¬ rsi + 1#64 = 256#64 := by simpa using h
    exact hQ2 _ _ _ (hi.2 hne) hi.1 rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_b4 hO hb (by omega) (toBytesLE_length _ _))
  · exact hQ3 _ _ _ (toNat_b0 hb) rfl rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_b4 hO hb (by omega) (toBytesLE_length _ _))

/-- One round of the second loop, for the tables at a variable `b`: the word at `rdx` and the word of the first
table its low byte picks loaded, a word stored 1024 bytes past `rdx`, then back to the head with `rdx` one word on,
or on to the `ret` after the last. -/
theorem vc_80 {b j : Nat} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hb : b + 12288 < 2 ^ 64)
    (hw : ∀ i < 12288, Foot Wl (Addr.add (BitVec.ofNat 64 b) i))
    (hd : ∀ i < 12288, Foot F.data (Addr.add (BitVec.ofNat 64 b) i)) (hj : j < 2816) (hdx : g.rdx.toNat = b + 4 * j)
    (hdi : g.rdi = BitVec.ofNat 64 b) (hsi : g.rsi = BitVec.ofNat 64 b + 11264#64) (hK : Kp g₀ g)
    (hO : Raf.Out b (b + 12288) V₀ V) (Q : Post)
    (hQ1 : ∀ g' f' V', j + 1 < 2816 → g'.rdx.toNat = b + 4 * (j + 1) → g'.rdi = BitVec.ofNat 64 b →
      g'.rsi = BitVec.ofNat 64 b + 11264#64 → Kp g₀ g' → Raf.Out b (b + 12288) V₀ V' → Q 80 g' f' V')
    (hQ2 : ∀ g' f' V', Kp g₀ g' → Raf.Out b (b + 12288) V₀ V' → Q 106 g' f' V') : W_80 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdx hdi hsi
  subst hdi hsi
  have h4 := step80 hb hdx hj
  have ha : (rdx + 4#64 + 1020#64).toNat = rdx.toNat + 1024 := toNat_1020 (by omega)
  wpx -implicitDefEqProofs [W_80, o5, Op.xorm, Op.zxr]
  intros
  refine ⟨ft_at hd (by omega) (by omega) (by omega), ?_⟩
  intros
  refine ⟨ft_b4 hd hb (by simp only [BitVec.toNat_setWidth, Nat.reducePow]; omega), ?_⟩
  intros
  refine ⟨ft_at hw (by omega) (by omega) (by omega), fun h => ?_, fun _ => ?_⟩
  · have hne : ¬ BitVec.ofNat 64 b + 11264#64 = rdx + 4#64 := by simpa using h
    exact hQ1 _ _ _ (h4.2 hne) h4.1 rfl rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))
  · exact hQ2 _ _ _ (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the tables as at the entry. -/
theorem vc (hw : ∀ i < 12288, Foot Wl (Addr.add 8015360#64 i)) (hd : ∀ i < 12288, Foot F.data (Addr.add 8015360#64 i))
    (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = 106 ∧ Kp g₀ g' ∧ Out V₀ V'))
      g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨k, hk, hs, hdi, hK, hO, ⟨rfl, rfl⟩ | ⟨rfl, hc1, hc8, rfl⟩⟩ |
    ⟨rfl, j, hj, hdx, hdi, hsi, hK, hO, rfl⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    exact vc_0 _ fun g' f' V' h => Or.inl ⟨5377, by decide, h⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_16 hs hK
    intro g' f' h1 h2 h3 h4
    exact Or.inl ⟨2817 + 10 * (256 - k) - 9 + g'.rdx.toNat, by omega,
      Or.inr (Or.inl ⟨k, hk, h1, h2.trans hdi, h3, hO, Or.inr ⟨rfl, by omega, by omega, rfl⟩⟩)⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_32 (b := 8015360) (by decide) hw hk hs hdi hK hO hc1 hc8
    · intro g' f' e1 e2 e3 e4 e5
      exact Or.inl ⟨2817 + 10 * (256 - k) - 9 + g'.rdx.toNat, by omega,
        Or.inr (Or.inl ⟨k, hk, e1, e2, e3, hO, Or.inr ⟨rfl, e5, by omega, rfl⟩⟩)⟩
    · intro g' f' V' e1 e2 e3 e4 e5
      exact Or.inl ⟨2817 + 10 * (256 - (k + 1)), by omega,
        Or.inr (Or.inl ⟨k + 1, e1, e2, e3, e4, e5, Or.inl ⟨rfl, rfl⟩⟩)⟩
    · intro g' f' V' e1 e2 e3 e4 e5
      exact Or.inl ⟨2816, by omega, Or.inr (Or.inr ⟨rfl, 0, by decide, e1, e2, e3, e4, e5, rfl⟩)⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_80 (b := 8015360) (by decide) hw hd hj hdx hdi hsi hK hO
    · intro g' f' V' e1 e2 e3 e4 e5 e6
      exact Or.inl ⟨2816 - (j + 1), by omega, Or.inr (Or.inr ⟨rfl, j + 1, e1, e2, e3, e4, e5, e6, rfl⟩)⟩
    · intro g' f' V' e1 e2
      exact Or.inr ⟨rfl, e1, e2⟩

/-- `Out` says the bytes outside `wr3` are as before. -/
theorem out_wr {V V' : Addr → Byte} (h : Out V V') : ∀ a : Addr, ¬ InR wr3 a.toNat → V' a = V a := fun a ha =>
  h a fun h' => ha (by simp only [wr3, InR, or_false]; omega)

/-- The `ret` at offset 106 of `c3`. -/
def r106 : List Byte := [0xc3]
theorem r106_0 : ∀ feat, Dec feat r106 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v106 : r106 <+: c3.drop 106 := by decide +kernel

/-- `csuTg 3`, at offset 0 of `sti`: `endbr64; jmp c3_at`. -/
def cs0 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x97, 0x14, 0x00, 0x00]
theorem cs0_0 : ∀ feat, Dec feat cs0 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem cs0_4 : ∀ feat, Dec feat cs0 4 (FV7z.mk .jmp 64 [.rel 5271] 5) := by dec_rfl
theorem vs0 : cs0 <+: sti.drop 0 := by decide +kernel
theorem tg3 : csuTg 3 = sti_at.add 0 := by decide +kernel
theorem calls3 : calls 3 = [] := by decide +kernel
theorem wrT3 : ∀ x ∈ wr3, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- The function at `c3_at` is one as `Csu.csu_ok` asks, for an invariant that goes from `3` to `4` through
`Out`. -/
theorem runsF {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hinE : CodeIn L c3_at c3)
    (hw : ∀ i < 12288, Foot Wl (Addr.add 8015360#64 i)) (hsp : 8027648 + 64 ≤ sp.toNat)
    (hJ : ∀ V V', J 3 V → Out V V' → J 4 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 3 c3_at :=
  cfg_runs (j := 0) c hC hinE (addr_add_zero _).symm (spAll prof)
    (Dec.shift (j := 106) (k := 0) (r106_0 _) v106 (by decide)) (lt_len (by decide)) Out Inv
    (fun _ _ _ => ⟨5378, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩) (vc hw fun i hi => c.hws _ (hw i hi))
    (fun _ _ h a ha => h a (by omega)) hJ

/-- `csuTg 3` is a function as `Csu.csu_ok` asks, for an invariant that goes from `3` to `4` through `Out`. -/
theorem runs3 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hinE : CodeIn L c3_at c3) (hw : ∀ i < 12288, Foot Wl (Addr.add 8015360#64 i)) (hsp : 8027648 + 64 ≤ sp.toNat)
    (hJ : ∀ V V', J 3 V → Out V V' → J 4 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 3 (csuTg 3) :=
  jmp_runs (j := 0) (rel := 5271) c hin hinE (by decide) tg3
    (Dec.shift (j := 0) (k := 0) (cs0_0 _) vs0 (by decide))
    (Dec.shift (j := 0) (k := 4) (cs0_4 _) vs0 (by decide))
    (sti_lt (by decide)) (by decide) (runsF c hC hinE hw hsp hJ)

/-- `csuTg 3` for `Jg`, its spec `wrSpec wr3`. -/
theorem runs3_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hinE : CodeIn L c3_at c3) (hw : ∀ i < 12288, Foot Wl (Addr.add 8015360#64 i))
    (hsp : 8027648 + 64 ≤ sp.toNat) (hspec : spec 3 = wrSpec wr3) (hD : ∀ k, (spec k).Dep)
    (hXw : ∀ k, 3 ≤ k → k < 3 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr3, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W', G 3 W → Out W W' → G 4 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 3 (csuTg 3) :=
  runs3 c hC hin hinE hw hsp fun W W' hJ hO =>
    jg_wr (by decide) calls3 hspec hD wrT3 hXw (out_wr hO) (hG W W' · hO) hJ

end FV7z.C3
