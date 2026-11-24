import FV7z.C15.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
/-!
# `csuTg 15`: the CRC-64 tables of 7-Zip (PLAN.md §M, constructors)

`csuTg 15`, at offset 224 of `sti`, is `endbr64; jmp c15_at`. The function there (`Crc64GenerateTable`) fills the
24576 bytes at `0x7967c0` (`wr15`) and returns, in two loops, as `C3` does with quadwords:

- the first takes `rdi` through the 256 quadwords of the first table, with an inner loop of eight steps for each,
  `rdx` the count left, and stores the quadword at `r8 + 8·rdi`;
- the second takes `rdx` through the quadwords of the table from the first on, loads the quadword at `rdx` and the
  quadword of the first table its low byte picks, and stores at `rdx + 2048`, up to `rsi = r8 + 22528`.

No later code takes those bytes as an address, so its spec says only where they lie (`wrSpec wr15`).

- `Inv`: the invariant at the four cut points (`Cuts.lean`), the measure as in `C3.Inv`.
- `step112`, `toNat_2040`: the loops' arithmetic (and `Ctor.inc_k`).
- `vc_0`, `vc_32`, `vc_48`, `vc_112`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches
  the `ret`. `vc_48` and `vc_112` are for the table at a variable `b`.
- `runsF`, `runs15`, `runs15_jg`: as `C3.runsF`, `C3.runs3`, `C3.runs3_jg`.
-/
namespace FV7z.C15
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The tables. -/
def wr15 : List (Nat × Nat) := [(7956416, 7980992)]

/-- The bytes outside the tables as before. -/
abbrev Out (V V' : Addr → Byte) : Prop := Raf.Out 7956416 (7956416 + 24576) V V'

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 0 ∧ n = 5378 ∧ g = g₀ ∧ V = V₀) ∨
  (∃ k < 256, g.rdi.toNat = k ∧ g.r8 = BitVec.ofNat 64 7956416 ∧ Kp g₀ g ∧ Out V₀ V ∧
    ((ℓ = 32 ∧ n = 2817 + 10 * (256 - k)) ∨
      (ℓ = 48 ∧ 1 ≤ g.rdx.toNat ∧ g.rdx.toNat ≤ 8 ∧ n = 2817 + 10 * (256 - k) - 9 + g.rdx.toNat))) ∨
  (ℓ = 112 ∧ ∃ j < 2816, g.rdx.toNat = 7956416 + 8 * j ∧ g.r8 = BitVec.ofNat 64 7956416 ∧
    g.rsi = 7978944#64 ∧ Kp g₀ g ∧ Out V₀ V ∧ n = 2816 - j)

/-- `rdx` one quadword on, and the second loop's test `cmp rsi, rdx`: not the end means another quadword. -/
theorem step112 {r : BitVec 64} {b j : Nat} (hb : b + 24576 < 2 ^ 64) (hr : r.toNat = b + 8 * j) (hj : j < 2816) :
    (r + 8#64).toNat = b + 8 * (j + 1) ∧ (¬ BitVec.ofNat 64 (b + 22528) = r + 8#64 → j + 1 < 2816) := by
  have e : (r + 8#64).toNat = b + 8 * (j + 1) := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨e, fun h => Nat.lt_of_le_of_ne (by omega) fun e' => h ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [e]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The second loop's store goes to `[rdx + 2040]` after `rdx` is one quadword on: 2048 bytes past the load. -/
theorem toNat_2040 {x : BitVec 64} (h : x.toNat + 2048 < 2 ^ 64) : (x + 8#64 + 2040#64).toNat = x.toNat + 2048 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- From the entry to the first loop's head: `r8` the table, `rdi` 0. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post)
    (hQ : ∀ g' f' V', Inv g V 32 5377 g' f' V' → Q 32 g' f' V') : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_0, o0]
  intros
  apply hQ
  exact Or.inr (Or.inl ⟨0, by decide, by simp, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl,
    Or.inl ⟨rfl, rfl⟩⟩)

/-- From the first loop's head to the inner one's: `rdx` 8. -/
theorem vc_32 {k : Nat} {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.rdi.toNat = k) (hK : Kp g₀ g)
    (Q : Post)
    (hQ : ∀ g' f', g'.rdi.toNat = k → g'.r8 = g.r8 → Kp g₀ g' → g'.rdx.toNat = 8 → Q 48 g' f' V) :
    W_32 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hQ
  wpx [W_32, o1]
  intros
  exact hQ _ _ hs rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) (by simp)

/-- One inner step of the first loop, for the table at a variable `b`: back to the inner head with `rdx` one less;
or, after the eighth, the quadword stored at `b + 8·rdi` and on to the next, or to the second loop after the last. -/
theorem vc_48 {b k : Nat} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hb : b + 24576 < 2 ^ 64)
    (hw : ∀ i < 24576, Foot Wl (Addr.add (BitVec.ofNat 64 b) i)) (hk : k < 256) (hs : g.rdi.toNat = k)
    (hr8 : g.r8 = BitVec.ofNat 64 b) (hK : Kp g₀ g) (hO : Raf.Out b (b + 24576) V₀ V)
    (hc1 : 1 ≤ g.rdx.toNat) (hc8 : g.rdx.toNat ≤ 8) (Q : Post)
    (hQ1 : ∀ g' f', g'.rdi.toNat = k → g'.r8 = BitVec.ofNat 64 b → Kp g₀ g' →
      g'.rdx.toNat + 1 = g.rdx.toNat → 1 ≤ g'.rdx.toNat → Q 48 g' f' V)
    (hQ2 : ∀ g' f' V', k + 1 < 256 → g'.rdi.toNat = k + 1 → g'.r8 = BitVec.ofNat 64 b → Kp g₀ g' →
      Raf.Out b (b + 24576) V₀ V' → Q 32 g' f' V')
    (hQ3 : ∀ g' f' V', g'.rdx = 7956416#64 → g'.rsi = 7978944#64 → g'.r8 = BitVec.ofNat 64 b → Kp g₀ g' →
      Raf.Out b (b + 24576) V₀ V' → Q 112 g' f' V') :
    W_48 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hr8 hc1 hc8 hQ1
  subst hr8
  wpx -implicitDefEqProofs [W_48, W_71, W_88, o2, o3, o4, Op.shr64]
  intros
  have hi := inc_k hs hk
  refine ⟨fun h => ?_, fun _ => ⟨ft_b8 hw hb (by omega), fun h => ?_, fun _ => ?_⟩⟩
  · have hne : ¬ rdx.setWidth 32 = 1#32 := by simpa using h
    have hd := dec32 hc1 hc8 hne
    exact hQ1 _ _ hs rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) hd.1 hd.2
  · have hne : ¬ rdi + 1#64 = 256#64 := by simpa using h
    exact hQ2 _ _ _ (hi.2 hne) hi.1 rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_b8 hO hb (by omega) (toBytesLE_length _ _))
  · exact hQ3 _ _ _ rfl rfl rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_b8 hO hb (by omega) (toBytesLE_length _ _))

/-- One round of the second loop, for the tables at a variable `b`: the quadword at `rdx` and the quadword of the
first table its low byte picks loaded, a quadword stored 2048 bytes past `rdx`, then back to the head with `rdx` one
quadword on, or on to the `ret` after the last. -/
theorem vc_112 {b j : Nat} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hb : b + 24576 < 2 ^ 64)
    (hw : ∀ i < 24576, Foot Wl (Addr.add (BitVec.ofNat 64 b) i))
    (hd : ∀ i < 24576, Foot F.data (Addr.add (BitVec.ofNat 64 b) i)) (hj : j < 2816) (hdx : g.rdx.toNat = b + 8 * j)
    (hr8 : g.r8 = BitVec.ofNat 64 b) (hsi : g.rsi = BitVec.ofNat 64 (b + 22528)) (hK : Kp g₀ g)
    (hO : Raf.Out b (b + 24576) V₀ V) (Q : Post)
    (hQ1 : ∀ g' f' V', j + 1 < 2816 → g'.rdx.toNat = b + 8 * (j + 1) → g'.r8 = BitVec.ofNat 64 b →
      g'.rsi = BitVec.ofNat 64 (b + 22528) → Kp g₀ g' → Raf.Out b (b + 24576) V₀ V' → Q 112 g' f' V')
    (hQ2 : ∀ g' f' V', Kp g₀ g' → Raf.Out b (b + 24576) V₀ V' → Q 142 g' f' V') : W_112 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdx hr8 hsi
  subst hr8 hsi
  have h8 := step112 hb hdx hj
  have ha : (rdx + 8#64 + 2040#64).toNat = rdx.toNat + 2048 := toNat_2040 (by omega)
  wpx -implicitDefEqProofs [W_112, o5, Op.xorm, Op.zxr, Op.shr64]
  intros
  refine ⟨ft_at hd (by omega) (by omega) (by omega), ?_⟩
  intros
  refine ⟨ft_b8 hd hb (by simp only [BitVec.toNat_setWidth, Nat.reducePow]; omega), ?_⟩
  intros
  refine ⟨ft_at hw (by omega) (by omega) (by omega), fun h => ?_, fun _ => ?_⟩
  · have hne : ¬ BitVec.ofNat 64 (b + 22528) = rdx + 8#64 := by simpa using h
    exact hQ1 _ _ _ (h8.2 hne) h8.1 rfl rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))
  · exact hQ2 _ _ _ (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the tables as at the entry. -/
theorem vc (hw : ∀ i < 24576, Foot Wl (Addr.add 7956416#64 i)) (hd : ∀ i < 24576, Foot F.data (Addr.add 7956416#64 i))
    (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (f : Rflags) (V : Addr → Byte)
    (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = 142 ∧ Kp g₀ g' ∧ Out V₀ V'))
      g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨k, hk, hs, hr8, hK, hO, ⟨rfl, rfl⟩ | ⟨rfl, hc1, hc8, rfl⟩⟩ |
    ⟨rfl, j, hj, hdx, hr8, hsi, hK, hO, rfl⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    exact vc_0 _ fun g' f' V' h => Or.inl ⟨5377, by decide, h⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_32 hs hK
    intro g' f' h1 h2 h3 h4
    exact Or.inl ⟨2817 + 10 * (256 - k) - 9 + g'.rdx.toNat, by omega,
      Or.inr (Or.inl ⟨k, hk, h1, h2.trans hr8, h3, hO, Or.inr ⟨rfl, by omega, by omega, rfl⟩⟩)⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_48 (b := 7956416) (by decide) hw hk hs hr8 hK hO hc1 hc8
    · intro g' f' e1 e2 e3 e4 e5
      exact Or.inl ⟨2817 + 10 * (256 - k) - 9 + g'.rdx.toNat, by omega,
        Or.inr (Or.inl ⟨k, hk, e1, e2, e3, hO, Or.inr ⟨rfl, e5, by omega, rfl⟩⟩)⟩
    · intro g' f' V' e1 e2 e3 e4 e5
      exact Or.inl ⟨2817 + 10 * (256 - (k + 1)), by omega,
        Or.inr (Or.inl ⟨k + 1, e1, e2, e3, e4, e5, Or.inl ⟨rfl, rfl⟩⟩)⟩
    · intro g' f' V' e1 e2 e3 e4 e5
      have e0 : g'.rdx.toNat = 7956416 + 8 * 0 := by rw [e1]; rfl
      exact Or.inl ⟨2816, by omega, Or.inr (Or.inr ⟨rfl, 0, by decide, e0, e3, e2, e4, e5, rfl⟩)⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_112 (b := 7956416) (by decide) hw hd hj hdx hr8 hsi hK hO
    · intro g' f' V' e1 e2 e3 e4 e5 e6
      exact Or.inl ⟨2816 - (j + 1), by omega, Or.inr (Or.inr ⟨rfl, j + 1, e1, e2, e3, e4, e5, e6, rfl⟩)⟩
    · intro g' f' V' e1 e2
      exact Or.inr ⟨rfl, e1, e2⟩

/-- `Out` says the bytes outside `wr15` are as before. -/
theorem out_wr {V V' : Addr → Byte} (h : Out V V') : ∀ a : Addr, ¬ InR wr15 a.toNat → V' a = V a := fun a ha =>
  h a fun h' => ha (by simp only [wr15, InR, or_false]; omega)

/-- The `ret` at offset 142 of `c15`. -/
def r142 : List Byte := [0xc3]
theorem r142_0 : ∀ feat, Dec feat r142 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v142 : r142 <+: c15.drop 142 := by decide +kernel

/-- `csuTg 15`, at offset 224 of `sti`: `endbr64; jmp c15_at`. -/
def c224 : List Byte := [0xf3, 0x0f, 0x1e, 0xfa, 0xe9, 0x47, 0x7c, 0x02, 0x00]
theorem c224_0 : ∀ feat, Dec feat c224 0 (FV7z.mk .endbr64 32 [] 4) := by dec_rfl
theorem c224_4 : ∀ feat, Dec feat c224 4 (FV7z.mk .jmp 64 [.rel 162887] 5) := by dec_rfl
theorem v224 : c224 <+: sti.drop 224 := by decide +kernel
theorem tg15 : csuTg 15 = sti_at.add 224 := by decide +kernel
theorem calls15 : calls 15 = [] := by decide +kernel
theorem wrT15 : ∀ x ∈ wr15, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- The function at `c15_at` is one as `Csu.csu_ok` asks, for an invariant that goes from `15` to `16` through
`Out`. -/
theorem runsF {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hinE : CodeIn L c15_at c15)
    (hw : ∀ i < 24576, Foot Wl (Addr.add 7956416#64 i)) (hsp : 7980992 + 64 ≤ sp.toNat)
    (hJ : ∀ V V', J 15 V → Out V V' → J 16 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 15 c15_at :=
  cfg_runs (j := 0) c hC hinE (addr_add_zero _).symm (spAll prof)
    (Dec.shift (j := 142) (k := 0) (r142_0 _) v142 (by decide)) (lt_len (by decide)) Out Inv
    (fun _ _ _ => ⟨5378, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩) (vc hw fun i hi => c.hws _ (hw i hi))
    (fun _ _ h a ha => h a (by omega)) hJ

/-- `csuTg 15` is a function as `Csu.csu_ok` asks, for an invariant that goes from `15` to `16` through `Out`. -/
theorem runs15 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hinE : CodeIn L c15_at c15) (hw : ∀ i < 24576, Foot Wl (Addr.add 7956416#64 i))
    (hsp : 7980992 + 64 ≤ sp.toNat) (hJ : ∀ V V', J 15 V → Out V V' → J 16 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 15 (csuTg 15) :=
  jmp_runs (j := 224) (rel := 162887) c hin hinE (lt_len (by decide)) tg15
    (Dec.shift (j := 224) (k := 0) (c224_0 _) v224 (by decide))
    (Dec.shift (j := 224) (k := 4) (c224_4 _) v224 (by decide))
    (sti_lt (by decide)) (by decide) (runsF c hC hinE hw hsp hJ)

/-- `csuTg 15` for `Jg`, its spec `wrSpec wr15`. -/
theorem runs15_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hinE : CodeIn L c15_at c15) (hw : ∀ i < 24576, Foot Wl (Addr.add 7956416#64 i))
    (hsp : 7980992 + 64 ≤ sp.toNat) (hspec : spec 15 = wrSpec wr15) (hD : ∀ k, (spec k).Dep)
    (hXw : ∀ k, 3 ≤ k → k < 15 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr15, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W', G 15 W → Out W W' → G 16 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 15 (csuTg 15) :=
  runs15 c hC hin hinE hw hsp fun W W' hJ hO =>
    jg_wr (by decide) calls15 hspec hD wrT15 hXw (out_wr hO) (hG W W' · hO) hJ

end FV7z.C15
