import FV7z.C37.Cuts
import FV7z.Ctor.CfgReg
import FV7z.Ctor.Loop
/-!
# `csuTg 37`: a CRC-16 table, then RegisterArc (PLAN.md §M, constructors)

`csuTg 37`, at offset 576 of `sti`, fills the 512 bytes at `0x79cb40` (`wr37`) with 256 words, the CRC-16 (the
reflected polynomial `0xa001`) of each index, and then registers its handler: `mov rdi, 0x77a300; jmp RegisterArc`
(`tails`). The outer loop takes `rdx` through the 256 words and stores each at `rsi + 2·rdx`, `rsi` the table; the
inner loop takes eight steps for each word, `rcx` the count left. No later code takes the table's bytes as an
address, so its spec says only where they lie (`wrSpec wr37`).

- `Inv`: the invariant at the three cut points (`Cuts.lean`): the entry; the outer loop's head with `rdx = k`; the
  inner loop's head, the same and `rcx` from 1 to 8. The measure falls by one in each inner step and by at least two
  from the inner loop's last step to the next word.
- `vc_576`, `vc_592`, `vc_599`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches the
  `jmp` with `rdi` the handler's record. `vc_599` is for the table at a variable `b`.
- `runs37`: `csuTg 37` is a function as `Csu.csu_ok` asks (`cfg_reg_runs`), for an invariant that goes from `37` to
  `38` through `Out` and then `RegOut`; `runs37_jg`: for `Jg` (`jg_wreg`).
-/
namespace FV7z.C37
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The table. -/
def wr37 : List (Nat × Nat) := [(7981888, 7982400)]

/-- The bytes outside the table as before. -/
abbrev Out (V V' : Addr → Byte) : Prop := Raf.Out 7981888 (7981888 + 512) V V'

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 576 ∧ n = 2561 ∧ g = g₀ ∧ V = V₀) ∨
  ∃ k < 256, g.rdx.toNat = k ∧ g.rsi = BitVec.ofNat 64 7981888 ∧ Kp g₀ g ∧ Out V₀ V ∧
    ((ℓ = 592 ∧ n = 10 * (256 - k)) ∨
      (ℓ = 599 ∧ 1 ≤ g.rcx.toNat ∧ g.rcx.toNat ≤ 8 ∧ n = 10 * (256 - k) - 9 + g.rcx.toNat))

/-- From the entry to the outer loop's head: `rdx` 0, `rsi` the table. -/
theorem vc_576 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post)
    (hQ : ∀ g' f' V', Inv g V 592 2560 g' f' V' → Q 592 g' f' V') : W_576 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_576, o0]
  intros
  apply hQ
  exact Or.inr ⟨0, by decide, by simp, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- From the outer loop's head to the inner one's: `rcx` 8. -/
theorem vc_592 {k : Nat} {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} (hd : g.rdx.toNat = k) (hK : Kp g₀ g)
    (Q : Post)
    (hQ : ∀ g' f', g'.rdx.toNat = k → g'.rsi = g.rsi → Kp g₀ g' → g'.rcx.toNat = 8 → Q 599 g' f' V) :
    W_592 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd hQ
  wpx [W_592, o1]
  intros
  exact hQ _ _ hd rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) (by simp)

/-- One inner step, for the table at a variable `b`: back to the inner head with `rcx` one less; or, after the
eighth, the word stored at `b + 2·rdx` and on to the next word, or after the last to the `jmp` with `rdi` the
handler's record. -/
theorem vc_599 {b k : Nat} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hb : b + 512 < 2 ^ 64)
    (hw : ∀ i < 512, Foot Wl (Addr.add (BitVec.ofNat 64 b) i)) (hk : k < 256) (hd : g.rdx.toNat = k)
    (hsi : g.rsi = BitVec.ofNat 64 b) (hK : Kp g₀ g) (hO : Raf.Out b (b + 512) V₀ V)
    (hc1 : 1 ≤ g.rcx.toNat) (hc8 : g.rcx.toNat ≤ 8) (Q : Post)
    (hQ1 : ∀ g' f', g'.rdx.toNat = k → g'.rsi = BitVec.ofNat 64 b → Kp g₀ g' →
      g'.rcx.toNat + 1 = g.rcx.toNat → 1 ≤ g'.rcx.toNat → Q 599 g' f' V)
    (hQ2 : ∀ g' f' V', k + 1 < 256 → g'.rdx.toNat = k + 1 → g'.rsi = BitVec.ofNat 64 b → Kp g₀ g' →
      Raf.Out b (b + 512) V₀ V' → Q 592 g' f' V')
    (hQ3 : ∀ g' f' V', Kp g₀ g' → g'.rdi = BitVec.ofNat 64 7840512 → Raf.Out b (b + 512) V₀ V' →
      Q 644 g' f' V') : W_599 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd hsi hc1 hc8 hQ1
  subst hsi
  wpx -implicitDefEqProofs [W_599, W_620, W_637, o2, o3, o4, Op.zxr16]
  intros
  have hi := inc_k hd hk
  refine ⟨fun h => ?_, fun _ => ⟨ft_b2 hw hb (by omega), fun h => ?_, fun _ => ?_⟩⟩
  · have hne : ¬ rcx.setWidth 32 = 1#32 := by simpa using h
    have hc := dec32 hc1 hc8 hne
    exact hQ1 _ _ hd rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) hc.1 hc.2
  · have hne : ¬ rdx + 1#64 = 256#64 := by simpa using h
    exact hQ2 _ _ _ (hi.2 hne) hi.1 rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_b2 hO hb (by omega) (toBytesLE_length _ _))
  · exact hQ3 _ _ _ (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) rfl (out_b2 hO hb (by omega) (toBytesLE_length _ _))

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `jmp` with the registers
a call keeps, `rdi` the handler's record and the bytes outside the table as at the entry. -/
theorem vc (hw : ∀ i < 512, Foot Wl (Addr.add 7981888#64 i)) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat)
    (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨
      (j' = 644 ∧ Kp g₀ g' ∧ g'.rdi = BitVec.ofNat 64 7840512 ∧ Out V₀ V')) g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨k, hk, hd, hsi, hK, hO, ⟨rfl, rfl⟩ | ⟨rfl, hc1, hc8, rfl⟩⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    exact vc_576 _ fun g' f' V' h => Or.inl ⟨2560, by decide, h⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_592 hd hK
    intro g' f' h1 h2 h3 h4
    exact Or.inl ⟨10 * (256 - k) - 9 + g'.rcx.toNat, by omega,
      Or.inr ⟨k, hk, h1, h2.trans hsi, h3, hO, Or.inr ⟨rfl, by omega, by omega, rfl⟩⟩⟩
  · simp only [Wt, ↓reduceIte, Nat.reduceEqDiff]
    apply vc_599 (b := 7981888) (by decide) hw hk hd hsi hK hO hc1 hc8
    · intro g' f' e1 e2 e3 e4 e5
      exact Or.inl ⟨10 * (256 - k) - 9 + g'.rcx.toNat, by omega,
        Or.inr ⟨k, hk, e1, e2, e3, hO, Or.inr ⟨rfl, e5, by omega, rfl⟩⟩⟩
    · intro g' f' V' e1 e2 e3 e4 e5
      exact Or.inl ⟨10 * (256 - (k + 1)), by omega, Or.inr ⟨k + 1, e1, e2, e3, e4, e5, Or.inl ⟨rfl, rfl⟩⟩⟩
    · intro g' f' V' e1 e2 e3
      exact Or.inr ⟨rfl, e1, e2, e3⟩

/-- `Out` says the bytes outside `wr37` are as before. -/
theorem out_wr {V V' : Addr → Byte} (h : Out V V') : ∀ a : Addr, ¬ InR wr37 a.toNat → V' a = V a := fun a ha =>
  h a fun h' => ha (by simp only [wr37, InR, or_false]; omega)

/-- The `jmp RegisterArc` at offset 644 of `sti`. -/
def j644 : List Byte := [0xe9, 0x57, 0x27, 0x1b, 0x00]
theorem j644_0 : ∀ feat, Dec feat j644 0 (FV7z.mk .jmp 64 [.rel 1779543] 5) := by dec_rfl
theorem v644 : j644 <+: sti.drop 644 := by decide +kernel
theorem htgt37 : sti_at.add (644 + 5) + BitVec.ofNat 64 1779543 = (regAt 0).add 0 := by decide
theorem tg37 : csuTg 37 = sti_at.add 576 := by decide +kernel
theorem calls37 : calls 37 = [(0, 7840512)] := by decide +kernel
theorem wrT37 : ∀ x ∈ wr37, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- RegisterArc's table has room for the call. -/
theorem fits37 : Fits (regsAt 37) [(0, 7840512)] := by
  have h := fits_all 37 (by decide)
  rw [calls37] at h
  exact fits_of h

/-- `csuTg 37` is a function as `Csu.csu_ok` asks, for an invariant that goes from `37` to `38` through `Out` and
then `RegOut` of the handler's record, with RegisterArc's contract. -/
theorem runs37 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hw : ∀ i < 512, Foot Wl (Addr.add 7981888#64 i)) (hsp : 7991300 + 64 ≤ sp.toNat)
    (hR : RegSpec prof F Wl L s₀ o (regAt 0) (regCnt 0) (regTab 0) (regMax 0))
    (hinR : CodeIn L (regAt 0) (regCode 0))
    (hJ : ∀ V V' V'', J 37 V → Out V V' →
      RegOut (regCnt 0) (regTab 0) (regMax 0) (BitVec.ofNat 64 7840512) V' V'' → J 38 V'') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 37 (csuTg 37) :=
  cfg_reg_runs c hC hin tg37 (spAll prof) (Dec.shift (j := 644) (k := 0) (j644_0 _) v644 (by decide))
    (lt_len (by decide)) htgt37 hinR (reg_len 0) hR (reg_lay 0) (reg_arr 0)
    (.inr (by rw [show (regCnt 0).toNat = 7991296 from rfl]; omega)) Out Inv
    (fun _ _ _ => ⟨2561, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩) (vc hw) (fun _ _ h a ha => h a (by omega)) hJ

/-- `csuTg 37` for `Jg`, its spec `wrSpec wr37`. -/
theorem runs37_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hw : ∀ i < 512, Foot Wl (Addr.add 7981888#64 i)) (hsp : 7991300 + 64 ≤ sp.toNat)
    (hR : RegSpec prof F Wl L s₀ o (regAt 0) (regCnt 0) (regTab 0) (regMax 0))
    (hinR : CodeIn L (regAt 0) (regCode 0)) (hspec : spec 37 = wrSpec wr37) (hD : ∀ k, (spec k).Dep)
    (hT : ∀ k, ∀ x ∈ (spec k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hXw : ∀ k, 3 ≤ k → k < 37 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr37, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W' W'', G 37 W → Out W W' →
      RegOut (regCnt 0) (regTab 0) (regMax 0) (BitVec.ofNat 64 7840512) W' W'' → G 38 W'') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 37 (csuTg 37) :=
  runs37 c hC hin hw hsp hR hinR fun W W' W'' hJ hO hO' =>
    jg_wreg (by decide) calls37 fits37 hspec hD hT hXw (out_wr hO) hO' (hG W W' W'' · hO hO') hJ

end FV7z.C37
