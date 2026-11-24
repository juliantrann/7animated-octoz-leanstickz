import FV7z.C70.Cuts
import FV7z.Ctor.StSpec
import FV7z.Ctor.Loop
/-!
# `csuTg 70`: a CRC-16 table (PLAN.md §M, constructors)

`csuTg 70`, at offset 1440 of `sti`, fills the 512 bytes at `0x79d140` (`wr70`) with 256 words, the CRC-16 (the
polynomial `0x1021`) of each index, and returns. The outer loop walks `rsi` through the table two bytes at a time, up
to `r8`; the inner loop takes eight steps for each word, `rcx` the count left. No later code takes those bytes as an
address, so its spec says only where they lie (`wrSpec wr70`).

- `Inv`: the invariant at the three cut points (`Cuts.lean`): the entry; the outer loop's head with `rsi` at word `k`
  of the table; the inner loop's head, the same and `rcx` from 1 to 8. The measure falls by one in each inner step and
  by at least two from the inner loop's last step to the next word.
- `dec32`, `step2`: the inner count one less; `rsi` one word on, the outer loop's test.
- `vc_1440`, `vc_1464`, `vc_1472`, `vc`: the code from each cut point keeps it with a smaller measure, or reaches the
  `ret`. `vc_1464` and `vc_1472` are for the table at a variable `b`.
- `runs70`: `csuTg 70` is a function as `Csu.csu_ok` asks (`cfg_runs`), for an invariant that goes from `70` to `71`
  through `Out`; `runs70_jg`: for `Jg` (`jg_wr`).
-/
namespace FV7z.C70
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Ctor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The table. -/
def wr70 : List (Nat × Nat) := [(7983424, 7983936)]

/-- The bytes outside the table as before. -/
abbrev Out (V V' : Addr → Byte) : Prop := Raf.Out 7983424 (7983424 + 512) V V'

/-- The invariant at the cut points, from the registers `g₀` and bytes `V₀` at the entry. -/
def Inv (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat) (g : Gprs) (_ : Rflags) (V : Addr → Byte) : Prop :=
  (ℓ = 1440 ∧ n = 2561 ∧ g = g₀ ∧ V = V₀) ∨
  ∃ k < 256, g.rsi.toNat = 7983424 + 2 * k ∧ g.r8 = BitVec.ofNat 64 (7983424 + 512) ∧ Kp g₀ g ∧ Out V₀ V ∧
    ((ℓ = 1464 ∧ n = 10 * (256 - k)) ∨
      (ℓ = 1472 ∧ 1 ≤ g.rcx.toNat ∧ g.rcx.toNat ≤ 8 ∧ n = 10 * (256 - k) - 9 + g.rcx.toNat))

/-- The inner count one less (`sub ecx, 1`), when it was not 1. -/
theorem dec32 {x : BitVec 64} (h1 : 1 ≤ x.toNat) (h8 : x.toNat ≤ 8) (hne : ¬ x.setWidth 32 = 1#32) :
    ((x.setWidth 32 - 1#32).setWidth 64).toNat + 1 = x.toNat ∧ 1 ≤ ((x.setWidth 32 - 1#32).setWidth 64).toNat := by
  bv_omega

/-- `rsi` one word on, and the outer loop's test `cmp r8, rsi`: not the end means another word. -/
theorem step2 {r s : BitVec 64} {b k : Nat} (hb : b + 512 < 2 ^ 64) (hr : r = BitVec.ofNat 64 (b + 512))
    (hs : s.toNat = b + 2 * k) (hk : k < 256) :
    (s + 2#64).toNat = b + 2 * (k + 1) ∧ (¬ r = s + 2#64 → k + 1 < 256) := by
  subst hr
  refine ⟨?_, fun h => Nat.lt_of_le_of_ne (by omega) fun e => h ?_⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

/-- From the entry to the outer loop's head: `rsi` the table, `r8` its end. -/
theorem vc_1440 {g : Gprs} {f : Rflags} {V : Addr → Byte} (Q : Post)
    (hQ : ∀ g' f' V', Inv g V 1464 2560 g' f' V' → Q 1464 g' f' V') : W_1440 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_1440, o0]
  intros
  apply hQ
  exact Or.inr ⟨0, by decide, by simp, by simp, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ _ => rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- From the outer loop's head to the inner one's: `rcx` 8. -/
theorem vc_1464 {b k : Nat} {g₀ g : Gprs} {f : Rflags} {V : Addr → Byte} (hs : g.rsi.toNat = b + 2 * k)
    (hK : Kp g₀ g) (Q : Post)
    (hQ : ∀ g' f', g'.rsi.toNat = b + 2 * k → g'.r8 = g.r8 → Kp g₀ g' → g'.rcx.toNat = 8 → Q 1472 g' f' V) :
    W_1464 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hQ
  wpx [W_1464, o1]
  intros
  exact hQ _ _ hs rfl (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) (by simp)

/-- One inner step, for the table at a variable `b`: back to the inner head with `rcx` one less; or, after the
eighth, the word stored at `rsi` and on to the next word, or to the `ret` after the last. -/
theorem vc_1472 {b k : Nat} {g₀ g : Gprs} {f : Rflags} {V₀ V : Addr → Byte} (hb : b + 512 < 2 ^ 64)
    (hw : ∀ i < 512, Foot Wl (Addr.add (BitVec.ofNat 64 b) i)) (hk : k < 256) (hs : g.rsi.toNat = b + 2 * k)
    (hr8 : g.r8 = BitVec.ofNat 64 (b + 512)) (hK : Kp g₀ g) (hO : Raf.Out b (b + 512) V₀ V)
    (hc1 : 1 ≤ g.rcx.toNat) (hc8 : g.rcx.toNat ≤ 8) (Q : Post)
    (hQ1 : ∀ g' f', g'.rsi.toNat = b + 2 * k → g'.r8 = BitVec.ofNat 64 (b + 512) → Kp g₀ g' →
      g'.rcx.toNat + 1 = g.rcx.toNat → 1 ≤ g'.rcx.toNat → Q 1472 g' f' V)
    (hQ2 : ∀ g' f' V', k + 1 < 256 → g'.rsi.toNat = b + 2 * (k + 1) → g'.r8 = BitVec.ofNat 64 (b + 512) →
      Kp g₀ g' → Raf.Out b (b + 512) V₀ V' → Q 1464 g' f' V')
    (hQ3 : ∀ g' f' V', Kp g₀ g' → Raf.Out b (b + 512) V₀ V' → Q 1514 g' f' V') : W_1472 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hr8 hc1 hc8 hQ1
  wpx -implicitDefEqProofs [W_1472, W_1496, o2, o3, Op.zxr16]
  intros
  have h2 := step2 hb hr8 hs hk
  refine ⟨fun h => ?_, fun _ => ⟨ft_at hw (by omega) (by omega) (by omega), fun h => ?_, fun _ => ?_⟩⟩
  · have hne : ¬ rcx.setWidth 32 = 1#32 := by simpa using h
    have hd := dec32 hc1 hc8 hne
    exact hQ1 _ _ hs hr8 (Kp.of hK rfl rfl rfl rfl rfl rfl rfl) hd.1 hd.2
  · have hne : ¬ r8 = rsi + 2#64 := by simpa using h
    exact hQ2 _ _ _ (h2.2 hne) h2.1 hr8 (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))
  · exact hQ3 _ _ _ (Kp.of hK rfl rfl rfl rfl rfl rfl rfl)
      (out_at hO (toBytesLE_length _ _) (by omega) (by omega) (by omega))

/-- The code from each cut point keeps the invariant with a smaller measure, or reaches the `ret` with the registers
a call keeps and the bytes outside the table as at the entry. -/
theorem vc (hw : ∀ i < 512, Foot Wl (Addr.add 7983424#64 i)) (g₀ : Gprs) (V₀ : Addr → Byte) (ℓ n : Nat)
    (g : Gprs) (f : Rflags) (V : Addr → Byte) (h : Inv g₀ V₀ ℓ n g f V) :
    Wt ℓ F Wl (fun j' g' f' V' => (∃ n' < n, Inv g₀ V₀ j' n' g' f' V') ∨ (j' = 1514 ∧ Kp g₀ g' ∧ Out V₀ V'))
      g f V := by
  rcases h with ⟨rfl, rfl, rfl, rfl⟩ | ⟨k, hk, hs, hr8, hK, hO, ⟨rfl, rfl⟩ | ⟨rfl, hc1, hc8, rfl⟩⟩
  · simp only [Wt, ↓reduceIte]
    exact vc_1440 _ fun g' f' V' h => Or.inl ⟨2560, by decide, h⟩
  · simp only [Wt, ↓reduceIte]
    exact vc_1464 hs hK _ fun g' f' h1 h2 h3 h4 => Or.inl ⟨10 * (256 - k) - 9 + g'.rcx.toNat, by omega,
      Or.inr ⟨k, hk, h1, h2.trans hr8, h3, hO, Or.inr ⟨rfl, by omega, by omega, rfl⟩⟩⟩
  · simp only [Wt, ↓reduceIte]
    exact vc_1472 (b := 7983424) (by decide) hw hk hs hr8 hK hO hc1 hc8 _
      (fun g' f' e1 e2 e3 e4 e5 => Or.inl ⟨10 * (256 - k) - 9 + g'.rcx.toNat, by omega,
        Or.inr ⟨k, hk, e1, e2, e3, hO, Or.inr ⟨rfl, e5, by omega, rfl⟩⟩⟩)
      (fun g' f' V' e1 e2 e3 e4 e5 => Or.inl ⟨10 * (256 - (k + 1)), by omega,
        Or.inr ⟨k + 1, e1, e2, e3, e4, e5, Or.inl ⟨rfl, rfl⟩⟩⟩)
      fun g' f' V' e1 e2 => Or.inr ⟨rfl, e1, e2⟩

/-- `Out` says the bytes outside `wr70` are as before. -/
theorem out_wr {V V' : Addr → Byte} (h : Out V V') : ∀ a : Addr, ¬ InR wr70 a.toNat → V' a = V a := fun a ha =>
  h a fun h' => ha (by simp only [wr70, InR, or_false]; omega)

/-- The `ret` at offset 1514 of `sti`. -/
def r1514 : List Byte := [0xc3]
theorem r1514_0 : ∀ feat, Dec feat r1514 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem v1514 : r1514 <+: sti.drop 1514 := by decide +kernel
theorem tg70 : csuTg 70 = sti_at.add 1440 := by decide +kernel
theorem calls70 : calls 70 = [] := by decide +kernel
theorem wrT70 : ∀ x ∈ wr70, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide

/-- `csuTg 70` is a function as `Csu.csu_ok` asks, for an invariant that goes from `70` to `71` through `Out`. -/
theorem runs70 {J : Nat → (Addr → Byte) → Prop} {sp : Addr} {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg) (hin : CodeIn L sti_at sti)
    (hw : ∀ i < 512, Foot Wl (Addr.add 7983424#64 i)) (hsp : 7983936 + 64 ≤ sp.toNat)
    (hJ : ∀ V V', J 70 V → Out V V' → J 71 V') :
    Csu.Runs prof F Wl L s₀ o gev gP gE J sp a₀ a₁ a₂ 70 (csuTg 70) :=
  cfg_runs c hC hin tg70 (spAll prof) (Dec.shift (j := 1514) (k := 0) (r1514_0 _) v1514 (by decide))
    (lt_len (by decide)) Out Inv (fun _ _ _ => ⟨2561, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩) (vc hw)
    (fun _ _ h a ha => h a (by omega)) hJ

/-- `csuTg 70` for `Jg`, its spec `wrSpec wr70`. -/
theorem runs70_jg {V : Addr → Byte} {spec : Nat → CSpec} {G : Nat → (Addr → Byte) → Prop} {sp : Addr}
    {tg : Nat → Addr} {a₀ a₁ a₂ : BitVec 64} (c : Seg prof F Wl L s₀ o) (hC : Csu.Env F Wl L sp tg)
    (hin : CodeIn L sti_at sti) (hw : ∀ i < 512, Foot Wl (Addr.add 7983424#64 i)) (hsp : 7983936 + 64 ≤ sp.toNat)
    (hspec : spec 70 = wrSpec wr70) (hD : ∀ k, (spec k).Dep)
    (hXw : ∀ k, 3 ≤ k → k < 70 → ∀ x ∈ (spec k).wr, ∀ y ∈ wr70, x.2 ≤ y.1 ∨ y.2 ≤ x.1)
    (hG : ∀ W W', G 70 W → Out W W' → G 71 W') :
    Csu.Runs prof F Wl L s₀ o gev gP gE (Jg V sp.toNat spec G) sp a₀ a₁ a₂ 70 (csuTg 70) :=
  runs70 c hC hin hw hsp fun W W' hJ hO => jg_wr (by decide) calls70 hspec hD wrT70 hXw (out_wr hO) (hG W W' · hO) hJ

end FV7z.C70
