import FV7z.Strrchr.Mid
import FV7z.Strlen.Loop
/-!
# `__strrchr_sse2`, the loop (PLAN.md G2)

From `+256`, no 0 among the 64 bytes from `p`, `rsi` their matches: `rcx = p`, or, none, `rsi = 1` and `rcx = 0`
(`+528`), so that `rcx + bsr rsi` is the last match so far or null (`ROk`). Then `rdi` the 64-aligned address after
`p` (`+268`), and from `+303` a 64-byte chunk at a time: its least byte compared with 0 (`eax`), its bytes with the
character (`rdx`). No 0: `rdx`, if not 0, replaces `rsi` and `rdi` replaces `rcx` (`+288`), and on to the next chunk.
A 0: its first, from the chunk's zero mask (`+430`); the matches before it, if any, replace `rsi` and `rcx`; `bsr`,
`lea rax, [rcx + rsi]`, `ret`.

The loop's invariant: `rdi = A`, 64-aligned, `p < A ≤ p + E < A + 64`, `E ≤ n`, `rsi ≠ 0` and `rcx + bsr rsi` the
last of the `E` bytes from `p` that is `ch`; by induction on `p + n - A`.
-/
namespace FV7z.Strrchr
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

attribute [-simp] BitVec.getLsbD_eq_getElem

theorem set_r9' (g : Gprs) (v : BitVec 64) : g.set (regOf 9) v = { g with r9 := v } := rfl
theorem set_r10' (g : Gprs) (v : BitVec 64) : g.set (regOf 10) v = { g with r10 := v } := rfl
theorem get9' (g : Gprs) : g.get (regOf 9) = g.r9 := rfl
theorem get10' (g : Gprs) : g.get (regOf 10) = g.r10 := rfl

/-! ## Masks and the last match -/

theorem R_full {f : Nat → Bool} {x : BitVec 64} (h : R 0 64 f x) (i : Nat) :
    x.getLsbD i = (decide (i < 64) && f i) := by
  rw [h i, decide_eq_true (Nat.zero_le i), Bool.true_and]

/-- The loop's zero mask, its four loads folded in its order, is 0 iff none of the chunk's bytes is. -/
theorem mask4r_eq_zero (V : Addr → Byte) (B : Addr) :
    pmsk (peqb (pminb (pminb (pminb (rd16 V (B + BitVec.ofNat 64 32)) (rd16 V (B + BitVec.ofNat 64 48)))
      (rd16 V (B + BitVec.ofNat 64 16))) (rd16 V (B + BitVec.ofNat 64 0))) 0) = 0 ↔
    ∀ k < 64, V (Addr.add B k) ≠ 0 := by
  have e : ∀ c j, Addr.add (B + BitVec.ofNat 64 c) j = Addr.add B (c + j) := fun c j => addr_add_add B c j
  rw [zmask4_eq_zero]
  constructor
  · intro h k hk
    have hj : k % 16 < 16 := Nat.mod_lt _ (by decide)
    obtain ⟨h2, h3, h1, h0⟩ := h (k % 16) hj
    rw [lane_rd16 _ _ hj, e] at h0 h1 h2 h3
    have : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3 := by omega
    rcases this with h' | h' | h' | h'
    · rwa [show k = 0 + k % 16 by omega]
    · rwa [show k = 16 + k % 16 by omega]
    · rwa [show k = 32 + k % 16 by omega]
    · rwa [show k = 48 + k % 16 by omega]
  · intro h j hj
    rw [lane_rd16 _ _ hj, lane_rd16 _ _ hj, lane_rd16 _ _ hj, lane_rd16 _ _ hj, e, e, e, e]
    exact ⟨h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)⟩

/-- No `ch` in `[E, E')`: the last of the `E` bytes is the last of the `E'`. -/
theorem rok_ext {V : Addr → Byte} {p : Addr} {E E' : Nat} {ch : Byte} {a : Addr} (h : ROk V p E ch a)
    (hle : E ≤ E') (hno : ∀ k, E ≤ k → k < E' → V (Addr.add p k) ≠ ch) : ROk V p E' ch a := by
  refine ⟨fun h' => h.1 fun k hk => h' k (by omega), fun m hm hc hl => ?_⟩
  by_cases hmE : m < E
  · exact h.2 m hmE hc fun k h1 h2 => hl k h1 (by omega)
  · exact absurd hc (hno m (by omega) hm)

/-- A mask, not 0, of the `m` bytes from `A = p + d` that are `ch`: `bsr` gives the last of the `d + m` from `p`. -/
theorem rok_new {V : Addr → Byte} {p A : Addr} {d m : Nat} {ch : Byte} {K : BitVec 64}
    (hd : p.toNat + d = A.toNat) (hm : m ≤ 64)
    (hK : ∀ i, K.getLsbD i = (decide (i < m) && decide (V (Addr.add A i) = ch))) (hK0 : K ≠ 0) :
    ROk V p (d + m) ch (Addr.add A (highestSetBit K)) := by
  have hS := rok_mask hm hK
  rcases Str.last_with (fun k => V (Addr.add A k) = ch) m with h | ⟨q, hq, hc, hl⟩
  · exact absurd (hS.1.2 h) hK0
  · have ha : Addr.add A (highestSetBit K) = Addr.add A q := (hS.2 hK0).2 q hq hc hl
    have e : Addr.add A q = Addr.add p (d + q) := addr_eq (by omega)
    rw [ha, e]
    refine rok_last (by omega) (by rw [← e]; exact hc) fun k h1 h2 => ?_
    rw [addr_eq (a := p) (b := A) (i := k) (j := k - d) (by omega)]
    exact hl (k - d) (by omega) (by omega)

/-- 16 bytes of a chunk. -/
theorem foot16a {F : Footprint} {C : Addr} (h : ∀ k < 64, Foot F.data (Addr.add C k)) {q : Nat}
    (hq : q + 16 ≤ 64) : ∀ i < 16, Foot F.data (Addr.add (C + BitVec.ofNat 64 q) i) := by
  intro i hi
  have := h (q + i) (by omega)
  rw [← addr_add_add] at this
  exact this

theorem hsb_one : highestSetBit (1 : BitVec 64) = 0 := by
  have h : ∀ i < 64, 0 < i → (1 : BitVec 64).getLsbD i = false := by decide
  exact highestSetBit_eq (by decide) (by decide) fun i h1 h2 => h i h2 h1

/-- `rdi`, `rsi`, `rcx` and the call's registers as in `X`. -/
abbrev Kc (g₀ X g : Gprs) : Prop := KpR g₀ g ∧ g.rdi = X.rdi ∧ g.rsi = X.rsi ∧ g.rcx = X.rcx

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-! ## A chunk -/

/-- The 64 bytes from `rdi = A`, 64-aligned, from `+303`: loaded into `xmm5`, `xmm4`, `xmm3`, `xmm2`, their least
compared with 0 (`eax`), each with the character (`rdx`); `je` to `+288` if no 0, else on to `+430`. -/
theorem body (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {A : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 303) (hdi : X.cpu.gpr.rdi = A)
    (hkp : KpR g₀ X.cpu.gpr) (hx1 : xsOf X.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi)
    (hx7 : xsOf X.cpu.vec.zmm (xmmOf 7) = 0) (hA64 : A.toNat % 64 = 0)
    (hft : ∀ k < 64, Foot F.data (Addr.add A k))
    (none : (∀ k < 64, V (Addr.add A k) ≠ 0) → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = e'.add 288 → Kc g₀ X.cpu.gpr Y.cpu.gpr → R 0 64 (Fb V A (g₀.rsi.setWidth 8)) Y.cpu.gpr.rdx →
      xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → xsOf Y.cpu.vec.zmm (xmmOf 7) = 0 → GoG prof L o gev gP gE Y t')
    (found : (∃ k < 64, V (Addr.add A k) = 0) → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = e'.add 430 → Kc g₀ X.cpu.gpr Y.cpu.gpr → R 0 64 (Fb V A (g₀.rsi.setWidth 8)) Y.cpu.gpr.rdx →
      xsOf Y.cpu.vec.zmm (xmmOf 5) = rd16 V (A + BitVec.ofNat 64 0) →
      xsOf Y.cpu.vec.zmm (xmmOf 4) = rd16 V (A + BitVec.ofNat 64 16) →
      xsOf Y.cpu.vec.zmm (xmmOf 3) = rd16 V (A + BitVec.ofNat 64 32) →
      xsOf Y.cpu.vec.zmm (xmmOf 2) = rd16 V (A + BitVec.ofNat 64 48) →
      xsOf Y.cpu.vec.zmm (xmmOf 6) = 0 → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  subst hdi
  -- `movdqa xmm3, [rdi + 32]`, `pxor xmm6, xmm6`, `movdqa xmm2, [rdi + 48]`, `movdqa xmm0, xmm3`,
  -- `movdqa xmm4, [rdi + 16]`, `pminub xmm0, xmm2`
  refine c.s_blkV hin (b303 prof) hK hA hrip ?_
  refine wpV_v (foot16a hft (q := 32) (by omega)) (fun _ => al16 hA64 (by omega))
    (wpV_v0 (wpV_v (foot16a hft (q := 48) (by omega)) (fun _ => al16 hA64 (by omega))
    (wpV_v0 (wpV_v (foot16a hft (q := 16) (by omega)) (fun _ => al16 hA64 (by omega)) (wpV_v0 (wpV_nil ?_))))))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  generalize hxd : xsOf X.cpu.vec.zmm = x at hv₁ hx1 hx7
  simp (disch := decide) only [eaB, get7, xset_same, xset_ne, xor_self'] at hv₁
  have hg₁' : Y₁.cpu.gpr = X.cpu.gpr := by simp only [hg₁]
  have hs₀ : Kc g₀ X.cpu.gpr X.cpu.gpr := ⟨hkp, rfl, rfl, rfl⟩
  have hx0₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 0) =
      pminb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 32)) (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48)) := by
    rw [hv₁]; simp (disch := decide) only [xset_same] <;> rfl
  have hx1₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by
    rw [hv₁]; simp (disch := decide) only [xset_ne, hx1]
  have hx2₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 2) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48) := by
    rw [hv₁]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx3₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 3) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 32) := by
    rw [hv₁]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx4₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 4) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 16) := by
    rw [hv₁]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx6₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 6) = 0 := by
    rw [hv₁]; simp (disch := decide) only [xset_same, xset_ne]
  have hx7₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 7) = 0 := by
    rw [hv₁]; simp (disch := decide) only [xset_ne, hx7]
  -- `movdqa xmm5, [rdi]`, `pminub xmm0, xmm4`, `pminub xmm0, xmm5`, `pcmpeqb xmm0, xmm7`, `pmovmskb eax, xmm0`,
  -- `movdqa xmm0, xmm5`
  refine c.s_blkV hin (b330 prof) hK₁ hA₁ hr₁ ?_
  rw [hg₁']
  refine wpV_v (foot16a hft (q := 0) (by omega)) (fun _ => al16 hA64 (by omega))
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_nil ?_))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ hv₂
  simp (disch := decide) only [eaB, get7, set_rax, xset_same, xset_ne, hx0₁, hx4₁, hx7₁] at hg₂ hv₂
  have hs₂ : Kc g₀ X.cpu.gpr Y₂.cpu.gpr := by rw [hg₂]; exact hs₀
  have hax₂ : Y₂.cpu.gpr.rax = (pmsk (peqb (pminb (pminb (pminb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 32))
      (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48))) (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 16)))
      (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 0))) 0)).setWidth 64 := by
    simp only [hg₂] <;> rfl
  have hx0₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 0) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 0) := by
    rw [hv₂]; simp (disch := decide) only [xset_same] <;> rfl
  have hx1₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by
    rw [hv₂]; simp (disch := decide) only [xset_ne, hx1₁]
  have hx2₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 2) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48) := by
    rw [hv₂]; simp (disch := decide) only [xset_ne, hx2₁]
  have hx3₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 3) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 32) := by
    rw [hv₂]; simp (disch := decide) only [xset_ne, hx3₁]
  have hx4₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 4) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 16) := by
    rw [hv₂]; simp (disch := decide) only [xset_ne, hx4₁]
  have hx5₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 5) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 0) := by
    rw [hv₂]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx6₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 6) = 0 := by
    rw [hv₂]; simp (disch := decide) only [xset_ne, hx6₁]
  have hx7₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 7) = 0 := by
    rw [hv₂]; simp (disch := decide) only [xset_ne, hx7₁]
  -- `pcmpeqb xmm0, xmm1`, `pmovmskb r9d, xmm0`, `movdqa xmm0, xmm4`, `pcmpeqb xmm0, xmm1`, `pmovmskb edx, xmm0`,
  -- `movdqa xmm0, xmm3`
  refine c.s_blkV hin (b354 prof) hK₂ hA₂ hr₂ ?_
  refine wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_nil ?_))))))
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ hv₃
  simp (disch := decide) only [set_r9', set_rdx, xset_same, xset_ne, hx0₂, hx1₂, hx4₂, hx3₂] at hg₃ hv₃
  have hs₃ : Kc g₀ X.cpu.gpr Y₃.cpu.gpr := by rw [hg₃]; exact hs₂
  have hax₃ : Y₃.cpu.gpr.rax = Y₂.cpu.gpr.rax := by simp only [hg₃]
  have hr9₃ : R 0 16 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₃.cpu.gpr.r9 := by
    simp only [hg₃]; exact R_low (bits64 fun i => cbit' V X.cpu.gpr.rdi 0 i g₀.rsi)
  have hdx₃ : ∀ i, Y₃.cpu.gpr.rdx.getLsbD i = (decide (i < 16) && Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8) (i + 16)) := by
    simp only [hg₃]; exact bits64 fun i => cbit' V X.cpu.gpr.rdi 16 i g₀.rsi
  have hx0₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 0) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 32) := by
    rw [hv₃]; simp (disch := decide) only [xset_same] <;> rfl
  have hx1₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by
    rw [hv₃]; simp (disch := decide) only [xset_ne, hx1₂]
  have hx2₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 2) = rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48) := by
    rw [hv₃]; simp (disch := decide) only [xset_ne, hx2₂]
  -- `pcmpeqb xmm0, xmm1`, `shl rdx, 16`, `pmovmskb r10d, xmm0`, `movdqa xmm0, xmm2`, `pcmpeqb xmm0, xmm1`,
  -- `shl r10, 32`
  refine c.s_blkV hin (b379 prof) hK₃ hA₃ hr₃ ?_
  refine wpV_v0 (wpV_reg fun _ _ => wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_))))
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ hv₄
  simp (disch := decide) only [wr, gv, Src.val, set_rdx, set_r10', get2, get10', BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, xset_same, xset_ne, hx0₃, hx1₃, hx2₃] at hg₄ hv₄
  have hs₄ : Kc g₀ X.cpu.gpr Y₄.cpu.gpr := by rw [hg₄]; exact hs₃
  have hax₄ : Y₄.cpu.gpr.rax = Y₂.cpu.gpr.rax := by simp only [hg₄]; exact hax₃
  have hr9₄ : R 0 16 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₄.cpu.gpr.r9 := by simp only [hg₄]; exact hr9₃
  have hdx₄ : R 16 32 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₄.cpu.gpr.rdx := by
    simp only [hg₄]; exact R_shl hdx₃ (by omega)
  have hr10₄ : R 32 48 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₄.cpu.gpr.r10 := by
    simp only [hg₄]; exact R_m (fun i => cbit' V X.cpu.gpr.rdi 32 i g₀.rsi) (by omega)
  have hx0₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 0) = peqb (rd16 V (X.cpu.gpr.rdi + BitVec.ofNat 64 48)) (Bc g₀.rsi) := by
    rw [hv₄]; simp (disch := decide) only [xset_same] <;> rfl
  -- the vectors but `xmm0` as at `Y₂`
  have hxe : ∀ k, k ≠ xmmOf 0 → xsOf Y₄.cpu.vec.zmm k = xsOf Y₂.cpu.vec.zmm k := fun k hk => by
    rw [hv₄, hv₃]; simp only [xset_ne _ _ hk]
  -- `or rdx, r10`, `pmovmskb r8d, xmm0`, `or rdx, r9`, `shl r8, 48`, `or rdx, r8`, `test eax, eax`
  refine c.s_blkV hin (b404 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
    wpV_reg fun fl hP => wpV_nil ?_)
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ hf₅ hv₅
  simp only [wr, gv, Src.val, set_rdx, set_r8, get0, get2, get8, get9', get10', BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hx0₄] at hg₅ hP
  simp only [hax₄, hax₂, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq,
    BitVec.and_self] at hP
  have hs₅ : Kc g₀ X.cpu.gpr Y₅.cpu.gpr := by rw [hg₅]; exact hs₄
  have hv₅' : xsOf Y₅.cpu.vec.zmm = xsOf Y₄.cpu.vec.zmm := by simp only [hv₅]
  have hdx₅ : R 0 64 (Fb V X.cpu.gpr.rdi (g₀.rsi.setWidth 8)) Y₅.cpu.gpr.rdx := by
    simp only [hg₅]
    exact R_or (R_or' (R_or hdx₄ hr10₄ (by omega) (by omega)) hr9₄ (by omega) (by omega))
      (R_m (fun i => cbit' V X.cpu.gpr.rdi 48 i g₀.rsi) (by omega)) (by omega) (by omega)
  have hc := cond4_mask hP
  refine c.s_jccV hK₅ hA₅ hin (by rw [sr2_length]; omega) hr₅ (d424 prof.feat) (tgt := 288) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- no 0
    intro htk Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆⟩
    rw [hf₅, hc] at htk
    exact none ((mask4r_eq_zero V X.cpu.gpr.rdi).1 (eq_of_beq htk)) Y₆ t₆ hK₆ hA₆ hr₆ (by rw [hg₆]; exact hs₅)
      (by rw [hg₆]; exact hdx₅) (by rw [hv₆, hv₅', hxe (xmmOf 1) (by decide)]; exact hx1₂)
      (by rw [hv₆, hv₅', hxe (xmmOf 7) (by decide)]; exact hx7₂)
  · -- a 0
    intro hfa Y₆ t₆ hK₆ hA₆ ⟨hr₆, hg₆, hv₆⟩
    rw [hf₅, hc] at hfa
    have hne := ne_of_beq_false hfa
    have hex : ∃ k < 64, V (Addr.add X.cpu.gpr.rdi k) = 0 :=
      Classical.byContradiction fun hn => hne ((mask4r_eq_zero V _).2 fun k hk hv => hn ⟨k, hk, hv⟩)
    exact found hex Y₆ t₆ hK₆ hA₆ hr₆ (by rw [hg₆]; exact hs₅) (by rw [hg₆]; exact hdx₅)
      (by rw [hv₆, hv₅', hxe (xmmOf 5) (by decide)]; exact hx5₂)
      (by rw [hv₆, hv₅', hxe (xmmOf 4) (by decide)]; exact hx4₂)
      (by rw [hv₆, hv₅', hxe (xmmOf 3) (by decide)]; exact hx3₂)
      (by rw [hv₆, hv₅', hxe (xmmOf 2) (by decide)]; exact hx2₂)
      (by rw [hv₆, hv₅', hxe (xmmOf 6) (by decide)]; exact hx6₂)

/-! ## The chunk with the string's 0 -/

/-- The stretch from `479` to `496`: `shl r8, 48`, `or rax, r8`, `lea r8, [rax - 1]`, `xor r8, rax`,
`and rdx, r8`. -/
def o479a : List VOp := [
  VOp.op (Op.shl64 8 (.i 48)),
  VOp.op (Op.or 64 0 (.r 8)),
  VOp.op (Op.lea 64 8 (some 0) none 1 18446744073709551615),
  VOp.op (Op.xor 64 8 (.r 0)),
  VOp.op (Op.and 64 2 (.r 8))]

theorem b479a (prof : Profile) : BlkV prof sr2 479 496 o479a :=
  .cons (d479 _) (OpI.shl64 (.i 48)) (by rw [sr2_length]; decide) <|
  .cons (d483 _) (OpI.or (.r 8) (.inr rfl)) (by rw [sr2_length]; decide) <|
  .cons (d486 _) (OpI.lea (.inr rfl)) (by rw [sr2_length]; decide) <|
  .cons (d490 _) (OpI.xor (.r 0) (.inr rfl)) (by rw [sr2_length]; decide) <|
  .cons (d493 _) (OpI.and (.r 8) (.inr rfl)) (by rw [sr2_length]; decide) <|
  .nil 496

/-- The stretch from `496` to `504`: `cmovne rcx, rdi`, `cmovne rsi, rdx`. -/
def o496 : List VOp := [
  VOp.op (Op.cmov64 5 1 7),
  VOp.op (Op.cmov64 5 6 2)]

theorem b496 (prof : Profile) : BlkV prof sr2 496 504 o496 :=
  .cons (d496 _) (OpI.cmov64) (by rw [sr2_length]; decide) <|
  .cons (d500 _) (OpI.cmov64) (by rw [sr2_length]; decide) <|
  .nil 504

/-- From `+430`, the chunk at `A` with the string's 0, its four loads in `xmm5`, `xmm4`, `xmm3`, `xmm2`, `rdx` its
matches: its zero mask in `rax`, the matches before its first 0; none: `rcx + bsr rsi` as it was, else
`A + bsr` of them. -/
theorem exit430 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n E : Nat}
    {A : Addr} (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 430)
    (hkp : KpR g₀ X.cpu.gpr) (hdi : X.cpu.gpr.rdi = A) (hdx : R 0 64 (Fb V A (g₀.rsi.setWidth 8)) X.cpu.gpr.rdx)
    (hx5 : xsOf X.cpu.vec.zmm (xmmOf 5) = rd16 V (A + BitVec.ofNat 64 0))
    (hx4 : xsOf X.cpu.vec.zmm (xmmOf 4) = rd16 V (A + BitVec.ofNat 64 16))
    (hx3 : xsOf X.cpu.vec.zmm (xmmOf 3) = rd16 V (A + BitVec.ofNat 64 32))
    (hx2 : xsOf X.cpu.vec.zmm (xmmOf 2) = rd16 V (A + BitVec.ofNat 64 48))
    (hx6 : xsOf X.cpu.vec.zmm (xmmOf 6) = 0)
    (hpA : g₀.rdi.toNat < A.toNat) (hAE : A.toNat ≤ g₀.rdi.toNat + E) (hEn : E ≤ n)
    (hnA : g₀.rdi.toNat + n < A.toNat + 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hsi0 : X.cpu.gpr.rsi ≠ 0)
    (hok : ROk V g₀.rdi E (g₀.rsi.setWidth 8) (Addr.add X.cpu.gpr.rcx (highestSetBit X.cpu.gpr.rsi)))
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  -- the string's 0 at `A + q`
  have hq : g₀.rdi.toNat + n - A.toNat < 64 := by omega
  generalize hqd : g₀.rdi.toNat + n - A.toNat = q at hq
  -- `pcmpeqb xmm4, xmm6`, `pcmpeqb xmm3, xmm6`, `pcmpeqb xmm5, xmm6`, `pmovmskb eax, xmm4`,
  -- `pmovmskb r10d, xmm3`, `pcmpeqb xmm2, xmm6`
  refine c.s_blkV hin (b430 prof) hK hA hrip ?_
  refine wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_nil ?_))))))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  generalize hxd : xsOf X.cpu.vec.zmm = x at hg₁ hv₁ hx5 hx4 hx3 hx2 hx6
  simp (disch := decide) only [xset_same, xset_ne, hx5, hx4, hx3, hx2, hx6, set_rax, set_r10'] at hg₁ hv₁
  have hkp₁ : KpR g₀ Y₁.cpu.gpr := by simp only [KpR, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = A := by simp only [hg₁]; exact hdi
  have hsi₁ : Y₁.cpu.gpr.rsi = X.cpu.gpr.rsi := by simp only [hg₁]
  have hcx₁ : Y₁.cpu.gpr.rcx = X.cpu.gpr.rcx := by simp only [hg₁]
  have hdx₁ : R 0 64 (Fb V A (g₀.rsi.setWidth 8)) Y₁.cpu.gpr.rdx := by simp only [hg₁]; exact hdx
  have hax₁ : ∀ i, Y₁.cpu.gpr.rax.getLsbD i = (decide (i < 16) && Fb V A 0 (i + 16)) := by
    simp only [hg₁]; exact bits64 fun i => zbit' V A 16 i
  have hr10₁ : ∀ i, Y₁.cpu.gpr.r10.getLsbD i = (decide (i < 16) && Fb V A 0 (i + 32)) := by
    simp only [hg₁]; exact bits64 fun i => zbit' V A 32 i
  have hx5₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 5) = peqb (rd16 V (A + BitVec.ofNat 64 0)) 0 := by
    rw [hv₁]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx2₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 2) = peqb (rd16 V (A + BitVec.ofNat 64 48)) 0 := by
    rw [hv₁]; simp (disch := decide) only [xset_same] <;> rfl
  -- `pmovmskb r9d, xmm5`, `shl r10, 32`, `shl rax, 16`, `pmovmskb r8d, xmm2`, `or rax, r10`, `or rax, r9`
  refine c.s_blkV hin (b455 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ _
  simp only [wr, gv, Src.val, set_rax, set_r8, set_r9', set_r10', get0, get9', get10', BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hx5₁, hx2₁] at hg₂
  have hkp₂ : KpR g₀ Y₂.cpu.gpr := by simp only [KpR, hg₂]; exact hkp₁
  have hdi₂ : Y₂.cpu.gpr.rdi = A := by simp only [hg₂]; exact hdi₁
  have hsi₂ : Y₂.cpu.gpr.rsi = X.cpu.gpr.rsi := by simp only [hg₂]; exact hsi₁
  have hcx₂ : Y₂.cpu.gpr.rcx = X.cpu.gpr.rcx := by simp only [hg₂]; exact hcx₁
  have hdx₂ : R 0 64 (Fb V A (g₀.rsi.setWidth 8)) Y₂.cpu.gpr.rdx := by simp only [hg₂]; exact hdx₁
  have hax₂ : R 0 48 (Fb V A 0) Y₂.cpu.gpr.rax := by
    simp only [hg₂]
    exact R_or' (R_or (R_shl hax₁ (by omega)) (R_shl hr10₁ (by omega)) (by omega) (by omega))
      (R_low (bits64 fun i => zbit' V A 0 i)) (by omega) (by omega)
  have hr8₂ : ∀ i, Y₂.cpu.gpr.r8.getLsbD i = (decide (i < 16) && Fb V A 0 (i + 48)) := by
    simp only [hg₂]; exact bits64 fun i => zbit' V A 48 i
  -- `shl r8, 48`, `or rax, r8`, `lea r8, [rax - 1]`, `xor r8, rax`, `and rdx, r8`
  refine c.s_blkV hin (b479a prof) hK₂ hA₂ hr₂ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl hP =>
    wpV_nil ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃ _
  simp only [wr, gv, Src.val, eaG, optV, set_r8, set_rax, set_rdx, get0, get2, get8, BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, z_mul64, add_z64] at hg₃ hP
  have hkp₃ : KpR g₀ Y₃.cpu.gpr := by simp only [KpR, hg₃]; exact hkp₂
  have hdi₃ : Y₃.cpu.gpr.rdi = A := by simp only [hg₃]; exact hdi₂
  have hsi₃ : Y₃.cpu.gpr.rsi = X.cpu.gpr.rsi := by simp only [hg₃]; exact hsi₂
  have hcx₃ : Y₃.cpu.gpr.rcx = X.cpu.gpr.rcx := by simp only [hg₃]; exact hcx₂
  have hZ : R 0 64 (Fb V A 0) Y₃.cpu.gpr.rax := by
    simp only [hg₃]; exact R_or hax₂ (R_shl hr8₂ (by omega)) (by omega) (by omega)
  have hdx₃ : Y₃.cpu.gpr.rdx =
      Y₂.cpu.gpr.rdx &&& ((Y₃.cpu.gpr.rax + BitVec.ofNat 64 18446744073709551615) ^^^ Y₃.cpu.gpr.rax) := by
    simp only [hg₃] <;> rfl
  have hc : Y₃.cpu.rflags.cond 5 = !(Y₃.cpu.gpr.rdx == 0) := by
    rw [hf₃, cond5_mask hP]; simp only [hg₃]
  -- the zero mask: its lowest set bit `q`
  have h1 : Y₃.cpu.gpr.rax.getLsbD q = true := by
    rw [hZ q, decide_eq_true (Nat.zero_le q), decide_eq_true hq, Fb,
      addr_eq (a := A) (b := g₀.rdi) (i := q) (j := n) (by omega), hz]
    rfl
  have h0 : ∀ i < q, Y₃.cpu.gpr.rax.getLsbD i = false := fun i hi => by
    rw [hZ i, Fb, addr_eq (a := A) (b := g₀.rdi) (i := i) (j := A.toNat - g₀.rdi.toNat + i) (by omega),
      decide_eq_false (hnz (A.toNat - g₀.rdi.toNat + i) (by omega)), Bool.and_false]
  have hZ0 : Y₃.cpu.gpr.rax.toNat ≠ 0 := fun h => by
    rw [← BitVec.testBit_toNat, h, Nat.zero_testBit] at h1
    exact Bool.false_ne_true h1
  have hY := toNat_pred64 Y₃.cpu.gpr.rax hZ0
  have hKb : ∀ i, Y₃.cpu.gpr.rdx.getLsbD i = (decide (i < q) && decide (V (Addr.add A i) = g₀.rsi.setWidth 8)) := by
    intro i
    rw [hdx₃, BitVec.getLsbD_and, getLsbD_blsmsk h1 h0 hY i, R_full hdx₂ i, Fb]
    by_cases hi : i < q
    · rw [decide_eq_true hi, decide_eq_true (show i ≤ q by omega), decide_eq_true (show i < 64 by omega)]
      simp only [Bool.true_and, Bool.and_true]
    · rw [decide_eq_false hi]
      by_cases hiq : i = q
      · rw [hiq, addr_eq (a := A) (b := g₀.rdi) (i := q) (j := n) (by omega), hz,
          decide_eq_false (fun h : (0 : Byte) = g₀.rsi.setWidth 8 => hch h.symm)]
        simp only [Bool.and_false, Bool.false_and]
      · rw [decide_eq_false (show ¬ i ≤ q by omega)]
        simp only [Bool.and_false, Bool.false_and]
  have hn : A.toNat - g₀.rdi.toNat + q = n := by omega
  -- `cmovne rcx, rdi`, `cmovne rsi, rdx`
  refine c.s_blkV hin (b496 prof) hK₃ hA₃ hr₃ ?_
  refine wpV_reg fun fl₄ hP₄ => wpV_reg fun _ _ => wpV_nil ?_
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ _
  subst hP₄
  -- `bsr rsi, rsi`, `lea rax, [rcx + rsi]`, `ret`, from `rcx` and `rsi` not 0 with `rcx + bsr rsi` as asked
  have last : ∀ {a b : BitVec 64}, KpR g₀ Y₄.cpu.gpr → Y₄.cpu.gpr.rcx = a → Y₄.cpu.gpr.rsi = b → b ≠ 0 →
      ROk V g₀.rdi n (g₀.rsi.setWidth 8) (Addr.add a (highestSetBit b)) → GoG prof L o gev gP gE Y₄ t₄ := by
    intro a b hkp₄ hca hsb hb hok'
    refine c.s_bsr64 hK₄ hA₄ hin (by rw [sr2_length]; omega) hr₄ (d504 prof.feat)
      (by simp only [rv, get6, BitVec.setWidth_eq, hsb]; exact hb) ?_
    rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
    simp only [rv, get6, BitVec.setWidth_eq, set_rsi, hsb] at hg₅
    refine c.s_blkV hin (b508 prof) hK₅ hA₅ hr₅ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ _ _
    simp only [wr, eaG, optV, set_rax, get1, get6, BitVec.setWidth_eq, BitVec.mul_one, BitVec.add_zero] at hg₆
    simp only [hg₅] at hg₆
    have hkp₆ : KpR g₀ Y₆.cpu.gpr := by simp only [KpR, hg₆]; exact hkp₄
    have hax₆ : Y₆.cpu.gpr.rax = Addr.add a (highestSetBit b) := by
      simp only [hg₆]
      rw [hca]
      rfl
    exact ret_atR c hin (by rw [sr2_length]; omega) (d512 prof.feat) hK₆ hA₆ hr₆ hkp₆ (by rw [hax₆]; exact hok') hR
  by_cases hd0 : Y₃.cpu.gpr.rdx = 0
  · -- no match before the 0: `rcx`, `rsi` as they were
    have hc' : Y₃.cpu.rflags.cond 5 = false := by rw [hc, hd0] <;> rfl
    simp only [rfz_cond, hc', Bool.false_eq_true, ↓reduceIte] at hg₄
    have hkp₄ : KpR g₀ Y₄.cpu.gpr := by simp only [KpR, hg₄]; exact hkp₃
    have hno : ∀ k, E ≤ k → k < n → V (Addr.add g₀.rdi k) ≠ g₀.rsi.setWidth 8 := fun k h1 h2 => by
      have hb := hKb (g₀.rdi.toNat + k - A.toNat)
      rw [hd0, getLsbD_zero', decide_eq_true (show g₀.rdi.toNat + k - A.toNat < q by omega), Bool.true_and] at hb
      rw [addr_eq (a := g₀.rdi) (b := A) (i := k) (j := g₀.rdi.toNat + k - A.toNat) (by omega)]
      exact of_decide_eq_false hb.symm
    exact last hkp₄ (by rw [hg₄]; exact hcx₃) (by rw [hg₄]; exact hsi₃) hsi0 (rok_ext hok hEn hno)
  · -- the last match before the 0: `rcx = A`, `rsi` the matches
    have hc' : Y₃.cpu.rflags.cond 5 = true := by rw [hc, beq_false_of_ne hd0] <;> rfl
    simp only [rfz_cond, hc', ↓reduceIte, wr, gv, set_rcx, set_rsi, get2, get7,
      BitVec.setWidth_eq] at hg₄
    have hkp₄ : KpR g₀ Y₄.cpu.gpr := by simp only [KpR, hg₄]; exact hkp₃
    have hok' := rok_new (p := g₀.rdi) (d := A.toNat - g₀.rdi.toNat) (by omega) (by omega) hKb hd0
    rw [hn] at hok'
    exact last hkp₄ (by rw [hg₄]; exact hdi₃) (by simp only [hg₄]) hd0 hok'

/-! ## The loop -/

/-- From `+303`, by the bytes left to look at. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {g₀ : Gprs} {n : Nat}
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) :
    ∀ m (Y : State) (t : Nat) (A : Addr) (E : Nat), g₀.rdi.toNat + n - A.toNat < m → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 303 → Y.cpu.gpr.rdi = A → KpR g₀ Y.cpu.gpr →
      xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → xsOf Y.cpu.vec.zmm (xmmOf 7) = 0 →
      A.toNat % 64 = 0 → g₀.rdi.toNat < A.toNat → A.toNat ≤ g₀.rdi.toNat + E → g₀.rdi.toNat + E < A.toNat + 64 →
      E ≤ n → Y.cpu.gpr.rsi ≠ 0 →
      ROk V g₀.rdi E (g₀.rsi.setWidth 8) (Addr.add Y.cpu.gpr.rcx (highestSetBit Y.cpu.gpr.rsi)) →
      GoG prof L o gev gP gE Y t := by
  intro m
  induction m with
  | zero => intro _ _ _ _ h; omega
  | succ m ih =>
  intro Y t A E hm hK hA hrip hdi hkp hx1 hx7 hA64 hpA hAE hEA hEn hsi0 hok
  have hAn : A.toNat ≤ g₀.rdi.toNat + n := by omega
  have hft' : ∀ k < 64, Foot F.data (Addr.add A k) := fun k hk => by
    have := footk (d := 0) hft hA64 rfl (by omega) (by omega) hov k hk
    rwa [Nat.zero_add] at this
  refine body c hin hK hA hrip hdi hkp hx1 hx7 hA64 hft' ?_ ?_
  · -- no 0 in `[A, A + 64)`: `test rdx, rdx`, `cmovne rsi, rdx`, `cmovne rcx, rdi`, `add rdi, 64`
    intro hall Y₁ t₁ hK₁ hA₁ hr₁ ⟨hkp₁, hdi₁, hsi₁, hcx₁⟩ hdx₁ hx1₁ hx7₁
    rw [hdi] at hdi₁
    have hge := all_nz (C := A) (d := 0) hz (by omega) fun k hk => by rw [Nat.zero_add]; exact hall k hk
    refine c.s_blkV hin (b288 prof) hK₁ hA₁ hr₁ ?_
    refine wpV_reg fun fl hP => wpV_reg fun fl₂ hP₂ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
    intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ hv₂
    subst hP₂
    simp only [gv, Src.val, get2, BitVec.setWidth_eq, BitVec.and_self] at hP
    have hc := cond5_mask hP
    have ht : (addR A (BitVec.ofNat 64 64)).toNat = A.toNat + 64 := add64 (by omega)
    have hx1₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by rw [hv₂]; exact hx1₁
    have hx7₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 7) = 0 := by rw [hv₂]; exact hx7₁
    by_cases hd0 : Y₁.cpu.gpr.rdx = 0
    · -- no match: `rsi`, `rcx` as they were
      have hc' : fl.cond 5 = false := by rw [hc, hd0] <;> rfl
      simp only [rfz_cond, hc', Bool.false_eq_true, ↓reduceIte, wr, gv, Src.val, set_rdi, get7, BitVec.setWidth_eq,
        hdi₁] at hg₂
      generalize hA' : addR A (BitVec.ofNat 64 64) = A' at hg₂ ht
      have hno : ∀ k, E ≤ k → k < A.toNat - g₀.rdi.toNat + 64 → V (Addr.add g₀.rdi k) ≠ g₀.rsi.setWidth 8 :=
        fun k h1 h2 => by
          have hb := R_full hdx₁ (g₀.rdi.toNat + k - A.toNat)
          rw [hd0, getLsbD_zero', decide_eq_true (show g₀.rdi.toNat + k - A.toNat < 64 by omega), Bool.true_and,
            Fb] at hb
          rw [addr_eq (a := g₀.rdi) (b := A) (i := k) (j := g₀.rdi.toNat + k - A.toNat) (by omega)]
          exact of_decide_eq_false hb.symm
      refine ih Y₂ t₂ A' (A.toNat - g₀.rdi.toNat + 64) (by omega) hK₂ hA₂ hr₂ (by simp only [hg₂])
        (by simp only [KpR, hg₂]; exact hkp₁) hx1₂ hx7₂ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by simp only [hg₂, hsi₁]; exact hsi0) ?_
      simp only [hg₂, hsi₁, hcx₁]
      exact rok_ext hok (by omega) hno
    · -- a match: `rsi` the chunk's matches, `rcx = A`
      have hc' : fl.cond 5 = true := by rw [hc, beq_false_of_ne hd0] <;> rfl
      simp only [rfz_cond, hc', ↓reduceIte, wr, gv, Src.val, set_rsi, set_rcx, set_rdi, get2,
        get7, BitVec.setWidth_eq, hdi₁] at hg₂
      generalize hA' : addR A (BitVec.ofNat 64 64) = A' at hg₂ ht
      have hok' := rok_new (p := g₀.rdi) (d := A.toNat - g₀.rdi.toNat) (by omega) (Nat.le_refl 64) (R_full hdx₁) hd0
      refine ih Y₂ t₂ A' (A.toNat - g₀.rdi.toNat + 64) (by omega) hK₂ hA₂ hr₂ (by simp only [hg₂])
        (by simp only [KpR, hg₂]; exact hkp₁) hx1₂ hx7₂ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by simp only [hg₂]; exact hd0) ?_
      simp only [hg₂]
      exact hok'
  · -- a 0 in `[A, A + 64)`: the end
    intro hex Y₁ t₁ hK₁ hA₁ hr₁ ⟨hkp₁, hdi₁, hsi₁, hcx₁⟩ hdx₁ hx5 hx4 hx3 hx2 hx6
    rw [hdi] at hdi₁
    have hlt := some_zero (C := A) (d := 0) hnz (by omega) (by
      obtain ⟨k, hk, hv⟩ := hex
      exact ⟨k, hk, by rw [Nat.zero_add]; exact hv⟩)
    exact exit430 c hin hK₁ hA₁ hr₁ hkp₁ hdi₁ hdx₁ hx5 hx4 hx3 hx2 hx6 hpA hAE hEn (by omega) hnz hz hch
      (by rw [hsi₁]; exact hsi0) (by rw [hsi₁, hcx₁]; exact hok) hR

/-! ## Into the loop -/

/-- From `+268`, the `E` bytes from `p` looked at, up to the 64-aligned address after `p` or past it, `rcx + bsr rsi`
their last match or null: `add rdi, 64`, `pxor xmm7, xmm7`, `and rdi, -64`, `jmp +303`, the loop. -/
theorem at268 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 268) (hkp : KpR g₀ X.cpu.gpr)
    (hdi : X.cpu.gpr.rdi = g₀.rdi) (hx1 : xsOf X.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi) {E : Nat} (hEn : E ≤ n)
    (hE1 : (g₀.rdi.toNat + 64) / 64 * 64 ≤ g₀.rdi.toNat + E) (hE2 : E ≤ 64) (hsi0 : X.cpu.gpr.rsi ≠ 0)
    (hok : ROk V g₀.rdi E (g₀.rsi.setWidth 8) (Addr.add X.cpu.gpr.rcx (highestSetBit X.cpu.gpr.rsi))) :
    GoG prof L o gev gP gE X t := by
  refine c.s_blkV hin (b268 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_)
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, set_rdi, get7, BitVec.setWidth_eq, hdi] at hg₁
  have ht : (addR g₀.rdi (BitVec.ofNat 64 64)).toNat = g₀.rdi.toNat + 64 := add64 (by omega)
  have hB : Y₁.cpu.gpr.rdi.toNat = (g₀.rdi.toNat + 64) / 64 * 64 := by
    simp only [hg₁]; rw [Strlen.and_m64, ht]
  refine c.s_jmpV hK₁ hA₁ hin (by rw [sr2_length]; omega) hr₁ (d280 prof.feat) (tgt := 303) rfl
    (by rw [sr2_length]; omega) ?_
  intro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
  refine loop c hin hov hnz hz hch hft hR _ Y₂ t₂ Y₁.cpu.gpr.rdi E (Nat.lt_succ_self _) hK₂ hA₂ hr₂
    (by rw [hg₂]) (by rw [hg₂]; simp only [KpR, hg₁]; exact hkp)
    (by rw [hv₂, hv₁]; simp (disch := decide) only [xset_ne, hx1])
    (by rw [hv₂, hv₁]; simp (disch := decide) only [xset_same, xor_self']) (by omega) (by omega) (by omega)
    (by omega) hEn (by rw [hg₂]; simp only [hg₁]; exact hsi0) (by rw [hg₂]; simp only [hg₁]; exact hok)

/-- From `+256`, no 0 among the `E` bytes from `p`, `rsi` their matches: `test rsi, rsi`, `mov rcx, rdi`; none:
`je +528`, `mov esi, 1`, `xor ecx, ecx`, `jmp +268`; then `at268`. -/
theorem from256E (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {g₀ : Gprs} {n : Nat}
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) :
    ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 256 → KpR g₀ Y.cpu.gpr →
      Y.cpu.gpr.rdi = g₀.rdi → ∀ E,
      (∀ i, Y.cpu.gpr.rsi.getLsbD i = (decide (i < E) && Fb V g₀.rdi (g₀.rsi.setWidth 8) i)) →
      xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → E ≤ n → (g₀.rdi.toNat + 64) / 64 * 64 ≤ g₀.rdi.toNat + E →
      E ≤ 64 → GoG prof L o gev gP gE Y t' := by
  intro Y t hK hA hrip hkp hdi E hsi hx1 hEn hE1 hE2
  have hS := rok_mask hE2 hsi
  refine c.s_blkV hin (b256 prof) hK hA hrip ?_
  refine wpV_reg fun fl hP => wpV_reg fun fl₂ hP₂ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  simp only [wr, gv, Src.val, set_rcx, get6, get7, BitVec.setWidth_eq, BitVec.and_self] at hg₁ hP
  have hc : Y₁.cpu.rflags.cond 4 = (Y.cpu.gpr.rsi == 0) := by rw [hf₁, hP₂, rfz_cond, cond4_mask hP]
  refine c.s_jccV hK₁ hA₁ hin (by rw [sr2_length]; omega) hr₁ (d262 prof.feat) (tgt := 528) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- no match: `rsi = 1`, `rcx = 0`
    intro htk Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    rw [hc] at htk
    have h0 := eq_of_beq htk
    refine c.s_blkV hin (b528 prof) hK₂ hA₂ hr₂ ?_
    refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
    intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ hv₃
    simp only [wr, gv, Src.val, set_rsi, set_rcx, get1, xor_self'] at hg₃
    refine c.s_jmpV hK₃ hA₃ hin (by rw [sr2_length]; omega) hr₃ (d535 prof.feat) (tgt := 268) rfl
      (by rw [sr2_length]; omega) ?_
    intro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hv₄⟩
    have hsi₄ : Y₄.cpu.gpr.rsi = 1 := by rw [hg₄]; simp only [hg₃] <;> decide
    have hcx₄ : Y₄.cpu.gpr.rcx = 0 := by rw [hg₄]; simp only [hg₃] <;> decide
    exact at268 c hin hov hnz hz hch hft hR hK₄ hA₄ hr₄
      (by rw [hg₄]; simp only [KpR, hg₃, hg₂, hg₁]; exact hkp) (by rw [hg₄]; simp only [hg₃, hg₂, hg₁]; exact hdi)
      (by rw [hv₄, hv₃, hv₂, hv₁]; exact hx1) hEn hE1 hE2 (by rw [hsi₄]; decide)
      (by rw [hsi₄, hcx₄, hsb_one, addr_add_zero]; exact rok_none (hS.1.1 h0))
  · -- `rcx = p`
    intro hfa Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
    rw [hc] at hfa
    have hne := ne_of_beq_false hfa
    exact at268 c hin hov hnz hz hch hft hR hK₂ hA₂ hr₂ (by rw [hg₂]; simp only [KpR, hg₁]; exact hkp)
      (by rw [hg₂]; simp only [hg₁]; exact hdi) (by rw [hv₂, hv₁]; exact hx1) hEn hE1 hE2
      (by rw [hg₂]; simp only [hg₁]; exact hne) (by rw [hg₂]; simp only [hg₁]; rw [hdi]; exact hS.2 hne)

/-- `from256E` for all 64 bytes from `p`. -/
theorem from256 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {g₀ : Gprs} {n : Nat}
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) :
    ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 256 → KpR g₀ Y.cpu.gpr →
      Y.cpu.gpr.rdi = g₀.rdi → R 0 64 (Fb V g₀.rdi (g₀.rsi.setWidth 8)) Y.cpu.gpr.rsi →
      xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → 64 ≤ n → GoG prof L o gev gP gE Y t' :=
  fun Y t hK hA hrip hkp hdi hsi hx1 h64 => from256E c hin hov hnz hz hch hft hR Y t hK hA hrip hkp hdi 64
    (R_full hsi) hx1 h64 (by omega) (Nat.le_refl 64)

end FV7z.Strrchr
