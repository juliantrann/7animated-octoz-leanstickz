import FV7z.Strlen.Run
/-!
# `__strlen_sse2`, the loop (PLAN.md M, the PLT contracts)

From `+256` with `rax` a 64-aligned `A`, `p < A + 64 ≤ p + n` and `xmm1`–`xmm3` 0, the loop looks at the 64 bytes
from `A + 64` (`+256` … `+286`), then at the 64 from `A + 128` (`+288` … `+321`), a chunk at a time: the four loads
folded by `pminub`, compared with `xmm3`, the mask tested. A chunk with a 0 goes to `+340` (by `+336`, which adds 64
to `rax`, for the first), with `rax` the chunk's start; else on, back to `+256` with `A + 128`.
-/
namespace FV7z.Strlen
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- A chunk: the four loads from `rax + d` folded by `pminub`, `pcmpeqb` with `xmm3`, `pmovmskb edx`, `test`. -/
def oC (d : Nat) : List VOp := [VOp.movdqa_m 0 0 d, VOp.pminub_m 0 0 (d + 16), VOp.pminub_m 0 0 (d + 32),
  VOp.pminub_m 0 0 (d + 48), VOp.pcmpeqb 0 3, VOp.pmovmskb 2 0, VOp.op (Op.test 32 2 (.r 2))]

theorem b256C (prof : Profile) : BlkV prof sl2 256 286 (oC 64) := b256 prof
theorem b292C (prof : Profile) : BlkV prof sl2 292 321 (oC 0) := b292 prof

/-- `xmm1`–`xmm3` are 0. -/
abbrev Z3 (x : XRegs) : Prop := x (xmmOf 1) = 0 ∧ x (xmmOf 2) = 0 ∧ x (xmmOf 3) = 0

/-! ## Masks -/

/-- The mask of a chunk is 0 iff none of its 64 bytes is. -/
theorem mask4_eq_zero (V : Addr → Byte) (B : Addr) (d : Nat) :
    pmsk (peqb (pminb (pminb (pminb (rd16 V (B + BitVec.ofNat 64 d)) (rd16 V (B + BitVec.ofNat 64 (d + 16))))
      (rd16 V (B + BitVec.ofNat 64 (d + 32)))) (rd16 V (B + BitVec.ofNat 64 (d + 48)))) 0) = 0 ↔
    ∀ k < 64, V (Addr.add B (d + k)) ≠ 0 := by
  have e : ∀ c j, Addr.add (B + BitVec.ofNat 64 c) j = Addr.add B (c + j) := fun c j => addr_add_add B c j
  rw [zmask4_eq_zero]
  constructor
  · intro h k hk
    have hj : k % 16 < 16 := Nat.mod_lt _ (by decide)
    obtain ⟨h0, h1, h2, h3⟩ := h (k % 16) hj
    rw [lane_rd16 _ _ hj, e] at h0 h1 h2 h3
    have : k / 16 = 0 ∨ k / 16 = 1 ∨ k / 16 = 2 ∨ k / 16 = 3 := by omega
    rcases this with h' | h' | h' | h'
    · rwa [show d + k = d + k % 16 by omega]
    · rwa [show d + k = d + 16 + k % 16 by omega]
    · rwa [show d + k = d + 32 + k % 16 by omega]
    · rwa [show d + k = d + 48 + k % 16 by omega]
  · intro h j hj
    rw [lane_rd16 _ _ hj, lane_rd16 _ _ hj, lane_rd16 _ _ hj, lane_rd16 _ _ hj, e, e, e, e]
    refine ⟨h j (by omega), ?_, ?_, ?_⟩
    · rw [show d + 16 + j = d + (16 + j) by omega]; exact h _ (by omega)
    · rw [show d + 32 + j = d + (32 + j) by omega]; exact h _ (by omega)
    · rw [show d + 48 + j = d + (48 + j) by omega]; exact h _ (by omega)

theorem cond5_mask {w : Nat} {f fl : Rflags} {M : BitVec w} (h : LogF f M fl) : fl.cond 5 = !(M == 0) := by
  obtain ⟨af, rfl⟩ := h
  rw [cond5, arith_zf]

theorem nz_iff {M : BitVec 32} {P : Prop} (hM : M = 0 ↔ P) : (!(M == 0)) = true ↔ ¬ P := by
  rw [← hM]
  by_cases hm : M = 0
  · subst hm; decide
  · rw [beq_false_of_ne hm]; exact ⟨fun _ => hm, fun _ => rfl⟩

theorem z_iff {M : BitVec 32} {P : Prop} (hM : M = 0 ↔ P) : (!(M == 0)) = false ↔ P := by
  rw [← hM]
  by_cases hm : M = 0
  · subst hm; decide
  · rw [beq_false_of_ne hm]; exact ⟨fun h => absurd h (by decide), fun h => absurd h hm⟩

/-! ## Bytes and addresses -/

/-- The 64 bytes of a chunk from a 64-aligned `C + d` between the string's first page and its last are to read. -/
theorem footk {F : Footprint} {p C : Addr} {n d : Nat}
    (hft : ∀ x : Addr, p.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (p.toNat + n) / 4096 → Foot F.data x)
    (hC : C.toNat % 64 = 0) (hd : d % 64 = 0) (h1 : p.toNat < C.toNat + d + 64) (h2 : C.toNat + d ≤ p.toNat + n)
    (hn : p.toNat + n < 2 ^ 64) : ∀ k < 64, Foot F.data (Addr.add C (d + k)) := by
  intro k hk
  have := C.isLt
  have hk' : (Addr.add C (d + k)).toNat = C.toNat + d + k := by
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  apply hft <;> rw [hk'] <;> omega

/-- A load of 16 of a chunk's bytes. -/
theorem foot16g {F : Footprint} {C : Addr} {d : Nat} (h : ∀ k < 64, Foot F.data (Addr.add C (d + k))) {q : Nat}
    (hq : q + 16 ≤ 64) : ∀ i < 16, Foot F.data (Addr.add (C + BitVec.ofNat 64 (d + q)) i) := by
  intro i hi
  have := h (q + i) (by omega)
  rw [← Nat.add_assoc, ← addr_add_add] at this
  exact this

/-- A 0 in a chunk not before the string: the string ends in the chunk. -/
theorem some_zero {V : Addr → Byte} {p C : Addr} {n d : Nat} (hnz : ∀ k < n, V (Addr.add p k) ≠ 0)
    (hpC : p.toNat ≤ C.toNat + d) (hex : ∃ k < 64, V (Addr.add C (d + k)) = 0) : p.toNat + n < C.toNat + d + 64 := by
  obtain ⟨k, hk, hv⟩ := hex
  refine Classical.byContradiction fun hge => hnz (C.toNat + d + k - p.toNat) (by omega) ?_
  rw [addr_eq (a := p) (b := C) (i := C.toNat + d + k - p.toNat) (j := d + k) (by omega)]
  exact hv

/-- No 0 in a chunk not after the string's end: the string goes past the chunk. -/
theorem all_nz {V : Addr → Byte} {p C : Addr} {n d : Nat} (hz : V (Addr.add p n) = 0)
    (hle : C.toNat + d ≤ p.toNat + n) (hall : ∀ k < 64, V (Addr.add C (d + k)) ≠ 0) :
    C.toNat + d + 64 ≤ p.toNat + n := by
  refine Classical.byContradiction fun hlt => hall (p.toNat + n - C.toNat - d) (by omega) ?_
  rw [addr_eq (a := C) (b := p) (i := d + (p.toNat + n - C.toNat - d)) (j := n) (by omega)]
  exact hz

theorem add64 {A : Addr} (h : A.toNat + 64 < 2 ^ 64) : (addR A (BitVec.ofNat 64 64)).toNat = A.toNat + 64 := by
  have h0 : ((BitVec.ofBool false).setWidth 64).toNat = 0 := by decide
  simp only [addR, BitVec.toNat_add, BitVec.toNat_ofNat, h0]
  omega

theorem sub128 {A : Addr} (h : A.toNat + 128 < 2 ^ 64) :
    (subR A (BitVec.ofNat 64 18446744073709551488)).toNat = A.toNat + 128 := by
  have h0 : ((BitVec.ofBool false).setWidth 64).toNat = 0 := by decide
  have := A.isLt
  simp only [subR, BitVec.toNat_sub, BitVec.toNat_ofNat, h0]
  omega

/-! ## A chunk -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- A chunk from `rax + d` and its `jne`: to `tgt` if one of its bytes is 0, else on; `rax`, the call's registers,
`xmm1`–`xmm3` kept. -/
theorem chunk (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {j j' rel tgt d : Nat}
    (hb : BlkV prof sl2 j j' (oC d)) (hj' : j' < sl2.length)
    (hd : Dec prof.feat sl2 j' (FV7z.mk (.jcc 5) 64 [.rel rel] 2)) (htgt : (j' + 2 + rel) % 2 ^ 64 = tgt % 2 ^ 64)
    (ht : tgt < sl2.length) {X : State} {t : Nat} {g₀ : Gprs} {C : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add j)
    (hax : X.cpu.gpr.rax = C) (hkp : Kp g₀ X.cpu.gpr) (hz3 : Z3 (xsOf X.cpu.vec.zmm))
    (hC : C.toNat % 64 = 0) (hd16 : d % 16 = 0) (hft : ∀ k < 64, Foot F.data (Addr.add C (d + k)))
    (found : (∃ k < 64, V (Addr.add C (d + k)) = 0) → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = e'.add tgt → Y.cpu.gpr.rax = C → Kp g₀ Y.cpu.gpr → Z3 (xsOf Y.cpu.vec.zmm) →
      GoG prof L o gev gP gE Y t')
    (none : (∀ k < 64, V (Addr.add C (d + k)) ≠ 0) → ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
      Y.cpu.rip = e'.add (j' + 2) → Y.cpu.gpr.rax = C → Kp g₀ Y.cpu.gpr → Z3 (xsOf Y.cpu.vec.zmm) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  subst hax
  obtain ⟨hx1, hx2, hx3⟩ := hz3
  refine c.s_blkV hin hb hK hA hrip ?_
  refine wpV_v (foot16g hft (q := 0) (by omega)) (fun _ => al16 hC (by omega))
    (wpV_v (foot16g hft (q := 16) (by omega)) (fun _ => al16 hC (by omega))
    (wpV_v (foot16g hft (q := 32) (by omega)) (fun _ => al16 hC (by omega))
    (wpV_v (foot16g hft (q := 48) (by omega)) (fun _ => al16 hC (by omega))
    (wpV_v0 (wpV_v0 (wpV_reg fun fl hP => wpV_nil ?_))))))
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ hf₁ hv₁
  generalize hxd : xsOf X.cpu.vec.zmm = x at hg₁ hv₁ hP hx1 hx2 hx3
  simp (disch := decide) only [eaB, gv, Src.val, set_rdx, get0, get2, xset_same, xset_ne, hx3, BitVec.setWidth_eq,
    BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.and_self] at hg₁ hP
  have hax₁ : Y₁.cpu.gpr.rax = X.cpu.gpr.rax := by simp only [hg₁]
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  have hz₁ : Z3 (xsOf Y₁.cpu.vec.zmm) := by
    rw [hv₁]
    refine ⟨?_, ?_, ?_⟩ <;> simp (disch := decide) only [xset_ne, hx1, hx2, hx3]
  refine c.s_jccV hK₁ hA₁ hin hj' hr₁ hd htgt ht ?_ ?_
  · intro htk
    rw [hf₁, cond5_mask hP] at htk
    have hm := (nz_iff (mask4_eq_zero V _ d)).1 htk
    have hex : ∃ k < 64, V (Addr.add X.cpu.gpr.rax (d + k)) = 0 :=
      Classical.byContradiction fun hn => hm fun k hk hv => hn ⟨k, hk, hv⟩
    intro Y t' hKY hAY ⟨hrY, hgY, hvY⟩
    exact found hex Y t' hKY hAY hrY (by rw [hgY, hax₁]) (by rw [hgY]; exact hkp₁) (by rw [hvY]; exact hz₁)
  · intro hfa
    rw [hf₁, cond5_mask hP] at hfa
    have hall := (z_iff (mask4_eq_zero V _ d)).1 hfa
    intro Y t' hKY hAY ⟨hrY, hgY, hvY⟩
    exact none hall Y t' hKY hAY hrY (by rw [hgY, hax₁]) (by rw [hgY]; exact hkp₁) (by rw [hvY]; exact hz₁)

/-! ## The loop -/

/-- From `+256`, by the bytes left to look at. -/
theorem loop (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {g₀ : Gprs} {n : Nat}
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) :
    ∀ m (Y : State) (t : Nat) (A : Addr), g₀.rdi.toNat + n - A.toNat < m → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 256 → Y.cpu.gpr.rax = A → Kp g₀ Y.cpu.gpr →
      Z3 (xsOf Y.cpu.vec.zmm) → A.toNat % 64 = 0 → g₀.rdi.toNat < A.toNat + 64 →
      A.toNat + 64 ≤ g₀.rdi.toNat + n → GoG prof L o gev gP gE Y t := by
  intro m
  induction m with
  | zero => intro _ _ _ h; omega
  | succ m ih =>
  intro Y t A hm hK hA hrip hax hkp hz3 hA64 hpA hAn
  refine chunk (tgt := 336) c hin (b256C prof) (by rw [sl2_length]; omega) (d286 prof.feat) rfl
    (by rw [sl2_length]; omega) hK hA hrip hax hkp hz3 hA64 rfl (footk hft hA64 rfl (by omega) hAn hov) ?_ ?_
  · -- a 0 in `[A + 64, A + 128)`: `add rax, 64`, the end
    intro hex Y₁ t₁ hK₁ hA₁ hr₁ hax₁ hkp₁ hz₁
    have hlt := some_zero hnz (by omega) hex
    refine c.s_blkV hin (b336 prof) hK₁ hA₁ hr₁ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ hv₂
    simp only [wr, gv, Src.val, set_rax, get0, BitVec.setWidth_eq, hax₁] at hg₂
    have hax₂ : Y₂.cpu.gpr.rax = addR A (BitVec.ofNat 64 64) := by simp only [hg₂]
    have hkp₂ : Kp g₀ Y₂.cpu.gpr := by simp only [Kp, hg₂]; exact hkp₁
    have ht₂ : Y₂.cpu.gpr.rax.toNat = A.toNat + 64 := by rw [hax₂]; exact add64 (by omega)
    obtain ⟨hx1, hx2, hx3⟩ := hz₁
    rw [← hv₂] at hx1 hx2 hx3
    exact exit340 c hin hK₂ hA₂ hr₂ hkp₂ hx1 hx2 hx3 (by omega) (by omega) (by omega) (by omega) hov hnz hz hft hR
  · -- none in `[A + 64, A + 128)`: `sub rax, -128`, the next chunk
    intro hall Y₁ t₁ hK₁ hA₁ hr₁ hax₁ hkp₁ hz₁
    have hge := all_nz hz (by omega) hall
    refine c.s_blkV hin (b288 prof) hK₁ hA₁ hr₁ ?_
    refine wpV_reg fun _ _ => wpV_nil ?_
    intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ hv₂
    simp only [wr, gv, Src.val, set_rax, get0, BitVec.setWidth_eq, hax₁] at hg₂
    have hkp₂ : Kp g₀ Y₂.cpu.gpr := by simp only [Kp, hg₂]; exact hkp₁
    have hz₂ : Z3 (xsOf Y₂.cpu.vec.zmm) := by rw [hv₂]; exact hz₁
    have ht₂ : (subR A (BitVec.ofNat 64 18446744073709551488)).toNat = A.toNat + 128 := sub128 (by omega)
    generalize hA' : subR A (BitVec.ofNat 64 18446744073709551488) = A' at hg₂ ht₂
    have hax₂ : Y₂.cpu.gpr.rax = A' := by simp only [hg₂]
    refine chunk (tgt := 340) c hin (b292C prof) (by rw [sl2_length]; omega) (d321 prof.feat) rfl
      (by rw [sl2_length]; omega) hK₂ hA₂ hr₂ hax₂ hkp₂ hz₂ (by omega) rfl
      (footk (d := 0) hft (by omega) rfl (by omega) (by omega) hov) ?_ ?_
    · -- a 0 in `[A + 128, A + 192)`: the end
      intro hex Y₃ t₃ hK₃ hA₃ hr₃ hax₃ hkp₃ hz₃
      have hlt := some_zero hnz (by omega) hex
      obtain ⟨hx1, hx2, hx3⟩ := hz₃
      have hB : Y₃.cpu.gpr.rax.toNat = A.toNat + 128 := by rw [hax₃]; exact ht₂
      exact exit340 c hin hK₃ hA₃ hr₃ hkp₃ hx1 hx2 hx3 (by omega) (by omega) (by omega) (by omega) hov hnz hz hft hR
    · -- none: `jmp` back to `+256` with `A + 128`
      intro hall' Y₃ t₃ hK₃ hA₃ hr₃ hax₃ hkp₃ hz₃
      have hge' := all_nz (d := 0) hz (by omega) hall'
      refine c.s_jmpV hK₃ hA₃ hin (by rw [sl2_length]; omega) hr₃ (d323 prof.feat) (tgt := 256) rfl
        (by rw [sl2_length]; omega) ?_
      intro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hv₄⟩
      refine ih Y₄ t₄ A' (by omega) hK₄ hA₄ hr₄ (by rw [hg₄]; exact hax₃) (by rw [hg₄]; exact hkp₃)
        (by rw [hv₄]; exact hz₃) (by omega) (by omega) (by omega)

end FV7z.Strlen
