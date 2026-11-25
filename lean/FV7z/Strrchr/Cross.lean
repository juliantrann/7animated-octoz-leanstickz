import FV7z.Strrchr.Loop
/-!
# `__strrchr_sse2`, near a page's end (PLAN.md G2)

From `+560`, `p` among the last 63 bytes of its page: the 64 bytes from `A`, `p` rounded down to 64, all on `p`'s page,
compared with 0 (`rdx`) and with the character (`rsi`), both masks shifted right by `p - A` (`ecx = edi - eax`). No 0:
to `+256` with the `E = A + 64 - p` bytes from `p` looked at (`from256E`); else the matches up to the first 0, none:
`+544`, else the last (`bsr rax, rsi`, `add rax, rdi`).
-/
namespace FV7z.Strrchr
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen

attribute [-simp] BitVec.getLsbD_eq_getElem

/-- A mask of the 64 bytes from `A`, shifted right by `s`: the `64 - s` bytes from `p = A + s`. -/
theorem shr_bits {x : BitVec 64} {V : Addr → Byte} {A p : Addr} {c : Byte} {s : Nat} (h : R 0 64 (Fb V A c) x)
    (hs : A.toNat + s = p.toNat) (i : Nat) : (x >>> s).getLsbD i = (decide (i < 64 - s) && Fb V p c i) := by
  rw [BitVec.getLsbD_ushiftRight, R_full h, Fb, Fb, addr_eq (a := A) (b := p) (i := s + i) (j := i) (by omega)]
  by_cases hi : i < 64 - s
  · rw [decide_eq_true hi, decide_eq_true (show s + i < 64 by omega)]
  · rw [decide_eq_false hi, decide_eq_false (show ¬ s + i < 64 by omega)]

theorem addR_addr (p : Addr) (k : Nat) : addR (BitVec.ofNat 64 k) p = Addr.add p k := by
  have h0 : ((BitVec.ofBool false).setWidth 64).toNat = 0 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [addR, Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, h0]
  omega

/-- The stretch from `560` to `571`: `mov rax, rdi`, `pxor xmm0, xmm0`, `and rax, -64`. -/
def o560a : List VOp := [
  VOp.op (Op.mov 64 0 (.r 7)),
  VOp.pxor 0 0,
  VOp.op (Op.and 64 0 (.i 18446744073709551552))]

theorem b560a (prof : Profile) : BlkV prof sr2 560 571 o560a :=
  .cons (d560 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [sr2_length]; decide) <|
  .cons (d563 _) (VOpI.pxor) (by rw [sr2_length]; decide) <|
  .cons (d567 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by rw [sr2_length]; decide) <|
  .nil 571

/-- The stretch from `571` to `584`: `movdqu xmm5, [rax]`, `movdqa xmm6, xmm5`, `movdqu xmm4, [rax + 16]`. -/
def o571 : List VOp := [
  VOp.movdqu_m 5 0 0,
  VOp.movdqa 6 5,
  VOp.movdqu_m 4 0 16]

theorem b571 (prof : Profile) : BlkV prof sr2 571 584 o571 :=
  .cons (d571 _) (VOpI.movdqu_m) (by rw [sr2_length]; decide) <|
  .cons (d575 _) (VOpI.movdqa) (by rw [sr2_length]; decide) <|
  .cons (d579 _) (VOpI.movdqu_m) (by rw [sr2_length]; decide) <|
  .nil 584

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

/-- From `+560`, `p` among the last 63 bytes of its page. -/
theorem path560 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sr2) {g₀ : Gprs} {n : Nat}
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0) (hch : g₀.rsi.setWidth 8 ≠ 0#8)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : RetR prof F Wl L s₀ o gev gP gE V g₀ n) :
    ∀ Y t', KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e'.add 560 → KpR g₀ Y.cpu.gpr →
      Y.cpu.gpr.rdi = g₀.rdi → xsOf Y.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi → 4032 < g₀.rdi.toNat % 4096 →
      GoG prof L o gev gP gE Y t' := by
  intro X t hK hA hrip hkp hdi hx1 hq
  have hp := g₀.rdi.isLt
  -- `mov rax, rdi`, `pxor xmm0, xmm0`, `and rax, -64`
  refine c.s_blkV hin (b560a prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_)
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, set_rax, get0, get7, BitVec.setWidth_eq, hdi] at hg₁
  have hkp₁ : KpR g₀ Y₁.cpu.gpr := by simp only [KpR, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := by simp only [hg₁]
  have hAn : Y₁.cpu.gpr.rax.toNat = g₀.rdi.toNat / 64 * 64 := by simp only [hg₁]; exact Strlen.and_m64 _
  have hx0₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 0) = 0 := by rw [hv₁]; simp (disch := decide) only [xset_same, xor_self']
  have hx1₁ : xsOf Y₁.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by rw [hv₁]; simp (disch := decide) only [xset_ne, hx1]
  obtain ⟨A, hax₁⟩ : ∃ A, Y₁.cpu.gpr.rax = A := ⟨_, rfl⟩
  rw [hax₁] at hAn
  have hA64 : A.toNat % 64 = 0 := by omega
  -- the 64 bytes from `A`, on `p`'s page
  have hftA : ∀ k < 64, Foot F.data (Addr.add Y₁.cpu.gpr.rax k) := fun k hk => by
    rw [hax₁]
    have hk' : (Addr.add A k).toNat = A.toNat + k := add_toNat64 hA64 hk
    apply hft <;> rw [hk'] <;> omega
  -- `movdqu xmm5, [rax]`, `movdqa xmm6, xmm5`, `movdqu xmm4, [rax + 16]`
  refine c.s_blkV hin (b571 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16a hftA (q := 0) (by omega)) (fun h => nomatch h)
    (wpV_v0 (wpV_v (foot16a hftA (q := 16) (by omega)) (fun h => nomatch h) (wpV_nil ?_)))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ _ hv₂
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hv₂ hx0₁ hx1₁
  simp (disch := decide) only [eaB, get0, hax₁, xset_same] at hv₂
  have hg₂' : Y₂.cpu.gpr = Y₁.cpu.gpr := by simp only [hg₂]
  have hx0₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 0) = 0 := by rw [hv₂]; simp (disch := decide) only [xset_ne, hx0₁]
  have hx1₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by rw [hv₂]; simp (disch := decide) only [xset_ne, hx1₁]
  have hx4₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 4) = rd16 V (A + BitVec.ofNat 64 16) := by
    rw [hv₂]; simp (disch := decide) only [xset_same] <;> rfl
  have hx5₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 5) = rd16 V (A + BitVec.ofNat 64 0) := by
    rw [hv₂]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx6₂ : xsOf Y₂.cpu.vec.zmm (xmmOf 6) = rd16 V (A + BitVec.ofNat 64 0) := by
    rw [hv₂]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  -- `pcmpeqb xmm5, xmm1`, `pcmpeqb xmm6, xmm0`, `movdqu xmm3, [rax + 32]`, `pmovmskb esi, xmm6`,
  -- `movdqa xmm6, xmm4`, `movdqu xmm2, [rax + 48]`
  refine c.s_blkV hin (b584 prof) hK₂ hA₂ hr₂ ?_
  rw [hg₂']
  refine wpV_v0 (wpV_v0 (wpV_v (foot16a hftA (q := 32) (by omega)) (fun h => nomatch h)
    (wpV_v0 (wpV_v0 (wpV_v (foot16a hftA (q := 48) (by omega)) (fun h => nomatch h) (wpV_nil ?_))))))
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃ _ hv₃
  simp (disch := decide) only [eaB, get0, hax₁, set_rsi, xset_same, xset_ne, hx0₂, hx1₂, hx4₂, hx5₂, hx6₂] at hg₃ hv₃
  have hkp₃ : KpR g₀ Y₃.cpu.gpr := by simp only [KpR, hg₃]; exact hkp₁
  have hdi₃ : Y₃.cpu.gpr.rdi = g₀.rdi := by simp only [hg₃]; exact hdi₁
  have hax₃ : Y₃.cpu.gpr.rax = A := by simp only [hg₃]
  have hsi₃ : ∀ i, Y₃.cpu.gpr.rsi.getLsbD i = (decide (i < 16) && Fb V A 0 i) := by
    simp only [hg₃]; exact bits64 fun i => zbit' V A 0 i
  have hx0₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 0) = 0 := by rw [hv₃]; simp (disch := decide) only [xset_ne, hx0₂]
  have hx1₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by rw [hv₃]; simp (disch := decide) only [xset_ne, hx1₂]
  have hx2₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 2) = rd16 V (A + BitVec.ofNat 64 48) := by
    rw [hv₃]; simp (disch := decide) only [xset_same] <;> rfl
  have hx3₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 3) = rd16 V (A + BitVec.ofNat 64 32) := by
    rw [hv₃]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx4₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 4) = rd16 V (A + BitVec.ofNat 64 16) := by
    rw [hv₃]; simp (disch := decide) only [xset_ne, hx4₂]
  have hx5₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 5) = peqb (rd16 V (A + BitVec.ofNat 64 0)) (Bc g₀.rsi) := by
    rw [hv₃]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx6₃ : xsOf Y₃.cpu.vec.zmm (xmmOf 6) = rd16 V (A + BitVec.ofNat 64 16) := by
    rw [hv₃]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  -- `pcmpeqb xmm4, xmm1`, `pcmpeqb xmm6, xmm0`, `pmovmskb edx, xmm6`, `movdqa xmm6, xmm3`, `pcmpeqb xmm3, xmm1`,
  -- `pcmpeqb xmm6, xmm0`
  refine c.s_blkV hin (b610 prof) hK₃ hA₃ hr₃ ?_
  refine wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_nil ?_))))))
  intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ hv₄
  generalize hxd₄ : xsOf Y₃.cpu.vec.zmm = x₄ at hg₄ hv₄ hx0₃ hx1₃ hx2₃ hx3₃ hx4₃ hx5₃ hx6₃
  simp (disch := decide) only [set_rdx, xset_same, xset_ne, hx0₃, hx1₃, hx3₃, hx4₃, hx6₃] at hg₄ hv₄
  have hkp₄ : KpR g₀ Y₄.cpu.gpr := by simp only [KpR, hg₄]; exact hkp₃
  have hdi₄ : Y₄.cpu.gpr.rdi = g₀.rdi := by simp only [hg₄]; exact hdi₃
  have hax₄ : Y₄.cpu.gpr.rax = A := by simp only [hg₄]; exact hax₃
  have hsi₄ : ∀ i, Y₄.cpu.gpr.rsi.getLsbD i = (decide (i < 16) && Fb V A 0 i) := by simp only [hg₄]; exact hsi₃
  have hdx₄ : ∀ i, Y₄.cpu.gpr.rdx.getLsbD i = (decide (i < 16) && Fb V A 0 (i + 16)) := by
    simp only [hg₄]; exact bits64 fun i => zbit' V A 16 i
  have hx0₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 0) = 0 := by rw [hv₄]; simp (disch := decide) only [xset_ne, hx0₃]
  have hx1₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by rw [hv₄]; simp (disch := decide) only [xset_ne, hx1₃]
  have hx2₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 2) = rd16 V (A + BitVec.ofNat 64 48) := by
    rw [hv₄]; simp (disch := decide) only [xset_ne, hx2₃]
  have hx3₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 3) = peqb (rd16 V (A + BitVec.ofNat 64 32)) (Bc g₀.rsi) := by
    rw [hv₄]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx4₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 4) = peqb (rd16 V (A + BitVec.ofNat 64 16)) (Bc g₀.rsi) := by
    rw [hv₄]; simp (disch := decide) only [xset_same, xset_ne] <;> rfl
  have hx5₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 5) = peqb (rd16 V (A + BitVec.ofNat 64 0)) (Bc g₀.rsi) := by
    rw [hv₄]; simp (disch := decide) only [xset_ne, hx5₃]
  have hx6₄ : xsOf Y₄.cpu.vec.zmm (xmmOf 6) = peqb (rd16 V (A + BitVec.ofNat 64 32)) 0 := by
    rw [hv₄]; simp (disch := decide) only [xset_same] <;> rfl
  -- `pcmpeqb xmm0, xmm2`, `shl rdx, 16`, `pmovmskb r9d, xmm3`, `pmovmskb r8d, xmm6`, `pmovmskb ecx, xmm0`,
  -- `shl r9, 32`
  refine c.s_blkV hin (b634 prof) hK₄ hA₄ hr₄ ?_
  refine wpV_v0 (wpV_reg fun _ _ => wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_))))
  intro Y₅ t₅ hK₅ hA₅ hr₅ hg₅ _ hv₅
  generalize hxd₅ : xsOf Y₄.cpu.vec.zmm = x₅ at hg₅ hv₅ hx0₄ hx1₄ hx2₄ hx3₄ hx4₄ hx5₄ hx6₄
  simp (disch := decide) only [wr, gv, Src.val, set_rdx, set_r8, set_r9', set_rcx, get2, get9', BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, xset_same, xset_ne, hx0₄, hx2₄, hx3₄, hx6₄] at hg₅ hv₅
  have hkp₅ : KpR g₀ Y₅.cpu.gpr := by simp only [KpR, hg₅]; exact hkp₄
  have hdi₅ : Y₅.cpu.gpr.rdi = g₀.rdi := by simp only [hg₅]; exact hdi₄
  have hax₅ : Y₅.cpu.gpr.rax = A := by simp only [hg₅]; exact hax₄
  have hsi₅ : ∀ i, Y₅.cpu.gpr.rsi.getLsbD i = (decide (i < 16) && Fb V A 0 i) := by simp only [hg₅]; exact hsi₄
  have hdx₅ : R 16 32 (Fb V A 0) Y₅.cpu.gpr.rdx := by simp only [hg₅]; exact R_shl hdx₄ (by omega)
  have hr9₅ : R 32 48 (Fb V A (g₀.rsi.setWidth 8)) Y₅.cpu.gpr.r9 := by
    simp only [hg₅]; exact R_m (fun i => cbit' V A 32 i g₀.rsi) (by omega)
  have hr8₅ : ∀ i, Y₅.cpu.gpr.r8.getLsbD i = (decide (i < 16) && Fb V A 0 (i + 32)) := by
    simp only [hg₅]; exact bits64 fun i => zbit' V A 32 i
  have hcx₅ : ∀ i, Y₅.cpu.gpr.rcx.getLsbD i = (decide (i < 16) && Fb V A 0 (i + 48)) := by
    simp only [hg₅]; exact bits64 fun i => zbit V A 48 i
  have hx1₅ : xsOf Y₅.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by rw [hv₅]; simp (disch := decide) only [xset_ne, hx1₄]
  have hx2₅ : xsOf Y₅.cpu.vec.zmm (xmmOf 2) = rd16 V (A + BitVec.ofNat 64 48) := by
    rw [hv₅]; simp (disch := decide) only [xset_ne, hx2₄]
  have hx4₅ : xsOf Y₅.cpu.vec.zmm (xmmOf 4) = peqb (rd16 V (A + BitVec.ofNat 64 16)) (Bc g₀.rsi) := by
    rw [hv₅]; simp (disch := decide) only [xset_ne, hx4₄]
  have hx5₅ : xsOf Y₅.cpu.vec.zmm (xmmOf 5) = peqb (rd16 V (A + BitVec.ofNat 64 0)) (Bc g₀.rsi) := by
    rw [hv₅]; simp (disch := decide) only [xset_ne, hx5₄]
  -- `shl r8, 32`, `pcmpeqb xmm2, xmm1`, `or rdx, r8`, `shl rcx, 48`, `pmovmskb r8d, xmm5`, `or rdx, rsi`
  refine c.s_blkV hin (b660 prof) hK₅ hA₅ hr₅ ?_
  refine wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_))
  intro Y₆ t₆ hK₆ hA₆ hr₆ hg₆ _ hv₆
  generalize hxd₆ : xsOf Y₅.cpu.vec.zmm = x₆ at hg₆ hv₆ hx1₅ hx2₅ hx4₅ hx5₅
  simp (disch := decide) only [wr, gv, Src.val, set_rdx, set_r8, set_rcx, get1, get2, get6, get8,
    BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, xset_ne, hx1₅, hx2₅,
    hx5₅] at hg₆ hv₆
  have hkp₆ : KpR g₀ Y₆.cpu.gpr := by simp only [KpR, hg₆]; exact hkp₅
  have hdi₆ : Y₆.cpu.gpr.rdi = g₀.rdi := by simp only [hg₆]; exact hdi₅
  have hax₆ : Y₆.cpu.gpr.rax = A := by simp only [hg₆]; exact hax₅
  have hr9₆ : R 32 48 (Fb V A (g₀.rsi.setWidth 8)) Y₆.cpu.gpr.r9 := by simp only [hg₆]; exact hr9₅
  have hdx₆ : R 0 48 (Fb V A 0) Y₆.cpu.gpr.rdx := by
    simp only [hg₆]
    exact R_or' (R_or hdx₅ (R_shl hr8₅ (by omega)) (by omega) (by omega)) (R_low hsi₅) (by omega) (by omega)
  have hcx₆ : R 48 64 (Fb V A 0) Y₆.cpu.gpr.rcx := by simp only [hg₆]; exact R_shl hcx₅ (by omega)
  have hr8₆ : ∀ i, Y₆.cpu.gpr.r8.getLsbD i = (decide (i < 16) && Fb V A (g₀.rsi.setWidth 8) i) := by
    simp only [hg₆]; exact bits64 fun i => cbit' V A 0 i g₀.rsi
  have hx2₆ : xsOf Y₆.cpu.vec.zmm (xmmOf 2) = peqb (rd16 V (A + BitVec.ofNat 64 48)) (Bc g₀.rsi) := by
    rw [hv₆]; simp (disch := decide) only [xset_same] <;> rfl
  have hx4₆ : xsOf Y₆.cpu.vec.zmm (xmmOf 4) = peqb (rd16 V (A + BitVec.ofNat 64 16)) (Bc g₀.rsi) := by
    rw [hv₆]; simp (disch := decide) only [xset_ne, hx4₅]
  -- `pmovmskb esi, xmm4`, `or rdx, rcx`, `pmovmskb ecx, xmm2`, `shl rsi, 16`, `shl rcx, 48`, `or rsi, r9`
  refine c.s_blkV hin (b683 prof) hK₆ hA₆ hr₆ ?_
  refine wpV_v0 (wpV_reg fun _ _ => wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_))
  intro Y₇ t₇ hK₇ hA₇ hr₇ hg₇ _ hv₇
  simp only [wr, gv, Src.val, set_rdx, set_rsi, set_rcx, get1, get2, get6, get9', BitVec.setWidth_eq,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hx2₆, hx4₆] at hg₇
  have hkp₇ : KpR g₀ Y₇.cpu.gpr := by simp only [KpR, hg₇]; exact hkp₆
  have hdi₇ : Y₇.cpu.gpr.rdi = g₀.rdi := by simp only [hg₇]; exact hdi₆
  have hax₇ : Y₇.cpu.gpr.rax = A := by simp only [hg₇]; exact hax₆
  have hr8₇ : ∀ i, Y₇.cpu.gpr.r8.getLsbD i = (decide (i < 16) && Fb V A (g₀.rsi.setWidth 8) i) := by
    simp only [hg₇]; exact hr8₆
  have hdx₇ : R 0 64 (Fb V A 0) Y₇.cpu.gpr.rdx := by
    simp only [hg₇]; exact R_or hdx₆ hcx₆ (by omega) (by omega)
  have hsi₇ : R 16 48 (Fb V A (g₀.rsi.setWidth 8)) Y₇.cpu.gpr.rsi := by
    simp only [hg₇]; exact R_or (R_m (fun i => cbit' V A 16 i g₀.rsi) (by omega)) hr9₆ (by omega) (by omega)
  have hcx₇ : R 48 64 (Fb V A (g₀.rsi.setWidth 8)) Y₇.cpu.gpr.rcx := by
    simp only [hg₇]; exact R_m (fun i => cbit' V A 48 i g₀.rsi) (by omega)
  -- `or rsi, r8`, `or rsi, rcx`, `mov ecx, edi`, `sub ecx, eax`, `shr rdx, cl`, `shr rsi, cl`
  refine c.s_blkV hin (b705 prof) hK₇ hA₇ hr₇ ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
    wpV_reg fun _ _ => wpV_nil ?_
  intro Y₈ t₈ hK₈ hA₈ hr₈ hg₈ _ hv₈
  simp only [wr, gv, Src.val, set_rdx, set_rsi, set_rcx, get0, get1, get2, get6, get7, get8, BitVec.setWidth_eq,
    subR_eq] at hg₈
  have hkp₈ : KpR g₀ Y₈.cpu.gpr := by simp only [KpR, hg₈]; exact hkp₇
  have hdi₈ : Y₈.cpu.gpr.rdi = g₀.rdi := by simp only [hg₈]; exact hdi₇
  -- the shift: `p - A`
  have hcl : (Y₈.cpu.gpr.rcx.setWidth 8).toNat % 64 = g₀.rdi.toNat - A.toNat := by
    simp only [hg₈, hax₇, hdi₇]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, Nat.reducePow, hAn]
    omega
  have hsR : R 0 64 (Fb V A (g₀.rsi.setWidth 8)) ((Y₇.cpu.gpr.rsi ||| Y₇.cpu.gpr.r8) ||| Y₇.cpu.gpr.rcx) :=
    R_or (R_or' hsi₇ (R_low hr8₇) (by omega) (by omega)) hcx₇ (by omega) (by omega)
  have hdx₈ : Y₈.cpu.gpr.rdx = Y₇.cpu.gpr.rdx >>> ((Y₈.cpu.gpr.rcx.setWidth 8).toNat % 64) := by
    simp only [hg₈]
  have hsi₈ : Y₈.cpu.gpr.rsi =
      ((Y₇.cpu.gpr.rsi ||| Y₇.cpu.gpr.r8) ||| Y₇.cpu.gpr.rcx) >>> ((Y₈.cpu.gpr.rcx.setWidth 8).toNat % 64) := by
    simp only [hg₈]
  rw [hcl] at hdx₈ hsi₈
  have hs : A.toNat + (g₀.rdi.toNat - A.toNat) = g₀.rdi.toNat := by omega
  have hZ : ∀ i, Y₈.cpu.gpr.rdx.getLsbD i = (decide (i < 64 - (g₀.rdi.toNat - A.toNat)) && Fb V g₀.rdi 0 i) :=
    fun i => by rw [hdx₈]; exact shr_bits hdx₇ hs i
  have hM : ∀ i, Y₈.cpu.gpr.rsi.getLsbD i =
      (decide (i < 64 - (g₀.rdi.toNat - A.toNat)) && Fb V g₀.rdi (g₀.rsi.setWidth 8) i) :=
    fun i => by rw [hsi₈]; exact shr_bits hsR hs i
  have hx1₈ : xsOf Y₈.cpu.vec.zmm (xmmOf 1) = Bc g₀.rsi := by
    rw [hv₈, hv₇, hv₆]; simp (disch := decide) only [xset_ne, hx1₅]
  -- `test rdx, rdx`, `je +256`
  refine c.s_blkV hin (b721 prof) hK₈ hA₈ hr₈ ?_
  refine wpV_reg fun fl hP => wpV_nil ?_
  intro Y₉ t₉ hK₉ hA₉ hr₉ hg₉ hf₉ hv₉
  simp only [gv, Src.val, get2, BitVec.setWidth_eq, BitVec.and_self] at hP
  have hc := cond4_mask hP
  have hg₉' : Y₉.cpu.gpr = Y₈.cpu.gpr := by simp only [hg₉]
  refine c.s_jccV hK₉ hA₉ hin (by rw [sr2_length]; omega) hr₉ (d724 prof.feat) (tgt := 256) rfl
    (by rw [sr2_length]; omega) ?_ ?_
  · -- no 0 up to `A + 64`: `from256E`
    intro htk Y₁₀ t₁₀ hK₁₀ hA₁₀ ⟨hr₁₀, hg₁₀, hv₁₀⟩
    rw [hf₉, hc] at htk
    have h0 := eq_of_beq htk
    have hEn : 64 - (g₀.rdi.toNat - A.toNat) ≤ n := Classical.byContradiction fun h => by
      have hb := hZ n
      rw [h0, getLsbD_zero', decide_eq_true (show n < 64 - (g₀.rdi.toNat - A.toNat) by omega), Fb, hz] at hb
      exact absurd hb (by decide)
    exact from256E c hin hov hnz hz hch hft hR Y₁₀ t₁₀ hK₁₀ hA₁₀ hr₁₀ (by rw [hg₁₀, hg₉']; exact hkp₈)
      (by rw [hg₁₀, hg₉']; exact hdi₈) _ (by rw [hg₁₀, hg₉']; exact hM)
      (by rw [hv₁₀, hv₉]; exact hx1₈) hEn (by omega) (by omega)
  · -- a 0 before `A + 64`: the matches before it
    intro hfa Y₁₀ t₁₀ hK₁₀ hA₁₀ ⟨hr₁₀, hg₁₀, _⟩
    rw [hf₉, hc] at hfa
    have hne := ne_of_beq_false hfa
    have hnE : n < 64 - (g₀.rdi.toNat - A.toNat) := Classical.byContradiction fun h => hne (by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [hZ, getLsbD_zero', Fb]
      by_cases hiE : i < 64 - (g₀.rdi.toNat - A.toNat)
      · rw [decide_eq_false (hnz i (by omega)), Bool.and_false]
      · rw [decide_eq_false hiE, Bool.false_and])
    have h1 : Y₈.cpu.gpr.rdx.getLsbD n = true := by
      rw [hZ, decide_eq_true hnE, Fb, hz]
      rfl
    have h0 : ∀ i < n, Y₈.cpu.gpr.rdx.getLsbD i = false := fun i hi => by
      rw [hZ, Fb, decide_eq_false (hnz i hi), Bool.and_false]
    have hZ0 : Y₈.cpu.gpr.rdx.toNat ≠ 0 := fun h => by
      rw [← BitVec.testBit_toNat, h, Nat.zero_testBit] at h1
      exact Bool.false_ne_true h1
    have hY := toNat_pred64 Y₈.cpu.gpr.rdx hZ0
    -- `lea rax, [rdx - 1]`, `xor rax, rdx`, `and rsi, rax`
    refine c.s_blkV hin (b730 prof) hK₁₀ hA₁₀ hr₁₀ ?_
    rw [hg₁₀, hg₉']
    refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun fl₁ hP₁ => wpV_nil ?_
    intro Y₁₁ t₁₁ hK₁₁ hA₁₁ hr₁₁ hg₁₁ hf₁₁ _
    simp only [wr, gv, Src.val, eaG, optV, set_rax, set_rsi, get0, get2, get6, BitVec.setWidth_eq, z_mul64,
      add_z64] at hg₁₁ hP₁
    have hkp₁₁ : KpR g₀ Y₁₁.cpu.gpr := by simp only [KpR, hg₁₁]; exact hkp₈
    have hsi₁₁ : Y₁₁.cpu.gpr.rsi =
        Y₈.cpu.gpr.rsi &&& ((Y₈.cpu.gpr.rdx + BitVec.ofNat 64 18446744073709551615) ^^^ Y₈.cpu.gpr.rdx) := by
      simp only [hg₁₁] <;> rfl
    have hKb : ∀ i, Y₁₁.cpu.gpr.rsi.getLsbD i =
        (decide (i < n) && decide (V (Addr.add g₀.rdi i) = g₀.rsi.setWidth 8)) := by
      intro i
      rw [hsi₁₁, BitVec.getLsbD_and, getLsbD_blsmsk h1 h0 hY i, hM, Fb]
      by_cases hi : i < n
      · rw [decide_eq_true hi, decide_eq_true (show i ≤ n by omega),
          decide_eq_true (show i < 64 - (g₀.rdi.toNat - A.toNat) by omega)]
        simp only [Bool.true_and, Bool.and_true]
      · rw [decide_eq_false hi]
        by_cases hin' : i = n
        · rw [hin', hz, decide_eq_false (fun h : (0 : Byte) = g₀.rsi.setWidth 8 => hch h.symm)]
          simp only [Bool.and_false, Bool.false_and]
        · rw [decide_eq_false (show ¬ i ≤ n by omega)]
          simp only [Bool.and_false, Bool.false_and]
    have hS := rok_mask (by omega) hKb
    have hc₁ : fl₁.cond 4 = (Y₁₁.cpu.gpr.rsi == 0) := by rw [cond4_mask hP₁]; simp only [hg₁₁]
    refine c.s_jccV hK₁₁ hA₁₁ hin (by rw [sr2_length]; omega) hr₁₁ (d740 prof.feat) (tgt := 544) rfl
      (by rw [sr2_length]; omega) ?_ ?_
    · -- none before the 0
      intro htk Y₁₂ t₁₂ hK₁₂ hA₁₂ ⟨hr₁₂, hg₁₂, _⟩
      rw [hf₁₁, hc₁] at htk
      exact ret544 c hin hK₁₂ hA₁₂ hr₁₂ (by rw [hg₁₂]; exact hkp₁₁) (hS.1.1 (eq_of_beq htk)) hR
    · -- the last: `bsr rax, rsi`, `add rax, rdi`, `ret`
      intro hfa' Y₁₂ t₁₂ hK₁₂ hA₁₂ ⟨hr₁₂, hg₁₂, _⟩
      rw [hf₁₁, hc₁] at hfa'
      have hne' : Y₁₁.cpu.gpr.rsi ≠ 0 := ne_of_beq_false hfa'
      refine c.s_bsr64 hK₁₂ hA₁₂ hin (by rw [sr2_length]; omega) hr₁₂ (d746 prof.feat)
        (by simp only [rv, get6, BitVec.setWidth_eq, hg₁₂]; exact hne') ?_
      rintro Y₁₃ t₁₃ hK₁₃ hA₁₃ ⟨hr₁₃, hg₁₃⟩
      simp only [rv, get6, BitVec.setWidth_eq, set_rax, hg₁₂] at hg₁₃
      refine c.s_blkV hin (b750 prof) hK₁₃ hA₁₃ hr₁₃ ?_
      refine wpV_reg fun _ _ => wpV_nil ?_
      intro Y₁₄ t₁₄ hK₁₄ hA₁₄ hr₁₄ hg₁₄ _ _
      simp only [wr, gv, Src.val, set_rax, get0, get7, BitVec.setWidth_eq] at hg₁₄
      simp only [hg₁₃] at hg₁₄
      have hkp₁₄ : KpR g₀ Y₁₄.cpu.gpr := by simp only [KpR, hg₁₄]; exact hkp₁₁
      have hax₁₄ : Y₁₄.cpu.gpr.rax = Addr.add g₀.rdi (highestSetBit Y₁₁.cpu.gpr.rsi) := by
        simp only [hg₁₄]
        rw [show Y₁₁.cpu.gpr.rdi = g₀.rdi by simp only [hg₁₁]; exact hdi₈]
        exact addR_addr _ _
      exact ret_atR c hin (by rw [sr2_length]; omega) (d753 prof.feat) hK₁₄ hA₁₄ hr₁₄ hkp₁₄
        (by rw [hax₁₄]; exact hS.2 hne') hR

end FV7z.Strrchr
