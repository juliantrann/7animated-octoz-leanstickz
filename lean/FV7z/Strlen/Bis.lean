import FV7z.Strlen.Entry
/-! TRIAGE ONLY: `pathB` with its block `+148`–`+221` in three. -/
namespace FV7z.Strlen
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

/-- The stretch from `148` to `184`: the four masks. -/
def o148a : List VOp := [
  VOp.pcmpeqb_m 0 0 0,
  VOp.pcmpeqb_m 1 0 16,
  VOp.pcmpeqb_m 2 0 32,
  VOp.pcmpeqb_m 3 0 48,
  VOp.pmovmskb 6 0,
  VOp.pmovmskb 2 1,
  VOp.pmovmskb 8 2,
  VOp.pmovmskb 1 3]

theorem b148a (prof : Profile) : BlkV prof sl2 148 184 o148a :=
  .cons (d148 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d152 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d157 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d162 _) (VOpI.pcmpeqb_m) (by decide) <|
  .cons (d167 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d171 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d175 _) (VOpI.pmovmskb) (by decide) <|
  .cons (d180 _) (VOpI.pmovmskb) (by decide) <|
  .nil 184

/-- The stretch from `184` to `202`. -/
def o184 : List VOp := [
  VOp.op (Op.shl64 2 (.i 16)),
  VOp.op (Op.shl64 1 (.i 16)),
  VOp.op (Op.or 64 2 (.r 6)),
  VOp.op (Op.or 64 1 (.r 8)),
  VOp.op (Op.shl64 1 (.i 32))]

theorem b184 (prof : Profile) : BlkV prof sl2 184 202 o184 :=
  .cons (d184 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d188 _) (OpI.shl64 (.i 16)) (by decide) <|
  .cons (d192 _) (OpI.or (.r 6) (.inr rfl)) (by decide) <|
  .cons (d195 _) (OpI.or (.r 8) (.inr rfl)) (by decide) <|
  .cons (d198 _) (OpI.shl64 (.i 32)) (by decide) <|
  .nil 202

/-- The stretch from `202` to `221`. -/
def o202 : List VOp := [
  VOp.op (Op.or 64 2 (.r 1)),
  VOp.op (Op.mov 64 1 (.r 7)),
  VOp.op (Op.xor 64 1 (.r 0)),
  VOp.op (Op.and 64 0 (.i 18446744073709551552)),
  VOp.op (Op.sar64 2 (.r 1)),
  VOp.op (Op.test 64 2 (.r 2))]

theorem b202 (prof : Profile) : BlkV prof sl2 202 221 o202 :=
  .cons (d202 _) (OpI.or (.r 1) (.inr rfl)) (by decide) <|
  .cons (d205 _) (OpI.mov (.r 7) (.inr rfl)) (by decide) <|
  .cons (d208 _) (OpI.xor (.r 0) (.inr rfl)) (by decide) <|
  .cons (d211 _) (OpI.and (.i 18446744073709551552) (.inr rfl)) (by decide) <|
  .cons (d215 _) (OpI.sar64 (.r 1)) (by decide) <|
  .cons (d218 _) (OpI.test (.r 2) (.inr rfl)) (by decide) <|
  .nil 221

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB_split (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e'.add 144)
    (hax : X.cpu.gpr.rax = g₀.rdi) (hkp : Kp g₀ X.cpu.gpr) (hx : X4 (xsOf X.cpu.vec.zmm))
    (hov : g₀.rdi.toNat + n < 2 ^ 64)
    (hnz : ∀ k < n, V (Addr.add g₀.rdi k) ≠ 0) (hz : V (Addr.add g₀.rdi n) = 0)
    (hft : ∀ x : Addr, g₀.rdi.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (g₀.rdi.toNat + n) / 4096 →
      Foot F.data x)
    (hR : Ret prof F Wl L s₀ o gev gP gE V g₀ n) : GoG prof L o gev gP gE X t := by
  obtain ⟨hx0, hx1, hx2, hx3⟩ := hx
  -- `and rax, -64`
  refine c.s_blkV hin (b144 prof) hK hA hrip ?_
  refine wpV_reg fun _ _ => wpV_nil ?_
  intro Y₁ t₁ hK₁ hA₁ hr₁ hg₁ _ hv₁
  simp only [wr, gv, Src.val, set_rax, get0, BitVec.setWidth_eq] at hg₁
  have hB₁ : Y₁.cpu.gpr.rax.toNat = g₀.rdi.toNat / 64 * 64 := by simp only [hg₁]; rw [hax]; exact and_m64 _
  have hkp₁ : Kp g₀ Y₁.cpu.gpr := by simp only [Kp, hg₁]; exact hkp
  have hdi₁ : Y₁.cpu.gpr.rdi = g₀.rdi := hkp₁.1
  rw [← hv₁] at hx0 hx1 hx2 hx3
  -- the block's four masks joined, shifted right by `p - B`
  have hF := foot64 hft (B := Y₁.cpu.gpr.rax) (by omega) (by omega) (by omega)
  have hal : ∀ d, d % 16 = 0 → true = true → (Y₁.cpu.gpr.rax + BitVec.ofNat 64 d).toNat % 16 = 0 :=
    fun d h1 _ => al16 (by omega) h1
  refine c.s_blkV hin (b148a prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl)
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl)
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl)
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_nil ?_))))))))
  intro Ya ta hKa hAa hra hga _ _
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hga hx0 hx1 hx2 hx3
  simp (disch := decide) only [eaB, gv, set_rcx, set_rdx, set_rsi, set_r8, get0, xset_same, xset_ne,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, hx0, hx1, hx2, hx3] at hga
  -- `shl rdx, 16`, `shl rcx, 16`, `or rdx, rsi`, `or rcx, r8`, `shl rcx, 32`
  refine c.s_blkV hin (b184 prof) hKa hAa hra ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_
  intro Yb tb hKb hAb hrb hgb _ _
  simp only [wr, gv, Src.val, set_rcx, set_rdx, get1, get2, get6, get8, BitVec.setWidth_eq] at hgb
  simp only [hga] at hgb
  -- `or rdx, rcx`, `mov rcx, rdi`, `xor rcx, rax`, `and rax, -64`, `sar rdx, cl`, `test rdx, rdx`
  refine c.s_blkV hin (b202 prof) hKb hAb hrb ?_
  refine wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
    wpV_reg fun fl hP => wpV_nil ?_
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  simp only [wr, gv, Src.val, set_rax, set_rcx, set_rdx, get0, get1, get2, get7, BitVec.setWidth_eq] at hg₂ hP
  simp only [hgb] at hg₂ hP
  simp (disch := decide) only [BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    BitVec.and_self] at hg₂ hP
  have hkp₂ : Kp g₀ Y₂.cpu.gpr := by simp only [Kp, hg₂]; exact hkp₁
  generalize hBd : Y₁.cpu.gpr.rax = B at hg₂ hP hB₁
  have hax₂ : Y₂.cpu.gpr.rax = B := by simp only [hg₂]; exact and_low (by omega)
  have hS : (Y₂.cpu.gpr.rdx = 0 ↔ B.toNat + 64 ≤ g₀.rdi.toNat + n) ∧
      (g₀.rdi.toNat + n < B.toNat + 64 → lowestSetBit Y₂.cpu.gpr.rdx = n) := by
    simp only [hg₂]
    exact sar_spec (fun i hi _ => by
        rw [getLsbD_join _ _ _ _ (fun i => decide (V (Addr.add B i) = 0)) (zbit V B 0) (zbit V B 16) (zbit V B 32)
          (zbit V B 48) hi])
      (by rw [hdi₁, cnt64 hB₁]; omega) (by omega) (by omega) hnz hz
  have hc : fl.cond 4 = (Y₂.cpu.gpr.rdx == 0) := by rw [cond4_mask hP]; simp only [hg₂]
  refine c.s_jccV hK₂ hA₂ hin (by rw [sl2_length]; omega) hr₂ (d221 prof.feat) (tgt := 240) rfl
    (by rw [sl2_length]; omega) ?_ ?_
  · -- none: `xmm1`–`xmm3` zeroed, the loop from `B`
    intro htk Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
    rw [hf₂, hc] at htk
    have hge := hS.1.1 (eq_of_beq htk)
    refine c.s_blkV hin (b240 prof) hK₃ hA₃ hr₃ ?_
    refine wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_nil ?_)))
    intro Y₄ t₄ hK₄ hA₄ hr₄ hg₄ _ hv₄
    have hz₄ : Z3 (xsOf Y₄.cpu.vec.zmm) := by
      rw [hv₄]
      refine ⟨?_, ?_, ?_⟩ <;> simp (disch := decide) only [xset_same, xset_ne, xor_self']
    have hax₄ : Y₄.cpu.gpr.rax = B := by rw [hg₄, hg₃]; exact hax₂
    have hkp₄ : Kp g₀ Y₄.cpu.gpr := by rw [hg₄, hg₃]; exact hkp₂
    exact loop c hin hov hnz hz hft hR _ Y₄ t₄ B (Nat.lt_succ_self _) hK₄ hA₄ hr₄ hax₄ hkp₄ hz₄ (by omega)
      (by omega) hge
  · -- a bit: `bsf rax, rdx`, `ret`
    intro hfa Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
    rw [hf₂, hc] at hfa
    have hne : Y₂.cpu.gpr.rdx ≠ 0 := ne_of_beq_false hfa
    have hlt : g₀.rdi.toNat + n < B.toNat + 64 := Classical.byContradiction fun h => hne (hS.1.2 (by omega))
    have hlow : lowestSetBit (rv Y₃ 64 2) = n := by
      simp only [rv, get2, BitVec.setWidth_eq, hg₃]; exact hS.2 hlt
    refine c.s_bsf64 hK₃ hA₃ hin (by rw [sl2_length]; omega) hr₃ (d223 prof.feat)
      (by simp only [rv, get2, BitVec.setWidth_eq, hg₃]; exact hne) ?_
    rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
    have hkp₄ : Kp g₀ Y₄.cpu.gpr := by simp only [Kp, hg₄, set_rax, hg₃]; exact hkp₂
    have hax₄ : Y₄.cpu.gpr.rax = BitVec.ofNat 64 n := by simp only [hg₄, set_rax, hlow]
    exact ret_at c hin (by rw [sl2_length]; omega) (d227 prof.feat) hK₄ hA₄ hr₄ hkp₄ hax₄ hR

end FV7z.Strlen
