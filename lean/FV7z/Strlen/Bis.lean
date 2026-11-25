import FV7z.Strlen.Entry
/-! TRIAGE ONLY: `pathB` cut off at five points. -/
namespace FV7z.Strlen
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e' : Addr} {V : Addr → Byte}

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB_s1 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
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
  refine c.s_blkV hin (b148 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl)
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl)
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl)
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_))))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hg₂ hP hx0 hx1 hx2 hx3
  simp only [wr, gv, Src.val, eaB, set_rax, set_rcx, set_rdx, set_rsi, set_r8, get0, get1, get2, get6, get7,
    get8] at hg₂ hP
  sorry

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB_s2 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
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
  refine c.s_blkV hin (b148 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl)
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl)
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl)
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_))))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hg₂ hP hx0 hx1 hx2 hx3
  simp only [wr, gv, Src.val, eaB, set_rax, set_rcx, set_rdx, set_rsi, set_r8, get0, get1, get2, get6, get7,
    get8] at hg₂ hP
  simp (disch := decide) only [xset_same, xset_ne] at hg₂ hP
  sorry

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB_s3 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
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
  refine c.s_blkV hin (b148 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl)
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl)
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl)
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_))))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hg₂ hP hx0 hx1 hx2 hx3
  simp only [wr, gv, Src.val, eaB, set_rax, set_rcx, set_rdx, set_rsi, set_r8, get0, get1, get2, get6, get7,
    get8] at hg₂ hP
  simp (disch := decide) only [xset_same, xset_ne] at hg₂ hP
  simp only [hx0, hx1, hx2, hx3] at hg₂ hP
  sorry

set_option maxHeartbeats 4000000 in
/-- From `+144`, `rax = p`, `xmm0`–`xmm3` 0. -/
theorem pathB_s4 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e' sl2) {X : State} {t : Nat} {g₀ : Gprs} {n : Nat}
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
  refine c.s_blkV hin (b148 prof) hK₁ hA₁ hr₁ ?_
  refine wpV_v (foot16 hF (d := 0) (by omega)) (hal 0 rfl)
    (wpV_v (foot16 hF (d := 16) (by omega)) (hal 16 rfl)
    (wpV_v (foot16 hF (d := 32) (by omega)) (hal 32 rfl)
    (wpV_v (foot16 hF (d := 48) (by omega)) (hal 48 rfl)
    (wpV_v0 (wpV_v0 (wpV_v0 (wpV_v0 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ =>
      wpV_reg fun _ _ => wpV_reg fun fl hP => wpV_nil ?_))))))))
  intro Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂ _
  generalize hxd : xsOf Y₁.cpu.vec.zmm = x at hg₂ hP hx0 hx1 hx2 hx3
  simp only [wr, gv, Src.val, eaB, set_rax, set_rcx, set_rdx, set_rsi, set_r8, get0, get1, get2, get6, get7,
    get8] at hg₂ hP
  simp (disch := decide) only [xset_same, xset_ne] at hg₂ hP
  simp only [hx0, hx1, hx2, hx3] at hg₂ hP
  simp only [BitVec.setWidth_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, BitVec.and_self] at hg₂ hP
  sorry

end FV7z.Strlen
