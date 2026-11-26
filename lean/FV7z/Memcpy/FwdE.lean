import FV7z.Memcpy.Fwd
/-!
# `__memmove_sse2_unaligned`: above 128 bytes with `rdi ≤ rsi`, from `498` to the loop (PLAN.md M)

From `498`: five loads (the first 16 bytes of the source into `xmm4`, its last 64 into `xmm5` to `xmm8`),
`r11 = rdi`, `rcx = rdi + rdx - 16`, `r8 = (rdi & 15) - 16`, and `rsi`, `rdi` up and `rdx` down by
`a₀ = 16 - rdi % 16`, so that `rdi` is a multiple of 16. Then `cmp rdx, [rip + d]` against the non-temporal
threshold (`thrA`) and `ja 767`; at or below it the loop at `563` (`loopF`).

- `bP498`, `bP522`, `bP541`, `bP550`: the stretches; `and15_toNat`, `sub_r8`, `add_r8`: the alignment's arithmetic.
- `p498`: to `ret` as `RetC` asks, given what follows from `767` with the same registers (`hNT`).
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The five loads, at `498`. -/
theorem bP498 (prof : Profile) :
    BlkV prof mc2 498 522 [VOp.movups_m 4 6 0, VOp.movups_mi 5 6 2 18446744073709551600,
      VOp.movups_mi 6 6 2 18446744073709551584, VOp.movups_mi 7 6 2 18446744073709551568,
      VOp.movups_mi 8 6 2 18446744073709551552] :=
  .cons (d498 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d501 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide) <|
  .cons (d506 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide) <|
  .cons (d511 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide) <|
  .cons (d516 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide) <| .nil _

/-- `mov r11, rdi`, `lea rcx, [rdi + rdx - 16]`, `mov r8, rdi`, `and r8, 15`, `sub r8, 16`. -/
theorem bP522 (prof : Profile) :
    BlkV prof mc2 522 541 [VOp.op (Op.mov 64 11 (.r 7)), VOp.op (Op.lea 64 1 (some 7) (some 2) 1 18446744073709551600),
      VOp.op (Op.mov 64 8 (.r 7)), VOp.op (Op.and 64 8 (.i 15)), VOp.op (Op.sub 64 8 (.i 16))] :=
  .cons (d522 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d525 _) (OpI.lea (b := some 7) (i := some 2) (sc := 1) (d := 18446744073709551600) (.inr rfl))
    (by rw [mc2_length]; decide) <|
  .cons (d530 _) (OpI.mov (.r 7) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d533 _) (OpI.and (.i 15) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d537 _) (OpI.sub (.i 16) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `sub rsi, r8`, `sub rdi, r8`, `add rdx, r8`. -/
theorem bP541 (prof : Profile) :
    BlkV prof mc2 541 550 [VOp.op (Op.sub 64 6 (.r 8)), VOp.op (Op.sub 64 7 (.r 8)), VOp.op (Op.add 64 2 (.r 8))] :=
  .cons (d541 _) (OpI.sub (.r 8) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d544 _) (OpI.sub (.r 8) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d547 _) (OpI.add (.r 8) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- The address of the non-temporal threshold (`__x86_shared_non_temporal_threshold`) the copy at `e` reads,
`[rip + 1362219]` at `550`. -/
def thrA (e : Addr) : Nat := (Addr.add e 557 + BitVec.ofNat 64 1362219).toNat

/-- `cmp rdx, [rip + 1362219]`, at `e + 550`. -/
theorem bP550 (prof : Profile) (e : Addr) : BlkA prof mc2 e 550 557 [Op.cmpma 64 2 (thrA e)] :=
  .cons (d550 prof.feat)
    (OpIA.cmpm_rip (.inr (.inr rfl)) (by rw [thrA, BitVec.ofNat_toNat, BitVec.setWidth_eq, addr_add_add]))
    (by rw [mc2_length]; decide) (.nil _)

theorem set_r11 (g : Gprs) (v : BitVec 64) : g.set (regOf 11) v = { g with r11 := v } := rfl

theorem and15_toNat (x : Addr) : (x &&& BitVec.ofNat 64 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (BitVec.ofNat 64 15).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- `y - r8`, `r8 = (x & 15) - 16`: `y` and `16 - x % 16`. -/
theorem sub_r8 (y x : Addr) :
    y - ((x &&& BitVec.ofNat 64 15) - BitVec.ofNat 64 16) = Addr.add y (16 - x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have h := and15_toNat x
  have := y.isLt
  have := Nat.mod_lt x.toNat (show 16 > 0 by decide)
  simp only [Addr.add, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

/-- `y + r8`, `r8 = (x & 15) - 16`, `16 ≤ y`: `y` less `16 - x % 16`. -/
theorem add_r8 {y : Addr} (x : Addr) (hy : 16 ≤ y.toNat) :
    (y + ((x &&& BitVec.ofNat 64 15) - BitVec.ofNat 64 16)).toNat = y.toNat - (16 - x.toNat % 16) := by
  have h := and15_toNat x
  have := y.isLt
  have := Nat.mod_lt x.toNat (show 16 > 0 by decide)
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `498`, `128 < rdx`, `rdi ≤ rsi`: the loads and the alignment, then the loop at `563` (`loopF`) or, past
the non-temporal threshold, `767` (`hNT`). -/
theorem p498 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 498)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h128 : 128 < g₀.rdx.toNat) (hds : g₀.rdi.toNat ≤ g₀.rsi.toNat)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r)
    (hNT : ∀ {Y : State} {t' : Nat}, KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e.add 767 →
      LoopR g₀ r (16 - g₀.rdi.toNat % 16) Y.cpu.gpr → TailX V g₀.rsi g₀.rdx.toNat (xsOf Y.cpu.vec.zmm) →
      GoG prof L o gev gP gE Y t') : GoG prof L o gev gP gE X t := by
  -- the five loads
  have hea0 : eaB X.cpu.gpr 6 0 = Addr.add g₀.rsi 0 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 0 = _
    rw [get6, hsi]
    rfl
  have hea5 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551600 = Addr.add g₀.rsi (g₀.rdx.toNat - 16) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rsi g₀.rdx (by decide) (by omega)
  have hea6 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551584 = Addr.add g₀.rsi (g₀.rdx.toNat - 32) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551584 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551584) (k := 32) g₀.rsi g₀.rdx (by decide) (by omega)
  have hea7 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551568 = Addr.add g₀.rsi (g₀.rdx.toNat - 48) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551568 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551568) (k := 48) g₀.rsi g₀.rdx (by decide) (by omega)
  have hea8 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551552 = Addr.add g₀.rsi (g₀.rdx.toNat - 64) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551552 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551552) (k := 64) g₀.rsi g₀.rdx (by decide) (by omega)
  refine c.s_blkV hin (bP498 prof) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m, VOp.movups_mi]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, ?_⟩
  · rw [hea0, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea5, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea6, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea7, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea8, addr_add_add]
    exact hsrc _ (by omega)
  intro Y1 t1 hK1 hA1 hr1 hg1 _ hx1
  rw [hea0, hea5, hea6, hea7, hea8] at hx1
  have hT1 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y1.cpu.vec.zmm) := by
    rw [hx1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide),
        xset_same]
    · rw [xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
    · rw [xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
    · rw [xset_ne _ _ (by decide), xset_same]
    · rw [xset_same]
  -- `r11`, `rcx` and `r8`
  refine c.s_blkV hin (bP522 prof) hK1 hA1 hr1
    (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y2 t2 hK2 hA2 hr2 hg2 _ hx2
  simp only [wr, gv, Src.val, get7, get8, set_r11, set_rcx, set_r8, BitVec.setWidth_eq, subR_eq] at hg2
  have hdi2 : Y2.cpu.gpr.rdi = g₀.rdi := by rw [hg2, hg1]; exact hdi
  have hsi2 : Y2.cpu.gpr.rsi = g₀.rsi := by rw [hg2, hg1]; exact hsi
  have hdx2 : Y2.cpu.gpr.rdx = g₀.rdx := by rw [hg2, hg1]; exact hdx
  have h112 : Y2.cpu.gpr.r11 = g₀.rdi := by rw [hg2, hg1]; exact hdi
  have hkp2 : KpS g₀ Y2.cpu.gpr := by
    have h := hkp
    unfold KpS at h ⊢
    rw [hg2, hg1]
    exact h
  have hax2 : Y2.cpu.gpr.rax = r := by rw [hg2, hg1]; exact hax
  have hcx2 : Y2.cpu.gpr.rcx = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    rw [hg2]
    exact eaG_back (by rw [hg1]; exact hdi) (by rw [hg1]; exact hdx) (k := 16) (by decide) (by omega)
  have hr82 : Y2.cpu.gpr.r8 = (g₀.rdi &&& BitVec.ofNat 64 15) - BitVec.ofNat 64 16 := by
    rw [hg2, hg1, hdi]
  have hT2 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y2.cpu.vec.zmm) := by
    rw [hx2]
    exact hT1
  -- `rsi`, `rdi`, `rdx` by `a₀ = 16 - rdi % 16`
  refine c.s_blkV hin (bP541 prof) hK2 hA2 hr2 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y3 t3 hK3 hA3 hr3 hg3 _ hx3
  simp only [wr, gv, Src.val, get2, get6, get7, get8, set_rsi, set_rdi, set_rdx, BitVec.setWidth_eq, subR_eq,
    addR_eq] at hg3
  have hsi3 : Y3.cpu.gpr.rsi = Addr.add g₀.rsi (16 - g₀.rdi.toNat % 16) := by
    rw [hg3]
    show Y2.cpu.gpr.rsi - Y2.cpu.gpr.r8 = _
    rw [hsi2, hr82]
    exact sub_r8 _ _
  have hdi3 : Y3.cpu.gpr.rdi = Addr.add g₀.rdi (16 - g₀.rdi.toNat % 16) := by
    rw [hg3]
    show Y2.cpu.gpr.rdi - Y2.cpu.gpr.r8 = _
    rw [hdi2, hr82]
    exact sub_r8 _ _
  have hdx3 : Y3.cpu.gpr.rdx.toNat = g₀.rdx.toNat - (16 - g₀.rdi.toNat % 16) := by
    rw [hg3]
    show (Y2.cpu.gpr.rdx + Y2.cpu.gpr.r8).toNat = _
    rw [hdx2, hr82]
    exact add_r8 _ (by omega)
  have hkp3 : KpS g₀ Y3.cpu.gpr := by
    have h := hkp2
    unfold KpS at h ⊢
    rw [hg3]
    exact h
  have hL3 : LoopR g₀ r (16 - g₀.rdi.toNat % 16) Y3.cpu.gpr :=
    ⟨hdi3, hsi3, hdx3, by rw [hg3]; exact hcx2, by rw [hg3]; exact h112, hkp3, by rw [hg3]; exact hax2⟩
  have hT3 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y3.cpu.vec.zmm) := by
    rw [hx3]
    exact hT2
  -- `cmp rdx, [rip + 1362219]`, `ja 767`
  refine c.s_blkA_v hin (bP550 prof e) Y3.cpu.vec hK3 hA3 hr3 rfl rfl ?_
  dsimp only [wp, Op.cmpma]
  refine ⟨fun i hi => hthr i (by omega), fun fl _ => ?_⟩
  intro Y4 t4 hK4 hA4 hr4 hg4 _ hv4
  refine c.s_jccV hK4 hA4 hin (by rw [mc2_length]; decide) hr4 (d557 prof.feat) (tgt := 767) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro _ Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
    have e5 : Y5.cpu.gpr = Y3.cpu.gpr := by rw [hg5, hg4]
    exact hNT hK5 hA5 hr5 (by rw [e5]; exact hL3) (by rw [hv5, hv4]; exact hT3)
  · intro _ Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
    have e5 : Y5.cpu.gpr = Y3.cpu.gpr := by rw [hg5, hg4]
    exact loopF c hin hsrc hst hd64 hs64 hds hsp hsp8 (a₀ := 16 - g₀.rdi.toNat % 16) (by omega) hR
      (g₀.rdx.toNat + 1) (16 - g₀.rdi.toNat % 16) (by omega) hK5 hA5 hr5 (by rw [e5]; exact hL3)
      (by rw [hv5, hv4]; exact hT3) (FwdP.start V g₀.rdi g₀.rsi _) (Nat.le_refl _) (by omega) (by omega)

end FV7z.Memcpy
