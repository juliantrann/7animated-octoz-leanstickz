import FV7z.Memcpy.Bwd
import FV7z.Memcpy.FwdE
/-!
# `__memmove_sse2_unaligned`: into the backward loop (PLAN.md M)

From `632`, more than 128 bytes and `rsi ≤ rdi`: the first 64 and the last 16 bytes loaded (`HeadX`), `r11` at the
last 16 bytes of the destination, `r9` there less `(rdi + rdx - 16) % 16`, a multiple of 16, `rcx` likewise in the
source, `rdx` the offset `bB0` of their end; then, past the non-temporal threshold (the same as at `550`), `870`,
else the loop at `695`.

- `bQ632`, `bQ653`, `bQ673`, `bQ682`: the blocks; `bB0`, `bB0_spec`: the loop's first offset.
- `sub_and15`, `sub_and15_toNat`, `eaG_back6`: the address arithmetic.
- `p632`: from `632` to `loopB`, or to `870` (`hNT`).
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The five loads, at `632`. -/
theorem bQ632 (prof : Profile) :
    BlkV prof mc2 632 653 [VOp.movups_m 4 6 0, VOp.movups_m 5 6 16, VOp.movups_m 6 6 32, VOp.movups_m 7 6 48,
      VOp.movups_mi 8 6 2 18446744073709551600] :=
  .cons (d632 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d635 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d639 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d643 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d647 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide) <| .nil _

/-- `lea r11, [rdi + rdx - 16]`, `lea rcx, [rsi + rdx - 16]`, `mov r9, r11`, `mov r8, r11`, `and r8, 15`. -/
theorem bQ653 (prof : Profile) :
    BlkV prof mc2 653 673 [VOp.op (Op.lea 64 11 (some 7) (some 2) 1 18446744073709551600),
      VOp.op (Op.lea 64 1 (some 6) (some 2) 1 18446744073709551600), VOp.op (Op.mov 64 9 (.r 11)),
      VOp.op (Op.mov 64 8 (.r 11)), VOp.op (Op.and 64 8 (.i 15))] :=
  .cons (d653 _) (OpI.lea (b := some 7) (i := some 2) (sc := 1) (d := 18446744073709551600) (.inr rfl))
    (by rw [mc2_length]; decide) <|
  .cons (d658 _) (OpI.lea (b := some 6) (i := some 2) (sc := 1) (d := 18446744073709551600) (.inr rfl))
    (by rw [mc2_length]; decide) <|
  .cons (d663 _) (OpI.mov (.r 11) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d666 _) (OpI.mov (.r 11) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d669 _) (OpI.and (.i 15) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `sub rcx, r8`, `sub r9, r8`, `sub rdx, r8`. -/
theorem bQ673 (prof : Profile) :
    BlkV prof mc2 673 682 [VOp.op (Op.sub 64 1 (.r 8)), VOp.op (Op.sub 64 9 (.r 8)), VOp.op (Op.sub 64 2 (.r 8))] :=
  .cons (d673 _) (OpI.sub (.r 8) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d676 _) (OpI.sub (.r 8) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d679 _) (OpI.sub (.r 8) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `[rip + 1362087]` at `682` is the threshold read at `550`. -/
theorem thr682 (e : Addr) : Addr.add e 689 + BitVec.ofNat 64 1362087 = BitVec.ofNat 64 (thrA e) := by
  rw [thrA, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `cmp rdx, [rip + 1362087]`, at `e + 682`. -/
theorem bQ682 (prof : Profile) (e : Addr) : BlkA prof mc2 e 682 689 [Op.cmpma 64 2 (thrA e)] :=
  .cons (d682 prof.feat) (OpIA.cmpm_rip (.inr (.inr rfl)) (by rw [addr_add_add]; exact thr682 e))
    (by rw [mc2_length]; decide) (.nil _)

theorem get9 (g : Gprs) : g.get (regOf 9) = g.r9 := rfl
theorem get11 (g : Gprs) : g.get (regOf 11) = g.r11 := rfl
theorem set_r9b (g : Gprs) (v : BitVec 64) : g.set (regOf 9) v = { g with r9 := v } := rfl

theorem eaG_back6 {g : Gprs} {a d : Addr} (h6 : g.rsi = a) (h2 : g.rdx = d) {k D : Nat} (hD : D + k = 2 ^ 64)
    (hk : k ≤ d.toNat) : eaG g (some 6) (some 2) 1 D = a.add (d.toNat - k) := by
  rw [← ea_back a d hD hk, ← h6, ← h2]
  apply BitVec.eq_of_toNat_eq
  simp [eaG, optV]

/-- `y + m - (x & 15)`. -/
theorem sub_and15 (y x : Addr) (m : Nat) (h : x.toNat % 16 ≤ m) :
    Addr.add y m - (x &&& BitVec.ofNat 64 15) = Addr.add y (m - x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  have h1 := and15_toNat x
  have := y.isLt
  have := Nat.mod_lt x.toNat (show 16 > 0 by decide)
  simp only [Addr.add, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, h1]
  omega

/-- `y - (x & 15)`. -/
theorem sub_and15_toNat (y x : Addr) (h : x.toNat % 16 ≤ y.toNat) :
    (y - (x &&& BitVec.ofNat 64 15)).toNat = y.toNat - x.toNat % 16 := by
  have h1 := and15_toNat x
  have := y.isLt
  have := Nat.mod_lt x.toNat (show 16 > 0 by decide)
  simp only [BitVec.toNat_sub, h1]
  omega

/-- The backward loop's first offset: the end of the copy less `(rdi + rdx - 16) % 16`. -/
def bB0 (g₀ : Gprs) : Nat := g₀.rdx.toNat - (Addr.add g₀.rdi (g₀.rdx.toNat - 16)).toNat % 16

theorem bB0_spec {g₀ : Gprs} (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (h128 : 128 < g₀.rdx.toNat) :
    g₀.rdx.toNat - 16 ≤ bB0 g₀ ∧ bB0 g₀ ≤ g₀.rdx.toNat ∧ (g₀.rdi.toNat + bB0 g₀) % 16 = 0 ∧ 64 < bB0 g₀ := by
  unfold bB0
  rw [toNat_add_of_fits (a := g₀.rdi) (n := g₀.rdx.toNat) (i := g₀.rdx.toNat - 16) (by omega) (by omega)]
  omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `632`, `128 < rdx`, `rsi ≤ rdi`: the loads and the alignment, then the loop at `695` (`loopB`) or, past
the non-temporal threshold, `870` (`hNT`). -/
theorem p632 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 632)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h128 : 128 < g₀.rdx.toNat) (hsd : g₀.rsi.toNat ≤ g₀.rdi.toNat)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hthr : ∀ i < 8, Foot F.data (Addr.add (BitVec.ofNat 64 (thrA e)) i))
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r)
    (hNT : ∀ {Y : State} {t' : Nat}, KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = e.add 870 →
      LoopB g₀ r (bB0 g₀) Y.cpu.gpr → HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y.cpu.vec.zmm) →
      GoG prof L o gev gP gE Y t') : GoG prof L o gev gP gE X t := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := bB0_spec hd64 h128
  -- the five loads
  have hea0 : eaB X.cpu.gpr 6 0 = Addr.add g₀.rsi 0 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 0 = _
    rw [get6, hsi]
    rfl
  have hea1 : eaB X.cpu.gpr 6 16 = Addr.add g₀.rsi 16 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 16 = _
    rw [get6, hsi]
    rfl
  have hea2 : eaB X.cpu.gpr 6 32 = Addr.add g₀.rsi 32 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 32 = _
    rw [get6, hsi]
    rfl
  have hea3 : eaB X.cpu.gpr 6 48 = Addr.add g₀.rsi 48 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 48 = _
    rw [get6, hsi]
    rfl
  have hea8 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551600 = Addr.add g₀.rsi (g₀.rdx.toNat - 16) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rsi g₀.rdx (by decide) (by omega)
  refine c.s_blkV hin (bQ632 prof) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m, VOp.movups_mi]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, ?_⟩
  · rw [hea0, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea1, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea2, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea3, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea8, addr_add_add]
    exact hsrc _ (by omega)
  intro Y1 t1 hK1 hA1 hr1 hg1 _ hx1
  rw [hea0, hea1, hea2, hea3, hea8] at hx1
  have hH1 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y1.cpu.vec.zmm) := by
    rw [hx1]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide),
        xset_same]
    · rw [xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
    · rw [xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
    · rw [xset_ne _ _ (by decide), xset_same]
    · rw [xset_same]
  -- `r11`, `rcx`, `r9` and `r8`
  refine c.s_blkV hin (bQ653 prof) hK1 hA1 hr1
    (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y2 t2 hK2 hA2 hr2 hg2 _ hx2
  simp only [wr, gv, Src.val, get8, get11, set_r11, set_rcx, set_r9b, set_r8, BitVec.setWidth_eq] at hg2
  have hdi2 : Y2.cpu.gpr.rdi = g₀.rdi := by rw [hg2, hg1]; exact hdi
  have hsi2 : Y2.cpu.gpr.rsi = g₀.rsi := by rw [hg2, hg1]; exact hsi
  have hdx2 : Y2.cpu.gpr.rdx = g₀.rdx := by rw [hg2, hg1]; exact hdx
  have hkp2 : KpS g₀ Y2.cpu.gpr := by
    have h := hkp
    unfold KpS at h ⊢
    rw [hg2, hg1]
    exact h
  have hax2 : Y2.cpu.gpr.rax = r := by rw [hg2, hg1]; exact hax
  have h112 : Y2.cpu.gpr.r11 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    rw [hg2]
    exact eaG_back (by rw [hg1]; exact hdi) (by rw [hg1]; exact hdx) (k := 16) (by decide) (by omega)
  have h92 : Y2.cpu.gpr.r9 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    rw [hg2]
    exact eaG_back (by rw [hg1]; exact hdi) (by rw [hg1]; exact hdx) (k := 16) (by decide) (by omega)
  have hcx2 : Y2.cpu.gpr.rcx = Addr.add g₀.rsi (g₀.rdx.toNat - 16) := by
    rw [hg2]
    exact eaG_back6 (by rw [hg1]; exact hsi) (by rw [hg1]; exact hdx) (k := 16) (by decide) (by omega)
  have hr82 : Y2.cpu.gpr.r8 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) &&& BitVec.ofNat 64 15 := by
    rw [← h112, hg2]
    try exact rfl
  have hH2 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y2.cpu.vec.zmm) := by
    rw [hx2]
    exact hH1
  -- `rcx`, `r9`, `rdx` less `r8`
  refine c.s_blkV hin (bQ673 prof) hK2 hA2 hr2 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y3 t3 hK3 hA3 hr3 hg3 _ hx3
  simp only [wr, gv, Src.val, get1, get2, get8, get9, set_rcx, set_r9b, set_rdx, BitVec.setWidth_eq, subR_eq] at hg3
  have hx16 : (Addr.add g₀.rdi (g₀.rdx.toNat - 16)).toNat % 16 ≤ g₀.rdx.toNat - 16 := by omega
  have hcx3 : Y3.cpu.gpr.rcx = Addr.add g₀.rsi (bB0 g₀ - 16) := by
    rw [hg3]
    show Y2.cpu.gpr.rcx - Y2.cpu.gpr.r8 = _
    rw [hcx2, hr82, sub_and15 g₀.rsi (Addr.add g₀.rdi (g₀.rdx.toNat - 16)) (g₀.rdx.toNat - 16) hx16]
    exact congrArg _ (by unfold bB0; omega)
  have h93 : Y3.cpu.gpr.r9 = Addr.add g₀.rdi (bB0 g₀ - 16) := by
    rw [hg3]
    show Y2.cpu.gpr.r9 - Y2.cpu.gpr.r8 = _
    rw [h92, hr82, sub_and15 g₀.rdi (Addr.add g₀.rdi (g₀.rdx.toNat - 16)) (g₀.rdx.toNat - 16) hx16]
    exact congrArg _ (by unfold bB0; omega)
  have hdx3 : Y3.cpu.gpr.rdx.toNat = bB0 g₀ := by
    rw [hg3]
    show (Y2.cpu.gpr.rdx - Y2.cpu.gpr.r8).toNat = g₀.rdx.toNat - (Addr.add g₀.rdi (g₀.rdx.toNat - 16)).toNat % 16
    rw [hdx2, hr82, sub_and15_toNat g₀.rdx (Addr.add g₀.rdi (g₀.rdx.toNat - 16)) (by omega)]
  have hkp3 : KpS g₀ Y3.cpu.gpr := by
    have h := hkp2
    unfold KpS at h ⊢
    rw [hg3]
    exact h
  have hL3 : LoopB g₀ r (bB0 g₀) Y3.cpu.gpr :=
    ⟨by rw [hg3]; exact hdi2, by rw [hg3]; exact hsi2, hdx3, hcx3, h93, by rw [hg3]; exact h112, hkp3,
      by rw [hg3]; exact hax2⟩
  have hH3 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y3.cpu.vec.zmm) := by
    rw [hx3]
    exact hH2
  -- `cmp rdx, [rip + 1362087]`, `ja 870`
  refine c.s_blkA_v hin (bQ682 prof e) Y3.cpu.vec hK3 hA3 hr3 rfl rfl ?_
  dsimp only [wp, Op.cmpma]
  refine ⟨fun i hi => hthr i (by omega), fun fl _ => ?_⟩
  intro Y4 t4 hK4 hA4 hr4 hg4 _ hv4
  refine c.s_jccV hK4 hA4 hin (by rw [mc2_length]; decide) hr4 (d689 prof.feat) (tgt := 870) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro _ Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
    have e5 : Y5.cpu.gpr = Y3.cpu.gpr := by rw [hg5, hg4]
    exact hNT hK5 hA5 hr5 (by rw [e5]; exact hL3) (by rw [hv5, hv4]; exact hH3)
  · intro _ Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
    have e5 : Y5.cpu.gpr = Y3.cpu.gpr := by rw [hg5, hg4]
    exact loopB c hin hsrc hst hd64 hs64 hsd hsp hsp8 (b₀ := bB0 g₀) hb1 hb2 hR (g₀.rdx.toNat + 1) (bB0 g₀)
      (by omega) hK5 hA5 hr5 (by rw [e5]; exact hL3) (by rw [hv5, hv4]; exact hH3) (FwdP.start V g₀.rdi g₀.rsi _)
      (Nat.le_refl _) hb3 hb4

end FV7z.Memcpy
