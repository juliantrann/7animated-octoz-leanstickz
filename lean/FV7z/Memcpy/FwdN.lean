import FV7z.Memcpy.FwdE
import FV7z.Lemmas.Xmm4
/-!
# `__memmove_sse2_unaligned`: the non-temporal forward loop (PLAN.md M)

Above the non-temporal threshold (`p498` jumps to `767`): `lea r10, [rdi + rdx]`, `cmp rsi, r10`, `jb 563`, the
loop of `Memcpy/Fwd.lean` when the source starts within the destination's end. Else, from `780`, two prefetches,
four loads from `rsi`, `rsi += 64`, `rdx -= 64`, four non-temporal stores (`movntdq`) at `rdi`, `rdi += 64`, again
while `rdx > 64`; then `sfence` and, at `849`, the same bytes as the tail at `611`.

- `bN767`, `bN780`, `bN794`, `bN809`, `bN836`, `bN840`, `bN846`: the blocks; `LoopR.set10`: `r10` is not kept.
- `loopN`: from `780`, by induction on the bytes left; `p767`: from `767`; `fwd498`: `p498` with `p767`.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- `lea r10, [rdi + rdx]`, `cmp rsi, r10`. -/
theorem bN767 (prof : Profile) :
    BlkV prof mc2 767 774 [VOp.op (Op.lea 64 10 (some 7) (some 2) 1 0), VOp.op (Op.cmp 64 6 (.r 10))] :=
  .cons (d767 _) (OpI.lea (b := some 7) (i := some 2) (sc := 1) (d := 0) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d771 _) (OpI.cmp (.r 10) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- Two prefetches. -/
theorem bN780 (prof : Profile) : BlkV prof mc2 780 794 [VOp.op Op.nop, VOp.op Op.nop] :=
  .cons (d780 _) OpI.prefetch (by rw [mc2_length]; decide) <|
  .cons (d787 _) OpI.prefetch (by rw [mc2_length]; decide) <| .nil _

/-- The loop's loads, at `794`. -/
theorem bN794 (prof : Profile) :
    BlkV prof mc2 794 809 [VOp.movups_m 0 6 0, VOp.movups_m 1 6 16, VOp.movups_m 2 6 32, VOp.movups_m 3 6 48] :=
  .cons (d794 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d797 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d801 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d805 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <| .nil _

/-- `add rsi, 64`, `sub rdx, 64`. -/
theorem bN809 (prof : Profile) :
    BlkV prof mc2 809 817 [VOp.op (Op.add 64 6 (.i 64)), VOp.op (Op.sub 64 2 (.i 64))] :=
  .cons (d809 _) (OpI.add (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d813 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `add rdi, 64`. -/
theorem bN836 (prof : Profile) : BlkV prof mc2 836 840 [VOp.op (Op.add 64 7 (.i 64))] :=
  .cons (d836 _) (OpI.add (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 64`. -/
theorem bN840 (prof : Profile) : BlkV prof mc2 840 844 [VOp.op (Op.cmp 64 2 (.i 64))] :=
  .cons (d840 _) (OpI.cmp (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `sfence`. -/
theorem bN846 (prof : Profile) : BlkV prof mc2 846 849 [VOp.op Op.nop] :=
  .cons (d846 _) OpI.sfence (by rw [mc2_length]; decide) <| .nil _

theorem LoopR.set10 {g₀ : Gprs} {r : Addr} {a : Nat} {g : Gprs} (h : LoopR g₀ r a g) (v : BitVec 64) :
    LoopR g₀ r a (g.set (regOf 10) v) :=
  ⟨h.di, h.si, h.dx, h.cx, h.r11, h.kp, h.ax⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `780`: the non-temporal loop, `a` bytes past the start, more than 64 left, until at most 64 are; then
`sfence` and `tailAt` from `849`. -/
theorem loopN (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {g₀ : Gprs} {r : Addr} {a₀ : Nat}
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hds : g₀.rdi.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (ha₀ : a₀ ≤ 16)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) :
    ∀ (m a : Nat) {X : State} {t : Nat} {V₂ : Addr → Byte}, g₀.rdx.toNat - a < m → KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V₂ → X.cpu.rip = e.add 780 → LoopR g₀ r a X.cpu.gpr →
      TailX V g₀.rsi g₀.rdx.toNat (xsOf X.cpu.vec.zmm) → FwdP V V₂ g₀.rdi g₀.rsi a₀ a → a₀ ≤ a →
      (g₀.rdi.toNat + a) % 16 = 0 → 64 < g₀.rdx.toNat - a → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero => intro a X t V₂ hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
  intro a X' t' V₂ hm hK' hA' hrip' hL' hT' hF ha hal h64
  -- two prefetches
  refine c.s_blkV hin (bN780 prof) hK' hA' hrip' (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro X t hK hA hrip hgX _ hxX
  have eX : X.cpu.gpr = X'.cpu.gpr := hgX
  have hL : LoopR g₀ r a X.cpu.gpr := by rw [eX]; exact hL'
  have hT : TailX V g₀.rsi g₀.rdx.toNat (xsOf X.cpu.vec.zmm) := by rw [hxX]; exact hT'
  have hn := Nat.le_of_lt hd64
  -- four loads from `rsi`
  have hea : ∀ k, eaB X.cpu.gpr 6 k = Addr.add g₀.rsi (a + k) := fun k => by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 k = _
    rw [get6, hL.si]
    exact addr_add_add _ _ _
  refine c.s_blkV hin (bN794 prof) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true, ?_⟩
  · rw [hea, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea, addr_add_add]
    exact hsrc _ (by omega)
  intro Y1 t1 hK1 hA1 hr1 hg1 _ hx1
  rw [hea, hea, hea, hea, Nat.add_zero] at hx1
  have hT1 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y1.cpu.vec.zmm) := by
    rw [hx1]
    exact ((((hT.set (xmmOf 0) _ (by decide) (by decide) (by decide) (by decide) (by decide)).set (xmmOf 1) _
      (by decide) (by decide) (by decide) (by decide) (by decide)).set (xmmOf 2) _
      (by decide) (by decide) (by decide) (by decide) (by decide)).set (xmmOf 3) _
      (by decide) (by decide) (by decide) (by decide) (by decide))
  -- `add rsi, 64`, `sub rdx, 64`
  refine c.s_blkV hin (bN809 prof) hK1 hA1 hr1 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y2 t2 hK2 hA2 hr2 hg2 _ hx2
  have hdi2 : Y2.cpu.gpr.rdi = Addr.add g₀.rdi a := by
    rw [hg2]
    show Y1.cpu.gpr.rdi = _
    rw [hg1]
    exact hL.di
  have hsi2 : Y2.cpu.gpr.rsi = Addr.add g₀.rsi (a + 64) := by
    have e : Y2.cpu.gpr.rsi = Addr.add Y1.cpu.gpr.rsi 64 := by
      rw [hg2]
      exact wr_add_rsi _ 64
    rw [e, hg1, hL.si, addr_add_add]
  have hdx2 : Y2.cpu.gpr.rdx.toNat = g₀.rdx.toNat - (a + 64) := by
    have e : Y2.cpu.gpr.rdx = Y1.cpu.gpr.rdx - BitVec.ofNat 64 64 := by
      rw [hg2]
      exact wr_sub_rdx _ 64
    have hle : 64 ≤ X.cpu.gpr.rdx.toNat := by rw [hL.dx]; omega
    rw [e, hg1, toNat_sub_le hle, hL.dx]
    omega
  have hcx2 : Y2.cpu.gpr.rcx = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    rw [hg2]
    show Y1.cpu.gpr.rcx = _
    rw [hg1]
    exact hL.cx
  have h112 : Y2.cpu.gpr.r11 = g₀.rdi := by
    rw [hg2]
    show Y1.cpu.gpr.r11 = _
    rw [hg1]
    exact hL.r11
  have hkp2 : KpS g₀ Y2.cpu.gpr := by
    rw [hg2, hg1]
    exact hL.kp
  have hax2 : Y2.cpu.gpr.rax = r := by
    rw [hg2]
    show Y1.cpu.gpr.rax = _
    rw [hg1]
    exact hL.ax
  have hT2 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y2.cpu.vec.zmm) := by
    rw [hx2]
    exact hT1
  -- four non-temporal stores at `rdi`
  have hed : ∀ {Z : State}, Z.cpu.gpr.rdi = Addr.add g₀.rdi a → ∀ k, eaD Z 7 k = Addr.add g₀.rdi (a + k) :=
    fun {Z} h k => by
      show Z.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 k = _
      rw [get7, h]
      exact addr_add_add _ _ _
  refine c.s_movntdq_stv hK2 hA2 hin (by rw [mc2_length]; decide) hr2 (d817 prof.feat)
    (by rw [hed hdi2, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed hdi2, addr_add_add]
    exact hst _ (by omega)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  have hdi3 : Y3.cpu.gpr.rdi = Addr.add g₀.rdi a := by rw [hg3]; exact hdi2
  refine c.s_movntdq_stv hK3 hA3 hin (by rw [mc2_length]; decide) hr3 (d821 prof.feat)
    (by rw [hed hdi3, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed hdi3, addr_add_add]
    exact hst _ (by omega)
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hv4⟩
  have hdi4 : Y4.cpu.gpr.rdi = Addr.add g₀.rdi a := by rw [hg4]; exact hdi3
  refine c.s_movntdq_stv hK4 hA4 hin (by rw [mc2_length]; decide) hr4 (d826 prof.feat)
    (by rw [hed hdi4, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed hdi4, addr_add_add]
    exact hst _ (by omega)
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have hdi5 : Y5.cpu.gpr.rdi = Addr.add g₀.rdi a := by rw [hg5]; exact hdi4
  refine c.s_movntdq_stv hK5 hA5 hin (by rw [mc2_length]; decide) hr5 (d831 prof.feat)
    (by rw [hed hdi5, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed hdi5, addr_add_add]
    exact hst _ (by omega)
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, hv6⟩
  have hx0 : xlo Y2 0 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi a) 16).map V₂) := by
    show xsOf Y2.cpu.vec.zmm (xmmOf 0) = _
    rw [hx2, hx1, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx1' : xlo Y3 1 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (a + 16)) 16).map V₂) := by
    show xsOf Y3.cpu.vec.zmm (xmmOf 1) = _
    rw [hv3, hx2, hx1, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx2' : xlo Y4 2 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (a + 32)) 16).map V₂) := by
    show xsOf Y4.cpu.vec.zmm (xmmOf 2) = _
    rw [hv4, hv3, hx2, hx1, xset_ne _ _ (by decide), xset_same]
  have hx3' : xlo Y5 3 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (a + 48)) 16).map V₂) := by
    show xsOf Y5.cpu.vec.zmm (xmmOf 3) = _
    rw [hv5, hv4, hv3, hx2, hx1, xset_same]
  have he0 : eaD Y2 7 0 = Addr.add g₀.rdi a := by rw [hed hdi2, Nat.add_zero]
  rw [he0, hed hdi3, hed hdi4, hed hdi5, hx0, hx1', hx2', hx3', toBytesLE_load, toBytesLE_load, toBytesLE_load,
    toBytesLE_load] at hA6
  have hl : ∀ p : Addr, ((byteAddrs p 16).map V₂).length = 16 := fun p => by rw [List.length_map, byteAddrs_len]
  have hb : ∀ q, a ≤ q → q + 16 ≤ g₀.rdx.toNat →
      ∀ j (hj : j < ((byteAddrs (Addr.add g₀.rsi q) 16).map V₂).length),
        ((byteAddrs (Addr.add g₀.rsi q) 16).map V₂)[j] = V (Addr.add g₀.rsi (q + j)) := fun q h1 h2 j hj => by
    have hj' : j < 16 := by rw [hl] at hj; exact hj
    rw [CopyP.ld j hj, hF.rd (i := q + j) hds (by omega) (by omega)]
  have hF6 := (((hF.st ha (o := a) rfl (by omega) (hl _) (hb a (by omega) (by omega))).st (by omega)
    (o := a + 16) (by omega) (by omega) (hl _) (hb (a + 16) (by omega) (by omega))).st (by omega)
    (o := a + 32) (by omega) (by omega) (hl _) (hb (a + 32) (by omega) (by omega))).st (by omega)
    (o := a + 48) (by omega) (by omega) (hl _) (hb (a + 48) (by omega) (by omega))
  rw [show a + 16 + 16 + 16 + 16 = a + 64 by omega] at hF6
  have e6 : Y6.cpu.gpr = Y2.cpu.gpr := by rw [hg6, hg5, hg4, hg3]
  have hT6 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y6.cpu.vec.zmm) := by
    rw [hv6, hv5, hv4, hv3]
    exact hT2
  -- `add rdi, 64`
  refine c.s_blkV hin (bN836 prof) hK6 hA6 hr6 (wpV_reg fun _ _ => wpV_nil ?_)
  intro Y7 t7 hK7 hA7 hr7 hg7 _ hx7
  have hdi7 : Y7.cpu.gpr.rdi = Addr.add g₀.rdi (a + 64) := by
    have e : Y7.cpu.gpr.rdi = Addr.add Y6.cpu.gpr.rdi 64 := by
      rw [hg7]
      exact wr_add_rdi _ 64
    rw [e, e6, hdi2, addr_add_add]
  have hsi7 : Y7.cpu.gpr.rsi = Addr.add g₀.rsi (a + 64) := by
    rw [hg7]
    show Y6.cpu.gpr.rsi = _
    rw [e6]
    exact hsi2
  have hdx7 : Y7.cpu.gpr.rdx.toNat = g₀.rdx.toNat - (a + 64) := by
    rw [hg7]
    show Y6.cpu.gpr.rdx.toNat = _
    rw [e6]
    exact hdx2
  have hcx7 : Y7.cpu.gpr.rcx = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    rw [hg7]
    show Y6.cpu.gpr.rcx = _
    rw [e6]
    exact hcx2
  have h117 : Y7.cpu.gpr.r11 = g₀.rdi := by
    rw [hg7]
    show Y6.cpu.gpr.r11 = _
    rw [e6]
    exact h112
  have hkp7 : KpS g₀ Y7.cpu.gpr := by
    rw [hg7, e6]
    exact hkp2
  have hax7 : Y7.cpu.gpr.rax = r := by
    rw [hg7]
    show Y6.cpu.gpr.rax = _
    rw [e6]
    exact hax2
  have hT7 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y7.cpu.vec.zmm) := by
    rw [hx7]
    exact hT6
  -- `cmp rdx, 64`, `ja 780`
  refine c.s_blkV hin (bN840 prof) hK7 hA7 hr7 (wpV_reg fun fl hP => wpV_nil ?_)
  intro Y8 t8 hK8 hA8 hr8 hg8 hf8 hx8
  simp only [gv, Src.val, get2] at hP
  have hq : (Y7.cpu.gpr.rdx.setWidth 64).toNat = g₀.rdx.toNat - (a + 64) := by rw [sw_64_64, hdx7]
  have e8 : Y8.cpu.gpr = Y7.cpu.gpr := by rw [hg8]
  have hT8 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y8.cpu.vec.zmm) := by
    rw [hx8]
    exact hT7
  refine c.s_jccV hK8 hA8 hin (by rw [mc2_length]; decide) hr8 (d844 prof.feat) (tgt := 780) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y9 t9 hK9 hA9 ⟨hr9, hg9, hv9⟩
    rw [hf8, hP, cond_7, subF_cf, subF_zf] at htk
    have h1 := ja_t htk
    simp only [hq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
    have e9 : Y9.cpu.gpr = Y7.cpu.gpr := by rw [hg9, e8]
    exact ih (a + 64) (by omega) hK9 hA9 hr9
      ⟨by rw [e9]; exact hdi7, by rw [e9]; exact hsi7, by rw [e9]; exact hdx7, by rw [e9]; exact hcx7,
        by rw [e9]; exact h117, by rw [e9]; exact hkp7, by rw [e9]; exact hax7⟩
      (by rw [hv9]; exact hT8) hF6 (by omega) (by omega) h1
  intro hfa Y9 t9 hK9 hA9 ⟨hr9, hg9, hv9⟩
  rw [hf8, hP, cond_7, subF_cf, subF_zf] at hfa
  have h1 := ja_f hfa
  simp only [hq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  have e9 : Y9.cpu.gpr = Y7.cpu.gpr := by rw [hg9, e8]
  -- `sfence`
  refine c.s_blkV hin (bN846 prof) hK9 hA9 hr9 (wpV_reg fun _ _ => wpV_nil ?_)
  intro Y10 t10 hK10 hA10 hr10 hg10 _ hx10
  have e10 : Y10.cpu.gpr = Y7.cpu.gpr := by rw [show Y10.cpu.gpr = Y9.cpu.gpr from hg10, e9]
  exact tailAt c hin (by rw [mc2_length]; decide) (d849 _) (d852 _) (d856 _) (d860 _) (d865 _) (d869 _) hst hd64
    hsp hsp8 (by omega) ha₀ (by omega) (by omega) hR hK10 hA10 hr10
    (by rw [e10]; exact hcx7) (by rw [e10]; exact h117) (by rw [e10]; exact hkp7) (by rw [e10]; exact hax7)
    (by rw [hx10, hv9]; exact hT8) hF6

/-- From `767`, `16 - rdi % 16` bytes past the start: to `loopF` at `563` or `loopN` at `780`, both forward
copies. -/
theorem p767 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {g₀ : Gprs} {r : Addr}
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hds : g₀.rdi.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (h128 : 128 < g₀.rdx.toNat)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) {Y : State} {t : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 767)
    (hL : LoopR g₀ r (16 - g₀.rdi.toNat % 16) Y.cpu.gpr)
    (hT : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y.cpu.vec.zmm)) :
    GoG prof L o gev gP gE Y t := by
  refine c.s_blkV hin (bN767 prof) hK hA hrip (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y2 t2 hK2 hA2 hr2 hg2 _ hx2
  have hL2 : LoopR g₀ r (16 - g₀.rdi.toNat % 16) Y2.cpu.gpr := by
    rw [hg2]
    exact hL.set10 _
  have hT2 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y2.cpu.vec.zmm) := by
    rw [hx2]
    exact hT
  refine c.s_jccV hK2 hA2 hin (by rw [mc2_length]; decide) hr2 (d774 prof.feat) (tgt := 563) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro _ Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
    exact loopF c hin hsrc hst hd64 hs64 hds hsp hsp8 (a₀ := 16 - g₀.rdi.toNat % 16) (by omega) hR
      (g₀.rdx.toNat + 1) (16 - g₀.rdi.toNat % 16) (by omega) hK3 hA3 hr3 (by rw [hg3]; exact hL2)
      (by rw [hv3]; exact hT2) (FwdP.start V g₀.rdi g₀.rsi _) (Nat.le_refl _) (by omega) (by omega)
  intro _ Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  exact loopN c hin hsrc hst hd64 hs64 hds hsp hsp8 (a₀ := 16 - g₀.rdi.toNat % 16) (by omega) hR
    (g₀.rdx.toNat + 1) (16 - g₀.rdi.toNat % 16) (by omega) hK3 hA3 hr3 (by rw [hg3]; exact hL2)
    (by rw [hv3]; exact hT2) (FwdP.start V g₀.rdi g₀.rsi _) (Nat.le_refl _) (by omega) (by omega)

/-- From `498`, more than 128 bytes, `rdi ≤ rsi`: the forward copy, `ret`. -/
theorem fwd498 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
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
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t :=
  p498 c hin hK hA hrip hkp hax hdi hsi hdx h128 hds hsrc hst hd64 hs64 hsp hsp8 hthr hR
    fun hK' hA' hr' hL' hT' => p767 c hin hsrc hst hd64 hs64 hds hsp hsp8 h128 hR hK' hA' hr' hL' hT'

end FV7z.Memcpy
