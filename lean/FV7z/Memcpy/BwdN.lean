import FV7z.Memcpy.BwdE
import FV7z.Memcpy.FwdN
/-!
# `__memmove_sse2_unaligned`: the non-temporal backward loop (PLAN.md M)

Above the non-temporal threshold (`p632` jumps to `870`): `lea r10, [rcx + rdx]`, `cmp r9, r10`, `jb 695`, the
loop of `Memcpy/Bwd.lean` when the destination starts within the source's end. Else, from `883`, two prefetches,
four loads from `rcx` downwards, `rcx -= 64`, `rdx -= 64`, four non-temporal stores (`movntdq`) at `r9` downwards,
`r9 -= 64`, again while `rdx > 64`; then `sfence` and, at `953`, the same bytes as the tail at `747`.

- `bBN870`, `bBN883`, `bBN894`, `bBN909`, `bBN940`, `bBN944`, `bBN950`: the blocks; `LoopB.set10`.
- `loopBN`: from `883`, by induction on the offset; `p870`: from `870`; `bwd632`: `p632` with `p870`.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- `lea r10, [rcx + rdx]`, `cmp r9, r10`. -/
theorem bBN870 (prof : Profile) :
    BlkV prof mc2 870 877 [VOp.op (Op.lea 64 10 (some 1) (some 2) 1 0), VOp.op (Op.cmp 64 9 (.r 10))] :=
  .cons (d870 _) (OpI.lea (b := some 1) (i := some 2) (sc := 1) (d := 0) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d874 _) (OpI.cmp (.r 10) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- Two prefetches. -/
theorem bBN883 (prof : Profile) : BlkV prof mc2 883 894 [VOp.op Op.nop, VOp.op Op.nop] :=
  .cons (d883 _) OpI.prefetch (by rw [mc2_length]; decide) <|
  .cons (d887 _) OpI.prefetch (by rw [mc2_length]; decide) <| .nil _

/-- The loop's loads, at `894`. -/
theorem bBN894 (prof : Profile) :
    BlkV prof mc2 894 909 [VOp.movups_m 0 1 0, VOp.movups_m 1 1 18446744073709551600,
      VOp.movups_m 2 1 18446744073709551584, VOp.movups_m 3 1 18446744073709551568] :=
  .cons (d894 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d897 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d901 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d905 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <| .nil _

/-- `sub rcx, 64`, `sub rdx, 64`. -/
theorem bBN909 (prof : Profile) :
    BlkV prof mc2 909 917 [VOp.op (Op.sub 64 1 (.i 64)), VOp.op (Op.sub 64 2 (.i 64))] :=
  .cons (d909 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d913 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `sub r9, 64`. -/
theorem bBN940 (prof : Profile) : BlkV prof mc2 940 944 [VOp.op (Op.sub 64 9 (.i 64))] :=
  .cons (d940 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 64`. -/
theorem bBN944 (prof : Profile) : BlkV prof mc2 944 948 [VOp.op (Op.cmp 64 2 (.i 64))] :=
  .cons (d944 _) (OpI.cmp (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `sfence`. -/
theorem bBN950 (prof : Profile) : BlkV prof mc2 950 953 [VOp.op Op.nop] :=
  .cons (d950 _) OpI.sfence (by rw [mc2_length]; decide) <| .nil _

theorem LoopB.set10 {g₀ : Gprs} {r : Addr} {b : Nat} {g : Gprs} (h : LoopB g₀ r b g) (v : BitVec 64) :
    LoopB g₀ r b (g.set (regOf 10) v) :=
  ⟨h.di, h.si, h.dx, h.cx, h.r9, h.r11, h.kp, h.ax⟩

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `883`: the non-temporal loop, the bytes from offset `b > 64` on stored, until `b ≤ 64`; then `sfence` and
`tailBAt` from `953`. -/
theorem loopBN (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {g₀ : Gprs} {r : Addr} {b₀ : Nat}
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsd : g₀.rsi.toNat ≤ g₀.rdi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (hb₀ : g₀.rdx.toNat - 16 ≤ b₀) (hb₀n : b₀ ≤ g₀.rdx.toNat)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) :
    ∀ (m b : Nat) {X : State} {t : Nat} {V₂ : Addr → Byte}, b < m → KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V₂ → X.cpu.rip = e.add 883 → LoopB g₀ r b X.cpu.gpr →
      HeadX V g₀.rsi g₀.rdx.toNat (xsOf X.cpu.vec.zmm) → FwdP V V₂ g₀.rdi g₀.rsi b b₀ → b ≤ b₀ →
      (g₀.rdi.toNat + b) % 16 = 0 → 64 < b → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero => intro b X t V₂ hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
  intro b X' t' V₂ hm hK' hA' hrip' hL' hH' hF hb hal h64
  -- two prefetches
  refine c.s_blkV hin (bBN883 prof) hK' hA' hrip' (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro X t hK hA hrip hgX _ hxX
  have eX : X.cpu.gpr = X'.cpu.gpr := hgX
  have hL : LoopB g₀ r b X.cpu.gpr := by rw [eX]; exact hL'
  have hH : HeadX V g₀.rsi g₀.rdx.toNat (xsOf X.cpu.vec.zmm) := by rw [hxX]; exact hH'
  have hn := Nat.le_of_lt hd64
  have hn64 : g₀.rdi.toNat + b₀ ≤ 2 ^ 64 := by omega
  -- four loads from `rcx`, downwards
  have hea0 : eaB X.cpu.gpr 1 0 = Addr.add g₀.rsi (b - 16) := by
    show X.cpu.gpr.get (regOf 1) + BitVec.ofNat 64 0 = _
    rw [get1, hL.cx]
    exact BitVec.add_zero _
  have hea : ∀ k D, D + k = 2 ^ 64 → k ≤ b - 16 → eaB X.cpu.gpr 1 D = Addr.add g₀.rsi (b - 16 - k) :=
    fun k D hD hk => by
      show X.cpu.gpr.get (regOf 1) + BitVec.ofNat 64 D = _
      rw [get1, hL.cx]
      exact add_back _ _ hD hk
  have e1 := hea 16 18446744073709551600 (by decide) (by omega)
  have e2 := hea 32 18446744073709551584 (by decide) (by omega)
  have e3 := hea 48 18446744073709551568 (by decide) (by omega)
  refine c.s_blkV hin (bBN894 prof) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true, ?_⟩
  · rw [hea0, addr_add_add]
    exact hsrc _ (by omega)
  · rw [e1, addr_add_add]
    exact hsrc _ (by omega)
  · rw [e2, addr_add_add]
    exact hsrc _ (by omega)
  · rw [e3, addr_add_add]
    exact hsrc _ (by omega)
  intro Y1 t1 hK1 hA1 hr1 hg1 _ hx1
  rw [hea0, e1, e2, e3] at hx1
  have hH1 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y1.cpu.vec.zmm) := by
    rw [hx1]
    exact ((((hH.set (xmmOf 0) _ (by decide) (by decide) (by decide) (by decide) (by decide)).set (xmmOf 1) _
      (by decide) (by decide) (by decide) (by decide) (by decide)).set (xmmOf 2) _
      (by decide) (by decide) (by decide) (by decide) (by decide)).set (xmmOf 3) _
      (by decide) (by decide) (by decide) (by decide) (by decide))
  -- `sub rcx, 64`, `sub rdx, 64`
  refine c.s_blkV hin (bBN909 prof) hK1 hA1 hr1 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y2 t2 hK2 hA2 hr2 hg2 _ hx2
  have hdi2 : Y2.cpu.gpr.rdi = g₀.rdi := by
    rw [hg2]
    show Y1.cpu.gpr.rdi = _
    rw [hg1]
    exact hL.di
  have hsi2 : Y2.cpu.gpr.rsi = g₀.rsi := by
    rw [hg2]
    show Y1.cpu.gpr.rsi = _
    rw [hg1]
    exact hL.si
  have hcx2 : Y2.cpu.gpr.rcx = Addr.add g₀.rsi (b - 16) - BitVec.ofNat 64 64 := by
    have e : Y2.cpu.gpr.rcx = Y1.cpu.gpr.rcx - BitVec.ofNat 64 64 := by
      rw [hg2]
      exact wr_sub_rcx _ 64
    rw [e, hg1, hL.cx]
  have hdx2 : Y2.cpu.gpr.rdx.toNat = b - 64 := by
    have e : Y2.cpu.gpr.rdx = Y1.cpu.gpr.rdx - BitVec.ofNat 64 64 := by
      rw [hg2]
      exact wr_sub_rdx _ 64
    have hle : 64 ≤ X.cpu.gpr.rdx.toNat := by rw [hL.dx]; omega
    rw [e, hg1, toNat_sub_le hle, hL.dx]
  have h92 : Y2.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) := by
    rw [hg2]
    show Y1.cpu.gpr.r9 = _
    rw [hg1]
    exact hL.r9
  have h112 : Y2.cpu.gpr.r11 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
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
  have hH2 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y2.cpu.vec.zmm) := by
    rw [hx2]
    exact hH1
  -- four non-temporal stores at `r9`, downwards
  have hed0 : ∀ {Z : State}, Z.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) → eaD Z 9 0 = Addr.add g₀.rdi (b - 16) :=
    fun {Z} h => by
      show Z.cpu.gpr.r9 + BitVec.ofNat 64 0 = _
      rw [h]
      exact BitVec.add_zero _
  have hed : ∀ {Z : State}, Z.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) → ∀ k D, D + k = 2 ^ 64 → k ≤ b - 16 →
      eaD Z 9 D = Addr.add g₀.rdi (b - 16 - k) := fun {Z} h k D hD hk => by
    show Z.cpu.gpr.r9 + BitVec.ofNat 64 D = _
    rw [h]
    exact add_back _ _ hD hk
  refine c.s_movntdq_stv hK2 hA2 hin (by rw [mc2_length]; decide) hr2 (d917 prof.feat)
    (by rw [hed0 h92, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed0 h92, addr_add_add]
    exact hst _ (by omega)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  have h93 : Y3.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) := by rw [hg3]; exact h92
  have f3 := hed h93 16 18446744073709551600 (by decide) (by omega)
  refine c.s_movntdq_stv hK3 hA3 hin (by rw [mc2_length]; decide) hr3 (d922 prof.feat)
    (by rw [f3, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [f3, addr_add_add]
    exact hst _ (by omega)
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hv4⟩
  have h94 : Y4.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) := by rw [hg4]; exact h93
  have f4 := hed h94 32 18446744073709551584 (by decide) (by omega)
  refine c.s_movntdq_stv hK4 hA4 hin (by rw [mc2_length]; decide) hr4 (d928 prof.feat)
    (by rw [f4, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [f4, addr_add_add]
    exact hst _ (by omega)
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have h95 : Y5.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) := by rw [hg5]; exact h94
  have f5 := hed h95 48 18446744073709551568 (by decide) (by omega)
  refine c.s_movntdq_stv hK5 hA5 hin (by rw [mc2_length]; decide) hr5 (d934 prof.feat)
    (by rw [f5, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [f5, addr_add_add]
    exact hst _ (by omega)
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, hv6⟩
  have hx0 : xlo Y2 0 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (b - 16)) 16).map V₂) := by
    show xsOf Y2.cpu.vec.zmm (xmmOf 0) = _
    rw [hx2, hx1, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx1' : xlo Y3 1 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (b - 16 - 16)) 16).map V₂) := by
    show xsOf Y3.cpu.vec.zmm (xmmOf 1) = _
    rw [hv3, hx2, hx1, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx2' : xlo Y4 2 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (b - 16 - 32)) 16).map V₂) := by
    show xsOf Y4.cpu.vec.zmm (xmmOf 2) = _
    rw [hv4, hv3, hx2, hx1, xset_ne _ _ (by decide), xset_same]
  have hx3' : xlo Y5 3 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (b - 16 - 48)) 16).map V₂) := by
    show xsOf Y5.cpu.vec.zmm (xmmOf 3) = _
    rw [hv5, hv4, hv3, hx2, hx1, xset_same]
  rw [hed0 h92, f3, f4, f5, hx0, hx1', hx2', hx3', toBytesLE_load, toBytesLE_load, toBytesLE_load,
    toBytesLE_load] at hA6
  have hl : ∀ p : Addr, ((byteAddrs p 16).map V₂).length = 16 := fun p => by rw [List.length_map, byteAddrs_len]
  have hbB : ∀ q, q + 16 ≤ b →
      ∀ j (hj : j < ((byteAddrs (Addr.add g₀.rsi q) 16).map V₂).length),
        ((byteAddrs (Addr.add g₀.rsi q) 16).map V₂)[j] = V (Addr.add g₀.rsi (q + j)) := fun q h1 j hj => by
    have hj' : j < 16 := by rw [hl] at hj; exact hj
    rw [CopyP.ld j hj, hF.rdB hsd (i := q + j) (by omega) (by omega)]
  have hF6 := (((hF.stB hb (o := b - 16) (by omega) hn64 (hl _) (hbB (b - 16) (by omega))).stB (by omega)
    (o := b - 16 - 16) (by omega) hn64 (hl _) (hbB (b - 16 - 16) (by omega))).stB (by omega)
    (o := b - 16 - 32) (by omega) hn64 (hl _) (hbB (b - 16 - 32) (by omega))).stB (by omega)
    (o := b - 16 - 48) (by omega) hn64 (hl _) (hbB (b - 16 - 48) (by omega))
  rw [show b - 16 - 48 = b - 64 by omega] at hF6
  have e6 : Y6.cpu.gpr = Y2.cpu.gpr := by rw [hg6, hg5, hg4, hg3]
  have hH6 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y6.cpu.vec.zmm) := by
    rw [hv6, hv5, hv4, hv3]
    exact hH2
  -- `sub r9, 64`
  refine c.s_blkV hin (bBN940 prof) hK6 hA6 hr6 (wpV_reg fun _ _ => wpV_nil ?_)
  intro Y7 t7 hK7 hA7 hr7 hg7 _ hx7
  have h97 : Y7.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) - BitVec.ofNat 64 64 := by
    have e : Y7.cpu.gpr.r9 = Y6.cpu.gpr.r9 - BitVec.ofNat 64 64 := by
      rw [hg7]
      exact wr_sub_r9 _ 64
    rw [e, e6, h92]
  have hdi7 : Y7.cpu.gpr.rdi = g₀.rdi := by
    rw [hg7]
    show Y6.cpu.gpr.rdi = _
    rw [e6]
    exact hdi2
  have hsi7 : Y7.cpu.gpr.rsi = g₀.rsi := by
    rw [hg7]
    show Y6.cpu.gpr.rsi = _
    rw [e6]
    exact hsi2
  have hdx7 : Y7.cpu.gpr.rdx.toNat = b - 64 := by
    rw [hg7]
    show Y6.cpu.gpr.rdx.toNat = _
    rw [e6]
    exact hdx2
  have hcx7 : Y7.cpu.gpr.rcx = Addr.add g₀.rsi (b - 16) - BitVec.ofNat 64 64 := by
    rw [hg7]
    show Y6.cpu.gpr.rcx = _
    rw [e6]
    exact hcx2
  have h117 : Y7.cpu.gpr.r11 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
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
  have hH7 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y7.cpu.vec.zmm) := by
    rw [hx7]
    exact hH6
  -- `cmp rdx, 64`, `ja 883`
  refine c.s_blkV hin (bBN944 prof) hK7 hA7 hr7 (wpV_reg fun fl hP => wpV_nil ?_)
  intro Y8 t8 hK8 hA8 hr8 hg8 hf8 hx8
  simp only [gv, Src.val, get2] at hP
  have hq : (Y7.cpu.gpr.rdx.setWidth 64).toNat = b - 64 := by rw [sw_64_64, hdx7]
  have e8 : Y8.cpu.gpr = Y7.cpu.gpr := by rw [hg8]
  have hH8 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y8.cpu.vec.zmm) := by
    rw [hx8]
    exact hH7
  refine c.s_jccV hK8 hA8 hin (by rw [mc2_length]; decide) hr8 (d948 prof.feat) (tgt := 883) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro htk Y9 t9 hK9 hA9 ⟨hr9, hg9, hv9⟩
    rw [hf8, hP, cond_7, subF_cf, subF_zf] at htk
    have h1 := ja_t htk
    simp only [hq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
    have e9 : Y9.cpu.gpr = Y7.cpu.gpr := by rw [hg9, e8]
    exact ih (b - 64) (by omega) hK9 hA9 hr9
      ⟨by rw [e9]; exact hdi7, by rw [e9]; exact hsi7, by rw [e9]; exact hdx7,
        by rw [e9, hcx7, sub_back g₀.rsi (m := b - 16) (k := 64) (by omega)]; exact congrArg _ (by omega),
        by rw [e9, h97, sub_back g₀.rdi (m := b - 16) (k := 64) (by omega)]; exact congrArg _ (by omega),
        by rw [e9]; exact h117, by rw [e9]; exact hkp7, by rw [e9]; exact hax7⟩
      (by rw [hv9]; exact hH8) hF6 (by omega) (by omega) h1
  intro hfa Y9 t9 hK9 hA9 ⟨hr9, hg9, hv9⟩
  rw [hf8, hP, cond_7, subF_cf, subF_zf] at hfa
  have h1 := ja_f hfa
  simp only [hq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h1
  have e9 : Y9.cpu.gpr = Y7.cpu.gpr := by rw [hg9, e8]
  -- `sfence`
  refine c.s_blkV hin (bBN950 prof) hK9 hA9 hr9 (wpV_reg fun _ _ => wpV_nil ?_)
  intro Y10 t10 hK10 hA10 hr10 hg10 _ hx10
  have e10 : Y10.cpu.gpr = Y7.cpu.gpr := by rw [show Y10.cpu.gpr = Y9.cpu.gpr from hg10, e9]
  exact tailBAt c hin (by rw [mc2_length]; decide) (d953 _) (d956 _) (d960 _) (d964 _) (d968 _) (d972 _) hst hd64
    hsp hsp8 (by omega) hb₀ hb₀n (by omega) (by omega) hR hK10 hA10 hr10
    (by rw [e10]; exact hdi7) (by rw [e10]; exact h117) (by rw [e10]; exact hkp7) (by rw [e10]; exact hax7)
    (by rw [hx10, hv9]; exact hH8) hF6

/-- From `870`, the bytes from offset `bB0` on to be stored first: to `loopB` at `695` or `loopBN` at `883`, both
backward copies. -/
theorem p870 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {g₀ : Gprs} {r : Addr}
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsd : g₀.rsi.toNat ≤ g₀.rdi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (h128 : 128 < g₀.rdx.toNat)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) {Y : State} {t : Nat}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V) (hrip : Y.cpu.rip = e.add 870)
    (hL : LoopB g₀ r (bB0 g₀) Y.cpu.gpr) (hH : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y.cpu.vec.zmm)) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := bB0_spec hd64 h128
  refine c.s_blkV hin (bBN870 prof) hK hA hrip (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
  intro Y2 t2 hK2 hA2 hr2 hg2 _ hx2
  have hL2 : LoopB g₀ r (bB0 g₀) Y2.cpu.gpr := by
    rw [hg2]
    exact hL.set10 _
  have hH2 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y2.cpu.vec.zmm) := by
    rw [hx2]
    exact hH
  refine c.s_jccV hK2 hA2 hin (by rw [mc2_length]; decide) hr2 (d877 prof.feat) (tgt := 695) rfl
    (by rw [mc2_length]; decide) ?_ ?_
  · intro _ Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
    exact loopB c hin hsrc hst hd64 hs64 hsd hsp hsp8 (b₀ := bB0 g₀) hb1 hb2 hR (g₀.rdx.toNat + 1) (bB0 g₀)
      (by omega) hK3 hA3 hr3 (by rw [hg3]; exact hL2) (by rw [hv3]; exact hH2) (FwdP.start V g₀.rdi g₀.rsi _)
      (Nat.le_refl _) hb3 hb4
  intro _ Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  exact loopBN c hin hsrc hst hd64 hs64 hsd hsp hsp8 (b₀ := bB0 g₀) hb1 hb2 hR (g₀.rdx.toNat + 1) (bB0 g₀)
    (by omega) hK3 hA3 hr3 (by rw [hg3]; exact hL2) (by rw [hv3]; exact hH2) (FwdP.start V g₀.rdi g₀.rsi _)
    (Nat.le_refl _) hb3 hb4

/-- From `632`, more than 128 bytes, `rsi ≤ rdi`: the backward copy, `ret`. -/
theorem bwd632 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
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
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t :=
  p632 c hin hK hA hrip hkp hax hdi hsi hdx h128 hsd hsrc hst hd64 hs64 hsp hsp8 hthr hR
    fun hK' hA' hr' hL' hH' => p870 c hin hsrc hst hd64 hs64 hsd hsp hsp8 h128 hR hK' hA' hr' hL' hH'

end FV7z.Memcpy
