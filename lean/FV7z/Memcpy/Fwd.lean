import FV7z.Memcpy.FwdP
import FV7z.Lemmas.Xmm3
/-!
# `__memmove_sse2_unaligned`: the forward loop above 128 bytes (PLAN.md M)

From `563`, `rdi` a multiple of 16 and `a` bytes past the start: four loads from `rsi`, `rsi += 64`, `rdx -= 64`,
four aligned stores (`movaps`) at `rdi`, `rdi += 64`, and again while `rdx > 64`. Then, at `611`, the last 64 bytes
of the source from `xmm5` to `xmm8` at the end and its first 16 from `xmm4` at the start (`r11`), and `ret`.

- `bF563`, `bF578`, `bF601`, `bF605`: the loop's blocks; `LoopR`: its registers.
- `tailAt`: from `611` (or `849`, the same bytes after the non-temporal loop); `loopF`: from `563`, by induction
  on the bytes left.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The loop's loads, at `563`. -/
theorem bF563 (prof : Profile) :
    BlkV prof mc2 563 578 [VOp.movups_m 0 6 0, VOp.movups_m 1 6 16, VOp.movups_m 2 6 32, VOp.movups_m 3 6 48] :=
  .cons (d563 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d566 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d570 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d574 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <| .nil _

/-- `add rsi, 64`, `sub rdx, 64`. -/
theorem bF578 (prof : Profile) :
    BlkV prof mc2 578 586 [VOp.op (Op.add 64 6 (.i 64)), VOp.op (Op.sub 64 2 (.i 64))] :=
  .cons (d578 _) (OpI.add (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d582 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `add rdi, 64`. -/
theorem bF601 (prof : Profile) : BlkV prof mc2 601 605 [VOp.op (Op.add 64 7 (.i 64))] :=
  .cons (d601 _) (OpI.add (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 64`. -/
theorem bF605 (prof : Profile) : BlkV prof mc2 605 609 [VOp.op (Op.cmp 64 2 (.i 64))] :=
  .cons (d605 _) (OpI.cmp (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- The registers at the top of the loop, `a` bytes past the start of a copy from `g₀`, returning `r`. -/
structure LoopR (g₀ : Gprs) (r : Addr) (a : Nat) (g : Gprs) : Prop where
  di : g.rdi = Addr.add g₀.rdi a
  si : g.rsi = Addr.add g₀.rsi a
  dx : g.rdx.toNat = g₀.rdx.toNat - a
  cx : g.rcx = Addr.add g₀.rdi (g₀.rdx.toNat - 16)
  r11 : g.r11 = g₀.rdi
  kp : KpS g₀ g
  ax : g.rax = r

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `j` (`611` or `849`), the bytes from `a₀ ≤ 16` to `a ≥ rdx - 64` copied: the last 64 bytes, the first 16,
`ret`. -/
theorem tailAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {j : Nat} (hj : j + 20 < mc2.length)
    (h0 : Dec prof.feat mc2 j (FV7z.mk (.sse .movups) 32 [.mem (mbd 1 0 128), .xmm 5] 3))
    (h1 : Dec prof.feat mc2 (j + 3) (FV7z.mk (.sse .movups) 32 [.mem (mbd 1 18446744073709551600 128), .xmm 6] 4))
    (h2 : Dec prof.feat mc2 (j + 3 + 4)
      (FV7z.mk (.sse .movups) 32 [.mem (mbd 1 18446744073709551584 128), .xmm 7] 4))
    (h3 : Dec prof.feat mc2 (j + 3 + 4 + 4)
      (FV7z.mk (.sse .movups) 32 [.mem (mbd 1 18446744073709551568 128), .xmm 8] 5))
    (h4 : Dec prof.feat mc2 (j + 3 + 4 + 4 + 5) (FV7z.mk (.sse .movups) 32 [.mem (mbd 11 0 128), .xmm 4] 4))
    (h5 : Dec prof.feat mc2 (j + 3 + 4 + 4 + 5 + 4) (FV7z.mk .ret 64 [] 1)) {g₀ : Gprs} {r : Addr} {a₀ a : Nat}
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (h64 : 64 ≤ g₀.rdx.toNat) (ha₀ : a₀ ≤ 16)
    (ha : g₀.rdx.toNat ≤ a + 64) (han : a ≤ g₀.rdx.toNat)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) {Y : State} {t : Nat} {V₂ : Addr → Byte}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₂) (hrip : Y.cpu.rip = e.add j)
    (hcx : Y.cpu.gpr.rcx = Addr.add g₀.rdi (g₀.rdx.toNat - 16)) (h11 : Y.cpu.gpr.r11 = g₀.rdi)
    (hkp : KpS g₀ Y.cpu.gpr) (hax : Y.cpu.gpr.rax = r)
    (hT : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y.cpu.vec.zmm)) (hF : FwdP V V₂ g₀.rdi g₀.rsi a₀ a) :
    GoG prof L o gev gP gE Y t := by
  have he0 : eaD Y 1 0 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    show Y.cpu.gpr.get (regOf 1) + BitVec.ofNat 64 0 = _
    rw [get1, hcx]
    exact BitVec.add_zero _
  refine c.s_movups_stv hK hA hin (by omega) hrip h0 (fun i hi => ?_) ?_
  · rw [he0, addr_add_add]
    exact hst _ (by omega)
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, hv2⟩
  have he1 : eaD Y2 1 18446744073709551600 = Addr.add g₀.rdi (g₀.rdx.toNat - 32) := by
    show Y2.cpu.gpr.get (regOf 1) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get1, hg2, hcx,
      add_back g₀.rdi (g₀.rdx.toNat - 16) (k := 16) (D := 18446744073709551600) (by decide) (by omega)]
    congr 1
  refine c.s_movups_stv hK2 hA2 hin (by omega) hr2 h1 (fun i hi => ?_) ?_
  · rw [he1, addr_add_add]
    exact hst _ (by omega)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  have he2 : eaD Y3 1 18446744073709551584 = Addr.add g₀.rdi (g₀.rdx.toNat - 48) := by
    show Y3.cpu.gpr.get (regOf 1) + BitVec.ofNat 64 18446744073709551584 = _
    rw [get1, hg3, hg2, hcx,
      add_back g₀.rdi (g₀.rdx.toNat - 16) (k := 32) (D := 18446744073709551584) (by decide) (by omega)]
    congr 1
  refine c.s_movups_stv hK3 hA3 hin (by omega) hr3 h2 (fun i hi => ?_) ?_
  · rw [he2, addr_add_add]
    exact hst _ (by omega)
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hv4⟩
  have he3 : eaD Y4 1 18446744073709551568 = Addr.add g₀.rdi (g₀.rdx.toNat - 64) := by
    show Y4.cpu.gpr.get (regOf 1) + BitVec.ofNat 64 18446744073709551568 = _
    rw [get1, hg4, hg3, hg2, hcx,
      add_back g₀.rdi (g₀.rdx.toNat - 16) (k := 48) (D := 18446744073709551568) (by decide) (by omega)]
    congr 1
  refine c.s_movups_stv hK4 hA4 hin (by omega) hr4 h3 (fun i hi => ?_) ?_
  · rw [he3, addr_add_add]
    exact hst _ (by omega)
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have he4 : eaD Y5 11 0 = Addr.add g₀.rdi 0 := by
    show Y5.cpu.gpr.r11 + BitVec.ofNat 64 0 = _
    rw [hg5, hg4, hg3, hg2, h11]
    rfl
  refine c.s_movups_stv hK5 hA5 hin (by omega) hr5 h4 (fun i hi => ?_) ?_
  · rw [he4, addr_add_add]
    exact hst _ (by omega)
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, _⟩
  have hx5 : xlo Y 5 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 16)) 16).map V) := hT.x5
  have hx6 : xlo Y2 6 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 32)) 16).map V) := by
    show (Y2.cpu.vec.zmm (xmmOf 6)).setWidth 128 = _
    rw [hv2]
    exact hT.x6
  have hx7 : xlo Y3 7 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 48)) 16).map V) := by
    show (Y3.cpu.vec.zmm (xmmOf 7)).setWidth 128 = _
    rw [hv3, hv2]
    exact hT.x7
  have hx8 : xlo Y4 8 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 64)) 16).map V) := by
    show (Y4.cpu.vec.zmm (xmmOf 8)).setWidth 128 = _
    rw [hv4, hv3, hv2]
    exact hT.x8
  have hx4 : xlo Y5 4 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 0) 16).map V) := by
    show (Y5.cpu.vec.zmm (xmmOf 4)).setWidth 128 = _
    rw [hv5, hv4, hv3, hv2]
    exact hT.x4
  rw [he0, he1, he2, he3, he4, hx5, hx6, hx7, hx8, hx4, toBytesLE_load, toBytesLE_load, toBytesLE_load,
    toBytesLE_load, toBytesLE_load] at hA6
  have hn := Nat.le_of_lt hd64
  have hl : ∀ p : Addr, ((byteAddrs p 16).map V).length = 16 := fun p => by rw [List.length_map, byteAddrs_len]
  have hC := (hF.copyP han).st hn (o := g₀.rdx.toNat - 16) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := g₀.rdx.toNat - 32) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := g₀.rdx.toNat - 48) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := g₀.rdx.toNat - 64) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := 0) (k := 16) (hl _) (by omega) CopyP.ld
  have e6 : Y6.cpu.gpr = Y.cpu.gpr := by rw [hg6, hg5, hg4, hg3, hg2]
  refine ret_atC c hin (by omega) h5 hK6 hA6 hr6 (by rw [e6]; exact hkp)
    (by rw [e6]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi ?_) hC.2 hR
  by_cases c0 : i < 16
  · exact Or.inr ⟨by omega, by omega⟩
  by_cases c1 : i < a
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨by omega, c1⟩))))
  by_cases c2 : g₀.rdx.toNat - 16 ≤ i
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨c2, by omega⟩))))
  by_cases c3 : g₀.rdx.toNat - 32 ≤ i
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨c3, by omega⟩)))
  by_cases c4 : g₀.rdx.toNat - 48 ≤ i
  · exact Or.inl (Or.inl (Or.inr ⟨c4, by omega⟩))
  exact Or.inl (Or.inr ⟨by omega, by omega⟩)

/-- From `563`: the loop, `a` bytes past the start, more than 64 left, until at most 64 are; then `tailF`. -/
theorem loopF (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {g₀ : Gprs} {r : Addr} {a₀ : Nat}
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hds : g₀.rdi.toNat ≤ g₀.rsi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (ha₀ : a₀ ≤ 16)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) :
    ∀ (m a : Nat) {X : State} {t : Nat} {V₂ : Addr → Byte}, g₀.rdx.toNat - a < m → KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V₂ → X.cpu.rip = e.add 563 → LoopR g₀ r a X.cpu.gpr →
      TailX V g₀.rsi g₀.rdx.toNat (xsOf X.cpu.vec.zmm) → FwdP V V₂ g₀.rdi g₀.rsi a₀ a → a₀ ≤ a →
      (g₀.rdi.toNat + a) % 16 = 0 → 64 < g₀.rdx.toNat - a → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero => intro a X t V₂ hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
  intro a X t V₂ hm hK hA hrip hL hT hF ha hal h64
  have hn := Nat.le_of_lt hd64
  -- four loads from `rsi`
  have hea : ∀ k, eaB X.cpu.gpr 6 k = Addr.add g₀.rsi (a + k) := fun k => by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 k = _
    rw [get6, hL.si]
    exact addr_add_add _ _ _
  refine c.s_blkV hin (bF563 prof) hK hA hrip ?_
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
  refine c.s_blkV hin (bF578 prof) hK1 hA1 hr1 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
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
  -- four aligned stores at `rdi`
  have hed : ∀ {Z : State}, Z.cpu.gpr.rdi = Addr.add g₀.rdi a → ∀ k, eaD Z 7 k = Addr.add g₀.rdi (a + k) :=
    fun {Z} h k => by
      show Z.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 k = _
      rw [get7, h]
      exact addr_add_add _ _ _
  refine c.s_movaps_stv hK2 hA2 hin (by rw [mc2_length]; decide) hr2 (d586 prof.feat)
    (by rw [hed hdi2, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed hdi2, addr_add_add]
    exact hst _ (by omega)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  have hdi3 : Y3.cpu.gpr.rdi = Addr.add g₀.rdi a := by rw [hg3]; exact hdi2
  refine c.s_movaps_stv hK3 hA3 hin (by rw [mc2_length]; decide) hr3 (d589 prof.feat)
    (by rw [hed hdi3, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed hdi3, addr_add_add]
    exact hst _ (by omega)
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hv4⟩
  have hdi4 : Y4.cpu.gpr.rdi = Addr.add g₀.rdi a := by rw [hg4]; exact hdi3
  refine c.s_movaps_stv hK4 hA4 hin (by rw [mc2_length]; decide) hr4 (d593 prof.feat)
    (by rw [hed hdi4, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed hdi4, addr_add_add]
    exact hst _ (by omega)
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have hdi5 : Y5.cpu.gpr.rdi = Addr.add g₀.rdi a := by rw [hg5]; exact hdi4
  refine c.s_movaps_stv hK5 hA5 hin (by rw [mc2_length]; decide) hr5 (d597 prof.feat)
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
  refine c.s_blkV hin (bF601 prof) hK6 hA6 hr6 (wpV_reg fun _ _ => wpV_nil ?_)
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
  -- `cmp rdx, 64`, `ja 563`
  refine c.s_blkV hin (bF605 prof) hK7 hA7 hr7 (wpV_reg fun fl hP => wpV_nil ?_)
  intro Y8 t8 hK8 hA8 hr8 hg8 hf8 hx8
  simp only [gv, Src.val, get2] at hP
  have hq : (Y7.cpu.gpr.rdx.setWidth 64).toNat = g₀.rdx.toNat - (a + 64) := by rw [sw_64_64, hdx7]
  have e8 : Y8.cpu.gpr = Y7.cpu.gpr := by rw [hg8]
  have hT8 : TailX V g₀.rsi g₀.rdx.toNat (xsOf Y8.cpu.vec.zmm) := by
    rw [hx8]
    exact hT7
  refine c.s_jccV hK8 hA8 hin (by rw [mc2_length]; decide) hr8 (d609 prof.feat) (tgt := 563) rfl
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
  exact tailAt c hin (by rw [mc2_length]; decide) (d611 _) (d614 _) (d618 _) (d622 _) (d627 _) (d631 _) hst hd64
    hsp hsp8 (by omega) ha₀ (by omega) (by omega) hR hK9 hA9 hr9
    (by rw [e9]; exact hcx7) (by rw [e9]; exact h117) (by rw [e9]; exact hkp7) (by rw [e9]; exact hax7)
    (by rw [hv9]; exact hT8) hF6

end FV7z.Memcpy
