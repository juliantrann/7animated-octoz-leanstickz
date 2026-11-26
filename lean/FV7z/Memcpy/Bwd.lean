import FV7z.Memcpy.Fwd
import FV7z.Memcpy.BwdP
/-!
# `__memmove_sse2_unaligned`: the backward loop above 128 bytes (PLAN.md M)

From `695`, `r9 + 16` a multiple of 16 and the bytes from offset `b` on stored: four loads from `rcx` downwards,
`rcx -= 64`, `rdx -= 64`, four aligned stores (`movaps`) at `r9` downwards, `r9 -= 64`, and again while `rdx > 64`.
Then, at `747`, the first 64 bytes of the source from `xmm4` to `xmm7` at the start and its last 16 from `xmm8` at
the end (`r11`), and `ret`.

- `bB695`, `bB710`, `bB737`, `bB741`: the loop's blocks.
- `tailBAt`: from `747` (or `953`, the same bytes after the non-temporal loop); `loopB`: from `695`, by induction
  on the offset.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The loop's loads, at `695`. -/
theorem bB695 (prof : Profile) :
    BlkV prof mc2 695 710 [VOp.movups_m 0 1 0, VOp.movups_m 1 1 18446744073709551600,
      VOp.movups_m 2 1 18446744073709551584, VOp.movups_m 3 1 18446744073709551568] :=
  .cons (d695 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d698 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d702 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <|
  .cons (d706 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide) <| .nil _

/-- `sub rcx, 64`, `sub rdx, 64`. -/
theorem bB710 (prof : Profile) :
    BlkV prof mc2 710 718 [VOp.op (Op.sub 64 1 (.i 64)), VOp.op (Op.sub 64 2 (.i 64))] :=
  .cons (d710 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <|
  .cons (d714 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `sub r9, 64`. -/
theorem bB737 (prof : Profile) : BlkV prof mc2 737 741 [VOp.op (Op.sub 64 9 (.i 64))] :=
  .cons (d737 _) (OpI.sub (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

/-- `cmp rdx, 64`. -/
theorem bB741 (prof : Profile) : BlkV prof mc2 741 745 [VOp.op (Op.cmp 64 2 (.i 64))] :=
  .cons (d741 _) (OpI.cmp (.i 64) (.inr rfl)) (by rw [mc2_length]; decide) <| .nil _

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `j` (`747` or `953`), the bytes from `b ≤ 64` to `b₀ ≥ rdx - 16` copied: the first 64 bytes, the last 16,
`ret`. -/
theorem tailBAt (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {j : Nat} (hj : j + 19 < mc2.length)
    (h0 : Dec prof.feat mc2 j (FV7z.mk (.sse .movups) 32 [.mem (mbd 7 0 128), .xmm 4] 3))
    (h1 : Dec prof.feat mc2 (j + 3) (FV7z.mk (.sse .movups) 32 [.mem (mbd 7 16 128), .xmm 5] 4))
    (h2 : Dec prof.feat mc2 (j + 3 + 4) (FV7z.mk (.sse .movups) 32 [.mem (mbd 7 32 128), .xmm 6] 4))
    (h3 : Dec prof.feat mc2 (j + 3 + 4 + 4) (FV7z.mk (.sse .movups) 32 [.mem (mbd 7 48 128), .xmm 7] 4))
    (h4 : Dec prof.feat mc2 (j + 3 + 4 + 4 + 4) (FV7z.mk (.sse .movups) 32 [.mem (mbd 11 0 128), .xmm 8] 4))
    (h5 : Dec prof.feat mc2 (j + 3 + 4 + 4 + 4 + 4) (FV7z.mk .ret 64 [] 1)) {g₀ : Gprs} {r : Addr} {b b₀ : Nat}
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (h64 : 64 ≤ g₀.rdx.toNat) (hb₀ : g₀.rdx.toNat - 16 ≤ b₀)
    (hb₀n : b₀ ≤ g₀.rdx.toNat) (hb : b ≤ 64) (hbb : b ≤ b₀)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) {Y : State} {t : Nat} {V₂ : Addr → Byte}
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₂) (hrip : Y.cpu.rip = e.add j)
    (hdi : Y.cpu.gpr.rdi = g₀.rdi) (h11 : Y.cpu.gpr.r11 = Addr.add g₀.rdi (g₀.rdx.toNat - 16))
    (hkp : KpS g₀ Y.cpu.gpr) (hax : Y.cpu.gpr.rax = r)
    (hH : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y.cpu.vec.zmm)) (hF : FwdP V V₂ g₀.rdi g₀.rsi b b₀) :
    GoG prof L o gev gP gE Y t := by
  have he0 : eaD Y 7 0 = Addr.add g₀.rdi 0 := by
    show Y.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 0 = _
    rw [get7, hdi]
    rfl
  refine c.s_movups_stv hK hA hin (by omega) hrip h0 (fun i hi => ?_) ?_
  · rw [he0, addr_add_add]
    exact hst _ (by omega)
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, hv2⟩
  have he1 : eaD Y2 7 16 = Addr.add g₀.rdi 16 := by
    show Y2.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 16 = _
    rw [get7, hg2, hdi]
    rfl
  refine c.s_movups_stv hK2 hA2 hin (by omega) hr2 h1 (fun i hi => ?_) ?_
  · rw [he1, addr_add_add]
    exact hst _ (by omega)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  have he2 : eaD Y3 7 32 = Addr.add g₀.rdi 32 := by
    show Y3.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 32 = _
    rw [get7, hg3, hg2, hdi]
    rfl
  refine c.s_movups_stv hK3 hA3 hin (by omega) hr3 h2 (fun i hi => ?_) ?_
  · rw [he2, addr_add_add]
    exact hst _ (by omega)
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hv4⟩
  have he3 : eaD Y4 7 48 = Addr.add g₀.rdi 48 := by
    show Y4.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 48 = _
    rw [get7, hg4, hg3, hg2, hdi]
    rfl
  refine c.s_movups_stv hK4 hA4 hin (by omega) hr4 h3 (fun i hi => ?_) ?_
  · rw [he3, addr_add_add]
    exact hst _ (by omega)
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have he4 : eaD Y5 11 0 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    show Y5.cpu.gpr.r11 + BitVec.ofNat 64 0 = _
    rw [hg5, hg4, hg3, hg2, h11]
    exact BitVec.add_zero _
  refine c.s_movups_stv hK5 hA5 hin (by omega) hr5 h4 (fun i hi => ?_) ?_
  · rw [he4, addr_add_add]
    exact hst _ (by omega)
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, _⟩
  have hx4 : xlo Y 4 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 0) 16).map V) := hH.x4
  have hx5 : xlo Y2 5 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 16) 16).map V) := by
    show (Y2.cpu.vec.zmm (xmmOf 5)).setWidth 128 = _
    rw [hv2]
    exact hH.x5
  have hx6 : xlo Y3 6 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 32) 16).map V) := by
    show (Y3.cpu.vec.zmm (xmmOf 6)).setWidth 128 = _
    rw [hv3, hv2]
    exact hH.x6
  have hx7 : xlo Y4 7 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 48) 16).map V) := by
    show (Y4.cpu.vec.zmm (xmmOf 7)).setWidth 128 = _
    rw [hv4, hv3, hv2]
    exact hH.x7
  have hx8 : xlo Y5 8 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 16)) 16).map V) := by
    show (Y5.cpu.vec.zmm (xmmOf 8)).setWidth 128 = _
    rw [hv5, hv4, hv3, hv2]
    exact hH.x8
  rw [he0, he1, he2, he3, he4, hx4, hx5, hx6, hx7, hx8, toBytesLE_load, toBytesLE_load, toBytesLE_load,
    toBytesLE_load, toBytesLE_load] at hA6
  have hn := Nat.le_of_lt hd64
  have hl : ∀ p : Addr, ((byteAddrs p 16).map V).length = 16 := fun p => by rw [List.length_map, byteAddrs_len]
  have hC := (hF.copyP hb₀n).st hn (o := 0) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := 16) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := 32) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := 48) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := g₀.rdx.toNat - 16) (k := 16) (hl _) (by omega) CopyP.ld
  have e6 : Y6.cpu.gpr = Y.cpu.gpr := by rw [hg6, hg5, hg4, hg3, hg2]
  refine ret_atC c hin (by omega) h5 hK6 hA6 hr6 (by rw [e6]; exact hkp) (by rw [e6]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi ?_) hC.2 hR
  by_cases c0 : i < 16
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))))
  by_cases c1 : i < 32
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩)))
  by_cases c2 : i < 48
  · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
  by_cases c3 : i < 64
  · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
  by_cases c4 : g₀.rdx.toNat - 16 ≤ i
  · exact Or.inr ⟨c4, by omega⟩
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨by omega, by omega⟩))))

/-- From `695`: the loop, the bytes from offset `b > 64` on stored, until `b ≤ 64`; then `tailBAt`. -/
theorem loopB (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {g₀ : Gprs} {r : Addr} {b₀ : Nat}
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64) (hs64 : g₀.rsi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsd : g₀.rsi.toNat ≤ g₀.rdi.toNat)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64) (hb₀ : g₀.rdx.toNat - 16 ≤ b₀) (hb₀n : b₀ ≤ g₀.rdx.toNat)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) :
    ∀ (m b : Nat) {X : State} {t : Nat} {V₂ : Addr → Byte}, b < m → KeptW Wl s₀ X →
      Agree F X.proc.mm.mem V₂ → X.cpu.rip = e.add 695 → LoopB g₀ r b X.cpu.gpr →
      HeadX V g₀.rsi g₀.rdx.toNat (xsOf X.cpu.vec.zmm) → FwdP V V₂ g₀.rdi g₀.rsi b b₀ → b ≤ b₀ →
      (g₀.rdi.toNat + b) % 16 = 0 → 64 < b → GoG prof L o gev gP gE X t := by
  intro m
  induction m with
  | zero => intro b X t V₂ hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
  intro b X t V₂ hm hK hA hrip hL hH hF hb hal h64
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
  refine c.s_blkV hin (bB695 prof) hK hA hrip ?_
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
  refine c.s_blkV hin (bB710 prof) hK1 hA1 hr1 (wpV_reg fun _ _ => wpV_reg fun _ _ => wpV_nil ?_)
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
  -- four aligned stores at `r9`, downwards
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
  refine c.s_movaps_stv hK2 hA2 hin (by rw [mc2_length]; decide) hr2 (d718 prof.feat)
    (by rw [hed0 h92, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [hed0 h92, addr_add_add]
    exact hst _ (by omega)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  have h93 : Y3.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) := by rw [hg3]; exact h92
  have f3 := hed h93 16 18446744073709551600 (by decide) (by omega)
  refine c.s_movaps_stv hK3 hA3 hin (by rw [mc2_length]; decide) hr3 (d722 prof.feat)
    (by rw [f3, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [f3, addr_add_add]
    exact hst _ (by omega)
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hv4⟩
  have h94 : Y4.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) := by rw [hg4]; exact h93
  have f4 := hed h94 32 18446744073709551584 (by decide) (by omega)
  refine c.s_movaps_stv hK4 hA4 hin (by rw [mc2_length]; decide) hr4 (d727 prof.feat)
    (by rw [f4, toNat_add_of_fits (n := g₀.rdx.toNat) (by omega) hn]; omega) (fun i hi => ?_) ?_
  · rw [f4, addr_add_add]
    exact hst _ (by omega)
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have h95 : Y5.cpu.gpr.r9 = Addr.add g₀.rdi (b - 16) := by rw [hg5]; exact h94
  have f5 := hed h95 48 18446744073709551568 (by decide) (by omega)
  refine c.s_movaps_stv hK5 hA5 hin (by rw [mc2_length]; decide) hr5 (d732 prof.feat)
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
  refine c.s_blkV hin (bB737 prof) hK6 hA6 hr6 (wpV_reg fun _ _ => wpV_nil ?_)
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
  -- `cmp rdx, 64`, `ja 695`
  refine c.s_blkV hin (bB741 prof) hK7 hA7 hr7 (wpV_reg fun fl hP => wpV_nil ?_)
  intro Y8 t8 hK8 hA8 hr8 hg8 hf8 hx8
  simp only [gv, Src.val, get2] at hP
  have hq : (Y7.cpu.gpr.rdx.setWidth 64).toNat = b - 64 := by rw [sw_64_64, hdx7]
  have e8 : Y8.cpu.gpr = Y7.cpu.gpr := by rw [hg8]
  have hH8 : HeadX V g₀.rsi g₀.rdx.toNat (xsOf Y8.cpu.vec.zmm) := by
    rw [hx8]
    exact hH7
  refine c.s_jccV hK8 hA8 hin (by rw [mc2_length]; decide) hr8 (d745 prof.feat) (tgt := 695) rfl
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
  exact tailBAt c hin (by rw [mc2_length]; decide) (d747 _) (d750 _) (d754 _) (d758 _) (d762 _) (d766 _) hst hd64
    hsp hsp8 (by omega) hb₀ hb₀n (by omega) (by omega) hR hK9 hA9 hr9
    (by rw [e9]; exact hdi7) (by rw [e9]; exact h117) (by rw [e9]; exact hkp7) (by rw [e9]; exact hax7)
    (by rw [hv9]; exact hH8) hF6

end FV7z.Memcpy
