import FV7z.Memcpy.Sse2
/-!
# `__memmove_sse2_unaligned`: the copy of 32 to 64 bytes (PLAN.md M, the PLT contracts)

From `448`, with `32 ≤ rdx ≤ 64`: four loads (`[rsi]`, `[rsi + 16]`, `[rsi + rdx - 16]`, `[rsi + rdx - 32]`),
four stores at the same offsets from `rdi`, `ret`. As `p16` (`Memcpy/Sse2.lean`), each store adds its offsets to
`CopyP`.

- `bL448`: the loads; `p448`: the copy and the `ret`, as `RetC` (`Memcpy/Erms.lean`) asks.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The four loads of a copy of 32 to 64 bytes, at `448`. -/
theorem bL448 (prof : Profile) :
    BlkV prof mc2 448 465 [VOp.movups_m 0 6 0, VOp.movups_m 1 6 16, VOp.movups_mi 2 6 2 18446744073709551600,
      VOp.movups_mi 3 6 2 18446744073709551584] :=
  .cons (d448 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide)
    (.cons (d451 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide)
      (.cons (d455 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide)
        (.cons (d460 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide) (.nil _))))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `448`, `32 ≤ rdx ≤ 64`: four loads, four stores, `ret`. -/
theorem p448 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 448)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h32 : 32 ≤ g₀.rdx.toNat) (h64 : g₀.rdx.toNat ≤ 64)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hea0 : eaB X.cpu.gpr 6 0 = Addr.add g₀.rsi 0 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 0 = _
    rw [get6, hsi]
    rfl
  have hea1 : eaB X.cpu.gpr 6 16 = Addr.add g₀.rsi 16 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 16 = _
    rw [get6, hsi]
    rfl
  have hea2 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551600 = Addr.add g₀.rsi (g₀.rdx.toNat - 16) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rsi g₀.rdx (by decide) (by omega)
  have hea3 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551584 = Addr.add g₀.rsi (g₀.rdx.toNat - 32) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551584 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551584) (k := 32) g₀.rsi g₀.rdx (by decide) h32
  refine c.s_blkV hin (bL448 prof) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m, VOp.movups_mi]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true, ?_⟩
  · rw [hea0, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea1, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea2, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea3, addr_add_add]
    exact hsrc _ (by omega)
  intro Y t₁ hK₁ hA₁ hr₁ hg₁ _ hx₁
  rw [hea0, hea1, hea2, hea3] at hx₁
  have hx0 : xlo Y 0 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 0) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 0) = _
    rw [hx₁, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx1 : xlo Y 1 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 16) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 1) = _
    rw [hx₁, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx2 : xlo Y 2 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 16)) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 2) = _
    rw [hx₁, xset_ne _ _ (by decide), xset_same]
  have hx3 : xlo Y 3 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 32)) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 3) = _
    rw [hx₁, xset_same]
  have he0 : eaD Y 7 0 = Addr.add g₀.rdi 0 := by
    show Y.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 0 = _
    rw [get7, hg₁, hdi]
    rfl
  refine c.s_movups_stv hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d465 prof.feat) (fun i hi => ?_) ?_
  · rw [he0, addr_add_add]
    exact hst _ (by omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
  have he1 : eaD Y₂ 7 16 = Addr.add g₀.rdi 16 := by
    show Y₂.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 16 = _
    rw [get7, hg₂, hg₁, hdi]
    rfl
  have hx1' : xlo Y₂ 1 = xlo Y 1 := by
    show (Y₂.cpu.vec.zmm (xmmOf 1)).setWidth 128 = _
    rw [hv₂]
  refine c.s_movups_stv hK₂ hA₂ hin (by rw [mc2_length]; decide) hr₂ (d468 prof.feat) (fun i hi => ?_) ?_
  · rw [he1, addr_add_add]
    exact hst _ (by omega)
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, hv₃⟩
  have he2 : eaI Y₃ 7 2 18446744073709551600 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    show Y₃.cpu.gpr.get (regOf 7) + Y₃.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get7, get2, hg₃, hg₂, hg₁, hdi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rdi g₀.rdx (by decide) (by omega)
  have hx2' : xlo Y₃ 2 = xlo Y 2 := by
    show (Y₃.cpu.vec.zmm (xmmOf 2)).setWidth 128 = _
    rw [hv₃, hv₂]
  refine c.s_movups_sti hK₃ hA₃ hin (by rw [mc2_length]; decide) hr₃ (d472 prof.feat) (fun i hi => ?_) ?_
  · rw [he2, addr_add_add]
    exact hst _ (by omega)
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄, hv₄⟩
  have he3 : eaI Y₄ 7 2 18446744073709551584 = Addr.add g₀.rdi (g₀.rdx.toNat - 32) := by
    show Y₄.cpu.gpr.get (regOf 7) + Y₄.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551584 = _
    rw [get7, get2, hg₄, hg₃, hg₂, hg₁, hdi, hdx]
    exact ea_back (D := 18446744073709551584) (k := 32) g₀.rdi g₀.rdx (by decide) h32
  have hx3' : xlo Y₄ 3 = xlo Y 3 := by
    show (Y₄.cpu.vec.zmm (xmmOf 3)).setWidth 128 = _
    rw [hv₄, hv₃, hv₂]
  refine c.s_movups_sti hK₄ hA₄ hin (by rw [mc2_length]; decide) hr₄ (d477 prof.feat) (fun i hi => ?_) ?_
  · rw [he3, addr_add_add]
    exact hst _ (by omega)
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅, _⟩
  rw [he0, he1, he2, he3, hx1', hx2', hx3', hx0, hx1, hx2, hx3, toBytesLE_load, toBytesLE_load, toBytesLE_load,
    toBytesLE_load] at hA₅
  have hn := Nat.le_of_lt hd64
  have hl : ∀ a : Addr, ((byteAddrs a 16).map V).length = 16 := fun a => by rw [List.length_map, byteAddrs_len]
  have hC := ((((CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st hn (o := 0) (k := 16) (hl _) (by omega)
    CopyP.ld).st hn (o := 16) (k := 16) (hl _) (by omega) CopyP.ld).st hn
    (o := g₀.rdx.toNat - 16) (k := 16) (hl _) (by omega) CopyP.ld).st hn
    (o := g₀.rdx.toNat - 32) (k := 16) (hl _) (by omega) CopyP.ld
  refine ret_atC c hin (by rw [mc2_length]; decide) (d482 prof.feat) hK₅ hA₅ hr₅
    (by rw [hg₅, hg₄, hg₃, hg₂, hg₁]; exact hkp) (by rw [hg₅, hg₄, hg₃, hg₂, hg₁]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi (if h : i < 16 then Or.inl (Or.inl (Or.inl (Or.inr ⟨Nat.zero_le _, by omega⟩)))
      else if h' : i < 32 then Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
      else if h'' : g₀.rdx.toNat - 16 ≤ i then Or.inl (Or.inr ⟨h'', by omega⟩)
      else Or.inr ⟨by omega, by omega⟩)) hC.2 hR

end FV7z.Memcpy
