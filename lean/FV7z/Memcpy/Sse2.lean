import FV7z.Memcpy.Erms
import FV7z.Lemmas.Sse2c
import FV7z.Lemmas.CopyP
/-!
# `__memmove_sse2_unaligned`: the copy of 16 to 32 bytes (PLAN.md M, the PLT contracts)

From `43` (`__memmove_sse2_unaligned`) and `227` (`__memmove_sse2_unaligned_erms`), with `16 ≤ rdx ≤ 32`:
`movups xmm0, [rsi]`, `movups xmm1, [rsi + rdx - 16]`, `movups [rdi], xmm0`, `movups [rdi + rdx - 16], xmm1`, `ret`.
Both loads come before the stores, so the source and the destination may overlap. The stores overlap each other;
`CopyP` (`Lemmas/CopyP.lean`) adds the offsets of each.

- `bL43`: the loads; `p43`: the copy and the `ret`, as `RetC` (`Memcpy/Erms.lean`) asks.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The two loads of a copy of 16 to 32 bytes, at `43`. -/
theorem bL43 (prof : Profile) :
    BlkV prof mc2 43 51 [VOp.movups_m 0 6 0, VOp.movups_mi 1 6 2 18446744073709551600] :=
  .cons (d43 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide)
    (.cons (d46 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide) (.nil _))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- A load of 16 bytes stored back: the bytes. -/
theorem toBytesLE_load (V : Addr → Byte) (a : Addr) :
    toBytesLE (ofBytesLE 128 ((byteAddrs a 16).map V)) 16 = (byteAddrs a 16).map V := by
  have h := toBytesLE_ofBytesLE (w := 128) (bs := (byteAddrs a 16).map V) (by rw [List.length_map, byteAddrs_len])
  rwa [List.length_map, byteAddrs_len] at h

/-- From `43`, `16 ≤ rdx ≤ 32`: two loads, two stores, `ret`. -/
theorem p43 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 43)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h16 : 16 ≤ g₀.rdx.toNat) (h32 : g₀.rdx.toNat ≤ 32)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hea1 : eaB X.cpu.gpr 6 0 = g₀.rsi.add 0 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 0 = _
    rw [get6, hsi]
    rfl
  have hea2 : eaBI X.cpu.gpr 6 2 18446744073709551600 = g₀.rsi.add (g₀.rdx.toNat - 16) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back g₀.rsi g₀.rdx rfl h16
  refine c.s_blkV hin (bL43 prof) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m, VOp.movups_mi]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    ?_⟩
  · rw [hea1, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea2, addr_add_add]
    exact hsrc _ (by omega)
  intro Y t₁ hK₁ hA₁ hr₁ hg₁ _ hx₁
  simp only [hea1, hea2] at hx₁
  have hx0 : xlo Y 0 = ofBytesLE 128 ((byteAddrs (g₀.rsi.add 0) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 0) = _
    rw [hx₁, xset_ne _ _ (by decide), xset_same]
  have hx1 : xlo Y 1 = ofBytesLE 128 ((byteAddrs (g₀.rsi.add (g₀.rdx.toNat - 16)) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 1) = _
    rw [hx₁, xset_same]
  have he1 : eaD Y 7 0 = g₀.rdi.add 0 := by
    show Y.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 0 = _
    rw [get7, hg₁, hdi]
    rfl
  refine c.s_movups_stv hK₁ hA₁ hin (by rw [mc2_length]; decide) hr₁ (d51 prof.feat) (fun i hi => ?_) ?_
  · rw [he1, addr_add_add]
    exact hst _ (by omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
  have he2 : eaI Y₂ 7 2 18446744073709551600 = g₀.rdi.add (g₀.rdx.toNat - 16) := by
    show Y₂.cpu.gpr.get (regOf 7) + Y₂.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get7, get2, hg₂, hg₁, hdi, hdx]
    exact ea_back g₀.rdi g₀.rdx rfl h16
  have hx1' : xlo Y₂ 1 = xlo Y 1 := by
    show (Y₂.cpu.vec.zmm (xmmOf 1)).setWidth 128 = _
    rw [hv₂]
  refine c.s_movups_sti hK₂ hA₂ hin (by rw [mc2_length]; decide) hr₂ (d54 prof.feat) (fun i hi => ?_) ?_
  · rw [he2, addr_add_add]
    exact hst _ (by omega)
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
  rw [he1, he2, hx1', hx0, hx1, toBytesLE_load, toBytesLE_load] at hA₃
  have hC := ((CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st (Nat.le_of_lt hd64) (o := 0) (k := 16)
    (by rw [List.length_map, byteAddrs_len]) (by omega) CopyP.ld).st (Nat.le_of_lt hd64)
    (o := g₀.rdx.toNat - 16) (k := 16) (by rw [List.length_map, byteAddrs_len]) (by omega) CopyP.ld
  refine ret_atC c hin (by rw [mc2_length]; decide) (d59 prof.feat) hK₃ hA₃ hr₃ (by rw [hg₃, hg₂, hg₁]; exact hkp)
    (by rw [hg₃, hg₂, hg₁]; exact hax) (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => ?_) (fun i hi => hC.1 i hi ?_) hC.2 hR
  · rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2
    omega
  · by_cases h : i < 16
    · exact .inl (.inr ⟨Nat.zero_le _, by omega⟩)
    · exact .inr ⟨by omega, by omega⟩

end FV7z.Memcpy
