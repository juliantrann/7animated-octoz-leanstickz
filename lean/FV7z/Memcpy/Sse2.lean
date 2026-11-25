import FV7z.Memcpy.Erms
import FV7z.Lemmas.Sse2c
import FV7z.Lemmas.CopyP
/-!
# `__memmove_sse2_unaligned`: the copy of 16 to 32 bytes (PLAN.md M, the PLT contracts)

From `43` (`__memmove_sse2_unaligned`) and `227` (`__memmove_sse2_unaligned_erms`), with `16 ≤ rdx ≤ 32`:
`movups xmm0, [rsi]`, `movups xmm1, [rsi + rdx - 16]`, `movups [rdi], xmm0`, `movups [rdi + rdx - 16], xmm1`, `ret`.
Both loads come before the stores, so the source and the destination may overlap. The stores overlap each other;
`CopyP` (`Lemmas/CopyP.lean`) adds the offsets of each.

- `C16`: the decodings from `43` and from `227` (`c16_43`, `c16_227`); `bL16`: the loads.
- `p16`: the copy and the `ret`, as `RetC` (`Memcpy/Erms.lean`) asks.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The `movups` decodings of a copy of 16 to 32 bytes from `j`: two loads, two stores, `ret`. -/
structure C16 (feat : Features) (j : Nat) : Prop where
  l0 : Dec feat mc2 j (FV7z.mk (.sse (.movups)) 32 [.xmm 0, .mem (mbd 6 0 128)] 3)
  l1 : Dec feat mc2 (j + 3) (FV7z.mk (.sse (.movups)) 32 [.xmm 1, .mem (mbi 6 2 18446744073709551600 128)] 5)
  s0 : Dec feat mc2 (j + 3 + 5) (FV7z.mk (.sse (.movups)) 32 [.mem (mbd 7 0 128), .xmm 0] 3)
  s1 : Dec feat mc2 (j + 3 + 5 + 3) (FV7z.mk (.sse (.movups)) 32 [.mem (mbi 7 2 18446744073709551600 128), .xmm 1] 5)
  rt : Dec feat mc2 (j + 3 + 5 + 3 + 5) (FV7z.mk .ret 64 [] 1)
  lt : j + 3 + 5 + 3 + 5 < mc2.length

theorem c16_43 (feat : Features) : C16 feat 43 :=
  ⟨d43 feat, d46 feat, d51 feat, d54 feat, d59 feat, by rw [mc2_length]; decide⟩

theorem c16_227 (feat : Features) : C16 feat 227 :=
  ⟨d227 feat, d230 feat, d235 feat, d238 feat, d243 feat, by rw [mc2_length]; decide⟩

/-- The two loads of a copy of 16 to 32 bytes, from `j`. -/
theorem bL16 {prof : Profile} {j : Nat} (h : C16 prof.feat j) :
    BlkV prof mc2 j (j + 3 + 5) [VOp.movups_m 0 6 0, VOp.movups_mi 1 6 2 18446744073709551600] :=
  .cons h.l0 VOpI.movups_m (by have := h.lt; omega)
    (.cons h.l1 VOpI.movups_mi (by have := h.lt; show j + 3 < _; omega) (.nil _))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- A load of 16 bytes stored back: the bytes. -/
theorem toBytesLE_load (V : Addr → Byte) (a : Addr) :
    toBytesLE (ofBytesLE 128 ((byteAddrs a 16).map V)) 16 = (byteAddrs a 16).map V := by
  have h := toBytesLE_ofBytesLE (w := 128) (bs := (byteAddrs a 16).map V) (by rw [List.length_map, byteAddrs_len])
  rwa [List.length_map, byteAddrs_len] at h

/-- From `j` (`43` or `227`), `16 ≤ rdx ≤ 32`: two loads, two stores, `ret`. -/
theorem p16 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {j : Nat} (hc : C16 prof.feat j) {X : State} {t : Nat}
    {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add j)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h16 : 16 ≤ g₀.rdx.toNat) (h32 : g₀.rdx.toNat ≤ 32)
    (hsrc : ∀ i < g₀.rdx.toNat, Foot F.data (Addr.add g₀.rsi i))
    (hst : ∀ i < g₀.rdx.toNat, Foot Wl (Addr.add g₀.rdi i))
    (hd64 : g₀.rdi.toNat + g₀.rdx.toNat < 2 ^ 64)
    (hsp : g₀.rdi.toNat + g₀.rdx.toNat ≤ g₀.rsp.toNat ∨ g₀.rsp.toNat + 8 ≤ g₀.rdi.toNat)
    (hsp8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (hR : RetC prof F Wl L s₀ o gev gP gE V g₀ r) : GoG prof L o gev gP gE X t := by
  have hea1 : eaB X.cpu.gpr 6 0 = Addr.add g₀.rsi 0 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 0 = _
    rw [get6, hsi]
    rfl
  have hea2 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551600 = Addr.add g₀.rsi (g₀.rdx.toNat - 16) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rsi g₀.rdx (by decide) h16
  have hlt := hc.lt
  refine c.s_blkV hin (bL16 hc) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m, VOp.movups_mi]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    ?_⟩
  · rw [hea1, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea2, addr_add_add]
    exact hsrc _ (by omega)
  intro Y t₁ hK₁ hA₁ hr₁ hg₁ _ hx₁
  rw [hea1, hea2] at hx₁
  have hx0 : xlo Y 0 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 0) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 0) = _
    rw [hx₁, xset_ne _ _ (by decide), xset_same]
  have hx1 : xlo Y 1 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 16)) 16).map V) := by
    show xsOf Y.cpu.vec.zmm (xmmOf 1) = _
    rw [hx₁, xset_same]
  have he1 : eaD Y 7 0 = Addr.add g₀.rdi 0 := by
    show Y.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 0 = _
    rw [get7, hg₁, hdi]
    rfl
  refine c.s_movups_stv hK₁ hA₁ hin (by omega) hr₁ hc.s0 (fun i hi => ?_) ?_
  · rw [he1, addr_add_add]
    exact hst _ (by omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂, hv₂⟩
  have he2 : eaI Y₂ 7 2 18446744073709551600 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    show Y₂.cpu.gpr.get (regOf 7) + Y₂.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get7, get2, hg₂, hg₁, hdi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rdi g₀.rdx (by decide) h16
  have hx1' : xlo Y₂ 1 = xlo Y 1 := by
    show (Y₂.cpu.vec.zmm (xmmOf 1)).setWidth 128 = _
    rw [hv₂]
  refine c.s_movups_sti hK₂ hA₂ hin (by omega) hr₂ hc.s1 (fun i hi => ?_) ?_
  · rw [he2, addr_add_add]
    exact hst _ (by omega)
  rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃, _⟩
  rw [he1, he2, hx1', hx0, hx1, toBytesLE_load, toBytesLE_load] at hA₃
  have hC := ((CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st (Nat.le_of_lt hd64) (o := 0) (k := 16)
    (by rw [List.length_map, byteAddrs_len]) (by omega) CopyP.ld).st (Nat.le_of_lt hd64)
    (o := g₀.rdx.toNat - 16) (k := 16) (by rw [List.length_map, byteAddrs_len]) (by omega) CopyP.ld
  refine ret_atC c hin hlt hc.rt hK₃ hA₃ hr₃ (by rw [hg₃, hg₂, hg₁]; exact hkp)
    (by rw [hg₃, hg₂, hg₁]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi (if h : i < 16 then Or.inl (Or.inr ⟨Nat.zero_le _, by omega⟩)
      else Or.inr ⟨by omega, by omega⟩)) hC.2 hR

end FV7z.Memcpy
