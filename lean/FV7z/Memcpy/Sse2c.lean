import FV7z.Memcpy.Sse2b
/-!
# `__memmove_sse2_unaligned`: the copy of 64 to 128 bytes (PLAN.md M, the PLT contracts)

From `377`, with `64 ≤ rdx ≤ 128`: eight loads (`[rsi + 16k]` and `[rsi + rdx - 16(k+1)]`, `k < 4`), eight stores
at the same offsets from `rdi`, `ret`. As `p448` (`Memcpy/Sse2b.lean`), each store adds its offsets to `CopyP`.

- `bL377`: the loads; `p377`: the copy and the `ret`, as `RetC` (`Memcpy/Erms.lean`) asks.
-/
namespace FV7z.Memcpy
open ZellicX86 Decode FV7z.Leaf FV7z.Fn FV7z.Strlen FV7z.Memset

/-- The eight loads of a copy of 64 to 128 bytes, at `377`. -/
theorem bL377 (prof : Profile) :
    BlkV prof mc2 377 412 [VOp.movups_m 0 6 0, VOp.movups_m 1 6 16, VOp.movups_m 2 6 32,
      VOp.movups_m 3 6 48, VOp.movups_mi 4 6 2 18446744073709551600,
      VOp.movups_mi 5 6 2 18446744073709551584, VOp.movups_mi 6 6 2 18446744073709551568,
      VOp.movups_mi 7 6 2 18446744073709551552] :=
  .cons (d377 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide)
    (.cons (d380 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide)
      (.cons (d384 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide)
        (.cons (d388 prof.feat) VOpI.movups_m (by rw [mc2_length]; decide)
          (.cons (d392 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide)
            (.cons (d397 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide)
              (.cons (d402 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide)
                (.cons (d407 prof.feat) VOpI.movups_mi (by rw [mc2_length]; decide)
                  (.nil _))))))))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle} {F : Footprint} {Wl : List Rgn}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {e : Addr} {V : Addr → Byte}

/-- From `377`, `64 ≤ rdx ≤ 128`: eight loads, eight stores, `ret`. -/
theorem p377 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L e mc2) {X : State} {t : Nat} {g₀ : Gprs} {r : Addr}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = e.add 377)
    (hkp : KpS g₀ X.cpu.gpr) (hax : X.cpu.gpr.rax = r) (hdi : X.cpu.gpr.rdi = g₀.rdi)
    (hsi : X.cpu.gpr.rsi = g₀.rsi) (hdx : X.cpu.gpr.rdx = g₀.rdx)
    (h64 : 64 ≤ g₀.rdx.toNat) (h128 : g₀.rdx.toNat ≤ 128)
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
  have hea2 : eaB X.cpu.gpr 6 32 = Addr.add g₀.rsi 32 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 32 = _
    rw [get6, hsi]
    rfl
  have hea3 : eaB X.cpu.gpr 6 48 = Addr.add g₀.rsi 48 := by
    show X.cpu.gpr.get (regOf 6) + BitVec.ofNat 64 48 = _
    rw [get6, hsi]
    rfl
  have hea4 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551600 = Addr.add g₀.rsi (g₀.rdx.toNat - 16) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rsi g₀.rdx (by decide) (by omega)
  have hea5 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551584 = Addr.add g₀.rsi (g₀.rdx.toNat - 32) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551584 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551584) (k := 32) g₀.rsi g₀.rdx (by decide) (by omega)
  have hea6 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551568 = Addr.add g₀.rsi (g₀.rdx.toNat - 48) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551568 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551568) (k := 48) g₀.rsi g₀.rdx (by decide) (by omega)
  have hea7 : VOp.eaBI X.cpu.gpr 6 2 18446744073709551552 = Addr.add g₀.rsi (g₀.rdx.toNat - 64) := by
    show X.cpu.gpr.get (regOf 6) + X.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551552 = _
    rw [get6, get2, hsi, hdx]
    exact ea_back (D := 18446744073709551552) (k := 64) g₀.rsi g₀.rdx (by decide) (by omega)
  refine c.s_blkV hin (bL377 prof) hK hA hrip ?_
  dsimp only [wpV, VOp.movups_m, VOp.movups_mi]
  refine ⟨fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true,
    fun i hi => ?_, fun h => absurd h Bool.false_ne_true, fun i hi => ?_, fun h => absurd h Bool.false_ne_true, ?_⟩
  · rw [hea0, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea1, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea2, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea3, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea4, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea5, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea6, addr_add_add]
    exact hsrc _ (by omega)
  · rw [hea7, addr_add_add]
    exact hsrc _ (by omega)
  intro Y1 t1 hK1 hA1 hr1 hg1 _ hx
  rw [hea0, hea1, hea2, hea3, hea4, hea5, hea6, hea7] at hx
  have hx0 : xlo Y1 0 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 0) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 0) = _
    rw [hx, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide),
      xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx1 : xlo Y1 1 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 16) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 1) = _
    rw [hx, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide),
      xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx2 : xlo Y1 2 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 32) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 2) = _
    rw [hx, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide),
      xset_ne _ _ (by decide), xset_same]
  have hx3 : xlo Y1 3 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi 48) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 3) = _
    rw [hx, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide),
      xset_same]
  have hx4 : xlo Y1 4 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 16)) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 4) = _
    rw [hx, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx5 : xlo Y1 5 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 32)) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 5) = _
    rw [hx, xset_ne _ _ (by decide), xset_ne _ _ (by decide), xset_same]
  have hx6 : xlo Y1 6 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 48)) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 6) = _
    rw [hx, xset_ne _ _ (by decide), xset_same]
  have hx7 : xlo Y1 7 = ofBytesLE 128 ((byteAddrs (Addr.add g₀.rsi (g₀.rdx.toNat - 64)) 16).map V) := by
    show xsOf Y1.cpu.vec.zmm (xmmOf 7) = _
    rw [hx, xset_same]
  have he0 : eaD Y1 7 0 = Addr.add g₀.rdi 0 := by
    show Y1.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 0 = _
    rw [get7, hg1, hdi]
    rfl
  refine c.s_movups_stv hK1 hA1 hin (by rw [mc2_length]; decide) hr1 (d412 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he0, addr_add_add]
    exact hst _ (by omega)
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2, hv2⟩
  have he1 : eaD Y2 7 16 = Addr.add g₀.rdi 16 := by
    show Y2.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 16 = _
    rw [get7, hg2, hg1, hdi]
    rfl
  have hx1' : xlo Y2 1 = xlo Y1 1 := by
    show (Y2.cpu.vec.zmm (xmmOf 1)).setWidth 128 = _
    rw [hv2]
  refine c.s_movups_stv hK2 hA2 hin (by rw [mc2_length]; decide) hr2 (d415 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he1, addr_add_add]
    exact hst _ (by omega)
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hv3⟩
  have he2 : eaD Y3 7 32 = Addr.add g₀.rdi 32 := by
    show Y3.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 32 = _
    rw [get7, hg3, hg2, hg1, hdi]
    rfl
  have hx2' : xlo Y3 2 = xlo Y1 2 := by
    show (Y3.cpu.vec.zmm (xmmOf 2)).setWidth 128 = _
    rw [hv3, hv2]
  refine c.s_movups_stv hK3 hA3 hin (by rw [mc2_length]; decide) hr3 (d419 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he2, addr_add_add]
    exact hst _ (by omega)
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hv4⟩
  have he3 : eaD Y4 7 48 = Addr.add g₀.rdi 48 := by
    show Y4.cpu.gpr.get (regOf 7) + BitVec.ofNat 64 48 = _
    rw [get7, hg4, hg3, hg2, hg1, hdi]
    rfl
  have hx3' : xlo Y4 3 = xlo Y1 3 := by
    show (Y4.cpu.vec.zmm (xmmOf 3)).setWidth 128 = _
    rw [hv4, hv3, hv2]
  refine c.s_movups_stv hK4 hA4 hin (by rw [mc2_length]; decide) hr4 (d423 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he3, addr_add_add]
    exact hst _ (by omega)
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, hv5⟩
  have he4 : eaI Y5 7 2 18446744073709551600 = Addr.add g₀.rdi (g₀.rdx.toNat - 16) := by
    show Y5.cpu.gpr.get (regOf 7) + Y5.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551600 = _
    rw [get7, get2, hg5, hg4, hg3, hg2, hg1, hdi, hdx]
    exact ea_back (D := 18446744073709551600) (k := 16) g₀.rdi g₀.rdx (by decide) (by omega)
  have hx4' : xlo Y5 4 = xlo Y1 4 := by
    show (Y5.cpu.vec.zmm (xmmOf 4)).setWidth 128 = _
    rw [hv5, hv4, hv3, hv2]
  refine c.s_movups_sti hK5 hA5 hin (by rw [mc2_length]; decide) hr5 (d427 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he4, addr_add_add]
    exact hst _ (by omega)
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6, hv6⟩
  have he5 : eaI Y6 7 2 18446744073709551584 = Addr.add g₀.rdi (g₀.rdx.toNat - 32) := by
    show Y6.cpu.gpr.get (regOf 7) + Y6.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551584 = _
    rw [get7, get2, hg6, hg5, hg4, hg3, hg2, hg1, hdi, hdx]
    exact ea_back (D := 18446744073709551584) (k := 32) g₀.rdi g₀.rdx (by decide) (by omega)
  have hx5' : xlo Y6 5 = xlo Y1 5 := by
    show (Y6.cpu.vec.zmm (xmmOf 5)).setWidth 128 = _
    rw [hv6, hv5, hv4, hv3, hv2]
  refine c.s_movups_sti hK6 hA6 hin (by rw [mc2_length]; decide) hr6 (d432 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he5, addr_add_add]
    exact hst _ (by omega)
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, hv7⟩
  have he6 : eaI Y7 7 2 18446744073709551568 = Addr.add g₀.rdi (g₀.rdx.toNat - 48) := by
    show Y7.cpu.gpr.get (regOf 7) + Y7.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551568 = _
    rw [get7, get2, hg7, hg6, hg5, hg4, hg3, hg2, hg1, hdi, hdx]
    exact ea_back (D := 18446744073709551568) (k := 48) g₀.rdi g₀.rdx (by decide) (by omega)
  have hx6' : xlo Y7 6 = xlo Y1 6 := by
    show (Y7.cpu.vec.zmm (xmmOf 6)).setWidth 128 = _
    rw [hv7, hv6, hv5, hv4, hv3, hv2]
  refine c.s_movups_sti hK7 hA7 hin (by rw [mc2_length]; decide) hr7 (d437 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he6, addr_add_add]
    exact hst _ (by omega)
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, hv8⟩
  have he7 : eaI Y8 7 2 18446744073709551552 = Addr.add g₀.rdi (g₀.rdx.toNat - 64) := by
    show Y8.cpu.gpr.get (regOf 7) + Y8.cpu.gpr.get (regOf 2) + BitVec.ofNat 64 18446744073709551552 = _
    rw [get7, get2, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1, hdi, hdx]
    exact ea_back (D := 18446744073709551552) (k := 64) g₀.rdi g₀.rdx (by decide) (by omega)
  have hx7' : xlo Y8 7 = xlo Y1 7 := by
    show (Y8.cpu.vec.zmm (xmmOf 7)).setWidth 128 = _
    rw [hv8, hv7, hv6, hv5, hv4, hv3, hv2]
  refine c.s_movups_sti hK8 hA8 hin (by rw [mc2_length]; decide) hr8 (d442 prof.feat)
    (fun i hi => ?_) ?_
  · rw [he7, addr_add_add]
    exact hst _ (by omega)
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9, _⟩
  rw [he0, he1, he2, he3, he4, he5, he6, he7,
    hx1', hx2', hx3', hx4', hx5', hx6', hx7',
    hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7,
    toBytesLE_load, toBytesLE_load, toBytesLE_load, toBytesLE_load,
    toBytesLE_load, toBytesLE_load, toBytesLE_load, toBytesLE_load] at hA9
  have hn := Nat.le_of_lt hd64
  have hl : ∀ a : Addr, ((byteAddrs a 16).map V).length = 16 := fun a => by
    rw [List.length_map, byteAddrs_len]
  have hC := (CopyP.start V g₀.rdi g₀.rsi g₀.rdx.toNat).st hn (o := 0) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := 16) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := 32) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := 48) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := (g₀.rdx.toNat - 16)) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := (g₀.rdx.toNat - 32)) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := (g₀.rdx.toNat - 48)) (k := 16) (hl _) (by omega) CopyP.ld
  have hC := hC.st hn (o := (g₀.rdx.toNat - 64)) (k := 16) (hl _) (by omega) CopyP.ld
  refine ret_atC c hin (by rw [mc2_length]; decide) (d447 prof.feat) hK9 hA9 hr9
    (by rw [hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]; exact hkp)
    (by rw [hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]; exact hax)
    (fun i hi => hC.2 _ fun ⟨h1, h2⟩ => by rw [toNat_add_of_fits (n := 8) hi hsp8] at h1 h2; omega)
    (fun i hi => hC.1 i hi ?_) hC.2 hR
  by_cases c0 : i < 16
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩)))))))
  by_cases c1 : i < 32
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))))))
  by_cases c2 : i < 48
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩)))))
  by_cases c3 : i < 64
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))))
  by_cases c4 : g₀.rdx.toNat - 16 ≤ i
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩)))
  by_cases c5 : g₀.rdx.toNat - 32 ≤ i
  · exact Or.inl (Or.inl (Or.inr ⟨by omega, by omega⟩))
  by_cases c6 : g₀.rdx.toNat - 48 ≤ i
  · exact Or.inl (Or.inr ⟨by omega, by omega⟩)
  exact Or.inr ⟨by omega, by omega⟩

end FV7z.Memcpy
