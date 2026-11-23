import FV7z.Start.Plat
import FV7z.Start.Pgs
import FV7z.Start.Keep
/-!
# `_dl_phdr` and `_dl_phnum` at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `rdq(·, 0x7a8580) = 0x400040` (`h2`, `_dl_phdr`) and `rdq(·, 0x7a8598) = 8` (`h3`,
`_dl_phnum`). `_dl_aux_init` sets them from `AT_PHDR` and `AT_PHNUM`; no later store of the start code touches them.

- `ptr_gl`, `ent_gl`: a word of the variables above `0x7a8418` (but `_dl_osversion` and the CPU variables) is, in the
  bytes at `0x613434` and in `lif_ok`'s, that of `MB`.
- `ent_phd`: `h2` and `h3` of `lif_ok`, with `ctxOf_ph` (`TlsIn.lean`).
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar TlsMem_out rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- A word of the variables above `0x7a8418`, away from `_dl_osversion` (`0x7a8520`) and `_dl_platform`, is at the
call of `__libc_init_first` that of the bytes `MB` describes. -/
theorem ptr_gl {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {x : Nat}
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat)
    (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add (BitVec.ofNat 64 x) i))
    (hx : 0x7a8418 ≤ x ∧ x + 8 ≤ 0x7a8520 ∨ 0x7a8580 ≤ x ∧ x + 8 ≤ 0x7a9000) :
    rdq(W, BitVec.ofNat 64 x) = rdq(V, BitVec.ofNat 64 x) := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have t0 : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h : ∀ i < 8, W (Addr.add (BitVec.ofNat 64 x) i) = V (Addr.add (BitVec.ofNat 64 x) i) := by
    intro i hi
    have hx' : (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := by
      rw [toNat_add_of_fits (a := BitVec.ofNat 64 x) (n := 8) hi (by omega), t0]
    have hDa := hD i hi
    generalize Addr.add (BitVec.ofNat 64 x) i = a at hx' hDa ⊢
    rw [hW a (.inl hDa) ?_ ?_]
    · unfold PtrMem
      rw [Vst_out, ver_tls V ver hb' (by omega) (by omega) (by omega),
        TlsMem_out _ hb hb' (by unfold TlsVar; omega) (by omega)]
      all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
    · intro hj
      unfold Junk3 Junk2 Junk at hj
      rcases hj with h | h | h | h | h
      · omega
      · omega
      · omega
      · omega
      · unfold CpuVar at h
        omega
    · unfold Pim.PimVar
      omega
  rw [rd_ext (W' := W) (W := V) (BitVec.ofNat 64 x) 8 h]

/-- The same word in `lif_ok`'s bytes, below `0x7a85c8` (`Lif.LifMem`'s globals). -/
theorem ent_gl {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr} {x : Nat}
    (hx : 0x7a8418 ≤ x ∧ x + 8 ≤ 0x7a8520 ∨ 0x7a8580 ≤ x ∧ x + 8 ≤ 8029640)
    (hr : x + 8 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : x + 8 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      BitVec.ofNat 64 x) = rdq(W, BitVec.ofNat 64 x) := by
  have t0 : (BitVec.ofNat 64 x).toNat = x := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h : ∀ i < 8, Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64)
      (toBytesLE ra 8)) sp gY (Addr.add (BitVec.ofNat 64 x) i) = W (Addr.add (BitVec.ofNat 64 x) i) := by
    intro i hi
    have hx' : (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := by
      rw [toNat_add_of_fits (a := BitVec.ofNat 64 x) (n := 8) hi (by omega), t0]
    exact ent_keep (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩
  rw [rd_ext (BitVec.ofNat 64 x) 8 h]

/-- `h2` and `h3` of `lif_ok`: `_dl_phdr` is `0x400040` and `_dl_phnum` 8. -/
theorem ent_phd {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hM : MB K V) (hph : (K.vs K.M).phdr = 0x400040#64)
    (hpn : (K.vs K.M).phnum = 8#64) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD1 : ∀ i < 8, D (Addr.add 8029568#64 i)) (hD2 : ∀ i < 8, D (Addr.add 8029592#64 i))
    (hr : 8029600 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 8029600 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        8029568#64) = 4194368#64 ∧
      rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        8029592#64) = 8#64 :=
  ⟨((ent_gl (x := 8029568) (.inr ⟨by omega, by omega⟩) (by omega) hr' (by omega) hsn).trans
      (ptr_gl (x := 8029568) hb hb' hbp hW hD1 (.inr ⟨by omega, by omega⟩))).trans (hM.gl.phdr.trans hph),
    ((ent_gl (x := 8029592) (.inr ⟨by omega, by omega⟩) (by omega) hr' (by omega) hsn).trans
      (ptr_gl (x := 8029592) hb hb' hbp hW hD2 (.inr ⟨by omega, by omega⟩))).trans (hM.gl.phnum.trans hpn)⟩

end FV7z.Start
