import FV7z.Start.Plat
import FV7z.Start.Pgs
import FV7z.Start.Keep
/-!
# `_dl_phdr` and `_dl_phnum` at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `rdq(·, 0x7a8580) = 0x400040` (`h2`, `_dl_phdr`) and `rdq(·, 0x7a8598) = 8` (`h3`,
`_dl_phnum`). `_dl_aux_init` sets them from `AT_PHDR` and `AT_PHNUM`; no later store of the start code touches them.

- `GlAt`, `ptr_gl`, `ent_gl`, `ent_v`: bytes of `.data` below the GOT or of the variables above `0x7a8418` (but
  `_dl_osversion` and the CPU variables) are, at `0x613434` and in `lif_ok`'s bytes, those of `MB`.
- `bss_rdq`: a word of `.bss` is 0 in the launch bytes.
- `ent_phd`: `h2` and `h3` of `lif_ok`, with `ctxOf_ph` (`TlsIn.lean`).
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar TlsMem_out rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- Bytes `[x, x + n)` that no store of the start code after `_dl_aux_init` reaches, nor `__libc_init_first`: in
`.data` below the GOT, or among the variables above `0x7a8418` but `_dl_osversion` (`0x7a8520`), `_dl_platform` and
`Lif.LifMem`'s globals (from `0x7a85c8`). -/
def GlAt (x n : Nat) : Prop :=
  0x791ca0 ≤ x ∧ x + n ≤ 0x792018 ∨ 0x7a8418 ≤ x ∧ x + n ≤ 0x7a8520 ∨
    0x7a8580 ≤ x ∧ x + n ≤ 8029640

/-- Such bytes are, at the call of `__libc_init_first`, those `MB` describes. -/
theorem ptr_gl {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {x n : Nat}
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat)
    (hW : PtrW K W V b ver D) (hD : ∀ i < n, D (Addr.add (BitVec.ofNat 64 x) i)) (hx : GlAt x n) :
    List.map W (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) := by
  unfold GlAt at hx
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  refine rd_ext (W' := W) (W := V) _ n fun i hi => ?_
  have hx' : (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := tg hi (by omega)
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

/-- The same bytes in `lif_ok`'s bytes. -/
theorem ent_gl {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr} {x n : Nat} (hx : GlAt x n)
    (hr : x + n + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : x + n ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    List.map (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
        (byteAddrs (BitVec.ofNat 64 x) n) = List.map W (byteAddrs (BitVec.ofNat 64 x) n) := by
  unfold GlAt at hx
  refine rd_ext _ n fun i hi => ?_
  have hx' : (Addr.add (BitVec.ofNat 64 x) i).toNat = x + i := tg hi (by omega)
  exact ent_keep (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩

/-- Both: such bytes in `lif_ok`'s bytes are those of `MB`. -/
theorem ent_v {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} {x n : Nat} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD : ∀ i < n, D (Addr.add (BitVec.ofNat 64 x) i)) (hx : GlAt x n) (hr : x + n + 32 ≤ g.rsp.toNat)
    (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : x + n ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    List.map (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
        (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) :=
  (ent_gl hx hr hr' hsp hsn).trans (ptr_gl hb hb' hbp hW hD hx)

/-- A word of `.bss` is 0 in the launch bytes. -/
theorem bss_rdq {V : Addr → Byte} (hB : Bss V) {x : Nat} (hx : 0x7945d0 ≤ x ∧ x + 8 ≤ 0x7a86c0) :
    rdq(V, BitVec.ofNat 64 x) = 0#64 := by
  have e := rd_ext (W' := V) (W := fun _ => (0 : Byte)) (BitVec.ofNat 64 x) 8 fun i hi => by
    have t := tg (b := x) hi (by omega)
    exact hB _ (by omega) (by omega)
  rw [e]
  rfl

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
        8029592#64) = 8#64 := by
  have e1 := ent_v (ra := ra) (ra₀ := ra₀) (gY := gY) (x := 8029568) (n := 8) hb hb' hbp hW hD1
    (by unfold GlAt; omega) (by omega) hr' (by omega) hsn
  have e2 := ent_v (ra := ra) (ra₀ := ra₀) (gY := gY) (x := 8029592) (n := 8) hb hb' hbp hW hD2
    (by unfold GlAt; omega) (by omega) hr' (by omega) hsn
  rw [e1, e2]
  exact ⟨hM.gl.phdr.trans hph, hM.gl.phnum.trans hpn⟩

end FV7z.Start
