import FV7z.Start.Sdso
import FV7z.Start.Fpu
import FV7z.Start.La
/-!
# More words of the image at `_dl_non_dynamic_init` (PLAN.md G3, startup)

The words `Ndi.lif_ok` reads that are already known at the call of `__libc_init_first`, carried to `lif_ok`'s bytes.

- `ent_pgs`: `hpgs`, `_dl_pagesize` (`0x7933d8`) is 4096 (`ptr_ps`).
- `ent_la`: `hla`, the word at `0x7934e0` is 0 (`ptr_la`).
- `ptr_fw`: `hfw`, `__fpu_control` and `_dl_fpu_control` agree at the call of `__libc_init_first` (`mb_fpu`).
- `pse_pin`, `ent_pse`: `hpp`, `"/proc/self/exe"` at `0x7068e3` in the bytes at the entry of `_dl_get_origin`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (rd_ext)

/-- `hpgs` of `lif_ok`: `_dl_pagesize` is 4096. -/
theorem ent_pgs {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hM : MB K V) (hps : (K.vs K.M).pagesize = 4096#64)
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat)
    (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add 7943128#64 i)) (hr : 7943136 + 32 ≤ g.rsp.toNat)
    (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 7943136 ≤ sp.toNat + 80) (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      7943128#64) = 4096#64 := by
  have e := ent_gl (W := W) (ra := ra) (ra₀ := ra₀) (gY := gY) (x := 7943128) (n := 8)
    (by unfold KpAt; omega) hr hr' hsp hsn
  rw [e]
  exact ptr_ps hM hps hb hb' hbp hW hD

/-- `hla` of `lif_ok`: the word at `0x7934e0` is 0. -/
theorem ent_la {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add 7943392#64 i))
    (hr : 7943400 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 7943400 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      7943392#64) = 0#64 := by
  have e := ent_gl (W := W) (ra := ra) (ra₀ := ra₀) (gY := gY) (x := 7943392) (n := 8)
    (by unfold KpAt; omega) hr hr' hsp hsn
  rw [e]
  exact ptr_la hK hI hM hb hb' hW hD

/-- `hfw` of `lif_ok`: at the call of `__libc_init_first`, `__fpu_control` is `_dl_fpu_control`, both `0x037f`. -/
theorem ptr_fw {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hI : Img K.V0) (hM : MB K V) (hfp : (K.vs K.M).fpuControl = K.w0.fpuControl) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD1 : ∀ i < 2, D (Addr.add 7945344#64 i)) (hD2 : ∀ i < 2, D (Addr.add 7943116#64 i)) :
    rdw(W, 7945344#64) = rdw(W, 7943116#64) := by
  have e1 := ptr_gl (x := 7945344) (n := 2) hb hb' hbp hW hD1 (by unfold GlAt; omega)
  have e2 := ptr_gl (x := 7943116) (n := 2) hb hb' hbp hW hD2 (by unfold GlAt; omega)
  have m := mb_fpu hK hI hM hfp
  rw [e1, e2, m.1, m.2]

/-- `"/proc/self/exe"` in the file. -/
theorem pse_pin : Exe.bytesAt V2606.zzs.blob 0x7068e3 14 =
    some [0x2f, 0x70, 0x72, 0x6f, 0x63, 0x2f, 0x73, 0x65, 0x6c, 0x66, 0x2f, 0x65, 0x78, 0x65] := by
  decide +kernel

/-- `hpp` of `lif_ok`: `"/proc/self/exe"` in the bytes at the entry of `_dl_get_origin`. -/
theorem ent_pse {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) (hD : ∀ i < 14, D (Addr.add 7366691#64 i))
    (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    (byteAddrs 7366691#64 14).map
      (Ndi.nV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY) =
      Gor.pse := by
  have e := rd_ext (W' := Ndi.nV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64)
      (toBytesLE ra 8)) sp gY) (W := K.V0) (7366691#64) 14 fun i hi => by
    have t := tg (b := 7366691) hi (by omega)
    unfold Ndi.nV
    rw [Vst_out]
    · exact ent_ro hK hM hb hb' hW hr hr' hsp hsn (by omega) (by omega) (hD i hi)
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  rw [e, Img.rd hI pse_pin rfl (by decide) (by decide), Gor.pse_eq]

end FV7z.Start
