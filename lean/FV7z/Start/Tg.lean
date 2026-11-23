import FV7z.Start.Ro2
import FV7z.Tgv.Holds
/-!
# Tunable 11 at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`Ndi.lif_ok` asks that tunable 11 (its entry at `0x7918c8`, in `.data.rel.ro`) be unset (`hU`: type 1, not
initialized) with value 6 (`hm6`). The entry is below `0x791ca0`, so at the call of `_dl_non_dynamic_init` its
bytes are those of the file (`Start.ent_rdn`).

- `t11_pin`: the type, value and `initialized` byte of the entry in the file.
- `v0_t11`: so in the launch bytes.
- `ent_t11`, `ent_unset`: `hm6` and `hU` of `lif_ok`, the footprint parts of `hU` given.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tls (TlsMem)
open FV7z.StartB (GuardMem PtrMem)

theorem t11_8 : Tgv.ent 11#64 + 8#64 = BitVec.ofNat 64 7936208 := by decide
theorem t11_32 : Tgv.ent 11#64 + 32#64 = BitVec.ofNat 64 7936232 := by decide
theorem t11_40 : Tgv.ent 11#64 + 40#64 = BitVec.ofNat 64 7936240 := by decide

/-- The type of tunable 11 in the file: 1. -/
theorem t11_ty : Exe.bytesAt V2606.zzs.blob 7936208 4 = some [1, 0, 0, 0] := by decide +kernel
/-- Its value: 6. -/
theorem t11_va : Exe.bytesAt V2606.zzs.blob 7936232 8 = some [6, 0, 0, 0, 0, 0, 0, 0] := by decide +kernel
/-- Its `initialized` byte: 0. -/
theorem t11_in : Exe.bytesAt V2606.zzs.blob 7936240 1 = some [0] := by decide +kernel

/-- Tunable 11 in the launch bytes. -/
theorem v0_t11 {V : Addr → Byte} (hI : Img V) :
    rdd(V, Tgv.ent 11#64 + 8#64) = 1#32 ∧ rdq(V, Tgv.ent 11#64 + 32#64) = 6#64 ∧
      rdb(V, Tgv.ent 11#64 + 40#64) = 0#8 := by
  rw [t11_8, t11_32, t11_40, img_rd hI t11_ty rfl (by omega) (by omega), img_rd hI t11_va rfl (by omega) (by omega),
    img_rd hI t11_in rfl (by omega) (by omega)]
  exact ⟨rfl, rfl, rfl⟩

section E
variable {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
  {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
  (hb' : b.toNat + 8192 ≤ 2 ^ 63)
  (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
    ¬ Pim.PimVar (b + 2176#64) a →
    W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a)
  (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
  (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
  (hsn : sp.toNat + 120 ≤ 2 ^ 64)
include hK hI hM hb hb' hW hD hr hr' hsp hsn

/-- Tunable 11 in `lif_ok`'s bytes: type 1, value 6 (`hm6`), not initialized. -/
theorem ent_t11 :
    let M := Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY
    rdd(M, Tgv.ent 11#64 + 8#64) = 1#32 ∧ rdq(M, Tgv.ent 11#64 + 32#64) = 6#64 ∧
      rdb(M, Tgv.ent 11#64 + 40#64) = 0#8 := by
  intro M
  have c := v0_t11 hI
  rw [t11_8, t11_32, t11_40] at c ⊢
  exact ⟨(congrArg (ofBytesLE 32) (ent_rdn hK hM hb hb' hW hD hr hr' hsp hsn (x := 7936208) (n := 4) (by omega)
      (by omega))).trans c.1,
    (congrArg (ofBytesLE 64) (ent_rdn hK hM hb hb' hW hD hr hr' hsp hsn (x := 7936232) (n := 8) (by omega)
      (by omega))).trans c.2.1,
    (congrArg (ofBytesLE 8) (ent_rdn hK hM hb hb' hW hD hr hr' hsp hsn (x := 7936240) (n := 1) (by omega)
      (by omega))).trans c.2.2⟩

/-- `hU` of `lif_ok`, from the footprint. -/
theorem ent_unset {F : Footprint} (hty : ∀ i < 4, Foot F.data ((Tgv.ent 11#64 + 8#64).add i))
    (hva : ∀ i < 8, Foot F.data ((Tgv.ent 11#64 + 32#64).add i))
    (hin : ∀ i < 1, Foot F.data ((Tgv.ent 11#64 + 40#64).add i)) :
    Tgv.UnsetW F
      (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
      11#64 := by
  obtain ⟨c1, -, c3⟩ := ent_t11 (ra := ra) (ra₀ := ra₀) (gY := gY) hK hI hM hb hb' hW hD hr hr' hsp hsn
  exact ⟨hty, hva, hin, fun h => absurd (c1.symm.trans h) (by decide), c3⟩

end E

end FV7z.Start
