import FV7z.Start.Ro
import FV7z.Start.Inv
import FV7z.Lemmas.Got
/-!
# `strncmp`'s jump table at the entry of `__libc_init_first` (PLAN.md G3, startup)

`__strncmp_sse2` jumps by the table at `0x6f0df0` in `.rodata` (`NcmpTabV`). The image has its bytes
(`tab_pin`), so the bytes `fV …` at the entry of `__libc_init_first` have them too (`ent_tab`, by `ent_ro`).
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

theorem tab_pin : Exe.bytesAt V2606.zzs.blob 0x6f0df0 64 = some ncmpTab := by decide +kernel

theorem tab_add (k : Nat) : (0x6f0df0 : Addr).add k = BitVec.ofNat 64 (0x6f0df0 + k) := by
  have h0 : (0x6f0df0 : Addr).toNat = 7278064 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat, h0, Nat.reducePow]
  omega

/-- The table's `i`th byte, at `0x6f0df0 + i`. -/
theorem tab_toNat {i : Nat} (hi : i < 64) : ((0x6f0df0 : Addr).add i).toNat = 0x6f0df0 + i := by
  rw [tab_add]
  simp only [BitVec.toNat_ofNat, Nat.reducePow]
  omega

/-- `NcmpTabV` of the bytes at the entry of `__libc_init_first`, after its pushes: the image's. -/
theorem ent_tab {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D)
    (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
    (hr : 0x791ca0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x791ca0 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    NcmpTabV
      (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY) := by
  intro i hi
  have t := tab_toNat hi
  rw [ent_ro (a := (0x6f0df0 : Addr).add i) hK hM hb hb' hW hr hr' hsp hsn (by omega) (by omega)
    (hD _ (by omega) (by omega)), tab_add]
  exact hI _ _ _ tab_pin (by decide) (by decide) i hi

end FV7z.Start
