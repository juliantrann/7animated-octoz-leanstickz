import FV7z.Start.Lp
/-!
# The locale tables at the call of `__libc_init_first` (PLAN.md G3, startup)

`__ctype_init` (`Lif.lif_c`) reads `lp = rdq(fs - 112)` (`0x7922c0`, `Start.ptr_lpv`), then `ct = rdq(lp)` and the
three table pointers at `ct + 64`, `ct + 72`, `ct + 88`. Those bytes lie in the image, where nothing has stored
since the launch.

- `ptr_img`: 8 bytes of the image in `[0x780000, 0x791ca0)` or `[0x7922b8, 0x7933cc)` (apart from the variables of
  the start code) are, at `0x613434`, those of the launch (`K.V0`).
- `ct_pin`, `tab_pin`: in the file, `rdq(0x7922c0) = 0x7806e0` (`_nl_C_LC_CTYPE`), and the 32 bytes at
  `0x780720` hold `0x6f6140`, `0x6f5740`, 0, `0x6f5140`; measured by gdb on 26.06 as well.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- 8 bytes of the image away from what the start code stores are, at the call of `__libc_init_first`, those of
the launch. -/
theorem ptr_img {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a) {y : Addr}
    (hy : 0x780000 ≤ y.toNat ∧ y.toNat + 8 ≤ 0x791ca0 ∨ 0x7922b8 ≤ y.toNat ∧ y.toNat + 8 ≤ 0x7933cc)
    (hD : ∀ i < 8, D (y.add i)) : rdq(W, y) = rdq(K.V0, y) := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have hi0 := hK.himg
  suffices h : ∀ i < 8, W (y.add i) = K.V0 (y.add i) by rw [rd_ext (W' := W) (W := K.V0) y 8 h]
  intro i hi
  have hx : (y.add i).toNat = y.toNat + i := toNat_add_of_fits hi (by omega)
  have hDa := hD i hi
  generalize y.add i = a at hx hDa ⊢
  have hd : ¬ Foot (d3 ++ globals) a := by
    rcases hy with h | h
    · exact not_dg (lo := 0x780000) (hi := 0x791ca0) (by decide) (by omega) (by omega)
    · exact not_dg (lo := 0x7922b8) (hi := 0x7933cc) (by decide) (by omega) (by omega)
  rw [hW a (.inl hDa) ?_ ?_]
  · unfold PtrMem
    rw [Vst_out]
    · exact ver_img ver hK hM.same hb hb' (by omega) (by omega) (by unfold TlsVar; omega) (by omega) hd
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

/-- `_nl_global_locale`'s `LC_CTYPE` entry in the file: `0x7806e0`. -/
theorem ct_pin : Exe.bytesAt V2606.zzs.blob 0x7922c0 8 = some [0xe0, 0x06, 0x78, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Bytes 64 to 96 of `_nl_C_LC_CTYPE` in the file: the class, `toupper` and `tolower` tables at `+64`, `+72`,
`+88`. -/
theorem tab_pin : Exe.bytesAt V2606.zzs.blob 0x780720 32 = some [0x40, 0x61, 0x6f, 0, 0, 0, 0, 0,
    0x40, 0x57, 0x6f, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x40, 0x51, 0x6f, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- The four reads of `__ctype_init` in the launch bytes. -/
theorem v0_ct {K : Ctx} (hI : Img K.V0) :
    rdq(K.V0, 7938752#64) = 7866080#64 ∧ rdq(K.V0, 7866144#64) = 7299392#64 ∧
      rdq(K.V0, 7866152#64) = 7296832#64 ∧ rdq(K.V0, 7866168#64) = 7295296#64 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ofBytesLE 64 (List.map K.V0 (byteAddrs (BitVec.ofNat 64 0x7922c0) 8)) = _
    rw [hI.rd ct_pin rfl (by decide) (by decide)]
    rfl
  · show ofBytesLE 64 (List.map K.V0 (byteAddrs (BitVec.ofNat 64 (0x780720 + 0)) 8)) = _
    rw [hI.map tab_pin rfl (by decide) (by decide) (off := 0) (m := 8) (by decide)]
    rfl
  · show ofBytesLE 64 (List.map K.V0 (byteAddrs (BitVec.ofNat 64 (0x780720 + 8)) 8)) = _
    rw [hI.map tab_pin rfl (by decide) (by decide) (off := 8) (m := 8) (by decide)]
    rfl
  · show ofBytesLE 64 (List.map K.V0 (byteAddrs (BitVec.ofNat 64 (0x780720 + 24)) 8)) = _
    rw [hI.map tab_pin rfl (by decide) (by decide) (off := 24) (m := 8) (by decide)]
    rfl

end FV7z.Start
