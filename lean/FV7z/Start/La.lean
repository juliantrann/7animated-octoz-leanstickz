import FV7z.Start.Ctp
/-!
# The word at `0x7934e0` at the call of `__libc_init_first` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `rdq(·, 0x7934e0) = 0` (`hla`, read by `_dl_non_dynamic_init`'s tail). It is a `.data` word
that is 0 in the file, and `[0x793408, 0x793908)` holds no variable the start code stores to (`globals`, `d3`,
`TlsVar`, `PimVar`, `CpuVar` all lie outside).

- `ptr_img_mid`: 8 bytes in `[0x793408, 0x793908)` are, at `0x613434`, those of the launch (as `ptr_img`).
- `la_pin`: in the file, the 8 bytes at `0x7934e0` are 0.
- `ptr_la`: at `0x613434`, `rdq(0x7934e0) = 0`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- 8 bytes of `[0x793408, 0x793908)` are, at the call of `__libc_init_first`, those of the launch. -/
theorem ptr_img_mid {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a) {y : Addr}
    (hy : 0x793408 ≤ y.toNat ∧ y.toNat + 8 ≤ 0x793908)
    (hD : ∀ i < 8, D (y.add i)) : rdq(W, y) = rdq(K.V0, y) := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  suffices h : ∀ i < 8, W (y.add i) = K.V0 (y.add i) by rw [rd_ext (W' := W) (W := K.V0) y 8 h]
  intro i hi
  have hx : (y.add i).toNat = y.toNat + i := toNat_add_of_fits hi (by omega)
  have hDa := hD i hi
  generalize y.add i = a at hx hDa ⊢
  have hd : ¬ Foot (d3 ++ AuxInit.globals) a :=
    not_dg (lo := 0x793408) (hi := 0x793908) (by decide) (by omega) (by omega)
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

/-- The word at `0x7934e0` in the file: 0. -/
theorem la_pin : Exe.bytesAt V2606.zzs.blob 0x7934e0 8 = some [0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- At the call of `__libc_init_first`, the word at `0x7934e0` is 0. -/
theorem ptr_la {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a)
    (hD : ∀ i < 8, D (Addr.add 7943392#64 i)) : rdq(W, 7943392#64) = 0#64 := by
  have t0 : (7943392#64 : Addr).toNat = 7943392 := rfl
  rw [ptr_img_mid hK hM hb hb' hW ⟨by rw [t0]; omega, by rw [t0]; omega⟩ hD]
  show ofBytesLE 64 (List.map K.V0 (byteAddrs (BitVec.ofNat 64 (0x7934e0 + 0)) 8)) = _
  rw [hI.map la_pin rfl (by decide) (by decide) (off := 0) (m := 8) (by decide)]
  rfl

end FV7z.Start
