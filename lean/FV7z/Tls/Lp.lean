import FV7z.Tls.Mem
/-!
# The locale slot in the TLS block (PLAN.md G3, startup)

`Lif.lif_c` (by `__ctype_init`) reads `fs - 112`, the TLS slot `_nl_current_LC_CTYPE`. With the break `b`,
`__libc_setup_tls` puts the thread control block at `b + 2176` (the `fs` base) and copies the 40 bytes of the TLS
initialisation image (`0x777770`) to `b + 2048`, so `fs - 112 = b + 2064` is byte 16 of the image.

- `TlsMem_lp`: the 8 bytes at `b + 2064` in the bytes `__libc_setup_tls` leaves are those at `0x777780`.
- `lp_pin`: in the file they are `0x7922c0` (`_nl_global_locale`'s `LC_CTYPE` entry; measured by gdb on 26.06).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (Vst_out)
open FV7z.CpuFeat (Vst_at)

namespace FV7z.Tls

/-- The slot `fs - 112` after `__libc_setup_tls` holds byte 16 of the TLS initialisation image. -/
theorem TlsMem_lp (V : Addr → Byte) {b : Addr} (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) :
    rdq(TlsMem V b, b + 2064#64) = rdq(V, 7829376#64) := by
  have hl : ((byteAddrs 7829360#64 40).map V).length = 40 := by simp [byteAddrs]
  have hbn : (b + 2064#64).toNat = b.toNat + 2064 := by bv_omega
  have hbm : (2048#64 + b).toNat = b.toNat + 2048 := by bv_omega
  have t1 : (7829376#64 : Addr).toNat = 7829376 := rfl
  have t2 : (7829360#64 : Addr).toNat = 7829360 := rfl
  have h : ∀ i < 8, TlsMem V b (Addr.add (b + 2064#64) i) = V (Addr.add 7829376#64 i) := by
    intro i hi
    have hx : (Addr.add (b + 2064#64) i).toNat = b.toNat + 2064 + i := by
      rw [toNat_add_of_fits (a := b + 2064#64) (n := 8) hi (by omega), hbn]
    have he : Addr.add (b + 2064#64) i = Addr.add (2048#64 + b) (16 + i) := by
      apply BitVec.eq_of_toNat_eq
      rw [hx, toNat_add_of_fits (a := 2048#64 + b) (n := 24) (by omega) (by omega), hbm]
      omega
    have hv : Addr.add 7829376#64 i = Addr.add 7829360#64 (16 + i) := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_add_of_fits (a := 7829376#64) (n := 8) hi (by omega),
        toNat_add_of_fits (a := 7829360#64) (n := 24) (by omega) (by omega), t1, t2]
      omega
    generalize Addr.add (b + 2064#64) i = x at hx he ⊢
    unfold TlsMem WD WC T4
    rw [Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out, Vst_out,
      Vst_out, Vst_out, Vst_out]
    · rw [he, Vst_at ((byteAddrs 7829360#64 40).map V) (T3 V b) (2048#64 + b) (j := 16 + i) (by rw [hl]; omega)
        (by rw [hl]; bv_omega), hv]
      simp only [List.getElem_map, byteAddrs, List.getElem_range]
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  refine congrArg (ofBytesLE 64) (List.ext_getElem (by simp only [List.length_map, byteAddrs, List.length_range]) ?_)
  intro i h1 h2
  simp only [List.length_map, byteAddrs, List.length_range] at h1
  simp only [List.getElem_map, byteAddrs, List.getElem_range]
  exact h i h1

/-- Byte 16 of the TLS initialisation image in the file: `0x7922c0`. -/
theorem lp_pin : Exe.bytesAt V2606.zzs.blob 0x777780 8 = some [0xc0, 0x22, 0x79, 0, 0, 0, 0, 0] := by
  decide +kernel

end FV7z.Tls
