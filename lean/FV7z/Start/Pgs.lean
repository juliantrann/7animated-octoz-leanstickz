import FV7z.Start.Lp
import FV7z.Start.Psz
/-!
# `_dl_pagesize` at the call of `__libc_init_first` (PLAN.md G3, startup)

`Ndi.lif_ok` asks for `rdq(·, 0x7933d8) = 4096` (`hpgs`). None of the stores between `_dl_aux_init` and `0x613434`
(`__libc_setup_tls`, the stack guard, `_dl_osversion`, `__pthread_initialize_minimal`, the pointer guard) touches
`_dl_pagesize`.

- `ptr_ps`: in the bytes at `0x613434` (`launch_to_ptr`), `rdq(0x7933d8)` is that of the bytes `MB` describes, so
  4096 when `(K.vs K.M).pagesize = 4096` (`Start.ctxOf_ps` for a state `execve` starts 7zzs in).
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar TlsMem_out rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- At the call of `__libc_init_first`, `_dl_pagesize` is 4096. -/
theorem ptr_ps {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hM : MB K V)
    (hps : (K.vs K.M).pagesize = 4096#64) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 2072 + 448 < K.bp.toNat)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a)
    (hD : ∀ i < 8, D (Addr.add 7943128#64 i)) : rdq(W, 7943128#64) = 4096#64 := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have t0 : (7943128#64 : Addr).toNat = 7943128 := rfl
  have h : ∀ i < 8, W (Addr.add 7943128#64 i) = V (Addr.add 7943128#64 i) := by
    intro i hi
    have hx : (Addr.add 7943128#64 i).toNat = 7943128 + i := by
      rw [toNat_add_of_fits (a := 7943128#64) (n := 8) hi (by omega), t0]
    have hDa := hD i hi
    generalize Addr.add 7943128#64 i = a at hx hDa ⊢
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
  rw [← mb_ps hM hps, rd_ext (W' := W) (W := V) 7943128#64 8 h]

end FV7z.Start
