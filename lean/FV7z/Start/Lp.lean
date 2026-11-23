import FV7z.Start.ToPtr
import FV7z.Tls.Lp
/-!
# The locale slot at the call of `__libc_init_first` (PLAN.md G3, startup)

`launch_to_ptr` describes the bytes at `0x613434` as `PtrMem (VerMem (GuardMem (TlsMem V b) fb) ver) fb`, `fb =
b + 2176`, outside `Junk3` and `Pim.PimVar`. None of those stores touches `fs - 112 = b + 2064`.

- `ptr_lp`: there the slot holds byte 16 of the TLS image (`Tls.TlsMem_lp`), which `Tls.lp_pin` gives as
  `0x7922c0` in the file.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsMem_lp rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- At the call of `__libc_init_first`, the slot `fs - 112` holds byte 16 of the TLS initialisation image. -/
theorem ptr_lp {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop}
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a) :
    rdq(W, b + 2064#64) = rdq(V, 7829376#64) := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have h : ∀ i < 8, W ((b + 2064#64).add i) = TlsMem V b ((b + 2064#64).add i) := by
    intro i hi
    have hx : ((b + 2064#64).add i).toNat = b.toNat + 2064 + i := by simp only [Addr.add]; bv_omega
    generalize (b + 2064#64).add i = x at hx ⊢
    rw [hW x (Or.inr ⟨by omega, by omega⟩) ?_ ?_]
    · unfold PtrMem VerMem GuardMem
      rw [Vst_out, Vst_out, Vst_out, Vst_out]
      all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
    · intro hj
      unfold Junk3 at hj
      rcases hj with ⟨h1, -⟩ | hj
      · omega
      · exact not_junk2 (by omega) (by unfold CpuVar; omega) hj
    · unfold Pim.PimVar
      omega
  rw [← TlsMem_lp V hb hb', rd_ext (W' := W) (W := TlsMem V b) (b + 2064#64) 8 h]

end FV7z.Start
