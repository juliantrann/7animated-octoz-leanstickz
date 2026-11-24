import FV7z.Start.CxaRet
import FV7z.Start.Sdso
/-!
# `__libc_enable_secure` after the return of `__libc_init_first` (PLAN.md G3, startup)

At `0x61344a` glibc 2.31's `__libc_start_main` reads `__libc_enable_secure` (`0x791ce0`) and calls
`__libc_check_standard_fds` for a secure launch only. No layer between `0x613434` and the return of `__cxa_atexit`
stores to it (`sec_ret`), and at `0x613434` it is the `AT_SECURE` value, 0 (`vs_secure`).

- `RetAt.sec`: `__libc_enable_secure` at `0x613439` is 0.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Tls (rd_ext)

variable {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- `__libc_enable_secure` at `0x613439` is 0. -/
theorem RetAt.sec {K : Ctx} {V : Addr → Byte} {ver : BitVec 32} {D : Addr → Prop} (h : RetAt W W₂ Z B g)
    (hK : K.Ok) (hM : MB K V) (hbp : B.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V B ver D)
    (hD : ∀ i < 4, D (Addr.add 7937248#64 i)) :
    rdd(Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3, 7937248#64) = 0#32 := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he; have := h.hg
  have h1 : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have h2 : (B + 4544#64).toNat = B.toNat + 4544 := by bv_omega
  have t0 : (7937248#64 : Addr).toNat = 7937248 := rfl
  have e1 : List.map (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (byteAddrs 7937248#64 4) =
      List.map W (byteAddrs 7937248#64 4) := rd_ext _ 4 fun i hi => by
    have t : (Addr.add 7937248#64 i).toNat = 7937248 + i := by
      rw [toNat_add_of_fits hi (by rw [t0]; omega), t0]
    exact sec_ret (by omega) (by omega) h.nd (by omega) (by omega) (by omega) (by omega) (by omega) h.he'
      (by omega) (by omega) (by omega)
  have e2 := ptr_gl (x := 7937248) (n := 4) h.hb h.hb' hbp hW hD (by unfold GlAt; omega)
  rw [e1, e2]
  exact hM.gl.secure.trans (vs_secure hK K.M (Nat.le_refl _) ⟨K.sn, hK.hsn, hK.hsec⟩).1

end FV7z.Start
