import FV7z.Start.PlEnt
/-!
# `argv[0]` in `lif_ok`'s bytes (PLAN.md G3, startup)

`Ndi.lif_ok` states `ha0`, `nnz`, `nz` of its `W`, the bytes at the entry of `__libc_init_first` after `lif_a`'s
stores: the bytes at the `call` (`launch_to_ptr`'s `W`) with the return address of the `call`, `Lif.LifMem`'s
globals and stack words, and the return address of the next `call`. Above `rsp + 8` and the image, those are the
bytes at the `call`, which above the TLS block and `__libc_start_main`'s frame are the launch bytes (`ptr_hi`).

- `lif_hi`: a byte above `rsp + 8`, the image, the TLS block and the frame, in `lif_ok`'s `W`, is the launch byte.
- `lif_rdq_hi`: 8 such bytes.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (rd_ext)

theorem lif_hi {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g : Gprs}
    {ra ra₀ : BitVec 64} (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) {a : Addr} (hbp : K.bp.toNat + 376 ≤ a.toNat) (htl : b.toNat + 8192 ≤ a.toNat)
    (hr : g.rsp.toNat + 8 ≤ a.toNat) (hr0 : 32 ≤ g.rsp.toNat) (hDa : D a) :
    Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8) a = K.V0 a := by
  have ha := a.isLt
  rw [← ptr_hi hM hb hb' hW hbp htl hDa]
  unfold Lif.LifMem Lif.LifStk
  repeat rw [Vst_out]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

theorem lif_rdq_hi {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g : Gprs}
    {ra ra₀ : BitVec 64} (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) {y : Addr} (hy : y.toNat + 8 ≤ 2 ^ 64) (hbp : K.bp.toNat + 376 ≤ y.toNat)
    (htl : b.toNat + 8192 ≤ y.toNat) (hr : g.rsp.toNat + 8 ≤ y.toNat) (hr0 : 32 ≤ g.rsp.toNat)
    (hD : ∀ i < 8, D (Addr.add y i)) :
    rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8), y) = rdq(K.V0, y) :=
  rd_ext _ 8 fun i hi => by
    have t : (Addr.add y i).toNat = y.toNat + i := toNat_add_of_fits (n := 8) hi (by omega)
    exact lif_hi hM hb hb' hW (by omega) (by omega) (by omega) hr0 (hD i hi)

end FV7z.Start
