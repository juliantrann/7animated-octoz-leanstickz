import FV7z.Start.Ctp
import FV7z.Lif.Ent
/-!
# The reads of `__ctype_init` from the call of `__libc_init_first` (PLAN.md G3, startup)

`Ndi.lif_ok` asks, on the bytes `W` at the call of `_dl_non_dynamic_init`, for `rdq(W, fs - 112) = lp`,
`rdq(W, lp) = ct` and the three table pointers at `ct + 64`, `ct + 72`, `ct + 88` (`hlp`, `hct`, `ha`, `hb`,
`hc`). `W` is the bytes at `0x613434` (`launch_to_ptr`) with the stores of the `call` and of `lif_a`
(`Lif.ent_rd`); `ptr_lpv`, `ptr_img` and `v0_ct` give the values.

- `ent_ct`: the five reads, `lp = 0x7922c0`, `ct = 0x7806e0`, the tables `0x6f6140`, `0x6f5740`, `0x6f5140`, for a
  stack above the break's TLS block and image bytes in the data footprint.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tls (TlsMem)
open FV7z.StartB (GuardMem PtrMem)

/-- The five reads of `__ctype_init`, in the bytes at the call of `_dl_non_dynamic_init`: `g` the registers at the
entry of `__libc_init_first`, `V` the bytes at `0x613434`. -/
theorem ent_ct {K : Ctx} {W V' : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g : Gprs}
    {ra ra₀ : BitVec 64} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V') (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hbp : b.toNat + 2072 + 448 < K.bp.toNat)
    (hW : ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
      ¬ Pim.PimVar (b + 2176#64) a →
      W a = PtrMem (VerMem (GuardMem (TlsMem V' b) (b + 2176#64)) ver) (b + 2176#64) a)
    (hD : ∀ a : Addr, 0x780000 ≤ a.toNat → a.toNat < 0x7933cc → D a)
    (hgs : b.toNat + 2072 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) :
    rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8),
        b + 2176#64 - 112#64) = 7938752#64 ∧
      rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8),
        7938752#64) = 7866080#64 ∧
      rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8),
        7866080#64 + 64#64) = 7299392#64 ∧
      rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8),
        7866080#64 + 72#64) = 7296832#64 ∧
      rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8),
        7866080#64 + 88#64) = 7295296#64 := by
  have hr : 32 ≤ g.rsp.toNat := by omega
  have img : ∀ y : Addr, (0x780000 ≤ y.toNat ∧ y.toNat + 8 ≤ 0x791ca0 ∨ 0x7922b8 ≤ y.toNat ∧ y.toNat + 8 ≤ 0x7933cc) →
      rdq(Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8), y) =
        rdq(K.V0, y) := by
    intro y hy
    have hyl : y.toNat + 8 ≤ 0x7933cc := by omega
    rw [Lif.ent_rd (y := y) hr hr' (.inl (by omega)) (by omega) (.inl (by omega))]
    exact ptr_img hK hM hb hb' hW hy fun i hi =>
      hD _ (by rw [toNat_add_of_fits (a := y) (n := 8) hi (by omega)]; omega)
        (by rw [toNat_add_of_fits (a := y) (n := 8) hi (by omega)]; omega)
  have hbn : (b + 2064#64).toNat = b.toNat + 2064 := by bv_omega
  have e1 : b + 2176#64 - 112#64 = b + 2064#64 := by bv_omega
  have t1 : (7938752#64 : Addr).toNat = 7938752 := rfl
  have t2 : (7866144#64 : Addr).toNat = 7866144 := rfl
  have t3 : (7866152#64 : Addr).toNat = 7866152 := rfl
  have t4 : (7866168#64 : Addr).toNat = 7866168 := rfl
  have c := v0_ct hI
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, Lif.ent_rd (y := b + 2064#64) hr hr' (.inr (by omega)) (by omega) (.inl (by omega))]
    exact ptr_lpv hK hI hM hb hb' hbp hW
  · rw [img _ (.inr ⟨by omega, by omega⟩)]
    exact c.1
  · rw [show (7866080#64 : Addr) + 64#64 = 7866144#64 by decide, img _ (.inl ⟨by omega, by omega⟩)]
    exact c.2.1
  · rw [show (7866080#64 : Addr) + 72#64 = 7866152#64 by decide, img _ (.inl ⟨by omega, by omega⟩)]
    exact c.2.2.1
  · rw [show (7866080#64 : Addr) + 88#64 = 7866168#64 by decide, img _ (.inl ⟨by omega, by omega⟩)]
    exact c.2.2.2

end FV7z.Start
