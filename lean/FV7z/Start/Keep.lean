import FV7z.Start.Ro
/-!
# Bytes the start code keeps, at `_dl_non_dynamic_init` (PLAN.md G3, startup)

`ptr_img`, `ptr_img_mid`, `ptr_ro` repeat one argument: a byte of the image that no store between the launch and
`0x613434` touches is the launch byte. `ptr_keep` states it once, the memory at `0x613434` given as `PtrW`, and
`ent_keep` carries a byte through `__libc_init_first` and the pushes of `_dl_non_dynamic_init`.

- `PtrW`: the bytes at the call of `__libc_init_first` (`launch_to_ptr`).
- `ptr_keep`: a byte of the image away from the stores of the start code is, there, the launch byte.
- `ent_keep`: a byte below the stack and away from `Lif.LifMem`'s globals is, in `lif_ok`'s bytes, the same.
- `ptr_pl`, `ent_pl`: the word at `0x7a8550` (`.bss`) is 0 (`hpl0` of `Ndi.lif_ok`).
- `ptr_hi`, `ent_keep_hi`: the same for a byte of the stack above `__libc_start_main`'s frame (the strings and
  vectors `execve` puts there, the platform string among them).
- `ent_hw`: `_dl_hwcap` is 2 or 6 (`hhw` and the choice in `hn` of `Ndi.lif_ok`), from `CpuFeat.HwW` at `0x613434`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Tls (TlsMem TlsVar TlsMem_out rd_ext)
open FV7z.StartB (GuardMem PtrMem)

/-- The bytes at the call of `__libc_init_first`: those of `MB` with the TLS block at `b`, the stack guard, the
pointer guard and `_dl_osversion`, where `D` or the TLS block hold and no store of the start code lands. -/
def PtrW (K : Ctx) (W V : Addr → Byte) (b : Addr) (ver : BitVec 32) (D : Addr → Prop) : Prop :=
  ∀ a : Addr, D a ∨ (b.toNat ≤ a.toNat ∧ a.toNat < b.toNat + 8192) → ¬ Junk3 K a →
    ¬ Pim.PimVar (b + 2176#64) a →
    W a = PtrMem (VerMem (GuardMem (TlsMem V b) (b + 2176#64)) ver) (b + 2176#64) a

/-- A byte of the image that the start code does not store to is, at the call of `__libc_init_first`, the byte of
the launch. -/
theorem ptr_keep {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) {a : Addr}
    (h1 : 0x400000 ≤ a.toNat) (h2 : a.toNat + 448 < 0x7a9000) (hDa : D a) (hT : ¬ TlsVar a)
    (hv : ¬ (8029472 ≤ a.toNat ∧ a.toNat < 8029476)) (hd : ¬ Foot (d3 ++ AuxInit.globals) a) (hc : ¬ CpuVar a)
    (hp : ¬ Pim.PimVar (b + 2176#64) a) : W a = K.V0 a := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have hi0 := hK.himg
  rw [hW a (.inl hDa) ?_ hp]
  · unfold PtrMem
    rw [Vst_out]
    · exact ver_img ver hK hM.same hb hb' h1 (by omega) hT hv hd
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  · intro hj
    unfold Junk3 Junk2 Junk at hj
    rcases hj with h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · exact hc h

/-- A byte more than 32 bytes below `g.rsp`, below the pushes of `_dl_non_dynamic_init` and away from the globals
`__libc_init_first` stores to is, in `lif_ok`'s bytes, that at the call of `__libc_init_first`. -/
theorem ent_keep {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp a : Addr}
    (hr : a.toNat + 32 < g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : a.toNat < sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64)
    (hg : ¬ (7944640 ≤ a.toNat ∧ a.toNat < 7944644) ∧ ¬ (8013720 ≤ a.toNat ∧ a.toNat < 8013728) ∧
      ¬ (8029640 ≤ a.toNat ∧ a.toNat < 8029656)) :
    Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY a = W a := by
  obtain ⟨g1, g2, g3⟩ := hg
  unfold Ndi.fV Lif.LifMem Lif.LifStk
  repeat rw [Vst_out]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- At the call of `__libc_init_first`, the word at `0x7a8550` is 0: it is in `.bss` and no store of the start
code reaches it. -/
theorem ptr_pl {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hB : Bss K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add 8029520#64 i)) : rdq(W, 8029520#64) = 0#64 := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have t0 : (8029520#64 : Addr).toNat = 8029520 := rfl
  have h : ∀ i < 8, W (Addr.add 8029520#64 i) = (fun _ => (0 : Byte)) (Addr.add 8029520#64 i) := by
    intro i hi
    have hx : (Addr.add 8029520#64 i).toNat = 8029520 + i := by
      rw [toNat_add_of_fits (a := 8029520#64) (n := 8) hi (by omega), t0]
    have hDa := hD i hi
    generalize Addr.add 8029520#64 i = a at hx hDa ⊢
    have hd : ¬ Foot (d3 ++ AuxInit.globals) a :=
      not_dg (lo := 0x7a8550) (hi := 0x7a8558) (by decide) (by omega) (by omega)
    rw [ptr_keep hK hM hb hb' hW (by omega) (by omega) hDa (by unfold TlsVar; omega) (by omega) hd
      (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)]
    exact hB a (by omega) (by omega)
  rw [rd_ext (W' := W) (W := fun _ => (0 : Byte)) 8029520#64 8 h]
  rfl

/-- `hpl0` of `Ndi.lif_ok`: in the bytes at the `call` of `_dl_non_dynamic_init` after its pushes, the word at
`0x7a8550` is 0. -/
theorem ent_pl {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} (hK : K.Ok) (hB : Bss K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat)
    (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) (hD : ∀ i < 8, D (Addr.add 8029520#64 i))
    (hr : 8029528 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 8029528 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
      8029520#64) = 0#64 := by
  have t0 : (8029520#64 : Addr).toNat = 8029520 := rfl
  have h : ∀ i < 8, Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64)
      (toBytesLE ra 8)) sp gY (Addr.add 8029520#64 i) = W (Addr.add 8029520#64 i) := by
    intro i hi
    have hx : (Addr.add 8029520#64 i).toNat = 8029520 + i := by
      rw [toNat_add_of_fits (a := 8029520#64) (n := 8) hi (by omega), t0]
    exact ent_keep (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩
  rw [rd_ext 8029520#64 8 h]
  exact ptr_pl hK hB hM hb hb' hW hD

/-- A byte of the stack above `__libc_start_main`'s frame and above the break's TLS block is, at the call of
`__libc_init_first`, the byte of the launch: no store of the start code reaches it. -/
theorem ptr_hi {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hM : MB K V)
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) {a : Addr}
    (h1 : K.bp.toNat + 376 ≤ a.toNat) (h2 : b.toNat + 8192 ≤ a.toNat) (hDa : D a) : W a = K.V0 a := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  have ha := a.isLt
  rw [hW a (.inl hDa) ?_ (by unfold Pim.PimVar; omega)]
  · unfold PtrMem
    rw [Vst_out, ver_tls V ver hb' (by omega) (by omega) (by omega),
      TlsMem_out _ hb hb' (by unfold TlsVar; omega) (by omega)]
    · exact hM.same _ (by simp only [InStk]; omega)
        (not_dg (lo := 0x7a9000) (hi := 2 ^ 64) (by decide) (by omega) ha)
    all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega
  · intro hj
    unfold Junk3 Junk2 Junk CpuVar at hj
    omega

/-- A byte above `g.rsp + 8` (the return address of the call of `__libc_init_first`), above the pushes of
`_dl_non_dynamic_init` and above the image is, in `lif_ok`'s bytes, that at the call of `__libc_init_first`. -/
theorem ent_keep_hi {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp a : Addr}
    (hr : g.rsp.toNat + 8 ≤ a.toNat) (hr0 : 32 ≤ g.rsp.toNat) (hsp : sp.toNat + 120 ≤ a.toNat)
    (hg : 0x7a9000 ≤ a.toNat) :
    Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY a = W a := by
  have ha := a.isLt
  unfold Ndi.fV Lif.LifMem Lif.LifStk
  repeat rw [Vst_out]
  all_goals first | (simp only [toBytesLE_length]; bv_omega) | bv_omega

/-- `hhw` of `Ndi.lif_ok`, and which case of `hn`: `_dl_hwcap` (`0x7a4ac8`) is 2 or 6 in the bytes at the `call`
of `_dl_non_dynamic_init` after its pushes, as it is at the call of `__libc_init_first` (`CpuFeat.HwW`). -/
theorem ent_hw {W : Addr → Byte} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr} (h : CpuFeat.HwW W)
    (hr : 0x7a4ad0 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x7a4ad0 ≤ sp.toNat + 80)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        8014536#64) = 2#64 ∨
      rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY,
        8014536#64) = 6#64 := by
  have t0 : (8014536#64 : Addr).toNat = 8014536 := rfl
  have e : ∀ i < 8, Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64)
      (toBytesLE ra 8)) sp gY (Addr.add 8014536#64 i) = W (Addr.add 8014536#64 i) := by
    intro i hi
    have hx : (Addr.add 8014536#64 i).toNat = 8014536 + i := by
      rw [toNat_add_of_fits (a := 8014536#64) (n := 8) hi (by omega), t0]
    exact ent_keep (by omega) hr' (by omega) hsn ⟨by omega, by omega, by omega⟩
  rw [rd_ext 8014536#64 8 e]
  unfold CpuFeat.HwW at h
  exact h

end FV7z.Start
