import FV7z.Start.Lw
import FV7z.Start.Tg
/-!
# The byte conditions of `lif_ok`, together (PLAN.md G3, startup)

`Ndi.lif_ok` states some twenty facts about its bytes `fV W sp gY`: words of `.data` and `.bss` that are 0 or
set by `_dl_aux_init`, strings and tables in `.rodata`, tunable 11, `_dl_hwcap`. Each has its lemma; `ent_bytes`
gives them all from the conditions they share: the launch facts (`K.Ok`, `Img`, `Bss`, `MB`, `_dl_aux_init`'s
values), the bytes at the call of `__libc_init_first` (`PtrW`), and where `rsp` and `sp` lie (above the image and
the variables).

- `ent_bytes`: `h1`–`h5`, `hpn`, `hpz`, `hpp`, `hoz`, `hx1`, `hx1z`, `hx2`, `hx2z`, `hm6`, `_dl_hwcap`, `hpl0`,
  `hlenV`, `hslV`, `hph`, `hpgs`, `hla`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

set_option maxHeartbeats 800000 in
/-- The byte conditions of `lif_ok` for `M = fV …`, the bytes at the entry of `__libc_init_first` after its
pushes. -/
theorem ent_bytes {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} {M : Addr → Byte}
    (hMe : M = Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
    (hK : K.Ok) (hI : Img K.V0) (hB : Bss K.V0) (hM : MB K V) (hps : (K.vs K.M).pagesize = 4096#64)
    (hph : (K.vs K.M).phdr = 0x400040#64) (hpn : (K.vs K.M).phnum = 8#64)
    (hsd : (K.vs K.M).sysinfoDso = K.w0.sysinfoDso) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hbp : b.toNat + 2072 + 448 < K.bp.toNat) (hW : PtrW K W V b ver D)
    (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x7a9000 → D a) (hHw : CpuFeat.HwW W)
    (hr : 0x7a9000 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x7a9000 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) :
    rdq(M, 8029448#64) = 0#64 ∧ rdq(M, 8029568#64) = 4194368#64 ∧ rdq(M, 8029592#64) = 8#64 ∧
    rdq(M, 8029424#64) = 0#64 ∧ rdd(M, 7937248#64) = 0#32 ∧
    (∀ i < 14, M (Addr.add 7366691#64 i) ≠ 0) ∧ M (Addr.add 7366691#64 14) = 0 ∧
    (byteAddrs 7366691#64 14).map M = pse ∧ rdq(M, 8029440#64) = 0#64 ∧
    (∀ k < 6, M (Addr.add 7288953#64 k) ≠ 0) ∧ M (Addr.add 7288953#64 6) = 0 ∧
    (∀ k < 8, M (Addr.add 7288962#64 k) ≠ 0) ∧ M (Addr.add 7288962#64 8) = 0 ∧
    rdq(M, Tgv.ent 11#64 + 32#64) = 6#64 ∧ (rdq(M, 8014536#64) = 2#64 ∨ rdq(M, 8014536#64) = 6#64) ∧
    rdq(M, 8029520#64) = 0#64 ∧
    (∀ k < 3, rdq(M, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (Ipa.lA k)) ∧
    (∀ k < 3, ofBytesLE 8 (List.map M (byteAddrs (BitVec.ofNat 64 (Ipa.sA k)) 1)) = 47#8) ∧
    Ndi.Ph M ∧ rdq(M, 7943128#64) = 4096#64 ∧ rdq(M, 7943392#64) = 0#64 := by
  subst hMe
  have dv : ∀ {x n : Nat}, 0x400000 ≤ x → x + n ≤ 0x7a9000 → ∀ i < n, D (Addr.add (BitVec.ofNat 64 x) i) :=
    fun {x} {_} h1 h2 i hi => by
      have t := tg (b := x) hi (by omega)
      exact hD _ (by omega) (by omega)
  have hD' : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a := fun a h1 h2 => hD a h1 (by omega)
  have hr1 : 0x791ca0 + 32 ≤ g.rsp.toNat := by omega
  have hs1 : 0x791ca0 ≤ sp.toNat := by omega
  obtain ⟨p2, p3⟩ := ent_phd (ra := ra) (ra₀ := ra₀) (gY := gY) hM hph hpn hb hb' hbp hW
    (dv (by omega) (by omega)) (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn
  obtain ⟨x1, x1z, x2, x2z⟩ := ent_x (ra := ra) (ra₀ := ra₀) (gY := gY) hK hI hM hb hb' hW hD' hr1 hr' hs1 hsn
  obtain ⟨-, t6, -⟩ := ent_t11 (ra := ra) (ra₀ := ra₀) (gY := gY) hK hI hM hb hb' hW hD' hr1 hr' hs1 hsn
  obtain ⟨pn, pz⟩ := ent_pnz (ra := ra) (ra₀ := ra₀) (gY := gY) hK hI hM hb hb' hW (dv (by omega) (by omega))
    hr1 hr' hs1 hsn
  exact ⟨ent_sdso hK hB hM hsd hb hb' hbp hW (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn, p2, p3,
    ent_sm hB hM hb hb' hbp hW (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn,
    ent_sec hK hM hb hb' hbp hW (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn, pn, pz,
    ent_pse hK hI hM hb hb' hW (dv (by omega) (by omega)) hr1 hr' hs1 hsn,
    ent_oz hB hM hb hb' hbp hW (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn,
    x1, x1z, x2, x2z, t6, ent_hw hHw (by omega) hr' (by omega) hsn,
    ent_pl hK hB hM hb hb' hW (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn,
    ent_len hK hI hM hb hb' hW hD' hr1 hr' hs1 hsn, ent_sl hK hI hM hb hb' hW hD' hr1 hr' hs1 hsn,
    ent_ph hK hI hM hb hb' hW hD' hr1 hr' hs1 hsn,
    ent_pgs hM hps hb hb' hbp hW (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn,
    ent_la hK hI hM hb hb' hW (dv (by omega) (by omega)) (by omega) hr' (by omega) hsn⟩

end FV7z.Start
