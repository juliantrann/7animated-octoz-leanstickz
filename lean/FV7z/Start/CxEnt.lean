import FV7z.Start.EvEnt
import FV7z.Start.Nm
import FV7z.Start.LifCode
/-!
# `Cx` of `lif_ok`, from the launch (PLAN.md G3, startup)

`Ndi.Cx` bundles what the body of `_dl_non_dynamic_init` needs besides its bytes' words: the code of the body and
of `getenv`, the contracts of `strlen` and `strncmp` (hypotheses, like the other library contracts), the
environment (`ent_ev`), the seven names it asks `getenv` for (`ent_nms`, `nm_ok`; no environment string starts
with `LD_`, `no_ld`), and the footprints of its stack and of the data segment.

- `ent_cx`: `Cx … (evOf K) (fV …) sp`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- `Cx` for `lif_ok`'s bytes and the environment of the launch. -/
theorem ent_cx {prof : Profile} {L : List (Addr × List Byte)} {o : Oracle} {pl pc : List Byte}
    {Pm : (Addr → Byte) → Prop} {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop}
    {F : Footprint} {Wl : List Rgn} {g gY : Gprs} {ra ra₀ : BitVec 64} {sp : Addr}
    (hLC : LifCode L) (hil : CodeIn L 4198664#64 pl) (hl0 : 0 < pl.length)
    (hlen : Str.LenAt prof L o 4198664#64 Pm) (hic : CodeIn L 4198472#64 pc) (hc0 : 0 < pc.length)
    (hcmp : Str.NcmpAt prof L o 4198472#64 Pm)
    (hPm : ∀ W₁ : Addr → Byte, (∀ x : Addr, 7938048 ≤ x.toNat → x.toNat < 7940480 →
      W₁ x =
        Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY x) →
      Pm W₁)
    (hK : K.Ok) (hI : Img K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) (hDi : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
    {lo : Nat} (hbp : K.bp.toNat + 376 ≤ lo)
    (htl : b.toNat + 8192 ≤ lo) (hr : g.rsp.toNat + 8 ≤ lo) (hsp : sp.toNat + 120 ≤ lo)
    (hle : lo ≤ K.envp.toNat) (hls : ∀ i < K.N, lo ≤ (K.ptr i).toNat)
    (hDe : ∀ k < 8 * (K.N + 1), D (Addr.add K.envp k))
    (hDs : ∀ i < K.N, ∀ k ≤ K.len i, D (Addr.add (K.ptr i) k))
    (hs2 : ∀ i < K.N, (K.ptr i).toNat + K.len i + 2 ≤ 2 ^ 64) (hdx : g.rdx = K.envp)
    (hrl : 8013728 + 32 ≤ g.rsp.toNat) (hspl : 8013728 ≤ sp.toNat + 80)
    (hFe : ∀ k < 8 * (K.N + 1), Foot F.data (Addr.add K.envp k))
    (hFs : ∀ i < K.N, ∀ x : Addr, (K.ptr i).toNat / 4096 ≤ x.toNat / 4096 →
      x.toNat / 4096 ≤ ((K.ptr i).toNat + K.len i) / 4096 → Foot F.data x)
    (hF2 : ∀ i < K.N, Foot F.data (Addr.add (K.ptr i) 1))
    (hpg : ∀ x : Addr, 0x6f3000 ≤ x.toNat → x.toNat < 0x6f4000 → Foot F.data x)
    (noLD : ∀ i < K.N, ¬ (K.ez i 0 = 0x4c ∧ K.ez i 1 = 0x44 ∧ K.ez i 2 = 0x5f))
    (h72 : 8032256 + 72 ≤ sp.toNat) (hstk : ∀ i < 72, Foot Wl (Addr.add (sp - 72#64) i))
    (hFv : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (hWv : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot Wl x) :
    Ndi.Cx prof F Wl L o pl pc Pm (evOf K)
      (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY) sp := by
  have hr0 : 32 ≤ g.rsp.toNat := by omega
  have hsn : sp.toNat + 120 ≤ 2 ^ 64 := by have := K.envp.isLt; omega
  have hr' : g.rsp.toNat + 8 ≤ 2 ^ 64 := by have := K.envp.isLt; omega
  have hE := ent_ev (F := F) (ra := ra) (ra₀ := ra₀) (gY := gY) hK hM hb hb' hW hbp htl hr hsp hle hls hDe
    (fun i hi => hDs i hi _ (Nat.le_refl _)) hs2 hdx hrl hspl hFe hFs hF2
  have hN := ent_nms (ra := ra) (ra₀ := ra₀) (g := g) (gY := gY) (sp := sp) hK hI hM hb hb' hW hDi (by omega) hr'
    (by omega) hsn
  have hLD := no_ld (E := evOf K)
    (M := Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8)) sp gY)
    hK rfl (fun i hi => if_pos hi) (fun i hi k hk => by
      have t : ((K.ptr i).add k).toNat = (K.ptr i).toNat + k :=
        toNat_add_of_fits (n := K.len i + 1) (by omega) (by have := hs2 i hi; omega)
      have hl := hls i hi
      exact ent_hi hM hb hb' hW (by omega) (by omega) (by omega) hr0 (by omega) (hDs i hi k hk)) noLD
  exact ⟨hLC.ndi, hLC.gev, hil, hl0, hlen, hic, hc0, hcmp, hPm, hE,
    nm_ok (o := 0) (by decide) hN hpg hLD, nm_ok (o := 8) (by decide) hN hpg hLD,
    nm_ok (o := 24) (by decide) hN hpg hLD, nm_ok (o := 36) (by decide) hN hpg hLD,
    nm_ok (o := 48) (by decide) hN hpg hLD, nm_ok (o := 64) (by decide) hN hpg hLD,
    nm_ok (o := 82) (by decide) hN hpg hLD, h72, hstk, hFv, hWv⟩

end FV7z.Start
