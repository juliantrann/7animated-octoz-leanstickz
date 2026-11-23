import FV7z.Start.PlEnt
import FV7z.Start.Phd
/-!
# `hpl` of `lif_ok`: the platform string, in each case (PLAN.md G3, startup)

`init_cpu_features` leaves `_dl_platform` (`0x7a8548`) as `_dl_aux_init` set it from `AT_PLATFORM`, or points it
to `"xeon_phi"` or `"haswell"` in `.rodata` (`CpuFeat.PlW`, `mb_plat`). No store of the start code after that and
none of `__libc_init_first`'s prologue reaches the word (`ent_gl`), so in `lif_ok`'s bytes it is the word at the
end of `init_cpu_features`. Each case gives `Ndi.Pl`: the stack string with `pl_at`, the image strings with
`pl_ro`.

- `ent_plat`: `∃ q m, Ndi.Pl … q m` in `lif_ok`'s bytes.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

/-- The platform string for `lif_ok`'s `hpl`: `_dl_platform` in the bytes `Zm` at the end of `init_cpu_features`
(`PlW`-related to `MB`'s), the stack string at `P` (`AT_PLATFORM`), and the pages of both kinds of string in `F`. -/
theorem ent_plat {K : Ctx} {W V Zm : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} {g gY : Gprs}
    {ra ra₀ : BitVec 64} {sp : Addr} {F : Footprint} {P : Nat} (hK : K.Ok) (hI : Img K.V0) (hM : MB K V)
    (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63) (hW : PtrW K W V b ver D) (hPl : CpuFeat.PlW V Zm)
    (hZ : rdq(W, 8029512#64) = rdq(Zm, 8029512#64))
    (hD : ∀ a : Addr, 0x400000 ≤ a.toNat → a.toNat < 0x791ca0 → D a)
    (hr : 0x7a8550 + 32 ≤ g.rsp.toNat) (hr' : g.rsp.toNat + 8 ≤ 2 ^ 64) (hsp : 0x7a8550 ≤ sp.toNat)
    (hsn : sp.toNat + 120 ≤ 2 ^ 64) (hKp : (K.vs K.M).platform = BitVec.ofNat 64 P) (hP : P + 7 ≤ 2 ^ 64)
    (hbp : K.bp.toNat + 376 ≤ P) (htl : b.toNat + 8192 ≤ P) (hrP : g.rsp.toNat + 8 ≤ P)
    (hspP : sp.toNat + 120 ≤ P)
    (hDP : ∀ k < 7, D (BitVec.ofNat 64 (P + k)))
    (hV0 : ∀ k < platformString.length, K.V0 (BitVec.ofNat 64 (P + k)) = platformString.getD k 0)
    (hpgP : ∀ x : Addr, P / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (P + 6) / 4096 → Foot F.data x)
    (hpgR : ∀ x : Addr, 0x6ee000 ≤ x.toNat → x.toNat < 0x6ef000 → Foot F.data x) :
    ∃ q m, Ndi.Pl (Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8))
      sp gY) F sp q m := by
  have hq : rdq(Ndi.fV (Vst (Lif.LifMem (Vst W g.rsp (toBytesLE ra₀ 8)) g) (g.rsp - 32#64) (toBytesLE ra 8))
      sp gY, 8029512#64) = rdq(Zm, 8029512#64) := by
    rw [ent_gl (x := 8029512) (n := 8) (by unfold KpAt; omega) (by omega) hr' (by omega) hsn]
    exact hZ
  have hs := ent_pls (ra := ra) (ra₀ := ra₀) (g := g) (gY := gY) hK hI hM hb hb' hW hD (by omega) hr' (by omega) hsn
  rcases mb_plat hM hPl with h | h | h
  · rw [hKp] at h
    exact ⟨_, _, pl_at hP (hq.trans h) (by omega)
      (fun k hk => ent_pstr hM hb hb' hW hP hbp htl hrP (by omega) hspP hDP hV0 hk) hpgP⟩
  · exact ⟨_, _, pl_ro (.inl ⟨rfl, rfl⟩) (hq.trans h) hs hpgR⟩
  · exact ⟨_, _, pl_ro (.inr ⟨rfl, rfl⟩) (hq.trans h) hs hpgR⟩

end FV7z.Start
