import FV7z.Start.GsMain
/-!
# The registrars' counts at the call of `__libc_csu_init` (PLAN.md §M, `launch_to_main`)

`Ctor.at_ctor_gs` asks that the counts of the three registrars (`RegisterArc`, `RegisterCodec`, `RegisterHasher`,
`Ctor.regCnt`) be 0 at the call of `__libc_csu_init`. They lie in `.bss` with their tables
(`[0x79c7e0, 0x79f004)`, `Ndi.RegB`), which no layer of the start stores to: the start code (`ptr_keep`),
`_dl_non_dynamic_init` (`Ndi.ndi_rg`), `__init_misc` and `__ctype_init` (`ct_away`), `lif_a` (`lifW_away`) and
`__cxa_atexit (fini, NULL, NULL)` (`Cxa.Reg.out`).

- `Ndi.RegB`: a byte of those tables and counts.
- `Ndi.lbV_rg`, `Ndi.hV_rg`, `Ndi.ndi_rg`: `_dl_non_dynamic_init`'s stores miss them.
- `ptr_rg`: at `0x613434` they are 0, as in the image.
- `RetAt.rg0`: at `0x613439` they are 0; `csu_rg`: also after `__cxa_atexit (fini, NULL, NULL)`.
- `csu_rz`: the three counts there are 0.
-/
namespace FV7z.Ndi
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Gor (Lo)

/-- A byte of the registrars' tables and counts, `[0x79c7e0, 0x79f004)`. -/
def RegB (x : Addr) : Prop := 7981024 ≤ x.toNat ∧ x.toNat < 7991300

/-- `lV (bV U m)` is `U` on `RegB`. -/
theorem lbV_rg {U : Addr → Byte} {m : Nat} {x : Addr} (hx : RegB x) : lV (bV U m) x = U x := by
  unfold RegB at hx
  unfold lV bV
  rw [vlt (a := 7944528) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944520) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7943112) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029520) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029600) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029600) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029536) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029608) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029584) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 8029616) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega)]

/-- `hV V' …` is `V'` on `RegB`. -/
theorem hV_rg {V' : Addr → Byte} {r ph pn : BitVec 64} {x : Addr} (hx : RegB x) : hV V' r ph pn x = V' x := by
  unfold RegB at hx
  unfold hV aV
  rw [vlt (a := 8029532) (n := 4) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937208) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937216) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937224) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937232) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7937240) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944088) (n := 2) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944072) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega),
    vlt (a := 7944232) (n := 8) (x := x) (toBytesLE_length _ _) (by omega) (by omega)]

/-- A byte of `RegB` at the return of `_dl_non_dynamic_init` is the one at its entry. -/
theorem ndi_rg {W W' U W₂ : Addr → Byte} {sp b fsb r x : Addr} {m : Nat} {g : Gprs}
    (hE : Eqo sp W₂ (lV (bV U m)))
    (hU : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fsb a) → U a = hV W' r 4194368#64 8#64 a)
    (hL : ∀ a : Addr, Lo b fsb a → W' a = fV W sp g a) (hb : 8032256 ≤ b.toNat) (hf : 8032256 ≤ fsb.toNat)
    (hsp : 8032256 + 72 ≤ sp.toNat) (hs : sp.toNat + 120 ≤ 2 ^ 64) (hx : RegB x) : W₂ x = W x := by
  have hx' := hx
  unfold RegB at hx'
  have hu : x.toNat < 7937664 ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480 ∨ sp.toNat ≤ x.toNat ∨ Mal.Kf fsb x :=
    .inr (.inr (.inr (Or.inl (by unfold Mal.Kn; omega))))
  have hl : Lo b fsb x := ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hn : ¬ Scr sp x := by unfold Scr; omega
  rw [hE x hn, lbV_rg (U := U) (m := m) hx, hU x hu, hV_rg (V' := W') (r := r) (ph := 4194368#64) (pn := 8#64) hx,
    hL x hl, fV_out (W := W) (g := g) (x := x) hs (.inl (by omega))]

end FV7z.Ndi

namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.Ndi (RegB)

/-- At `0x613434` (`ptr_keep`'s bytes), a byte of `RegB` is 0: none of the layers before stores to it. -/
theorem ptr_rg {K : Ctx} {W V : Addr → Byte} {b : Addr} {ver : BitVec 32} {D : Addr → Prop} (hK : K.Ok)
    (hB : Bss K.V0) (hM : MB K V) (hb : 0x7a9000 ≤ b.toNat) (hb' : b.toNat + 8192 ≤ 2 ^ 63)
    (hW : PtrW K W V b ver D) {a : Addr} (hx : RegB a) (hDa : D a) : W a = 0 := by
  have hf : (b + 2176#64).toNat = b.toNat + 2176 := by bv_omega
  unfold Ndi.RegB at hx
  have hd : ¬ Foot (d3 ++ AuxInit.globals) a := not_dg (lo := 7981024) (hi := 7991300) (by decide) hx.1 hx.2
  rw [ptr_keep hK hM hb hb' hW (by omega) (by omega) hDa (by unfold Tls.TlsVar; omega) (by omega) hd
    (by unfold CpuVar; omega) (by unfold Pim.PimVar; omega)]
  exact hB a (by omega) (by omega)

variable {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- At `0x613439`, a byte of `RegB` is 0. -/
theorem RetAt.rg0 {K : Ctx} {V : Addr → Byte} {ver : BitVec 32} (h : RetAt W W₂ Z B g) (hK : K.Ok)
    (hB : Bss K.V0) (hM : MB K V) (hW : PtrW K W V B ver (fun _ => True)) {x : Addr} (hx : RegB x) :
    Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3 x = 0 := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs; have := h.he; have := h.he'; have := h.hg
  have h1 : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have h2 : (B + 4544#64).toNat = B.toNat + 4544 := by bv_omega
  have hx' := hx
  unfold Ndi.RegB at hx'
  obtain ⟨W', U, m, r, hE, hU, hL, -⟩ := h.nd
  have ha : Away x := by unfold Away; omega
  rw [ct_away ha (by omega) (by omega) (by omega),
    Ndi.ndi_rg hE hU hL (by omega) (by omega) (by omega) (by omega) hx]
  have e : lifW W Z x = W x := lifW_away ha (by omega) (by omega)
  rw [e]
  exact ptr_rg hK hB hM h.hb h.hb' hW hx trivial

/-- After `__cxa_atexit (fini, NULL, NULL)`, a byte of `RegB` is 0. -/
theorem csu_rg {K : Ctx} {V V'' : Addr → Byte} {ver : BitVec 32} {fn : BitVec 64} (h : RetAt W W₂ Z B g)
    (hKo : K.Ok) (hB : Bss K.V0) (hM : MB K V) (hW : PtrW K W V B ver (fun _ => True))
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
      (toBytesLE (lsm_at.add 1034) 8)) V'' (lifSp Z + 152#64) 8010400#64 8010416#64 0 fn 0 0)
    {x : Addr} (hx : RegB x) : V'' x = 0 := by
  have := h.hb; have := h.hb'; have := h.hsp; have := h.hs
  have hq : (lifSp Z + 152#64).toNat = (lifSp Z).toNat + 152 := by bv_omega
  have t1 : (8010400#64 : Addr).toNat = 8010400 := rfl
  have t2 : (8010416#64 : Addr).toNat = 8010416 := rfl
  have hx' := hx
  unfold Ndi.RegB at hx'
  rw [hR.out x (by omega) (by omega) (by omega) (by omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)]
  exact h.rg0 hKo hB hM hW hx

/-- After `__cxa_atexit (fini, NULL, NULL)`, the three registrars' counts are 0 (`Ctor.at_ctor_gs`'s `hz`). -/
theorem csu_rz {K : Ctx} {V V'' : Addr → Byte} {ver : BitVec 32} {fn : BitVec 64} (h : RetAt W W₂ Z B g)
    (hKo : K.Ok) (hB : Bss K.V0) (hM : MB K V) (hW : PtrW K W V B ver (fun _ => True))
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
      (toBytesLE (lsm_at.add 1034) 8)) V'' (lifSp Z + 152#64) 8010400#64 8010416#64 0 fn 0 0) :
    ∀ r < 3, rdd(V'', Ctor.regCnt r) = 0 := by
  have hz : ∀ c : Nat, 7981024 ≤ c → c + 4 ≤ 7991300 → rdd(V'', BitVec.ofNat 64 c) = 0 := by
    intro c h1 h2
    have z : ∀ i < 4, V'' (Addr.add (BitVec.ofNat 64 c) i) = 0 := fun i hi =>
      csu_rg h hKo hB hM hW hR (by unfold Ndi.RegB; rw [ofNat_add_toNat hi (by omega)]; omega)
    rw [rd_zero z]
    rfl
  intro r hr
  match r, hr with
  | 0, _ => exact hz 7991296 (by decide) (by decide)
  | 1, _ => exact hz 7981824 (by decide) (by decide)
  | 2, _ => exact hz 7981280 (by decide) (by decide)
  | n + 3, hr => exact absurd hr (by omega)

end FV7z.Start
