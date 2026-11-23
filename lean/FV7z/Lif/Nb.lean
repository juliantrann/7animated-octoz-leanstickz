import FV7z.Lif.Bc
import FV7z.Ndi.Far
/-!
# `__libc_init_first` after `_dl_non_dynamic_init` (PLAN.md G3, startup)

`lif_nb`: `lif_bc` from the bytes `W₂` that `ndi_ok`'s continuation gives at the return of `_dl_non_dynamic_init`
(`Eqo`, `hV`, `Lo`, `Same` over the bytes `W` at its entry), the reads stated on `W`: the caller's frame and `argv`
from `sp + 128` up (`ndi_stk`), the TLS word at `fs - 112` (`ndi_tls`), the locale words and tables in the image
(`ndi_glob`). `sp` is `_dl_non_dynamic_init`'s, so `rsp` at the return is `sp + 128`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Gor (Lo)
namespace FV7z.Lif

theorem rq_congr {V V' : Addr → Byte} {a : Addr} (h : ∀ i < 8, V' (a.add i) = V (a.add i)) :
    rdq(V', a) = rdq(V, a) := by
  refine congrArg _ (List.map_congr_left fun y hy => ?_)
  obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hy
  exact h j hj

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

set_option maxHeartbeats 1600000 in
/-- `lif_bc` at the return of `_dl_non_dynamic_init`, the bytes there from `ndi_ok`'s continuation. -/
theorem lif_nb {fb lp ct a0 : Addr} {a b cc : BitVec 64} {n : Nat} {pr : List Byte} {Pm : (Addr → Byte) → Prop}
    {W W' U W₂ : Addr → Byte} {sp bk r : Addr} {m : Nat} {g : Gprs}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L lif_at lif) (hinI : CodeIn L Ims.ims_at Ims.ims) (hci : CodeIn L Cti.cti_at Cti.cti)
    (hir : CodeIn L 4198480#64 pr) (hr0 : 0 < pr.length) (hrchr : Str.RchrAt prof L o 4198480#64 Pm)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W₂) (hrip : X.cpu.rip = lif_at.add 70)
    (hR : X.cpu.gpr.rsp = sp + 128#64)
    -- `ndi_ok`'s bytes at the return
    (hE : Ndi.Eqo sp W₂ (Ndi.lV (Ndi.bV U m)))
    (hU : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fb a) → U a = Ndi.hV W' r 4194368#64 8#64 a)
    (hL : ∀ a : Addr, Lo bk fb a → W' a = Ndi.fV W sp g a) (hS : Ndi.Same sp (Ndi.fV W sp g) W')
    (hbk : fb.toNat ≤ bk.toNat) (hfl : 8032256 + 112 ≤ fb.toNat) (hfsp : fb.toNat + 72 ≤ sp.toNat)
    (hs : sp.toNat + 160 ≤ 2 ^ 64)
    -- the frame, `__init_misc`'s variables
    (hst : ∀ i < 40, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40#64) i))
    (hl : ∀ i < 32, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hgl : ∀ i < 16, Foot Wl (Addr.add 7942968#64 i))
    -- `argv[0]`, a string of `n` characters
    (hsi : X.cpu.gpr.r12 ≠ 0) (fa : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.r12 i))
    (ha0 : rdq(W, X.cpu.gpr.r12) = a0) (hnz : a0 ≠ 0) (hrs : sp.toNat + 128 ≤ X.cpu.gpr.r12.toNat)
    (hr8 : X.cpu.gpr.r12.toNat + 8 ≤ 2 ^ 64)
    (nfit : a0.toNat + n < 2 ^ 64) (nnz : ∀ k < n, W (Addr.add a0 k) ≠ 0) (nz : W (Addr.add a0 n) = 0)
    (hns : sp.toNat + 128 ≤ a0.toNat)
    (npg : ∀ x : Addr, a0.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (a0.toNat + n) / 4096 → Foot F.data x)
    (hPm : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7937208 → W₁ a = W a) → Pm W₁)
    -- `__ctype_init`
    (hlp : rdq(W, fb - 112#64) = lp) (hct : rdq(W, lp) = ct) (ha : rdq(W, ct + 64#64) = a)
    (hb : rdq(W, ct + 72#64) = b) (hc : rdq(W, ct + 88#64) = cc)
    (hlg : 7937720 ≤ lp.toNat ∧ lp.toNat + 8 ≤ 7940480) (hcg : ct.toNat + 96 ≤ 7937208)
    (f1 : ∀ i < 8, Foot F.data ((fb - 112#64).add i)) (f2 : ∀ i < 8, Foot F.data (Addr.add lp i))
    (f3 : ∀ i < 32, Foot F.data ((ct + 64#64).add i)) (fw : ∀ i < 24, Foot Wl ((fb - 64#64).add i))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(W, sp + 152#64) = e₂.add j₂)
    (k : ∀ Z t' s, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Cti.CtMem (bcV W₂ X.cpu.gpr a0 s) fb a b cc) →
      Ims.Short W a0 n s → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp + 160#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = rdq(W, sp + 128#64) →
      Z.cpu.gpr.r12 = rdq(W, sp + 136#64) → Z.cpu.gpr.r13 = rdq(W, sp + 144#64) →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have eR : X.cpu.gpr.rsp.toNat = sp.toNat + 128 := by rw [hR]; bv_omega
  have e8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by bv_omega
  have e12 : (fb - 112#64).toNat = fb.toNat - 112 := by bv_omega
  have c64 : (ct + 64#64).toNat = ct.toNat + 64 := by bv_omega
  have c72 : (ct + 72#64).toNat = ct.toNat + 72 := by bv_omega
  have c88 : (ct + 88#64).toNat = ct.toNat + 88 := by bv_omega
  have s128 : (sp + 128#64).toNat = sp.toNat + 128 := by bv_omega
  have s136 : (sp + 136#64).toNat = sp.toNat + 136 := by bv_omega
  have s144 : (sp + 144#64).toNat = sp.toNat + 144 := by bv_omega
  have s152 : (sp + 152#64).toNat = sp.toNat + 152 := by bv_omega
  have r8 : X.cpu.gpr.rsp + 8#64 = sp + 136#64 := by rw [hR]; exact BitVec.add_assoc _ _ _
  have r16 : X.cpu.gpr.rsp + 16#64 = sp + 144#64 := by rw [hR]; exact BitVec.add_assoc _ _ _
  have r24 : X.cpu.gpr.rsp + 24#64 = sp + 152#64 := by rw [hR]; exact BitVec.add_assoc _ _ _
  have r32 : X.cpu.gpr.rsp + 32#64 = sp + 160#64 := by rw [hR]; exact BitVec.add_assoc _ _ _
  have hlo : 8032256 ≤ sp.toNat := by omega
  have hstk : ∀ x : Addr, sp.toNat + 120 ≤ x.toNat → W₂ x = W x := fun x hx =>
    Ndi.ndi_stk (W := W) (W' := W') (g := g) hE hU hS hlo (by omega) hx
  have hgb : ∀ x : Addr, (x.toNat < 7937208 ∨ 7937720 ≤ x.toNat ∧ x.toNat < 7940480) → W₂ x = W x := fun x hx =>
    Ndi.ndi_glob (W := W) (g := g) hE hU hL (by omega) (by omega) (by omega) (by omega) hx
  have hst' : ∀ (x : Addr) (k : Nat), sp.toNat + 120 ≤ x.toNat → x.toNat + k ≤ 2 ^ 64 →
      ∀ i < k, W₂ (x.add i) = W (x.add i) := fun x k h1 h2 i hi =>
    hstk (x.add i) (by rw [toNat_add_of_fits hi h2]; omega)
  have hgb' : ∀ (x : Addr) (k : Nat), (x.toNat + k ≤ 7937208 ∨ 7937720 ≤ x.toNat ∧ x.toNat + k ≤ 7940480) →
      ∀ i < k, W₂ (x.add i) = W (x.add i) := fun x k h i hi =>
    hgb (x.add i) (by rw [toNat_add_of_fits (a := x) hi (by omega)]; omega)
  have q12 : rdq(W₂, X.cpu.gpr.r12) = rdq(W, X.cpu.gpr.r12) :=
    rq_congr (hst' X.cpu.gpr.r12 8 (by omega) hr8)
  have q0 : rdq(W₂, sp + 128#64) = rdq(W, sp + 128#64) := rq_congr (hst' (sp + 128#64) 8 (by omega) (by omega))
  have q8 : rdq(W₂, sp + 136#64) = rdq(W, sp + 136#64) := rq_congr (hst' (sp + 136#64) 8 (by omega) (by omega))
  have q16 : rdq(W₂, sp + 144#64) = rdq(W, sp + 144#64) := rq_congr (hst' (sp + 144#64) 8 (by omega) (by omega))
  have q24 : rdq(W₂, sp + 152#64) = rdq(W, sp + 152#64) := rq_congr (hst' (sp + 152#64) 8 (by omega) (by omega))
  have qlp : rdq(W₂, fb - 112#64) = rdq(W, fb - 112#64) := rq_congr fun i hi => by
    have e := toNat_add_of_fits (a := fb - 112#64) (n := 8) hi (by omega)
    exact Ndi.ndi_tls (W := W) (g := g) hE hU hL hbk (by omega) (by omega) (by omega) (by omega)
  have qct : rdq(W₂, lp) = rdq(W, lp) := rq_congr (hgb' lp 8 (.inr hlg))
  have qa : rdq(W₂, ct + 64#64) = rdq(W, ct + 64#64) := rq_congr (hgb' (ct + 64#64) 8 (.inl (by omega)))
  have qb : rdq(W₂, ct + 72#64) = rdq(W, ct + 72#64) := rq_congr (hgb' (ct + 72#64) 8 (.inl (by omega)))
  have qc : rdq(W₂, ct + 88#64) = rdq(W, ct + 88#64) := rq_congr (hgb' (ct + 88#64) 8 (.inl (by omega)))
  have hap0 : BcAp X.cpu.gpr.rsp X.cpu.gpr.r12 8 := by unfold BcAp; omega
  have p1 : BcAp X.cpu.gpr.rsp (fb - 112#64) 8 := by unfold BcAp; omega
  have p2 : BcAp X.cpu.gpr.rsp lp 8 := by unfold BcAp; omega
  have p3 : BcAp X.cpu.gpr.rsp (ct + 64#64) 32 := by unfold BcAp; omega
  refine lif_bc (lp := lp) (ct := ct) (a := a) (b := b) (cc := cc) (a0 := a0) (n := n) (V := W₂) c hfs hin hinI
    hci hir hr0 hrchr hK hA hrip (by omega) (by omega) hst hl hgl (by omega) hsi fa (q12.trans ha0) hnz hap0 nfit
    (fun j hj => ?_) ?_ npg (fun j hj => ?_) (fun W₁ hW => hPm W₁ fun x hx => ?_) (qlp.trans hlp) (qct.trans hct)
    (qa.trans ha) (qb.trans hb) (qc.trans hc) p1 p2 p3 f1 f2 f3 fw (by omega) (by omega) (by omega) (by omega)
    hin₂ h₂ (by rw [r24]; exact q24.trans hra) ?_
  · have e := toNat_add_of_fits (a := a0) (i := j) (n := n) hj (by omega)
    rw [hstk (Addr.add a0 j) (by omega)]
    exact nnz j hj
  · have e := toNat_add_of_fits (a := a0) (i := n) (n := n + 1) (by omega) (by omega)
    rw [hstk (Addr.add a0 n) (by omega)]
    exact nz
  · have e := toNat_add_of_fits (a := a0) (i := j) (n := n + 1) (by omega) (by omega)
    omega
  · rw [hW x (.inl (by omega)), Ndi.vap (a := X.cpu.gpr.rsp - 8) (x := x) (n := 8) (toBytesLE_length _ _)
      (by omega) (.inl (by omega))]
    exact hgb x (.inl hx)
  intro Z t' s hKZ hAZ hSh hrZ hsZ hbx hbp h12 h13 h14 h15
  refine k Z t' s hKZ hAZ (short_congr (fun j hj => ?_) hSh) hrZ (by rw [hsZ, r32]) hbx
    (by rw [hbp, hR, q0]) (by rw [h12, r8, q8]) (by rw [h13, r16, q16]) h14 h15
  have e := toNat_add_of_fits (a := a0) (i := j) (n := n + 1) (by omega) (by omega)
  exact hstk (Addr.add a0 j) (by omega)

end FV7z.Lif
