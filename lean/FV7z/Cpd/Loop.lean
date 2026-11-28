import FV7z.Cpd.Inner
import FV7z.Cpd.Items
/-!
# `NCommandLineParser::CParser::~CParser`, the loop over the items from 48 and 157 (PLAN.md §M, M1)

The run from 157 to 170 (`from157`) and from 48 for each item (`from48`), by the pieces of `FV7z/Cpd/Inner.lean` and
the callees as hypotheses on the bytes (see there).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Ocv (rbx0 rbx0_eq rb_step rb_ne rb_last)
namespace FV7z.Cpd

variable {F : Footprint} {Wl : List Rgn}

/-! ## From 157 and from 48 -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- From 157 with `rbx` = `b` and the bytes for which `P` holds: `operator delete [] (b - 8, …)` (`hDA`, at
`0x601500`) gives `B0`, then 170 (`h170`). -/
theorem from157 {g₀ : Gprs} {ra b : Addr} {P B0 : (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpd_at cpd) (hin3 : CodeIn L 0x601500#64 Tiny.c601500)
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hDA : ∀ W, P W → Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x601500#64 (cpd_at.add 170)
      (fun g => g.rdi = b + 18446744073709551608#64) W B0)
    (h170 : AtJ prof F Wl L s₀ o gev gP gE 170 fun g W => B0 W ∧ Fr g₀ ra W ∧ Rs g₀ g) :
    AtJ prof F Wl L s₀ o gev gP gE 157 fun g W => P W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = b := by
  rintro Y W t' hKY hAY hrY ⟨hO, hfr, hR, hbx⟩
  refine (c_157 prof).run c hin _ hKY hAY hrY vc_157 ?_
  rintro j' g fl V₁ ⟨rfl, hs, h12, h15, hdi, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁
  subst hgU
  have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hs.trans hR.1
  have h12U : U.cpu.gpr.r12 = g₀.rdi := h12.trans hR.2.1
  have h15U : U.cpu.gpr.r15 = g₀.r15 := h15.trans hR.2.2
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_165 _) hin3 (by decide) tgt_165
    (by rw [hsU]; exact w6) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsU] at hA₂
  have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
    (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
  have hdi₂ : Y₂.cpu.gpr.rdi = b + 18446744073709551608#64 :=
    (congrArg Gprs.rdi hg₂).trans (hdi.trans (by rw [hbx]))
  refine hDA W hO Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
  rintro Z V'' t'' hKZ hAZ hB hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
  refine h170 Z V'' t'' hKZ hAZ hrZ ⟨hB, hfr.kf hkf, ?_, ?_, ?_⟩
  · rw [b1, hsY₂, a1s]
  · exact b4.trans ((congrArg Gprs.r12 hg₂).trans h12U)
  · exact b7.trans ((congrArg Gprs.r15 hg₂).trans h15U)

set_option maxHeartbeats 1000000 in
/-- From 48 for each item `i` below `N` (`g₀` the registers at the entry, `this` = `g₀.rdi`, `b` the 8 bytes at
`this` whenever `O` holds): the size `nI i` (`hn`) and `_items` = `itI i` (`hIt`) of the item; the steps as in
`FV7z/Cpd/Tail.lean` (`hP0`, `hQ0`, `hD1`, `hD2`) from `H i (nI i)` (`hOH`) to `H i 0`; `_items` freed when not 0
(`hE1`, else `hE0`) gives `O i`; then 48 again for `i - 1`, or 157 after the item 0 (`h157`). -/
theorem from48 {g₀ : Gprs} {ra b : Addr} {N : Nat}
    {O : Nat → (Addr → Byte) → Prop} {H : Nat → Nat → (Addr → Byte) → Prop}
    {J : Nat → Nat → BitVec 64 → (Addr → Byte) → Prop} {nI : Nat → BitVec 32} {itI : Nat → BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L cpd_at cpd)
    (hin1 : CodeIn L 0x6014f0#64 Tiny.c6014f0) (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hN : 24 * N < 18446744073709551616)
    (fb : ∀ i < 8, Foot F.data (Addr.add g₀.rdi i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (b + 18446744073709551608#64) i))
    (fn : ∀ i < N, ∀ j < 4, Foot F.data (Addr.add (ip b i + 16#64) j))
    (fa : ∀ i < N, ∀ j < 8, Foot F.data (Addr.add (ip b i + 8#64) j))
    (fe : ∀ i < N, ∀ k < (nI i).toNat, ∀ j < 8, Foot F.data (Addr.add (itI i + BitVec.ofNat 64 (8 * k)) j))
    (fp : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 →
      ∀ j < 8, Foot F.data (Addr.add (pk W (itI i) k) j))
    (hb : ∀ i W, O i W → rdq(W, g₀.rdi) = b)
    (hn : ∀ i < N, ∀ W, O (i + 1) W → rdd(W, ip b i + 16#64) = nI i)
    (hOH : ∀ i < N, ∀ W, O (i + 1) W → H i (nI i).toNat W)
    (hIt : ∀ i < N, ∀ k W, H i k W → rdq(W, ip b i + 8#64) = itI i)
    (hP0 : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k = 0 → H i k W)
    (hQ0 : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 →
      rdq(W, pk W (itI i) k) = 0 → J i k (pk W (itI i) k) W)
    (hD1 : ∀ i < N, ∀ k < (nI i).toNat, ∀ W, H i (k + 1) W → pk W (itI i) k ≠ 0 → rdq(W, pk W (itI i) k) ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014f0#64 (cpd_at.add 102)
        (fun g => g.rdi = rdq(W, pk W (itI i) k)) W (J i k (pk W (itI i) k)))
    (hD2 : ∀ i < N, ∀ k < (nI i).toNat, ∀ p W, p ≠ 0 → J i k p W →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014e0#64 (cpd_at.add 115)
        (fun g => g.rdi = p ∧ g.rsi = 16#64) W (H i k))
    (hE0 : ∀ i < N, ∀ W, H i 0 W → itI i = 0 → O i W)
    (hE1 : ∀ i < N, ∀ W, H i 0 W → itI i ≠ 0 →
      Call1 prof F Wl L s₀ o gev gP gE g₀.rsp 0x6014f0#64 (cpd_at.add 139) (fun g => g.rdi = itI i) W (O i))
    (h157 : AtJ prof F Wl L s₀ o gev gP gE 157 fun g W => O 0 W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = b) :
    ∀ i < N, AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => O (i + 1) W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧
      g.rbx = ip b (i + 1) := by
  -- 139: back to 48 for `i - 1`, or to 157 after the item 0
  have F139 : ∀ i, i < N →
      (∀ i', i = i' + 1 → AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => O (i' + 1) W ∧ Fr g₀ ra W ∧
        Rs g₀ g ∧ g.rbx = ip b (i' + 1)) →
      AtJ prof F Wl L s₀ o gev gP gE 139 fun g W => O i W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1) := by
    rintro i hi hnx Y W t' hKY hAY hrY ⟨hO, hfr, hR, hbx, h13⟩
    have h12 : Y.cpu.gpr.r12 = g₀.rdi := hR.2.1
    have hbY : rdq(W, Y.cpu.gpr.r12) = b := by rw [h12]; exact hb _ W hO
    have fbY : ∀ j < 8, Foot F.data (Addr.add Y.cpu.gpr.r12 j) := by rw [h12]; exact fb
    cases i with
    | zero =>
      have f13 : ∀ j < 8, Foot F.data (Addr.add (Y.cpu.gpr.r13 + 18446744073709551584#64) j) := by
        have e : ip b (0 + 1) + 18446744073709551584#64 = b + 18446744073709551608#64 := ip1_m32 b
        rw [h13, e]; exact fc
      have heq : b = Y.cpu.gpr.rbx := by rw [hbx]; exact (ip0 b).symm
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139e (g := Y.cpu.gpr) (V := W) hbY heq fbY f13) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12', h15, hbx', hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      exact h157 U W t₁ hKU hAU hrU ⟨hO, hfr, ⟨hs.trans hR.1, h12'.trans hR.2.1, h15.trans hR.2.2⟩,
        hbx'.trans heq.symm⟩
    | succ i =>
      have hne : b ≠ Y.cpu.gpr.rbx := by rw [hbx]; exact ip_ne b (by omega) (by omega)
      refine (c_139 prof).run c hin _ hKY hAY hrY (vc_139c (g := Y.cpu.gpr) (V := W) hbY hne fbY) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact hnx i rfl U W t₁ hKU hAU hrU ⟨hO, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rbx hgU).trans hbx⟩
  -- 129: `_items` freed when not 0, to 139
  have E129 : ∀ i, i < N →
      AtJ prof F Wl L s₀ o gev gP gE 139 (fun g W => O i W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1)) →
      AtJ prof F Wl L s₀ o gev gP gE 129 fun g W => H i 0 W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
        g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
    rintro i hi h139 Y W t' hKY hAY hrY ⟨hH, hfr, hR, hdi, hbx, h13⟩
    by_cases hz0 : itI i = 0
    · refine (c_129 prof).run c hin _ hKY hAY hrY (vc_129z (g := Y.cpu.gpr) (V := W) (hdi.trans hz0)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      exact h139 U W t₁ hKU hAU hrU ⟨hE0 i hi W hH hz0, hfr, by rw [hgU]; exact hR, by rw [hgU]; exact hbx,
        by rw [hgU]; exact h13⟩
    · refine (c_129 prof).run c hin _ hKY hAY hrY
        (vc_129n (g := Y.cpu.gpr) (V := W) (fun h => hz0 (hdi.symm.trans h))) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
      have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
      have hbxU : U.cpu.gpr.rbx = ip b i := by rw [hgU]; exact hbx
      have h13U : U.cpu.gpr.r13 = ip b (i + 1) := by rw [hgU]; exact h13
      have hdiU : U.cpu.gpr.rdi = itI i := by rw [hgU]; exact hdi
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_134 _) hin1 (by decide) tgt_134
        (by rw [hsU]; exact w6) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hsU] at hA₂
      have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
        (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
      have hdi₂ : Y₂.cpu.gpr.rdi = itI i := (congrArg Gprs.rdi hg₂).trans hdiU
      refine hE1 i hi W hH hz0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
      rintro Z V'' t'' hKZ hAZ hO hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
      refine h139 Z V'' t'' hKZ hAZ hrZ ⟨hO, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [b1, hsY₂, a1s]
      · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
      · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2)
      · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hbxU)
      · exact b5.trans ((congrArg Gprs.r13 hg₂).trans h13U)
  -- the item `i`, from 48 to 139
  have ITEM : ∀ i, i < N →
      AtJ prof F Wl L s₀ o gev gP gE 139 (fun g W => O i W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1)) →
      AtJ prof F Wl L s₀ o gev gP gE 48 fun g W => O (i + 1) W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧
        g.rbx = ip b (i + 1) := by
    intro i hi h139
    have hnI : (nI i).toNat < 4294967296 := (nI i).isLt
    have h129 := E129 i hi h139
    -- 102: `operator delete (p, 16)`, `rdi` = `_items` again, to 119
    have A102 : ∀ k, k < (nI i).toNat → ∀ p : BitVec 64, p ≠ 0 →
        AtJ prof F Wl L s₀ o gev gP gE 119 (fun g W => H i k W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1)) →
        AtJ prof F Wl L s₀ o gev gP gE 102 fun g W => J i k p W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.r14 = p ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
      rintro k hk p hp h119 Y W t' hKY hAY hrY ⟨hJ, hfr, hR, hp14, hb5, hbx, h13⟩
      refine (c_102 prof).run c hin _ hKY hAY hrY vc_102 ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
      have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
      have hb5U : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := by rw [hgU]; exact hb5
      have hbxU : U.cpu.gpr.rbx = ip b i := by rw [hgU]; exact hbx
      have h13U : U.cpu.gpr.r13 = ip b (i + 1) := by rw [hgU]; exact h13
      refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_110 _) hin2 (by decide) tgt_110
        (by rw [hsU]; exact w6) ?_
      rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
      rw [hsU] at hA₂
      have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
        (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
      have hdi₂ : Y₂.cpu.gpr.rdi = p ∧ Y₂.cpu.gpr.rsi = 16#64 :=
        ⟨(congrArg Gprs.rdi hg₂).trans ((congrArg Gprs.rdi hgU).trans hp14),
          (congrArg Gprs.rsi hg₂).trans (congrArg Gprs.rsi hgU)⟩
      refine hD2 i hi k hk p W hp hJ Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
      rintro Z V'' t'' hKZ hAZ hHk hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
      have hsZ : Z.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := by rw [b1, hsY₂, a1s]
      have hbxZ : Z.cpu.gpr.rbx = ip b i := b2.trans ((congrArg Gprs.rbx hg₂).trans hbxU)
      refine (c_115 prof).run c hin _ hKZ hAZ hrZ
        (vc_115 (it := itI i) (by rw [hbxZ]; exact hIt i hi k V'' hHk) (by rw [hbxZ]; exact fa i hi)) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁
      refine h119 U₂ V'' t₃ hKU₂ hAU₂ hrU₂ ⟨hHk, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · exact (congrArg Gprs.rsp hgU₂).trans hsZ
      · exact (congrArg Gprs.r12 hgU₂).trans (b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1))
      · exact (congrArg Gprs.r15 hgU₂).trans (b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2))
      · exact congrArg Gprs.rdi hgU₂
      · exact (congrArg Gprs.rbp hgU₂).trans (b3.trans ((congrArg Gprs.rbp hg₂).trans hb5U))
      · exact (congrArg Gprs.rbx hgU₂).trans hbxZ
      · exact (congrArg Gprs.r13 hgU₂).trans (b5.trans ((congrArg Gprs.r13 hg₂).trans h13U))
    -- 80: the step `k`, to 119
    have B80 : ∀ k, k < (nI i).toNat →
        AtJ prof F Wl L s₀ o gev gP gE 119 (fun g W => H i k W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1)) →
        AtJ prof F Wl L s₀ o gev gP gE 80 fun g W => H i (k + 1) W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
      rintro k hk h119 Y W t' hKY hAY hrY ⟨hHk, hfr, hR, hdi, hb5, hbx, h13⟩
      have hea : Y.cpu.gpr.rdi + Y.cpu.gpr.rbp = itI i + BitVec.ofNat 64 (8 * k) := by rw [hdi, hb5]
      by_cases hp0 : pk W (itI i) k = 0
      · refine (c_80 prof).run c hin _ hKY hAY hrY
          (vc_80z (p := pk W (itI i) k) (by rw [hea]) (by rw [hea]; exact fe i hi k hk) hp0) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact h119 U W t₁ hKU hAU hrU ⟨hP0 i hi k hk W hHk hp0, hfr, by rw [hgU]; exact hR,
          (congrArg Gprs.rdi hgU).trans hdi, (congrArg Gprs.rbp hgU).trans hb5, (congrArg Gprs.rbx hgU).trans hbx,
          (congrArg Gprs.r13 hgU).trans h13⟩
      · refine (c_80 prof).run c hin _ hKY hAY hrY
          (vc_80n (p := pk W (itI i) k) (q := rdq(W, pk W (itI i) k)) (by rw [hea]) (by rw [hea]; exact fe i hi k hk)
            hp0 rfl (fp i hi k hk W hHk hp0)) ?_
        rintro j' g fl V₁ ⟨hj, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        have hRU : Rs g₀ U.cpu.gpr := by rw [hgU]; exact hR
        have hb5U : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := (congrArg Gprs.rbp hgU).trans hb5
        have hbxU : U.cpu.gpr.rbx = ip b i := (congrArg Gprs.rbx hgU).trans hbx
        have h13U : U.cpu.gpr.r13 = ip b (i + 1) := (congrArg Gprs.r13 hgU).trans h13
        have hpU : U.cpu.gpr.r14 = pk W (itI i) k := congrArg Gprs.r14 hgU
        rcases hj with ⟨hq0, rfl⟩ | ⟨hq0, rfl⟩
        · exact A102 k hk _ hp0 h119 U W t₁ hKU hAU hrU
            ⟨hQ0 i hi k hk W hHk hp0 hq0, hfr, hRU, hpU, hb5U, hbxU, h13U⟩
        · -- `operator delete [] (q)`
          have hsU : U.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 := hRU.1
          refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_97 _) hin1 (by decide) tgt_97
            (by rw [hsU]; exact w6) ?_
          rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
          rw [hsU] at hA₂
          have hsY₂ : Y₂.cpu.gpr.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8 :=
            (congrArg Gprs.rsp hg₂).trans (congrArg (fun x : Addr => x - 8) hsU)
          have hdi₂ : Y₂.cpu.gpr.rdi = rdq(W, pk W (itI i) k) :=
            (congrArg Gprs.rdi hg₂).trans (congrArg Gprs.rdi hgU)
          refine hD1 i hi k hk W hHk hp0 hq0 Y₂ t₂ hK₂ hA₂ hr₂ hsY₂ hdi₂ ?_
          rintro Z V'' t'' hKZ hAZ hJ hrZ ⟨b1, b2, b3, b4, b5, b6, b7⟩ hkf
          refine A102 k hk _ hp0 h119 Z V'' t'' hKZ hAZ hrZ ⟨hJ, hfr.kf hkf, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · rw [b1, hsY₂, a1s]
          · exact b4.trans ((congrArg Gprs.r12 hg₂).trans hRU.2.1)
          · exact b7.trans ((congrArg Gprs.r15 hg₂).trans hRU.2.2)
          · exact b6.trans ((congrArg Gprs.r14 hg₂).trans hpU)
          · exact b3.trans ((congrArg Gprs.rbp hg₂).trans hb5U)
          · exact b2.trans ((congrArg Gprs.rbx hg₂).trans hbxU)
          · exact b5.trans ((congrArg Gprs.r13 hg₂).trans h13U)
    -- 119: `rbp` -= 8, to 129 after the step 0, else to 80
    have S119 : ∀ k, k < (nI i).toNat →
        (∀ k', k = k' + 1 → AtJ prof F Wl L s₀ o gev gP gE 80 fun g W => H i (k' + 1) W ∧ Fr g₀ ra W ∧
          Rs g₀ g ∧ g.rdi = itI i ∧ g.rbp = BitVec.ofNat 64 (8 * k') ∧ g.rbx = ip b i ∧
          g.r13 = ip b (i + 1)) →
        AtJ prof F Wl L s₀ o gev gP gE 119 fun g W => H i k W ∧ Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧
          g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧ g.r13 = ip b (i + 1) := by
      rintro k hk hnx Y W t' hKY hAY hrY ⟨hHk, hfr, hR, hdi, hb5, hbx, h13⟩
      cases k with
      | zero =>
        refine (c_119 prof).run c hin _ hKY hAY hrY (vc_119l (by rw [hb5]; exact rb_last)) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        exact h129 U W t₁ hKU hAU hrU ⟨hHk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi,
          (congrArg Gprs.rbx hgU).trans hbx, (congrArg Gprs.r13 hgU).trans h13⟩
      | succ k =>
        refine (c_119 prof).run c hin _ hKY hAY hrY
          (vc_119c (by rw [hb5, rb_step k (by omega)]; exact rb_ne k (by omega))) ?_
        rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
        subst V₁
        have hb5U : U.cpu.gpr.rbp = BitVec.ofNat 64 (8 * k) := by
          rw [hgU]
          show Y.cpu.gpr.rbp - 8#64 = _
          rw [hb5]
          exact rb_step k (by omega)
        exact hnx k rfl U W t₁ hKU hAU hrU ⟨hHk, hfr, by rw [hgU]; exact hR, (congrArg Gprs.rdi hgU).trans hdi,
          hb5U, (congrArg Gprs.rbx hgU).trans hbx, (congrArg Gprs.r13 hgU).trans h13⟩
    -- the steps, by induction
    have L80 : ∀ k, k < (nI i).toNat → AtJ prof F Wl L s₀ o gev gP gE 80 fun g W => H i (k + 1) W ∧
        Fr g₀ ra W ∧ Rs g₀ g ∧ g.rdi = itI i ∧ g.rbp = BitVec.ofNat 64 (8 * k) ∧ g.rbx = ip b i ∧
        g.r13 = ip b (i + 1) := by
      intro k
      induction k with
      | zero => exact fun hk => B80 0 hk (S119 0 hk fun k' e => absurd e (by omega))
      | succ k ih =>
        exact fun hk => B80 (k + 1) hk (S119 (k + 1) hk fun k' e => by
          obtain rfl : k = k' := by omega
          exact ih (by omega))
    -- 48: the item's size and `_items`
    rintro Y W t' hKY hAY hrY ⟨hO, hfr, hR, hbx⟩
    have hnY : rdd(W, Y.cpu.gpr.rbx + 18446744073709551608#64) = nI i := by
      rw [hbx, ip_m8]; exact hn i hi W hO
    have hitY : rdq(W, Y.cpu.gpr.rbx - 24#64 + 8#64) = itI i := by
      rw [hbx, ip_m24]; exact hIt i hi _ W (hOH i hi W hO)
    have fnY : ∀ j < 4, Foot F.data (Addr.add (Y.cpu.gpr.rbx + 18446744073709551608#64) j) := by
      rw [hbx, ip_m8]; exact fn i hi
    have faY : ∀ j < 8, Foot F.data (Addr.add (Y.cpu.gpr.rbx - 24#64 + 8#64) j) := by
      rw [hbx, ip_m24]; exact fa i hi
    have hbx24 : Y.cpu.gpr.rbx - 24#64 = ip b i := by rw [hbx]; exact ip_m24 b i
    by_cases hn0 : nI i = 0
    · refine (c_48 prof).run c hin _ hKY hAY hrY (vc_48z (g := Y.cpu.gpr) (V := W) hnY hn0 hitY fnY faY) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12, h15, hbx', h13', hdi, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      have e0 : (nI i).toNat = 0 := (congrArg BitVec.toNat hn0).trans rfl
      have hH0 := hOH i hi W hO
      rw [e0] at hH0
      exact h129 U W t₁ hKU hAU hrU ⟨hH0, hfr, ⟨hs.trans hR.1, h12.trans hR.2.1, h15.trans hR.2.2⟩,
        hdi, hbx'.trans hbx24, h13'.trans hbx⟩
    · refine (c_48 prof).run c hin _ hKY hAY hrY (vc_48n (g := Y.cpu.gpr) (V := W) hnY hn0 hitY fnY faY) ?_
      rintro j' g fl V₁ ⟨rfl, hs, h12, h15, hbx', h13', hdi, hb5, hV₁⟩ U t₁ hKU hAU hrU hgU -
      subst V₁
      subst hgU
      have hnz : (nI i).toNat ≠ 0 := fun e => hn0 (BitVec.eq_of_toNat_eq (e.trans rfl))
      have e1 : (nI i).toNat - 1 + 1 = (nI i).toNat := by omega
      exact L80 ((nI i).toNat - 1) (by omega) U W t₁ hKU hAU hrU
        ⟨by rw [e1]; exact hOH i hi W hO, hfr, ⟨hs.trans hR.1, h12.trans hR.2.1, h15.trans hR.2.2⟩, hdi,
          by rw [hb5, rbx0_eq hn0], hbx'.trans hbx24, h13'.trans hbx⟩
  -- the items, by induction
  intro i
  induction i with
  | zero => exact fun hi => ITEM 0 hi (F139 0 hi fun i' e => absurd e (by omega))
  | succ i ih =>
    exact fun hi => ITEM (i + 1) hi (F139 (i + 1) hi fun i' e => by
      obtain rfl : i = i' := by omega
      exact ih (by omega))

end FV7z.Cpd
