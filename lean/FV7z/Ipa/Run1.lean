import FV7z.Ipa.Loop
import FV7z.Hwc.Head2
/-!
# `_dl_init_paths`: from the entry to the return of `_dl_important_hwcaps` (58) (PLAN.md G3, startup)

`to58`: from the entry (`rsp = e`, the return address at `e`) the prologue (`vc_0`), the `call` at 53, the whole of
`_dl_important_hwcaps (_dl_platform, 0, &ncapstr, &max_capstrlen)` (`Hwc.from0`, `h = _dl_hwcap` 2 or 6), its `ret`
(1681), back at 58: `rax = P` the table, `ncapstr = E` (`0x791e98`), the bytes below the heap as at the entry but for
`max_capstrlen` and `ncapstr` (`0x791e90..0x791ea0`), those from `e - 0x58` up the prologue's (`iV0`), and the state
of the heap (`Pa`) for the next `malloc`.

The hypotheses on the bytes are on the entry's `V`; `iV0_out` and `v2_out` carry them to the bytes at the `call`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ipa

set_option maxRecDepth 100000

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}

theorem set4_rcx (g : Gprs) (v : Addr) : (g.set 4 v).rcx = g.rcx := rfl
theorem set4_rsi (g : Gprs) (v : Addr) : (g.set 4 v).rsi = g.rsi := rfl

/-! The addresses of the prologue, as `e + (2^64 - c)`. -/
theorem t8 (e : Addr) : e - 8 = e + 18446744073709551608#64 := by bv_omega
theorem t40s (e : Addr) : e - 40#64 = e + 18446744073709551576#64 := by bv_omega
theorem t88s (e : Addr) : e - 88#64 = e + 18446744073709551528#64 := by bv_omega
theorem t96 (e : Addr) : e + 18446744073709551528#64 - 8 = e + 18446744073709551520#64 := by bv_omega
theorem t104 (e : Addr) : e + 18446744073709551512#64 + 8#64 = e + 18446744073709551520#64 := by bv_omega
theorem t96p (e : Addr) : e + 18446744073709551520#64 + 8 = e + 18446744073709551528#64 := by bv_omega

/-- `iV0` with the addresses as `e + (2^64 - c)`. -/
theorem iV0_eq (V : Addr → Byte) {g : Gprs} {e : Addr} (h : g.rsp = e) :
    iV0 V g = Vst (Vst (Vst (Vst (Vst (Vst (Vst V
      (e + 18446744073709551608#64) (toBytesLE g.rbp 8)) (e + 18446744073709551600#64) (toBytesLE g.r15 8))
      (e + 18446744073709551592#64) (toBytesLE g.r14 8)) (e + 18446744073709551584#64) (toBytesLE g.r13 8))
      (e + 18446744073709551576#64) (toBytesLE g.r12 8)) (e + 18446744073709551568#64) (toBytesLE g.rbx 8))
      (e + 18446744073709551528#64) (toBytesLE g.rdi 8) := by
  simp only [iV0, h, t8, BitVec.add_assoc, BitVec.reduceAdd]

/-- The prologue stores in `[e - 88, e)` only. -/
theorem iV0_out (V : Addr → Byte) {g : Gprs} {e : Addr} (h : g.rsp = e) (hr0 : 96 ≤ e.toNat)
    (he : e.toNat + 8 ≤ 2 ^ 64) (a : Addr) (ha : a.toNat < e.toNat - 88 ∨ e.toNat ≤ a.toNat) : iV0 V g a = V a := by
  rw [iV0_eq V h]
  iout

/-- A load of 8 bytes two maps agree on. -/
theorem rdk {V V' : Addr → Byte} {P : Addr → Prop} (h : ∀ a, P a → V' a = V a) {x : Addr} {lo hi : Nat}
    (hp : ∀ a : Addr, lo ≤ a.toNat → a.toNat < hi → P a) (h1 : lo ≤ x.toNat) (h2 : x.toNat + 8 ≤ hi)
    (h3 : x.toNat + 8 ≤ 2 ^ 64) : rdq(V', x) = rdq(V, x) := by
  rw [kr h (rgn hp h1 h2 h3)]

set_option maxHeartbeats 8000000 in
/-- From the entry to 58, after `_dl_important_hwcaps` (see the module doc). -/
theorem to58 (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L ipa_at ipa)
    (hinh : CodeIn L Hwc.hwc_at Hwc.hwc)
    {cpy mlc sl : List Byte} {Pm Pa Pl : (Addr → Byte) → Prop}
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    (hins : CodeIn L 4198664#64 sl) (hs0 : 0 < sl.length) (hlen : Str.LenAt prof L o 4198664#64 Pl)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {V : Addr → Byte} {h e p : Addr} {cnt E H s : Nat}
    (hn : h = 2#64 ∧ cnt = 3 ∧ E = 8 ∧ H = 4 ∧ s = 151 ∨ h = 6#64 ∧ cnt = 4 ∧ E = 16 ∧ H = 8 ∧ s = 320)
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < e.toNat - 400 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      W a = V a) → Pa W)
    (hPl : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pl W)
    (he : 8388872 + 400 ≤ e.toNat) (he2 : e.toNat + 16 ≤ 2 ^ 64)
    (hal : (e + 18446744073709551512#64) &&& 15#64 = 0#64)
    (hFs : ∀ a : Addr, e.toNat - 400 ≤ a.toNat → a.toNat < e.toNat + 8 → Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, V (Addr.add 7288953#64 k) ≠ 0) (hx1z : V (Addr.add 7288953#64 6) = 0)
    (hx2 : ∀ k < 8, V (Addr.add 7288962#64 k) ≠ 0) (hx2z : V (Addr.add 7288962#64 8) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hU : Tgv.UnsetW F V 11#64) (hm6 : rdq(V, Tgv.ent 11#64 + 32#64) = 6#64)
    (hhw : rdq(V, 8014536#64) = h) (hfh : ∀ i < 8, Foot F.data (Addr.add 8014536#64 i))
    (hsm : rdq(V, 8029424#64) = 0#64) (hfm : ∀ i < 8, Foot F.data (Addr.add 8029424#64 i))
    (hpl : rdq(V, 8029512#64) = p) (hpl0 : rdq(V, 8029520#64) = 0#64)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add 8029520#64 i)) (hf2 : ∀ i < 8, Foot F.data (Addr.add 8029512#64 i))
    (hp0 : p ≠ 0#64) (hpd : p.toNat ≤ 7940480 ∨ e.toNat ≤ p.toNat)
    (hWb : ∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (X : State) (t : Nat) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ipa_at)
    (hsp : X.cpu.gpr.rsp = e)
    (k : ∀ Z t' (V₃ : Addr → Byte) (P : Addr), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₃ →
      Z.cpu.rip = ipa_at.add 58 → Z.cpu.gpr.rsp = e + 18446744073709551528#64 →
      Z.cpu.gpr.rbp = e + 18446744073709551608#64 → Z.cpu.gpr.rax = P →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      7940480 ≤ P.toNat → P.toNat + s ≤ e.toNat - 96 →
      (∀ a : Addr, P.toNat ≤ a.toNat → a.toNat < P.toNat + s → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937680 ∨ 7937696 ≤ a.toNat) → V₃ a = V a) →
      rdq(V₃, 7937688#64) = BitVec.ofNat 64 E →
      (∀ a : Addr, e.toNat - 88 ≤ a.toNat → V₃ a = iV0 V X.cpu.gpr a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < e.toNat - 96 →
        (a.toNat < P.toNat ∨ P.toNat + s ≤ a.toNat) → W a = V₃ a) → Pa W) →
      (∀ a : Addr, Mal.Kn a → V₃ a = V a) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hr0 : 96 ≤ e.toNat := by omega
  have hFW : ∀ a : Addr, e.toNat - 400 ≤ a.toNat → a.toNat < e.toNat + 8 → Foot Wl a :=
    fun a h1 h2 => (hFs a h1 h2).1
  have hFD : ∀ a : Addr, e.toNat - 400 ≤ a.toNat → a.toNat < e.toNat + 8 → Foot F.data a :=
    fun a h1 h2 => (hFs a h1 h2).2
  have hb : (e + 18446744073709551512#64).toNat = e.toNat - 104 := fo _ _ (by decide) (by omega)
  have hlo := iV0_out V hsp hr0 (by omega)
  -- 0: the prologue
  refine (c_0 prof).run c hin _ hK hA hrip
    (vc_0 (by rw [hsp, t88s]; ireg hFW) (by rw [hsp]; omega) hf1 hf2) ?_
  rintro j' g' fl V' ⟨rfl, hsp', hbp', hcx', hdx', hsi', hdi', hbx', h12', h13', h14', h15', rfl⟩
    Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have s₁ : Y₁.cpu.gpr.rsp = e + 18446744073709551528#64 := by
    simp only [hg₁, hsp', hsp, t8, t40s, BitVec.add_assoc, BitVec.reduceAdd]
  -- 53: `call _dl_important_hwcaps`
  refine c.s_call hK₁ hA₁ hin (lt_len (by omega)) hr₁ (call_53 _) hinh (by rw [Hwc.hwc_length]; decide) tgt_53
    (by rw [s₁, t96]; ireg hFW) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [s₁, t96] at hA₂
  -- the bytes at the `call`
  have v2o : ∀ a : Addr, ¬ (e.toNat - 96 ≤ a.toNat ∧ a.toNat < e.toNat) →
      Vst (iV0 V X.cpu.gpr) (e + 18446744073709551520#64) (toBytesLE (ipa_at.add (53 + 5)) 8) a = V a := by
    intro a ha
    rw [Tun.Vst_out _ _ _ _ (by ifd) (by ifd), hlo a (by omega)]
  have v2l : ∀ a : Addr, a.toNat < e.toNat - 96 →
      Vst (iV0 V X.cpu.gpr) (e + 18446744073709551520#64) (toBytesLE (ipa_at.add (53 + 5)) 8) a = V a :=
    fun a ha => v2o a (by omega)
  have hdi₂ : Y₂.cpu.gpr.rdi = p := by
    rw [hg₂, set4_rdi, hg₁, hdi', ← hpl]
    exact rdk (fun a ha => hlo a (Or.inl ha)) (lo := 0) (hi := e.toNat - 88) (fun a _ h2 => h2) (by omega)
      (by ipd) (by ipd)
  have hsi₂ : Y₂.cpu.gpr.rsi = 0#64 := by
    rw [hg₂, set4_rsi, hg₁, hsi', ← hpl0]
    exact rdk (fun a ha => hlo a (Or.inl ha)) (lo := 0) (hi := e.toNat - 88) (fun a _ h2 => h2) (by omega)
      (by ipd) (by ipd)
  -- `R`, the `temp` of `_dl_important_hwcaps`
  obtain ⟨R, hR1, hR2, hn'⟩ : ∃ R : Addr, e.toNat - 360 ≤ R.toNat ∧ R.toNat ≤ e.toNat - 344 ∧
      (h = 2#64 ∧ cnt = 3 ∧ E = 8 ∧ H = 4 ∧ s = 151 ∧ R = e + 18446744073709551512#64 + 18446744073709551376#64 ∨
        h = 6#64 ∧ cnt = 4 ∧ E = 16 ∧ H = 8 ∧ s = 320 ∧
          R = e + 18446744073709551512#64 + 18446744073709551360#64) := by
    rcases hn with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2, h3, h4, h5⟩
    · refine ⟨_, ?_, ?_, Or.inl ⟨h1, h2, h3, h4, h5, rfl⟩⟩ <;>
        rw [fo (r := e + 18446744073709551512#64) 18446744073709551376 240 (by decide) (by omega), hb] <;> omega
    · refine ⟨_, ?_, ?_, Or.inr ⟨h1, h2, h3, h4, h5, rfl⟩⟩ <;>
        rw [fo (r := e + 18446744073709551512#64) 18446744073709551360 256 (by decide) (by omega), hb] <;> omega
  -- `_dl_important_hwcaps`, from its entry to its `ret`
  refine Hwc.from0 c hfs hinh hinc hc0 hcpy hinm hm0 hmal hins hs0 hlen hint (h := h) (R := R)
    (bp := e + 18446744073709551512#64) (Q := 7937680#64) (N := 7937688#64) (p := p) hn'
    (fun W hW => hPm W fun a h1 h2 => by rw [hW a h1 (by ipd), v2l a (by omega)])
    (fun W hW => hPa W fun a h1 h2 => by rw [hW a (by omega) (by ipd), v2l a (by omega)])
    (fun W hW => hPl W fun a h1 => by rw [hW a h1, v2l a (by omega)])
    (by rw [hb]; omega) (by rw [hb]; omega) hal (fun a h1 h2 => hFs a (by omega) (by omega)) hpg
    (fun i hi => by
      rw [v2l (Addr.add 7288953#64 i) (by rw [toNat_add_of_fits (n := 6) hi (by ipd)]; ipd)]; exact hx1 i hi)
    (by rw [v2l (Addr.add 7288953#64 6) (by rw [toNat_add_of_fits (n := 7) (by decide) (by ipd)]; ipd)]; exact hx1z)
    (fun i hi => by
      rw [v2l (Addr.add 7288962#64 i) (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd)]; exact hx2 i hi)
    (by rw [v2l (Addr.add 7288962#64 8) (by rw [toNat_add_of_fits (n := 9) (by decide) (by ipd)]; ipd)]; exact hx2z)
    htls (Tgv.UnsetW.out hU (lo := e.toNat - 96) (hi := e.toNat) (by rw [Hwc.eent]; ipd) (by omega) v2o)
    ((rdk v2l (lo := 0) (hi := e.toNat - 96) (fun a _ h2 => h2) (by omega)
      (by rw [Hwc.eent]; ipd) (by rw [Hwc.eent]; ipd)).trans hm6)
    ((rdk v2l (lo := 0) (hi := e.toNat - 96) (fun a _ h2 => h2) (by omega) (by ipd) (by ipd)).trans hhw)
    hfh
    ((rdk v2l (lo := 0) (hi := e.toNat - 96) (fun a _ h2 => h2) (by omega) (by ipd) (by ipd)).trans hsm)
    hfm hp0 (by omega) (Or.inl (by ipd)) (by ipd)
    (fun i hi => hWb (Addr.add 7937688#64 i) (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd)
      (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd))
    (fun i hi => hWb (Addr.add 7937680#64 i) (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd)
      (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd))
    (by ipd) (Or.inl (by rw [hb]; ipd)) Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, set4_rsp, s₁, t96, t104])
    hdi₂ hsi₂ (by rw [hg₂, set4_rdx, hg₁, hdx']) (by rw [hg₂, set4_rcx, hg₁, hcx']) ?_
  -- at the `ret` (1681)
  intro Y t' W P hKY hAY hrY hax hP1 hP2 hPf hspY hbxY h12Y h13Y h14Y h15Y hbpY _ hS1 hS2 hNE hPaW hKnY
  rw [hb] at hS2
  -- the bytes `W` and the store of `max_capstrlen`
  have vY : ∀ a : Addr, (7937688 ≤ a.toNat ∨ a.toNat < 7937680) →
      Vst W 7937680#64 (toBytesLE (Hwc.caps E (Hwc.hl_ln cnt) cnt (fun _ => 0#64) 0) 8) a = W a :=
    fun a ha => Tun.Vst_out _ _ _ _ (by ipd) (by ipd)
  have hfr : ∀ a : Addr, e.toNat - 96 ≤ a.toNat →
      Vst W 7937680#64 (toBytesLE (Hwc.caps E (Hwc.hl_ln cnt) cnt (fun _ => 0#64) 0) 8) a =
        Vst (iV0 V X.cpu.gpr) (e + 18446744073709551520#64) (toBytesLE (ipa_at.add (53 + 5)) 8) a := by
    intro a ha
    rw [vY a (by omega), hS2 a (by omega) a.isLt (by ipd)]
  have hsY : Y.cpu.gpr.rsp = e + 18446744073709551520#64 := by rw [hspY, t104]
  -- 1681: `ret`
  refine c.s_ret hKY hAY hinh (Hwc.lt_len (by decide)) hrY (ret_1681 _) (by rw [hsY]; ireg hFD) hin
    (lt_len (j := 58) (by decide)) ?_ ?_
  · rw [hsY, rdk hfr (lo := e.toNat - 96) (hi := 2 ^ 64) (fun a h1 _ => h1) (by ifd) (by ifd) (by ifd)]
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by ifd), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t'' _ P hKZ hAZ hrZ (by rw [hgZ, set4_rsp, hsY, t96p])
    (by rw [hgZ, set4_rbp, hbpY, hg₂, set4_rbp, hg₁, hbp', hsp, t8]) (by rw [hgZ]; exact hax)
    (by rw [hgZ, set4_rbx, hbxY, hg₂, set4_rbx, hg₁, hbx']) (by rw [hgZ, set4_r12, h12Y, hg₂, set4_r12, hg₁, h12'])
    (by rw [hgZ, set4_r13, h13Y, hg₂, set4_r13, hg₁, h13']) (by rw [hgZ, set4_r14, h14Y, hg₂, set4_r14, hg₁, h14'])
    (by rw [hgZ, set4_r15, h15Y, hg₂, set4_r15, hg₁, h15']) hP1 (by omega) hPf ?_ ?_ ?_ ?_ ?_
  · intro a h1 h2
    rw [vY a (by omega), hS1 a (Nat.zero_le _) h1 (by ipd), v2l a (by omega)]
  · rw [rdk vY (lo := 7937688) (hi := 2 ^ 64) (fun a h1 _ => Or.inl h1) (by ipd) (by ipd) (by ipd)]
    exact hNE
  · intro a ha
    rw [hfr a (by omega), Tun.Vst_out _ _ _ _ (by ifd) (by ifd)]
  · intro W' hW'
    refine hPaW W' fun a h1 h2 h3 => ?_
    rw [hW' a h1 (by omega) h3, vY a (by omega)]
  · intro a ha
    have := Mal.Kn.lt ha
    rw [vY a (by omega), hKnY a ha, v2l a (by omega)]

end FV7z.Ipa
