import FV7z.Ipa.Run3
/-!
# `_dl_init_paths (NULL)`: from the entry to the return (PLAN.md G3, startup)

`whole`: `to58` (the prologue, `_dl_important_hwcaps`), `to75` (`malloc (40)`), `to267` (`malloc (160 q)`,
`_dl_all_dirs`), the loop over the three elements (`loop`, `memset` of each status array) to the epilogue and the
`ret` at 450, back to the caller (`rdq(V, e)`): `rsp = e + 8`, the registers a call keeps as at the entry, the bytes
below the heap as at the entry but for `0x791e80..0x791eb8` (`rtld_search_dirs`, `max_capstrlen`, `ncapstr`,
`_dl_capstrs`, `_dl_all_dirs`), and those from `e` up. With `r = e - 8` the frame's `rbp`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ipa

set_option maxRecDepth 100000

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {fb : Addr}

theorem w536 (e : Addr) : e + 18446744073709551608#64 + 18446744073709551536#64 = e + 18446744073709551528#64 := by
  bv_omega

/-- The registers the prologue stored, read back. -/
theorem iV0_rd (V : Addr → Byte) {g : Gprs} {e : Addr} (h : g.rsp = e) (hr0 : 96 ≤ e.toNat)
    (he : e.toNat + 8 ≤ 2 ^ 64) :
    rdq(iV0 V g, e + 18446744073709551608#64) = g.rbp ∧ rdq(iV0 V g, e + 18446744073709551600#64) = g.r15 ∧
    rdq(iV0 V g, e + 18446744073709551592#64) = g.r14 ∧ rdq(iV0 V g, e + 18446744073709551584#64) = g.r13 ∧
    rdq(iV0 V g, e + 18446744073709551576#64) = g.r12 ∧ rdq(iV0 V g, e + 18446744073709551568#64) = g.rbx ∧
    rdq(iV0 V g, e + 18446744073709551528#64) = g.rdi := by
  rw [iV0_eq V h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (ipeel; iself)

set_option maxHeartbeats 8000000 in
/-- `_dl_init_paths (NULL)` from the entry to the return (see the module doc). -/
theorem whole (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L ipa_at ipa)
    (hinh : CodeIn L Hwc.hwc_at Hwc.hwc)
    {cpy mlc sl ms : List Byte} {Pm Pa Pl Ps : (Addr → Byte) → Prop}
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length) (hmal : Mal.At prof L o 6500704#64 Pa)
    (hinl : CodeIn L 4198664#64 sl) (hl0 : 0 < sl.length) (hlenA : Str.LenAt prof L o 4198664#64 Pl)
    (hinz : CodeIn L 4198528#64 ms) (hz0 : 0 < ms.length) (hset : SetAt prof L o 4198528#64 Ps)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {V : Addr → Byte} {h e p : Addr} {cnt E H s : Nat}
    (hn : h = 2#64 ∧ cnt = 3 ∧ E = 8 ∧ H = 4 ∧ s = 151 ∨ h = 6#64 ∧ cnt = 4 ∧ E = 16 ∧ H = 8 ∧ s = 320)
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      W a = V a) → Pm W)
    (hPa : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < e.toNat - 400 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      W a = V a) → Pa W)
    (hPl : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = V a) → Pl W)
    (hPs : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      W a = V a) → Ps W)
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
    (hfN : ∀ x : Addr, 7937688 ≤ x.toNat → x.toNat < 7937696 → Foot F.data x)
    (hW7a : ∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a)
    (hW7b : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (hlenV : ∀ k < 3, rdq(V, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (lA k))
    (hslV : ∀ k < 3, ofBytesLE 8 (List.map V (byteAddrs (BitVec.ofNat 64 (sA k)) 1)) = 47#8)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, e) = e₂.add j₂)
    (X : State) (t : Nat) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ipa_at)
    (hsp : X.cpu.gpr.rsp = e) (hdi : X.cpu.gpr.rdi = 0#64)
    (k : ∀ Z t' (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rsp = e + 8 → Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp →
      Z.cpu.gpr.r12 = X.cpu.gpr.r12 → Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 →
      Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ e.toNat ≤ a.toNat) → V' a = V a) →
      (∀ a : Addr, Mal.Kn a → V' a = V a) → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hr0 : 96 ≤ e.toNat := by omega
  have hr8 : (e + 18446744073709551608#64).toNat = e.toNat - 8 := f8 hr0
  have hFD : ∀ a : Addr, e.toNat - 400 ≤ a.toNat → a.toNat < e.toNat + 8 → Foot F.data a :=
    fun a h1 h2 => (hFs a h1 h2).2
  have hFr : ∀ a : Addr, (e + 18446744073709551608#64).toNat - 88 ≤ a.toNat →
      a.toNat < (e + 18446744073709551608#64).toNat + 8 → Foot Wl a ∧ Foot F.data a :=
    fun a h1 h2 => hFs a (by rw [hr8] at h1; omega) (by rw [hr8] at h2; omega)
  obtain ⟨q, hq⟩ : ∃ q, E = 8 ∧ q = 2 ∨ E = 16 ∧ q = 3 := by
    rcases hn with ⟨-, -, rfl, -, -⟩ | ⟨-, -, rfl, -, -⟩
    · exact ⟨2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨3, Or.inr ⟨rfl, rfl⟩⟩
  obtain ⟨i0bp, i0r15, i0r14, i0r13, i0r12, i0bx, i0di⟩ := iV0_rd V hsp hr0 (by omega)
  -- the entry to 58
  refine to58 c hfs hin hinh hinc hc0 hcpy hinm hm0 hmal hinl hl0 hlenA hint hn hPm hPa hPl he he2 hal hFs hpg
    hx1 hx1z hx2 hx2z htls hU hm6 hhw hfh hsm hfm hpl hpl0 hf1 hf2 hp0 hpd hWb X t hK hA hrip hsp ?_
  intro Z₁ t₁ V₃ P hK₁ hA₁ hr₁ hs₁ hbp₁ _ hbx₁ h12₁ h13₁ h14₁ h15₁ _ _ _ hlo3 hN3 hfr3 hPa3 hKn3
  -- 58 to 75
  refine to75 c hin hinm hm0 hmal he he2 hFs hWb hlo3 hN3 hfr3 hPa3 hKn3 Z₁ t₁ hK₁ hA₁ hr₁ hs₁ ?_
  intro Z₂ t₂ V₄ A hK₂ hA₂ hr₂ hs₂ hax₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂ hA1 hA2 hAf hlo4 hN4 hfr4 hPa4 hKn4 hAk
  have hA2' : A.toNat + 40 ≤ (e + 18446744073709551608#64).toNat - 88 := by rw [hr8]; omega
  -- 75 to 267
  refine to267 c hin hinm hm0 hmal hq (by rw [hr8]; omega) (by rw [hr8]; omega) hFr hWb hfN hW7a hA1 hAk hA2'
    (fun a h1 h2 => (hAf a h1 h2).1) hN4
    (fun W hW => hPa4 W fun a h1 h2 h3 => hW a h1 (by rw [hr8]; omega) h3) Z₂ t₂ hK₂ hA₂ hr₂
    (by rw [hs₂, w536]) hax₂ (by rw [hbp₂, hbp₁]) ?_
  intro Z₃ t₃ V₅ B hK₃ hA₃ hr₃ hs₃ hbp₃ h15₃ h14₃ h12₃ hbx₃ h13₃ hB1 hB2 hBW h64 h72 h56 hk5 hKn5 hBk
  -- the bytes at 267
  have hlo5 : ∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480) → V₅ a = V a :=
    fun a ha => (hk5 a (by omega)).trans (hlo4 a (by omega) (by omega))
  have hfr5 : ∀ a : Addr, e.toNat - 56 ≤ a.toNat → V₅ a = iV0 V X.cpu.gpr a :=
    fun a ha => (hk5 a (by rw [hr8]; omega)).trans (hfr4 a (by omega))
  have hfr80 : ∀ a : Addr, (e.toNat - 88 ≤ a.toNat ∧ a.toNat < e.toNat - 80) → V₅ a = iV0 V X.cpu.gpr a :=
    fun a ha => (hk5 a (by rw [hr8]; omega)).trans (hfr4 a (by omega))
  have h80 : rdq(V₅, e + 18446744073709551608#64 + 18446744073709551536#64) = 0#64 := by
    rw [w536, rdk hfr80 (lo := e.toNat - 88) (hi := e.toNat - 80) (fun a h1 h2 => ⟨h1, h2⟩) (by ifd) (by ifd)
      (by ifd), i0di, hdi]
  have hlen : ∀ k < 3, rdq(V₅, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (lA k) := by
    intro k hk
    rw [rdk hlo5 (lo := 0) (hi := 7937664) (fun a _ h => Or.inl h) (Nat.zero_le _) (by ipd) (by ipd)]
    exact hlenV k hk
  have hsl : ∀ k < 3, ofBytesLE 8 (List.map V₅ (byteAddrs (BitVec.ofNat 64 (sA k)) 1)) = 47#8 := by
    intro k hk
    have hb : (BitVec.ofNat 64 (sA k)).toNat + 1 ≤ 7937664 := by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide +kernel
    rw [kr hlo5 (rgn (p := fun a : Addr => a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480)
      (lo := 0) (hi := 7937664) (fun a _ h => Or.inl h) (Nat.zero_le _) hb (by omega))]
    exact hslV k hk
  -- the loop from `i = 0`, to the `ret`
  refine loop c hin hinz hz0 hset hq (r := e + 18446744073709551608#64)
    (fun W hW => hPs W fun x h1 h2 => (hW x h1).trans (hlo5 x (by omega))) (by rw [hr8]; omega)
    (by rw [hr8]; omega) (fun x h1 h2 => hFr x h1 h2) hFR hW7b (fun x h1 h2 => hWb x (by omega) h2)
    h72 h64 h56 h80 hlen hsl hB1 hBk hB2 hBW hA1 hAk hA2' (fun a h1 h2 => (hAf a h1 h2).1) ?_
    0 (Nat.zero_le _) Z₃ t₃ V₅ B (A + 8#64) hK₃ hA₃ hr₃ hs₃ hbp₃ h15₃ (by omega) h14₃ (by ipd)
    (by rw [h12₃]; try rfl) (by rw [hbx₃]; try rfl) h13₃ (fun _ _ => rfl)
  -- 450: `ret`
  unfold Fin450
  intro Y t' V' hKY hAY hrY hsY hbxY h12Y h13Y h14Y h15Y hbpY hkY
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at hsY hbxY h12Y h13Y h14Y h15Y
  have hkE : ∀ a : Addr, e.toNat ≤ a.toNat → V' a = V a := fun a ha =>
    (hkY a (Or.inr (Or.inr (Or.inl (by rw [hr8]; omega))))).trans
      ((hfr5 a (by omega)).trans (iV0_out V hsp hr0 (by omega) a (Or.inr ha)))
  have rR : ∀ x : Addr, e.toNat - 56 ≤ x.toNat → x.toNat + 8 ≤ 2 ^ 64 → rdq(V₅, x) = rdq(iV0 V X.cpu.gpr, x) :=
    fun x h1 h2 => rdk hfr5 (lo := e.toNat - 56) (hi := 2 ^ 64) (fun a h _ => h) h1 h2 h2
  refine c.s_ret hKY hAY hin (lt_len (by omega)) hrY (ret_450 _) (by rw [hsY]; ireg hFD) hin₂ h₂ ?_ ?_
  · rw [hsY, rdk hkE (lo := e.toNat) (hi := 2 ^ 64) (fun a h _ => h) (Nat.le_refl _) (by omega) (by omega)]
    exact hra
  rintro Z t'' hKZ hAZ ⟨hrZ, hgZ⟩
  refine k Z t'' V' hKZ hAZ hrZ (by rw [hgZ, set4_rsp, hsY])
    (by rw [hgZ, set4_rbx, hbxY, rR _ (by ifd) (by ifd), i0bx])
    (by rw [hgZ, set4_rbp, hbpY, rR _ (by ifd) (by ifd), i0bp])
    (by rw [hgZ, set4_r12, h12Y, rR _ (by ifd) (by ifd), i0r12])
    (by rw [hgZ, set4_r13, h13Y, rR _ (by ifd) (by ifd), i0r13])
    (by rw [hgZ, set4_r14, h14Y, rR _ (by ifd) (by ifd), i0r14])
    (by rw [hgZ, set4_r15, h15Y, rR _ (by ifd) (by ifd), i0r15]) ?_
    fun a ha => (hkY a (Or.inr (Or.inr (Or.inr ha)))).trans ((hKn5 a ha).trans (hKn4 a ha))
  intro a ha
  rcases ha with ha | ha | ha
  · exact (hkY a (Or.inl (by omega))).trans (hlo5 a (Or.inl ha))
  · exact (hkY a (Or.inr (Or.inl ha))).trans (hlo5 a (Or.inr ha))
  · exact hkE a ha

end FV7z.Ipa
