import FV7z.Ipa.Run1
/-!
# `_dl_init_paths`: from 58 to the return of the first `malloc` (75) (PLAN.md G3, startup)

`to75`: `P` to `_dl_capstrs` (`0x791ea0`, `vc_58`), the `call` of `malloc (40)` at 70 (`Mal.At`, assumed), back at 75
with `rax = A`: `[A, A + 40)` in the heap below the frame, the bytes below the heap as at the entry but for
`0x791e90..0x791ea8`, those from `e - 0x58` up the prologue's, and the state of the heap for the next `malloc`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ipa

set_option maxRecDepth 100000

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

set_option maxHeartbeats 4000000 in
/-- From 58 to 75, after `malloc (40)` (see the module doc). -/
theorem to75 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ipa_at ipa) {mlc : List Byte}
    {Pa : (Addr → Byte) → Prop} (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length)
    (hmal : Mal.At prof L o 6500704#64 Pa) {V V₃ : Addr → Byte} {g : Gprs} {e P : Addr} {s E : Nat}
    (he : 8388872 + 400 ≤ e.toNat) (he2 : e.toNat + 16 ≤ 2 ^ 64)
    (hFs : ∀ a : Addr, e.toNat - 400 ≤ a.toNat → a.toNat < e.toNat + 8 → Foot Wl a ∧ Foot F.data a)
    (hWb : ∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (hlo3 : ∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937680 ∨ 7937696 ≤ a.toNat) → V₃ a = V a)
    (hN3 : rdq(V₃, 7937688#64) = BitVec.ofNat 64 E)
    (hfr3 : ∀ a : Addr, e.toNat - 88 ≤ a.toNat → V₃ a = iV0 V g a)
    (hPa3 : ∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < e.toNat - 96 →
      (a.toNat < P.toNat ∨ P.toNat + s ≤ a.toNat) → W a = V₃ a) → Pa W)
    (Z : State) (t : Nat) (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V₃) (hrip : Z.cpu.rip = ipa_at.add 58)
    (hsp : Z.cpu.gpr.rsp = e + 18446744073709551528#64)
    (k : ∀ Z' t' (V₄ : Addr → Byte) (A : Addr), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V₄ →
      Z'.cpu.rip = ipa_at.add 75 → Z'.cpu.gpr.rsp = e + 18446744073709551528#64 → Z'.cpu.gpr.rax = A →
      Z'.cpu.gpr.rbx = Z.cpu.gpr.rbx → Z'.cpu.gpr.rbp = Z.cpu.gpr.rbp → Z'.cpu.gpr.r12 = Z.cpu.gpr.r12 →
      Z'.cpu.gpr.r13 = Z.cpu.gpr.r13 → Z'.cpu.gpr.r14 = Z.cpu.gpr.r14 → Z'.cpu.gpr.r15 = Z.cpu.gpr.r15 →
      7940480 ≤ A.toNat → A.toNat + 40 ≤ e.toNat - 96 →
      (∀ a : Addr, A.toNat ≤ a.toNat → a.toNat < A.toNat + 40 → Foot Wl a ∧ Foot F.data a) →
      (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937680 ∨ 7937704 ≤ a.toNat) → V₄ a = V a) →
      rdq(V₄, 7937688#64) = BitVec.ofNat 64 E →
      (∀ a : Addr, e.toNat - 88 ≤ a.toNat → V₄ a = iV0 V g a) →
      (∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < e.toNat - 96 →
        (a.toNat < A.toNat ∨ A.toNat + 40 ≤ a.toNat) → W a = V₄ a) → Pa W) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  have hr0 : 96 ≤ e.toNat := by omega
  have hFW : ∀ a : Addr, e.toNat - 400 ≤ a.toNat → a.toNat < e.toNat + 8 → Foot Wl a :=
    fun a h1 h2 => (hFs a h1 h2).1
  have hFD : ∀ a : Addr, e.toNat - 400 ≤ a.toNat → a.toNat < e.toNat + 8 → Foot F.data a :=
    fun a h1 h2 => (hFs a h1 h2).2
  -- 58: `P` to `_dl_capstrs`, `rdi = 40`
  refine (c_58 prof).run c hin _ hK hA hrip
    (vc_58 fun i hi => hWb (Addr.add 7937696#64 i) (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd)
      (by rw [toNat_add_of_fits (n := 8) hi (by ipd)]; ipd)) ?_
  rintro j' g' fl V' ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have s₁ : Y₁.cpu.gpr.rsp = e + 18446744073709551528#64 := by rw [hg₁]; exact hsp
  -- 70: `call malloc`
  refine c.s_call hK₁ hA₁ hin (lt_len (by omega)) hr₁ (call_70 _) hinm hm0 tgt_70 (by rw [s₁, t96]; ireg hFW) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [s₁, t96] at hA₂
  have s₂ : Y₂.cpu.gpr.rsp = e + 18446744073709551520#64 := by rw [hg₂, set4_rsp, s₁, t96]
  have hdi : Y₂.cpu.gpr.rdi = 40#64 := by rw [hg₂, set4_rdi, hg₁]
  refine hmal c hK₂ hA₂ hr₂ (hPa3 _ fun a h1 h2 h3 => ?_) (by rw [hdi]; ipd) hin (lt_len (j := 75) (by omega))
    ?_ (by rw [s₂]; ireg hFD) ?_
  · rw [Tun.Vst_out _ _ _ _ (by ifd) (by ifd), Tun.Vst_out _ _ _ _ (by ipd) (by ipd)]
  · rw [s₂, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by ifd), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  -- 75: back from `malloc`
  intro Z₂ t₃ V₄ A hK₃ hA₃ hr₃ hs₃ hax hbx₃ hbp₃ h12₃ h13₃ h14₃ h15₃ hA1 hA2 hAf hkeep hPa4
  simp only [hdi, s₂, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, f96 hr0] at hA2 hAf hkeep hPa4
  refine k Z₂ t₃ V₄ A hK₃ hA₃ hr₃ (by rw [hs₃, s₂, t96p]) hax (by rw [hbx₃, hg₂, set4_rbx, hg₁])
    (by rw [hbp₃, hg₂, set4_rbp, hg₁]) (by rw [h12₃, hg₂, set4_r12, hg₁]) (by rw [h13₃, hg₂, set4_r13, hg₁])
    (by rw [h14₃, hg₂, set4_r14, hg₁]) (by rw [h15₃, hg₂, set4_r15, hg₁]) hA1 hA2 hAf ?_ ?_ ?_ hPa4
  · intro a h1 h2
    rw [hkeep a (Or.inl h1), Tun.Vst_out _ _ _ _ (by ifd) (by ifd), Tun.Vst_out _ _ _ _ (by ipd) (by ipd),
      hlo3 a h1 (by omega)]
  · rw [rdk hkeep (lo := 0) (hi := 7940480) (fun a _ h2 => Or.inl h2) (by omega) (by ipd) (by ipd),
      Tun.rd_Vst _ _ _ _ _ (by ifd) (by ipd) (by ifd), Tun.rd_Vst _ _ _ _ _ (by ipd) (by ipd) (by ipd)]
    exact hN3
  · intro a ha
    rw [hkeep a (Or.inr (by omega)), Tun.Vst_out _ _ _ _ (by ifd) (by ifd), Tun.Vst_out _ _ _ _ (by ipd) (by ipd),
      hfr3 a ha]

end FV7z.Ipa
