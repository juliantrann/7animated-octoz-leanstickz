import FV7z.Ipa.Run2
/-!
# `_dl_init_paths`: from 75 to the first `memset` (267) (PLAN.md G3, startup)

`to267`: `A` to `rtld_search_dirs.dirs` and `n = ncapstr` to `r - 0x38` (`vc_75`), the `call` of `malloc (160 q)`
at 148 (`Mal.At`, assumed), back at 153 with `rax = B`, `_dl_all_dirs` and the first element (`vc_153`), to 267:
the state the loop (`Ipa.loop`) starts from, its `i = 0`. Here `r = rbp`, the frame from `r - 0x58` (`rsp`) up.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ipa

set_option maxRecDepth 100000

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

theorem u88 (r : Addr) : r + 18446744073709551536#64 - 8 = r + 18446744073709551528#64 := by bv_omega
theorem u88p (r : Addr) : r + 18446744073709551528#64 + 8 = r + 18446744073709551536#64 := by bv_omega

set_option maxHeartbeats 4000000 in
/-- From 75 to 267, after `malloc (160 q)` (see the module doc). -/
theorem to267 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ipa_at ipa) {mlc : List Byte}
    {Pa : (Addr → Byte) → Prop} (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length)
    (hmal : Mal.At prof L o 6500704#64 Pa) {V₄ : Addr → Byte} {r A : Addr} {E q : Nat}
    (hq : E = 8 ∧ q = 2 ∨ E = 16 ∧ q = 3)
    (hr : 8029560 + 88 ≤ r.toNat) (hr2 : r.toNat + 16 ≤ 2 ^ 64)
    (hFs : ∀ a : Addr, r.toNat - 88 ≤ a.toNat → a.toNat < r.toNat + 8 → Foot Wl a ∧ Foot F.data a)
    (hWb : ∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (hfN : ∀ x : Addr, 7937688 ≤ x.toNat → x.toNat < 7937696 → Foot F.data x)
    (hW7a : ∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a)
    (hA1 : 7940480 ≤ A.toNat) (hA2 : A.toNat + 40 ≤ r.toNat - 88)
    (hAW : ∀ a : Addr, A.toNat ≤ a.toNat → a.toNat < A.toNat + 40 → Foot Wl a)
    (hN4 : rdq(V₄, 7937688#64) = BitVec.ofNat 64 E)
    (hPa4 : ∀ W : Addr → Byte, (∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < r.toNat - 88 →
      (a.toNat < A.toNat ∨ A.toNat + 40 ≤ a.toNat) → W a = V₄ a) → Pa W)
    (Z : State) (t : Nat) (hK : KeptW Wl s₀ Z) (hA : Agree F Z.proc.mm.mem V₄) (hrip : Z.cpu.rip = ipa_at.add 75)
    (hsp : Z.cpu.gpr.rsp = r + 18446744073709551536#64) (hax : Z.cpu.gpr.rax = A) (hbp : Z.cpu.gpr.rbp = r)
    (k : ∀ Z' t' (V₅ : Addr → Byte) (B : Addr), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem V₅ →
      Z'.cpu.rip = ipa_at.add 267 → Z'.cpu.gpr.rsp = r + 18446744073709551536#64 → Z'.cpu.gpr.rbp = r →
      Z'.cpu.gpr.r15 = B → Z'.cpu.gpr.r14 = A + 8#64 → Z'.cpu.gpr.r12 = 7364032#64 →
      Z'.cpu.gpr.rbx = 7364087#64 → Z'.cpu.gpr.r13 = BitVec.ofNat 64 (4 * E) →
      7940480 ≤ B.toNat → B.toNat + 160 * q ≤ r.toNat - 88 →
      (∀ a : Addr, B.toNat ≤ a.toNat → a.toNat < B.toNat + 160 * q → Foot Wl a) →
      rdq(V₅, r + 18446744073709551552#64) = BitVec.ofNat 64 (40 * q) →
      rdq(V₅, r + 18446744073709551544#64) = BitVec.ofNat 64 (2 ^ 64 - 40 * q) →
      rdq(V₅, r + 18446744073709551560#64) = BitVec.ofNat 64 E →
      (∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨
        r.toNat - 80 ≤ a.toNat ∧ a.toNat < r.toNat - 72 ∨ r.toNat - 48 ≤ a.toNat) → V₅ a = V₄ a) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Z t := by
  have hr0 : 96 ≤ r.toNat := by omega
  have hq3 : q ≤ 3 := by omega
  have hq160 : (BitVec.ofNat 64 (160 * q)).toNat = 160 * q := by
    simp only [BitVec.toNat_ofNat, Nat.reducePow]
    exact Nat.mod_eq_of_lt (by omega)
  have hFW : ∀ a : Addr, r.toNat - 88 ≤ a.toNat → a.toNat < r.toNat + 8 → Foot Wl a :=
    fun a h1 h2 => (hFs a h1 h2).1
  have hFD : ∀ a : Addr, r.toNat - 88 ≤ a.toNat → a.toNat < r.toNat + 8 → Foot F.data a :=
    fun a h1 h2 => (hFs a h1 h2).2
  have hA0 : Z.cpu.gpr.rax ≠ 0#64 := by
    rw [hax]; intro h; subst h; simp at hA1
  -- 75: `A` to `rtld_search_dirs.dirs`, `n` to `r - 0x38`, `rdi = 160 q`
  refine (c_75 prof).run c hin _ hK hA hrip
    (vc_75 hq hA0 hN4 (by ireg hWb) (by ireg hfN) (by rw [hbp]; ireg hFW)) ?_
  rintro j' g' fl V' ⟨rfl, hdi, hbx, h13, h14, hbp', hsp', h12, h15, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst hg₁
  rw [hbp] at hA₁
  -- 148: `call malloc`
  refine c.s_call hK₁ hA₁ hin (lt_len (by omega)) hr₁ (call_148 _) hinm hm0 tgt_148
    (by rw [hsp', hsp, u88]; ireg hFW) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp', hsp, u88] at hA₂
  have s₂ : Y₂.cpu.gpr.rsp = r + 18446744073709551528#64 := by rw [hg₂, set4_rsp, hsp', hsp, u88]
  have hdi₂ : Y₂.cpu.gpr.rdi = BitVec.ofNat 64 (160 * q) := by rw [hg₂, set4_rdi, hdi]
  refine hmal c hK₂ hA₂ hr₂ (hPa4 _ fun a h1 h2 h3 => ?_) (by rw [hdi₂, hq160]; omega) hin
    (lt_len (j := 153) (by omega)) ?_ (by rw [s₂]; ireg hFD) ?_
  · rw [Tun.Vst_out _ _ _ _ (by ifd) (by ifd), Tun.Vst_out _ _ _ _ (by ifd) (by ifd),
      Tun.Vst_out _ _ _ _ (by ipd) (by ipd)]
  · rw [s₂, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by ifd), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  -- 153: back from `malloc`
  intro Z₂ t₃ V₅ B hK₃ hA₃ hr₃ hs₃ hax₃ hbx₃ hbp₃ h12₃ h13₃ h14₃ h15₃ hB1 hB2 hBf hkeep _
  simp only [hdi₂, s₂, hq160, f88 hr0] at hB2 hBf hkeep
  have hbp₂ : Z₂.cpu.gpr.rbp = r := by rw [hbp₃, hg₂, set4_rbp, hbp', hbp]
  have h14₂ : Z₂.cpu.gpr.r14 = A := by rw [h14₃, hg₂, set4_r14, h14, hax]
  have hn5 : rdq(V₅, r + 18446744073709551560#64) = BitVec.ofNat 64 E := by
    rw [rdk hkeep (lo := r.toNat - 80) (hi := 2 ^ 64) (fun a h1 _ => Or.inr (by omega)) (by ifd) (by ifd)
        (by ifd),
      Tun.rd_Vst _ _ _ _ _ (by ifd) (by ifd) (by ifd),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by ifd), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  have hB0 : Z₂.cpu.gpr.rax ≠ 0#64 := by
    rw [hax₃]; intro h; subst h; simp at hB1
  refine (c_153 prof).run c hin _ hK₃ hA₃ hr₃
    (vc_153 hq hB0 (by rw [hbx₃, hg₂, set4_rbx, hbx]) (by rw [hbp₂]; exact hn5) (by rw [hbp₂]; exact hr)
      (by rw [hbp₂]; exact hr2) (by rw [hax₃]; exact hB1) (by rw [hax₃, hbp₂]; omega)
      (by rw [h14₂]; exact hA1) (by rw [h14₂, hbp₂]; omega) (by rw [h14₂]; exact hAW)
      (by rw [hax₃]; exact fun a h1 h2 => (hBf a h1 h2).1)
      (by rw [hbp₂]; exact fun a h1 h2 => hFs a (by omega) h2) hW7a hWb) ?_
  rintro j' g' fl V' ⟨rfl, h15', h14', h12', hbx', h13', hbp', hsp', h64', h72', hk'⟩ Y₃ t₄ hK₄ hA₄ hr₄ hg₄ -
  subst hg₄
  rw [hbp₂] at h64' h72' hk'
  refine k Y₃ t₄ V' B hK₄ hA₄ hr₄ (by rw [hsp', hs₃, s₂, u88p]) (by rw [hbp', hbp₂]) (by rw [h15', hax₃])
    (by rw [h14', h14₂]) h12' hbx' (by rw [h13', h13₃, hg₂, set4_r13, h13]) hB1 hB2
    (fun a h1 h2 => (hBf a h1 h2).1) h64' h72' ?_ ?_
  · rw [rdk hk' (lo := r.toNat - 56) (hi := 2 ^ 64) (fun a h1 _ => Or.inr (Or.inr (Or.inr h1))) (by ifd)
      (by ifd) (by ifd)]
    exact hn5
  · intro a ha
    rw [hk' a (by omega), hkeep a (by omega), Tun.Vst_out _ _ _ _ (by ifd) (by ifd),
      Tun.Vst_out _ _ _ _ (by ifd) (by ifd), Tun.Vst_out _ _ _ _ (by ipd) (by ipd)]

end FV7z.Ipa
