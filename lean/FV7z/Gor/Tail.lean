import FV7z.Gor.Holds
/-!
# `_dl_get_origin` after its `malloc`: to the caller (PLAN.md G3, startup)

- `epi`: from 255 (the epilogue), `rsp = B`: the four saved registers back from `B + 4104`, the `ret` to the return
  address at `B + 4136`.
- `t129`: from 129, `malloc (2)` returned `p ≠ 0`: `"/"` stored at `p` (the directory `/`), to the caller with
  `rax = p`.
- `t283`: from 283, `malloc (s + 2)` returned `p ≠ 0`: `mempcpy (p, B, s)` (`PcpyAt`), the NUL at `p + s`, to the
  caller with `rax = p`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gor

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}

/-- The epilogue from 255 and the `ret`: `rax = r12`, the saved registers read back from `B + 4104`, the return address
at `B + 4136` in code of the list. -/
theorem epi (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor) {X : State} {t : Nat} {V : Addr → Byte}
    {B e' : Addr} {code : List Byte} {j : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gor_at.add 255)
    (hsp : X.cpu.gpr.rsp = B) (hf : ∀ i < 40, Foot F.data (Addr.add (B + 4104#64) i))
    (hinr : CodeIn L e' code) (hj : j < code.length) (hra : rdq(V, B + 4136#64) = e'.add j)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e'.add j →
      Z.cpu.gpr.rax = X.cpu.gpr.r12 → Z.cpu.gpr.rsp = B + 4144#64 →
      Z.cpu.gpr.rbx = rdq(V, B + 4104#64) → Z.cpu.gpr.rbp = rdq(V, B + 4112#64) →
      Z.cpu.gpr.r12 = rdq(V, B + 4120#64) → Z.cpu.gpr.r13 = rdq(V, B + 4128#64) →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have slot : ∀ (a : Addr) (k : Nat), k < 40 → a = Addr.add (B + 4104#64) k → Foot F.data a :=
    fun a k hk ha => ha ▸ hf k hk
  refine (c_255 prof).run c hin _ hK hA hrip (vc_255 fun i hi => ?_) ?_
  · rw [hsp]
    exact hf i (by omega)
  rintro j' g₁ fl V' ⟨rfl, hax, hsp', hbx, hbp, h12, h13, h14, h15, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg -
  subst hg
  rw [hsp] at hsp' hbx hbp h12 h13
  have hsp'' : Y.cpu.gpr.rsp = B + 4136#64 := by rw [hsp']; bv_omega
  refine c.s_ret hK₁ hA₁ hin (lt_len (by decide)) hr₁ (ret_271 _) (fun i hi => ?_) hinr hj
    (by rw [hsp'']; exact hra) ?_
  · rw [hsp'']
    exact slot _ (32 + i) (by omega) (by simp only [Addr.add]; bv_omega)
  rintro Z t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  have e1 : B + 4104#64 + 8 = B + 4112#64 := by bv_omega
  have e2 : B + 4104#64 + 8 + 8 = B + 4120#64 := by bv_omega
  have e3 : B + 4104#64 + 8 + 8 + 8 = B + 4128#64 := by bv_omega
  rw [e1] at hbp
  rw [e2] at h12
  rw [e3] at h13
  refine k Z t₂ hK₂ hA₂ hr₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hg₂]; exact hax
  · rw [hg₂]
    show Y.cpu.gpr.rsp + 8 = _
    rw [hsp'']
    bv_omega
  · rw [hg₂]; exact hbx
  · rw [hg₂]; exact hbp
  · rw [hg₂]; exact h12
  · rw [hg₂]; exact h13
  · rw [hg₂]; exact h14
  · rw [hg₂]; exact h15

/-- From 129, `malloc (2)` returned `p ≠ 0`, apart from the frame: `"/"` and a NUL at `p`, to the caller with
`rax = p`, the saved registers back. -/
theorem t129 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor) {X : State} {t : Nat} {V : Addr → Byte}
    {B p e' : Addr} {code : List Byte} {j : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gor_at.add 129)
    (hsp : X.cpu.gpr.rsp = B) (hax : X.cpu.gpr.rax = p) (hp : p ≠ 0) (hw : ∀ i < 2, Foot Wl (Addr.add p i))
    (hBt : B.toNat + 4144 ≤ 2 ^ 64) (hpt : p.toNat + 2 ≤ 2 ^ 64)
    (hpa : p.toNat + 2 ≤ B.toNat + 4104 ∨ B.toNat + 4144 ≤ p.toNat)
    (hf : ∀ i < 40, Foot F.data (Addr.add (B + 4104#64) i))
    (hinr : CodeIn L e' code) (hj : j < code.length) (hra : rdq(V, B + 4136#64) = e'.add j)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vst V p (toBytesLE (BitVec.setWidth 16 47#32) 2)) →
      Z.cpu.rip = e'.add j → Z.cpu.gpr.rax = p → Z.cpu.gpr.rsp = B + 4144#64 →
      Z.cpu.gpr.rbx = rdq(V, B + 4104#64) → Z.cpu.gpr.rbp = rdq(V, B + 4112#64) →
      Z.cpu.gpr.r12 = rdq(V, B + 4120#64) → Z.cpu.gpr.r13 = rdq(V, B + 4128#64) →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_129 prof).run c hin _ hK hA hrip (vc_129 (by rw [hax]; exact hp) (by rw [hax]; exact hw)) ?_
  rintro j' g₁ fl V' ⟨rfl, h12, hkp, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg -
  subst hg
  rw [hax] at hA₁ h12
  have hrd : ∀ x : Addr, B.toNat + 4104 ≤ x.toNat → x.toNat + 8 ≤ B.toNat + 4144 →
      rdq(Vst V p (toBytesLE (BitVec.setWidth 16 47#32) 2), x) = rdq(V, x) := fun x h1 h2 => by
    rw [map_out V p _ x 8 (by rw [toBytesLE_length]; omega) (by omega) (by rw [toBytesLE_length]; omega)]
  refine epi c hin hK₁ hA₁ hr₁ (hkp.1.trans hsp) hf hinr hj
    (by rw [hrd _ (by bv_omega) (by bv_omega)]; exact hra) ?_
  intro Z t₂ hK₂ hA₂ hr₂ hax₂ hsp₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂
  exact k Z t₂ hK₂ hA₂ hr₂ (hax₂.trans h12) hsp₂ (hbx₂.trans (hrd _ (by bv_omega) (by bv_omega)))
    (hbp₂.trans (hrd _ (by bv_omega) (by bv_omega))) (h12₂.trans (hrd _ (by bv_omega) (by bv_omega)))
    (h13₂.trans (hrd _ (by bv_omega) (by bv_omega))) (h14₂.trans hkp.2.2.1) (h15₂.trans hkp.2.2.2)

/-- From 283, `malloc (s + 2)` returned `p ≠ 0`, apart from the frame and the slot of the return address of the `call`:
`mempcpy (p, B, s)` (`PcpyAt` of the `mempcpy` at `0x4010c0`), the NUL at `p + s`, to the caller with `rax = p`: the
bytes at `p` those at `B`, then a NUL, the others as they were but the slot below `B`. -/
theorem t283 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor) {X : State} {t : Nat} {V : Addr → Byte}
    {B p e' : Addr} {s : Nat} {code cpy : List Byte} {j : Nat} {Pm : (Addr → Byte) → Prop}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gor_at.add 283)
    (hsp : X.cpu.gpr.rsp = B) (hbp : X.cpu.gpr.rbp = B) (hax : X.cpu.gpr.rax = p) (hp : p ≠ 0)
    (hbx : X.cpu.gpr.rbx = BitVec.ofNat 64 s) (hs : s < 4096)
    (hB8 : 8 ≤ B.toNat) (hBt : B.toNat + 4144 ≤ 2 ^ 64) (hpt : p.toNat + s + 1 ≤ 2 ^ 64)
    (hpa : p.toNat + s + 1 ≤ B.toNat - 8 ∨ B.toNat + 4144 ≤ p.toNat)
    (hw : ∀ i < s + 1, Foot Wl (Addr.add p i)) (hst : ∀ i < 8, Foot Wl (Addr.add (B - 8) i))
    (hB : ∀ i < 4096, Foot F.data (Addr.add B i)) (hf : ∀ i < 40, Foot F.data (Addr.add (B + 4104#64) i))
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : PcpyAt prof L o 4198592#64 Pm)
    (hPm : Pm (Vst V (B - 8) (toBytesLE (gor_at.add (300 + 5)) 8)))
    (hinr : CodeIn L e' code) (hj : j < code.length) (hra : rdq(V, B + 4136#64) = e'.add j)
    (k : ∀ Z t' W, KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W →
      (∀ i < s, W (p.add i) = V (B.add i)) → W (p.add s) = 0 →
      (∀ a : Addr, (a.toNat < p.toNat ∨ p.toNat + s + 1 ≤ a.toNat) → (a.toNat < B.toNat - 8 ∨ B.toNat ≤ a.toNat) →
        W a = V a) →
      Z.cpu.rip = e'.add j → Z.cpu.gpr.rax = p → Z.cpu.gpr.rsp = B + 4144#64 →
      Z.cpu.gpr.rbx = rdq(V, B + 4104#64) → Z.cpu.gpr.rbp = rdq(V, B + 4112#64) →
      Z.cpu.gpr.r12 = rdq(V, B + 4120#64) → Z.cpu.gpr.r13 = rdq(V, B + 4128#64) →
      Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs64 : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
  have hb8 : (B - 8).toNat = B.toNat - 8 := by bv_omega
  refine (c_283 prof).run c hin _ hK hA hrip (vc_283 (k := s) (by omega) (by rw [hax]; exact hp) hbx) ?_
  rintro j' g₁ fl V' ⟨rfl, hdi, h12, hsi, hdx, hkp, rfl⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg -
  subst hg
  rw [hax] at hdi h12
  rw [hbp] at hsi
  have hsp₄ : Y₄.cpu.gpr.rsp = B := hkp.1.trans hsp
  -- the `call` of `mempcpy`
  refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_300 _) hinc hc0 (by decide) (fun i hi => ?_) ?_
  · rw [hsp₄]
    exact hst i hi
  rintro Y₅ t₅ hK₅ hA₅ ⟨hr₅, hg₅⟩
  rw [hsp₄] at hA₅ hg₅
  have hdi₅ : Y₅.cpu.gpr.rdi = p := by rw [hg₅]; exact hdi
  have hsi₅ : Y₅.cpu.gpr.rsi = B := by rw [hg₅]; exact hsi
  have hdx₅ : Y₅.cpu.gpr.rdx = BitVec.ofNat 64 s := by rw [hg₅]; exact hdx
  have hsp₅ : Y₅.cpu.gpr.rsp = B - 8 := by rw [hg₅]; rfl
  refine hcpy c hK₅ hA₅ hr₅ hPm hin (j := 305) (lt_len (by decide)) ?_ (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi => ?_) (by rw [hsi₅, hdx₅, hs64]; omega) (by rw [hdi₅, hdx₅, hs64]; omega)
    (by rw [hsi₅, hdi₅, hdx₅, hs64]; omega) (by rw [hdi₅, hdx₅, hsp₅, hs64, hb8]; omega) ?_
  · rw [hsp₅, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [hb8]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
    try rfl
  · rw [hsp₅]
    exact c.hws _ (hst i hi)
  · rw [hdx₅, hs64] at hi
    rw [hsi₅]
    exact hB i (by omega)
  · rw [hdx₅, hs64] at hi
    rw [hdi₅]
    exact hw i (by omega)
  intro Z₆ t₆ V₆ hK₆ hA₆ hr₆ hsp₆ hax₆ hbx₆ hbp₆ h12₆ h13₆ h14₆ h15₆ hcp₆ hf₆
  rw [hdi₅, hsi₅, hdx₅, hs64] at hcp₆
  rw [hdi₅, hdx₅, hs64] at hf₆
  rw [hdi₅, hdx₅] at hax₆
  -- the NUL
  refine (c_305 prof).run c hin _ hK₆ hA₆ hr₆ (vc_305 fun i hi => ?_) ?_
  · obtain rfl : i = 0 := by omega
    rw [hax₆, addr_add_zero]
    exact hw s (by omega)
  rintro j' g₇ fl V' ⟨rfl, rfl, rfl⟩ Y₇ t₇ hK₇ hA₇ hr₇ hg₇ -
  have hz : toBytesLE (0#8) 1 = [0#8] := by first | rfl | decide
  rw [hax₆, hz] at hA₇
  have hps : (p + BitVec.ofNat 64 s).toNat = p.toNat + s := by rw [BitVec.toNat_add, hs64]; omega
  have hout : ∀ a : Addr, (a.toNat < p.toNat ∨ p.toNat + s + 1 ≤ a.toNat) →
      (a.toNat < B.toNat - 8 ∨ B.toNat ≤ a.toNat) → Vst V₆ (p + BitVec.ofNat 64 s) [0#8] a = V a := by
    intro a h1 h2
    rw [Tun.Vst_out _ _ _ _ (by simp only [List.length_singleton]; rw [hps]; omega)
        (by simp only [List.length_singleton]; rw [hps]; omega),
      hf₆ a (by omega),
      Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega) (by rw [toBytesLE_length, hb8]; omega)]
  have hrd : ∀ x : Addr, B.toNat + 4104 ≤ x.toNat → x.toNat + 8 ≤ B.toNat + 4144 →
      rdq(Vst V₆ (p + BitVec.ofNat 64 s) [0#8], x) = rdq(V, x) := fun x h1 h2 => by
    rw [map_eq x 8 fun i hi => hout _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)]
  have hsp₇ : Y₇.cpu.gpr.rsp = B := by
    rw [hg₇, hsp₆, hsp₅]
    bv_omega
  refine epi c hin hK₇ hA₇ hr₇ hsp₇ hf hinr hj (by rw [hrd _ (by bv_omega) (by bv_omega)]; exact hra) ?_
  intro Z t' hKZ hAZ hrZ haxZ hspZ hbxZ hbpZ h12Z h13Z h14Z h15Z
  refine k Z t' _ hKZ hAZ (fun i hi => ?_) ?_ hout hrZ ?_ hspZ (hbxZ.trans (hrd _ (by bv_omega) (by bv_omega)))
    (hbpZ.trans (hrd _ (by bv_omega) (by bv_omega))) (h12Z.trans (hrd _ (by bv_omega) (by bv_omega)))
    (h13Z.trans (hrd _ (by bv_omega) (by bv_omega))) ?_ ?_
  · rw [Tun.Vst_out _ _ _ _ (by simp only [List.length_singleton]; rw [hps]; omega)
        (.inl (by simp only [Addr.add]; rw [hps]; bv_omega)),
      hcp₆ i hi,
      Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega)
        (.inr (by rw [toBytesLE_length, hb8]; simp only [Addr.add]; bv_omega))]
  · show Vst V₆ (p + BitVec.ofNat 64 s) [0#8] (p + BitVec.ofNat 64 s) = 0#8
    exact Vst_head _ _ _ _ (by simp only [List.length_nil]; rw [hps]; omega)
  · rw [haxZ, hg₇, h12₆, hg₅]
    exact h12
  · rw [h14Z, hg₇, h14₆, hg₅]
    exact hkp.2.2.1
  · rw [h15Z, hg₇, h15₆, hg₅]
    exact hkp.2.2.2

end FV7z.Gor
