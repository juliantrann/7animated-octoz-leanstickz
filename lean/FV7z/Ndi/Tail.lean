import FV7z.Ndi.Body
import FV7z.Ndi.Loop
import FV7z.Dpr.Holds
/-!
# `_dl_non_dynamic_init`: `_dl_protect_relro` and the return (PLAN.md G3, startup)

- `tail`: from the `call` of `_dl_protect_relro` (2879) to the caller — the RELRO pages become read-only (the event
  `mprotect (0x777000, 0x1b000, PROT_READ)`, the footprint `G` from then on), the epilogue pops the five registers
  the prologue pushed, `ret`.
- `ndi_c`: from the return of `_dl_init_paths` (2063) to the caller: `body_a`, `body_b`, `tail`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
namespace FV7z.Ndi

theorem t16 (sp : BitVec 64) (h : 16 ≤ sp.toNat) : (sp - 8#64 - 8#64).toNat = sp.toNat - 16 := by bv_omega
theorem t24 (sp : BitVec 64) : sp - 8#64 - 16#64 = sp - 24#64 := by bv_omega
theorem t24n (sp : BitVec 64) (h : 24 ≤ sp.toNat) : (sp - 8#64 - 16#64).toNat = sp.toNat - 24 := by bv_omega
theorem a24 (sp : BitVec 64) (i : Nat) : Addr.add (sp - 72#64) (48 + i) = Addr.add (sp - 24#64) i := by
  simp only [Addr.add]
  bv_omega
theorem a120 (sp : BitVec 64) (i : Nat) : Addr.add (sp + 80#64) (40 + i) = Addr.add (sp + 120#64) i := by
  simp only [Addr.add]
  bv_omega
theorem u128 (sp : BitVec 64) : sp + 120#64 + 8#64 = sp + 128#64 := by bv_omega
theorem tp (sp : BitVec 64) (k : Nat) (h : sp.toNat + k < 2 ^ 64) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
  bv_omega

/-- What a load of 8 bytes at `sp + k` reads: the bytes there are `V`'s. -/
theorem stk_rd {sp : Addr} {V M W : Addr → Byte} (h72 : 8032256 + 72 ≤ sp.toNat) (hM : Eqo sp W M) (hG : Gk V M)
    (k : Nat) (hf : sp.toNat + k + 8 ≤ 2 ^ 64) : rdq(W, sp + BitVec.ofNat 64 k) = rdq(V, sp + BitVec.ofNat 64 k) := by
  have e := tp sp k (by omega)
  rw [hM.rd (scr_out (by omega) (.inr (by omega))), hG.rd _ 8 (by omega) fun i hi => Bool.eq_false_iff.2 fun h' => by
    have := nv_data h'
    omega]

theorem lV_ra (M : Addr → Byte) : rdq(lV M, 7944520#64) = 7829360#64 := by
  unfold lV
  rw [vr (toBytesLE_length _ _) (by decide) (by decide) (by decide), vs (toBytesLE_length _ _) (by decide)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

theorem lV_rs (M : Addr → Byte) : rdq(lV M, 7944528#64) = 108688#64 := by
  unfold lV
  rw [vs (toBytesLE_length _ _) (by decide)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

/-- The event of the body: `mprotect (0x777000, 0x1b000, PROT_READ)`, answered 0. -/
abbrev ndiEv : Event := ⟨10, [7827456#64, 110592#64, 1#64, 108688#64, 1#64, 6#64], 0, [], []⟩

theorem tail {lim : Nat} {b fsb : Addr} {ks : Kst} {G : Footprint} {Wl' : List Rgn} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat} {V M W : Addr → Byte} {sp : Addr}
    (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks) (hin : CodeIn L ndi_at ndi)
    (hid : CodeIn L Dpr.dpr_at Dpr.dpr) (him : CodeIn L Mpr.mpr_at Mpr.mpr)
    (h72 : 8032256 + 72 ≤ sp.toNat) (hsn : sp.toNat + 128 ≤ 2 ^ 64)
    (hstk : ∀ i < 72, Foot Wl (Addr.add (sp - 72#64) i))
    (hr : ∀ x : Addr, 7827456 ≤ x.toNat → x.toNat < 8032256 → Foot F.data x)
    (hps : rdq(V, 7943128#64) = 4096#64) (hla : rdq(V, 7943392#64) = 0#64)
    (hra : rdq(M, 7944520#64) = 7829360#64) (hrs : rdq(M, 7944528#64) = 108688#64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hmap : ∀ i < 27, ∃ m, s₀.proc.mm.mem.mapAt (0x777 + i) = some m ∧ m.special = false)
    (hGo : G.own = []) (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages 0x777 27 (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hlG : ∀ i < 24, Foot G.data (Addr.add (sp - 24#64) i))
    (hl : ∀ i < 48, Foot G.data (Addr.add (sp + 80#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(V, sp + 120#64) = e₂.add j₂)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hM : Eqo sp W M) (hG : Gk V M)
    (hrip : X.cpu.rip = ndi_at.add 2879) (hsp : X.cpu.gpr.rsp = sp) (hdi : X.cpu.gpr.rdi = 7943392#64)
    (h10 : X.cpu.gpr.r10 = 108688#64) (h8 : X.cpu.gpr.r8 = 1#64) (h9 : X.cpu.gpr.r9 = 6#64)
    (k : ∀ s₁ Z t' W', Seg prof G Wl' L s₁ o → Base s₁ lim b fsb ks → KeptW Wl' s₁ Z →
      Agree G Z.proc.mm.mem W' → Eqo sp W' M → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp + 128#64 →
      Z.cpu.gpr.rbx = rdq(V, sp + 80#64) → Z.cpu.gpr.rbp = rdq(V, sp + 88#64) →
      Z.cpu.gpr.r12 = rdq(V, sp + 96#64) → Z.cpu.gpr.r13 = rdq(V, sp + 104#64) →
      Z.cpu.gpr.r14 = rdq(V, sp + 112#64) → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [ndiEv]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hlt := sp.isLt
  have e8 := t8 sp (by omega)
  have hw8 := w8 hstk
  -- the `call`
  refine c.s_call hK hA hin (lt_len (by decide)) hrip (call_2879 _) hid (Dpr.lt_len (by decide)) (by decide)
    (fun i hi => by rw [hsp]; exact hw8 i hi) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  rw [hsp] at hAY hgY
  replace hAY : Agree F Y.proc.mm.mem (Vst W (sp - 8#64) (toBytesLE (ndi_at.add (2879 + 5)) 8)) := hAY
  have hspY : Y.cpu.gpr.rsp = sp - 8#64 := by rw [hgY]; rfl
  have M₁ : Eqo sp (Vst W (sp - 8#64) (toBytesLE (ndi_at.add (2879 + 5)) 8)) M :=
    hM.push (by omega) (by rw [toBytesLE_length]; omega)
  have ev : Dpr.dprEv Y.cpu.gpr = ndiEv := by
    have : Dpr.dprEv Y.cpu.gpr =
        ⟨10, [7827456#64, 110592#64, 1#64, X.cpu.gpr.r10, X.cpu.gpr.r8, X.cpu.gpr.r9], 0, [], []⟩ := by
      rw [hgY]
      rfl
    rw [this, h10, h8, h9]
  have h15Y : Y.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hgY]; rfl
  -- `_dl_protect_relro`
  refine Dpr.dpr_ok (G := G) (Wl' := Wl') c hB hid him hKY hAY hrY (by rw [hgY]; exact hdi)
    (fun i hi => by
      rw [hspY, t24]
      have := hstk (48 + i) (by omega)
      rwa [a24 sp i] at this)
    (by rw [hspY, e8]; omega) (by rw [hspY, e8]; omega)
    (rf hr (by decide) _ 8 (by decide)) (rf hr (by decide) _ 8 (by decide)) (rf hr (by decide) _ 8 (by decide))
    (rf hr (by decide) _ 8 (by decide))
    (by rw [M₁.rdi h72 _ 8 (by decide), hG.rd _ 8 (by decide) (by decide)]; exact hps)
    (by rw [M₁.rdi h72 _ 8 (by decide), hG.rd _ 8 (by decide) (by decide)]; exact hla)
    (by rw [M₁.rdi h72 _ 8 (by decide)]; exact hra) (by rw [M₁.rdi h72 _ 8 (by decide)]; exact hrs)
    hmg hmap hGo hGc hfit hGw hGr hcode hww (fun i hi => by rw [hspY, t24]; exact hlG i hi) hin
    (lt_len (j := 2879 + 5) (by decide)) ?_ ?_
  · rw [hspY, vs (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _
  intro rc r11 s₁ Z t₂ c₁ hB₁ hKZ hAZ hrZ hgZ
  rw [ev]
  have hspZ : Z.cpu.gpr.rsp = sp := by
    rw [hgZ]
    show Y.cpu.gpr.rsp + 8#64 = sp
    rw [hspY]
    exact u8 sp
  have h15Z : Z.cpu.gpr.r15 = X.cpu.gpr.r15 := by rw [hgZ]; exact h15Y
  have M₂ : Eqo sp (Dpr.DprMem (Vst W (sp - 8#64) (toBytesLE (ndi_at.add (2879 + 5)) 8)) Y.cpu.gpr) M := by
    unfold Dpr.DprMem
    rw [hspY]
    have e16 := t16 sp (by omega)
    have e24 := t24n sp (by omega)
    exact (M₁.push (x := sp - 8#64 - 8#64) (by omega) (by rw [toBytesLE_length]; omega)).push
      (by omega) (by rw [toBytesLE_length]; omega)
  clear hgZ hgY hKY hAY hrY M₁ hK hA hrip
  -- the epilogue
  refine (c_2884 prof).run c₁ hin _ hKZ hAZ hrZ (vc_2884 (by rw [hspZ]; exact fun i hi => hl i (by omega))) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, rfl⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  rw [hspZ] at hg₃
  have hsp₃ : Y₃.cpu.gpr.rsp = sp + 120#64 := by rw [hg₃]
  -- `ret`
  refine c₁.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_2896 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₃]
    have := hl (40 + i) (by omega)
    rwa [a120 sp i] at this
  · rw [hsp₃]
    exact (stk_rd h72 M₂ hG 120 (by omega)).trans hret
  rintro Z₂ t' hKZ₂ hAZ₂ ⟨hrZ₂, hgZ₂⟩
  refine k s₁ Z₂ t' _ c₁ hB₁ hKZ₂ hAZ₂ M₂ hrZ₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hgZ₂]
    show Y₃.cpu.gpr.rsp + 8#64 = _
    rw [hsp₃]
    exact u128 sp
  · rw [hgZ₂]
    show Y₃.cpu.gpr.rbx = _
    rw [hg₃]
    exact stk_rd h72 M₂ hG 80 (by omega)
  · rw [hgZ₂]
    show Y₃.cpu.gpr.rbp = _
    rw [hg₃]
    exact stk_rd h72 M₂ hG 88 (by omega)
  · rw [hgZ₂]
    show Y₃.cpu.gpr.r12 = _
    rw [hg₃]
    exact stk_rd h72 M₂ hG 96 (by omega)
  · rw [hgZ₂]
    show Y₃.cpu.gpr.r13 = _
    rw [hg₃]
    exact stk_rd h72 M₂ hG 104 (by omega)
  · rw [hgZ₂]
    show Y₃.cpu.gpr.r14 = _
    rw [hg₃]
    exact stk_rd h72 M₂ hG 112 (by omega)
  · rw [hgZ₂]
    show Y₃.cpu.gpr.r15 = _
    rw [hg₃]
    exact h15Z
/-- From the return of `_dl_init_paths` (2063) to the caller, with no `LD_*` in the environment, not a secure exec
and the program headers of `7zzs`: the bytes are `lV (bV V n)` outside the 72 below `sp`, the registers the prologue
pushed are popped, the RELRO pages are read-only. -/
theorem ndi_c {lim : Nat} {b fsb : Addr} {ks : Kst} {G : Footprint} {Wl' : List Rgn} {e₂ : Addr}
    {code₂ : List Byte} {j₂ : Nat} {pl pc : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {V W : Addr → Byte}
    {sp p : Addr} {n : Nat} (c : Seg prof F Wl L s₀ o) (hB : Base s₀ lim b fsb ks)
    (cx : Cx prof F Wl L o pl pc Pm E V sp) (hpl : Pl V F sp p n) (hsec : rdd(V, 7937248#64) = 0#32)
    (hid : CodeIn L Dpr.dpr_at Dpr.dpr) (him : CodeIn L Mpr.mpr_at Mpr.mpr)
    (hfp : ∀ x : Addr, 4194368 ≤ x.toNat → x.toNat < 4194816 → Foot F.data x) (hph : Ph V)
    (hd1 : rdq(V, 8029568#64) = 4194368#64) (hd2 : rdq(V, 8029592#64) = 8#64) (hsn : sp.toNat + 128 ≤ 2 ^ 64)
    (hps : rdq(V, 7943128#64) = 4096#64) (hla : rdq(V, 7943392#64) = 0#64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hmap : ∀ i < 27, ∃ m, s₀.proc.mm.mem.mapAt (0x777 + i) = some m ∧ m.special = false)
    (hGo : G.own = []) (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot F.writes a ∧ inPages 0x777 27 (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot F.writes a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hlG : ∀ i < 24, Foot G.data (Addr.add (sp - 24#64) i))
    (hl : ∀ i < 48, Foot G.data (Addr.add (sp + 80#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(V, sp + 120#64) = e₂.add j₂)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hM : Eqo sp W V)
    (hrip : X.cpu.rip = ndi_at.add 2063) (hsp : X.cpu.gpr.rsp = sp)
    (k : ∀ s₁ Z t' W', Seg prof G Wl' L s₁ o → Base s₁ lim b fsb ks → KeptW Wl' s₁ Z →
      Agree G Z.proc.mm.mem W' → Eqo sp W' (lV (bV V n)) → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp + 128#64 →
      Z.cpu.gpr.rbx = rdq(V, sp + 80#64) → Z.cpu.gpr.rbp = rdq(V, sp + 88#64) →
      Z.cpu.gpr.r12 = rdq(V, sp + 96#64) → Z.cpu.gpr.r13 = rdq(V, sp + 104#64) →
      Z.cpu.gpr.r14 = rdq(V, sp + 112#64) → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [ndiEv]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine body_a c cx hpl hsec hK hA hM hrip hsp ?_
  intro Z₁ t₁ W₁ hK₁ hA₁ hM₁ hr₁ hsp₁ h15₁
  refine body_b c cx.hin cx.h72 cx.hr cx.hw hfp hph hd1 hd2 hK₁ hA₁ hM₁ (bV_gk V n) hr₁ hsp₁ ?_
  intro Z₂ t₂ W₂ hK₂ hA₂ hM₂ hr₂ hsp₂ h15₂ hdi h10 h8 h9
  refine tail c hB cx.hin hid him cx.h72 hsn cx.hstk cx.hr hps hla (lV_ra _) (lV_rs _) hmg hmap hGo hGc hfit hGw hGr
    hcode hww hlG hl hin₂ h₂ hret hK₂ hA₂ hM₂ (lV_gk (bV_gk V n)) hr₂ hsp₂ hdi h10 h8 h9 ?_
  intro s₁ Z t' W' c₁ hB₁ hKZ hAZ hMZ hrZ hspZ hbx hbp h12 h13 h14 h15
  exact k s₁ Z t' W' c₁ hB₁ hKZ hAZ hMZ hrZ hspZ hbx hbp h12 h13 h14 (by rw [h15, h15₂, h15₁])
end FV7z.Ndi
