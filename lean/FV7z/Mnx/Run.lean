import FV7z.Mnx.Holds
import FV7z.Mnx.Hand
import FV7z.Mhi.TailN
/-!
# `malloc` after the first call: from 52 to the return address (PLAN.md G3, `malloc`)

- `mal_tail`: as `Mhi.mhi_tailn` (the same code inline in `malloc_hook_ini`): `vc_52m` (`k ≤ 65`) or `vc_52l`
  (`k ≥ 66`), `vc_83`, the `call` of `_int_malloc` (`Im5.SecA`, a hypothesis: the chunk split off the top `T`),
  `vc_114m`, `vc_164r` and the `ret`.
- `mal_next`: from the entry: `vc_0n` (`n ≥ 9`) or `vc_0s` (`n ≤ 8`), the three pushes (`Mal.Vm`, `Vm_out`), then
  `mal_tail` on the bytes after them; the pops read back what the pushes left (`Mal.regs3`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at add_n)
open FV7z.Im2 (VspN VspN_rd V2n V2n_out)
open FV7z.Im5 (ClsA SecA)
open FV7z.Mhi (VspN_hd VspN_far VspN_frm)
namespace FV7z.Mnx
variable {F : Footprint} {Wl : List Rgn}

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `malloc` after the first call, from 52 (the pushes done, `rbx` the tcache index of `nb`, `rbp` = `n`) to the
return address with `T + 16` in `rax`, `n ≤ 4104` (`Im5.ClsA`): as `Mhi.mhi_tailn`. -/
theorem mal_tail {fb S T szw sm C n nb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hcls : ClsA n nb) (hsec : SecA n nb)
    (hrip : X.cpu.rip = mnx_at.add 52) (hbx : X.cpu.gpr.rbx = (nb + 18446744073709551599#64) >>> 4)
    (hbp : X.cpu.gpr.rbp = n)
    (hrsp : X.cpu.gpr.rsp = S + 192#64) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64)
    (hn : ∀ i < 64, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16)
    (hfn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j))
    (h1 : rdd(V, fb + 24#64) = 0#32) (hf1 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i))
    (hgm : rdq(V, 8013224#64) = 128#64) (hfc : rdd(V, 7940680#64) = 0)
    (hfz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 63 →
      rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (hlb : ∀ i, 64 ≤ i → i ≤ 99 →
      rdq(V, BitVec.ofNat 64 (7940768 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 224, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + nb.toNat + 16 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i)) (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : nb.toNat + 32 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 216#64) = e₂.add j₂)
    (k : ∀ (M : Addr → Byte) Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem M →
      (∀ a : Addr, a.toNat < S.toNat + 8 ∨ S.toNat + 192 ≤ a.toNat → M a = VspN T szw nb V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 224#64 ∧ Z.cpu.gpr.rbx = rdq(V, S + 192#64) ∧ Z.cpu.gpr.rbp = rdq(V, S + 200#64) ∧
        Z.cpu.gpr.r12 = rdq(V, S + 208#64)) →
      (Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨kb, hk1, hk2, hnbk⟩ := hcls.cases
  have hnbt := hcls.bnd
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  have htf' : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i) :=
    fun i hi => hWd _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  -- from 83 on, both ways
  suffices K : ∀ (Y₁ : State) (t₁ : Nat), KeptW Wl s₀ Y₁ → Agree F Y₁.proc.mm.mem V → Y₁.cpu.rip = mnx_at.add 83 →
      Y₁.cpu.gpr.rsp = S + 192#64 → Y₁.cpu.gpr.rbp = n → Y₁.cpu.gpr.r13 = X.cpu.gpr.r13 →
      Y₁.cpu.gpr.r14 = X.cpu.gpr.r14 → Y₁.cpu.gpr.r15 = X.cpu.gpr.r15 → GoG prof L o gev gP gE Y₁ t₁ by
    -- 52 → 83: the tcache bin `kb - 2` (`kb ≤ 65`) empty, or none (`kb ≥ 66`)
    by_cases h65 : kb ≤ 65
    · refine (c_52 prof fb).run c hfs hin _ hK hA hrip
        (vc_52m hk1 h65 (by rw [hbx, hnbk]) htb htc hC hn htf' htf hfn) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hv₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      rw [hv₁] at hA₁
      exact K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact hrsp) (by rw [hg₁]; exact hbp) (by rw [hg₁]) (by rw [hg₁])
        (by rw [hg₁])
    · refine (c_52 prof fb).run c hfs hin _ hK hA hrip
        (vc_52l (by omega) hk2 (by rw [hbx, hnbk]) htb htc hC htf' htf) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hv₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      rw [hv₁] at hA₁
      exact K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact hrsp) (by rw [hg₁]; exact hbp) (by rw [hg₁]) (by rw [hg₁])
        (by rw [hg₁])
  intro Y₁ t₁ hK₁ hA₁ hr₁ sp₁ bp₁ h13₁ h14₁ h15₁
  -- 83 → 109
  refine (c_83 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ (vc_83 h1 hf1) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hv₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  rw [hv₂] at hA₂
  have esp : Y₂.cpu.gpr.rsp = S + 192#64 := by rw [hg₂]; exact sp₁
  have e184 : S + 192#64 - 8 = S + 184#64 := by bv_omega
  -- the call
  refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_109 _) hinI (Imm.lt_len (j := 0) (by decide)) tgt_109
    (by rw [esp, e184]; exact off_ft hsw 184 rfl (by decide)) ?_
  rintro Z₀ t₀ hK₀ hA₀ ⟨hr₀, hg₀⟩
  rw [esp, e184] at hA₀
  -- `_int_malloc`
  have l8 : (toBytesLE (mnx_at.add (109 + 5)) 8).length = 8 := toBytesLE_length _ _
  have s184 : (S + 184#64).toNat = S.toNat + 184 := add_n _ _ (by omega)
  have P : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ S.toNat →
      List.map (Vst V (S + 184#64) (toBytesLE (mnx_at.add (109 + 5)) 8)) (byteAddrs x m) =
        List.map V (byteAddrs x m) := fun x m h =>
    rd_Vst _ _ _ _ _ (by rw [l8, s184]; omega) (by omega) (.inr (by rw [s184]; omega))
  have q : ∀ x : Addr, x.toNat + 8 ≤ S.toNat → rdq(Vst V (S + 184#64) (toBytesLE (mnx_at.add (109 + 5)) 8), x) =
      rdq(V, x) := fun x h => congrArg (ofBytesLE 64) (P x 8 h)
  have d : ∀ x : Addr, x.toNat + 4 ≤ S.toNat → rdd(Vst V (S + 184#64) (toBytesLE (mnx_at.add (109 + 5)) 8), x) =
      rdd(V, x) := fun x h => congrArg (ofBytesLE 32) (P x 4 h)
  have n8 : ∀ (x : Nat), x + 8 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 8 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have n4 : ∀ (x : Nat), x + 4 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 4 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have hT8 : (T + 8#64).toNat + 8 ≤ S.toNat := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  unfold SecA at hsec
  refine hsec (S := S) (T := T) (szw := szw) (sm := sm) c hfs hinI hK₀ hA₀ hr₀
    (by rw [hg₀]; show Y₂.cpu.gpr.rsp - 8 = _; rw [esp, e184])
    (by rw [hg₀, hg₂]; show Y₁.cpu.gpr.rbp = _; exact bp₁)
    (by rw [hg₀, hg₂]; rfl) hS hlo hfb
    (by rw [q _ (n8 _ (by omega))]; exact hgm) (by rw [d _ (n4 _ (by omega))]; exact hfc)
    (fun k hk => by rw [q _ (n8 _ (by omega))]; exact hfz k hk)
    (fun i i1 i2 => by rw [q _ (n8 _ (by omega))]; exact hbk i i1 i2)
    (fun i i1 i2 => by rw [q _ (n8 _ (by omega))]; exact hlb i i1 i2)
    (by rw [q _ hfb, htc]; exact hC)
    (by rw [q _ (n8 _ (by omega))]; exact htb) (by rw [q _ (n8 _ (by omega))]; exact hun)
    (by rw [d _ (n4 _ (by omega))]; exact hm0) (by rw [d _ (n4 _ (by omega))]; exact hm1)
    (by rw [d _ (n4 _ (by omega))]; exact hm2) (by rw [d _ (n4 _ (by omega))]; exact hm3)
    hW hgf htf (fun i hi => hsw i (by omega)) hT hTS htw hrw hpb
    (by rw [d _ (n4 _ (by omega))]; exact hp0)
    (by rw [q _ (n8 _ (by omega))]; exact htop) (by rw [q _ hT8]; exact hsz)
    (by rw [q _ (n8 _ (by omega))]; exact hsm) hle hge
    hin (lt_len (j := 109 + 5) (by decide)) (by
      rw [rd_Vst_self _ _ _ l8 (by rw [s184]; omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  rintro M Z₁ t₃ hfr hK₃ hA₃ hr₃ hax₃ ⟨sp₃, bx₃, bp₃, r12₃, r13₃, r14₃, r15₃⟩
  have hT' : T.toNat + nb.toNat + 16 < 2 ^ 64 := by omega
  -- the bytes above the frame
  have FAR : ∀ (x : Addr) (m : Nat), S.toNat + 192 ≤ x.toNat → x.toNat + m ≤ 2 ^ 64 →
      List.map (VspN T szw nb M) (byteAddrs x m) = List.map V (byteAddrs x m) := fun x m h1 h2 => by
    rw [← VspN_rd (T := T) (szw := szw) (nb := nb) V hT' h2 (.inr (by omega)) (.inr (by omega)) (by omega)]
    exact rd_eq h2 fun a ha _ => VspN_frm l8 hS hfr (.inr (by omega))
  -- 114 → 164
  have e8 : T + 16#64 + 18446744073709551608#64 = T + 8#64 := by bv_omega
  have hT0 : T + 16#64 ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    simp at this
    omega
  refine (c_114 prof fb).run c hfs hin _ hK₃ hA₃ (by rw [hr₃])
    (vc_114m hk1 (by omega) (by rw [hax₃]; exact hT0) (by rw [hax₃, e8, ← hnbk]; exact VspN_hd _ hT' (by omega))
      (by rw [hax₃, e8]; exact fun i hi => c.hws _ (htw i hi))) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hv₄⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  rw [hv₄] at hA₄
  have sp₄ : Y₄.cpu.gpr.rsp = S + 192#64 := by rw [hg₄]; exact sp₃
  -- 164 → 171
  refine (c_164 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
    (vc_164r (by rw [sp₄]; exact fun i hi => c.hws _ (off_ft hsw 192 rfl (by decide) i hi))) ?_
  rintro j' g fl V₅ ⟨rfl, hv₅, ax₅, sp₅, bx₅, bp₅, r12₅, r13₅, r14₅, r15₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  subst hg₅
  rw [hv₅] at hA₅
  have e216 : S + 192#64 + 8 + 8 + 8 = S + 216#64 := by bv_omega
  have e200 : S + 192#64 + 8 = S + 200#64 := by bv_omega
  have e208 : S + 192#64 + 8 + 8 = S + 208#64 := by bv_omega
  rw [sp₄] at sp₅ bx₅ bp₅ r12₅
  rw [e216] at sp₅
  rw [e200] at bp₅
  rw [e208] at r12₅
  have a192 : (S + 192#64).toNat = S.toNat + 192 := add_n _ _ (by omega)
  have a200 : (S + 200#64).toNat = S.toNat + 200 := add_n _ _ (by omega)
  have a208 : (S + 208#64).toNat = S.toNat + 208 := add_n _ _ (by omega)
  have a216 : (S + 216#64).toNat = S.toNat + 216 := add_n _ _ (by omega)
  -- the `ret`
  refine c.s_ret hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ret_171 _)
    (by rw [sp₅]; exact fun i hi => c.hws _ (off_ft hsw 216 rfl (by decide) i hi)) hin₂ h₂
    (by rw [sp₅, FAR _ _ (by omega) (by omega)]; exact hra) ?_
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k _ Z t' hK' hA' (fun a ha => VspN_frm l8 hS hfr ha) hr'
    (by rw [hg']; exact ax₅.trans (by rw [hg₄]; exact hax₃))
    ⟨by rw [hg']; show Y₅.cpu.gpr.rsp + 8 = _; rw [sp₅]; bv_omega, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_⟩
  · rw [hg']
    exact bx₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))
  · rw [hg']
    exact bp₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))
  · rw [hg']
    exact r12₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))
  · rw [hg']
    show Y₅.cpu.gpr.r13 = _
    rw [r13₅, hg₄]
    show Z₁.cpu.gpr.r13 = _
    rw [r13₃, hg₀]
    show Y₂.cpu.gpr.r13 = _
    rw [hg₂]
    exact h13₁
  · rw [hg']
    show Y₅.cpu.gpr.r14 = _
    rw [r14₅, hg₄]
    show Z₁.cpu.gpr.r14 = _
    rw [r14₃, hg₀]
    show Y₂.cpu.gpr.r14 = _
    rw [hg₂]
    exact h14₁
  · rw [hg']
    show Y₅.cpu.gpr.r15 = _
    rw [r15₅, hg₄]
    show Z₁.cpu.gpr.r15 = _
    rw [r15₃, hg₀]
    show Y₂.cpu.gpr.r15 = _
    rw [hg₂]
    exact h15₁

/-- The bytes after the three pushes from `S + 216`: below `S + 192` and from `S + 216` on, the entry's. -/
theorem Vm_out {g : Gprs} {S : Addr} (V : Addr → Byte) (hsp : g.rsp = S + 216#64) (hS : S.toNat + 256 < 2 ^ 64)
    {a : Addr} (ha : a.toNat < S.toNat + 192 ∨ S.toNat + 216 ≤ a.toNat) : Mal.Vm g V a = V a := by
  have e1 : (g.rsp - 8).toNat = S.toNat + 208 := by rw [hsp]; bv_omega
  have e2 : (g.rsp - 8 - 8).toNat = S.toNat + 200 := by rw [hsp]; bv_omega
  have e3 : (g.rsp - 8 - 8 - 8).toNat = S.toNat + 192 := by rw [hsp]; bv_omega
  unfold Mal.Vm
  rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, e3]; omega) (by rw [toBytesLE_length, e3]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e2]; omega) (by rw [toBytesLE_length, e2]; omega),
    Vst_out _ _ _ _ (by rw [toBytesLE_length, e1]; omega) (by rw [toBytesLE_length, e1]; omega)]

theorem s192 (S : Addr) : S + 216#64 - 8 - 8 - 8 = S + 192#64 := by bv_omega
theorem s200 (S : Addr) : S + 216#64 - 8 - 8 - 8 + 8 = S + 200#64 := by bv_omega
theorem s208 (S : Addr) : S + 216#64 - 8 - 8 - 8 + 8 + 8 = S + 208#64 := by bv_omega

/-- `malloc (n)` after the first call (`__malloc_hook` null, the tcache `C` made and its bins empty, one thread), from
its entry (`rsp = S + 216`) to the return address: the chunk `T + 16` split off the top `T` (`VspN`), the registers a
call keeps as at the entry. -/
theorem mal_next {fb S T szw sm C n nb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mnx_at mnx) (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hcls : ClsA n nb) (hsec : SecA n nb) (hrip : X.cpu.rip = mnx_at) (hdi : X.cpu.gpr.rdi = n)
    (hrsp : X.cpu.gpr.rsp = S + 216#64) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat) (hf24 : (fb + 24#64).toNat + 4 ≤ S.toNat)
    (hhk : rdq(V, 7940656#64) = 0#64) (hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i))
    (htc : rdq(V, fb + 18446744073709551576#64) = C) (hC : C ≠ 0#64) (hCS : C.toNat + 128 ≤ S.toNat)
    (hn : ∀ i < 64, ofBytesLE 16 ((byteAddrs (C + BitVec.ofNat 64 (2 * i)) 2).map V) = 0#16)
    (hfn : ∀ i < 64, ∀ j < 2, Foot F.data (Addr.add (C + BitVec.ofNat 64 (2 * i)) j))
    (h1 : rdd(V, fb + 24#64) = 0#32) (hf1 : ∀ i < 4, Foot F.data (Addr.add (fb + 24#64) i))
    (hgm : rdq(V, 8013224#64) = 128#64) (hfc : rdd(V, 7940680#64) = 0)
    (hfz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 63 →
      rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (hlb : ∀ i, 64 ≤ i → i ≤ 99 →
      rdq(V, BitVec.ofNat 64 (7940768 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 224, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + nb.toNat + 16 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i)) (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : nb.toNat + 32 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 216#64) = e₂.add j₂)
    (k : ∀ (M : Addr → Byte) Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem M →
      (∀ a : Addr, a.toNat < S.toNat + 8 ∨ S.toNat + 216 ≤ a.toNat → M a = VspN T szw nb V a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = T + 16#64 → Z.cpu.gpr.rsp = S + 224#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hR := X.cpu.gpr.rsp.isLt
  have hspn : X.cpu.gpr.rsp.toNat = S.toNat + 216 := by rw [hrsp, add_n _ _ (by omega)]
  have hst : ∀ i < 24, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => by
    have e : Addr.add (X.cpu.gpr.rsp - 24) i = Addr.add S (192 + i) := by rw [hrsp]; simp only [Addr.add]; bv_omega
    rw [e]
    exact hsw _ (by omega)
  have hsp' : 7940664 + 8 ≤ X.cpu.gpr.rsp.toNat := by omega
  have e192 : X.cpu.gpr.rsp - 8 - 8 - 8 = S + 192#64 := by rw [hrsp]; exact s192 S
  -- 52 on, the pushes done
  suffices K : ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Mal.Vm X.cpu.gpr V) →
      Y.cpu.rip = mnx_at.add 52 → Y.cpu.gpr.rsp = S + 192#64 →
      Y.cpu.gpr.rbx = (nb + 18446744073709551599#64) >>> 4 → Y.cpu.gpr.rbp = n →
      Y.cpu.gpr.r13 = X.cpu.gpr.r13 → Y.cpu.gpr.r14 = X.cpu.gpr.r14 → Y.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o gev gP gE Y t₁ by
    rcases hcls with (⟨h9, h10, h11⟩ | ⟨h8, h32⟩) | ⟨h9, h10, h11⟩
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
        (vc_0n hdi h9 (by omega) hhk hfh hsp' hst) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      refine K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact e192) ?_ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
        (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      rw [hg₁]
      show ((n + 23#64 &&& 18446744073709551600#64) + 18446744073709551599#64) >>> 4 = _
      rw [h11]
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
        (vc_0s hdi h8 hhk hfh hsp' hst) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      refine K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact e192) ?_ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
        (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      rw [hg₁, h32] <;> rfl
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [addr_add_zero]; exact hrip)
        (vc_0n hdi (by omega) h10 hhk hfh hsp' hst) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      refine K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact e192) ?_ (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
        (by rw [hg₁] <;> rfl) (by rw [hg₁] <;> rfl)
      rw [hg₁]
      show ((n + 23#64 &&& 18446744073709551600#64) + 18446744073709551599#64) >>> 4 = _
      rw [h11]
  intro Y t₁ hKY hAY hrY hspY hbxY hbpY h13 h14 h15
  -- what the tail reads, below the pushes, is the entry's
  have O : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ S.toNat + 192 →
      List.map (Mal.Vm X.cpu.gpr V) (byteAddrs x m) = List.map V (byteAddrs x m) := fun x m h =>
    rd_eq (by omega) fun a _ h2 => Vm_out V hrsp hS (.inl (by omega))
  have q : ∀ x : Addr, x.toNat + 8 ≤ S.toNat → rdq(Mal.Vm X.cpu.gpr V, x) = rdq(V, x) := fun x h =>
    congrArg (ofBytesLE 64) (O x 8 (by omega))
  have d : ∀ x : Addr, x.toNat + 4 ≤ S.toNat → rdd(Mal.Vm X.cpu.gpr V, x) = rdd(V, x) := fun x h =>
    congrArg (ofBytesLE 32) (O x 4 (by omega))
  have n8 : ∀ (x : Nat), x + 8 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 8 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have n4 : ∀ (x : Nat), x + 4 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 4 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have hT8 : (T + 8#64).toNat + 8 ≤ S.toNat := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hra' : rdq(Mal.Vm X.cpu.gpr V, S + 216#64) = e₂.add j₂ := by
    rw [← hra]
    exact congrArg (ofBytesLE 64) (rd_eq (by rw [add_n _ _ (by omega)]; omega)
      fun a h1 _ => Vm_out V hrsp hS (.inr (by rw [add_n _ _ (by omega)] at h1; omega)))
  refine mal_tail (S := S) (T := T) (szw := szw) (sm := sm) (C := C) (n := n) (nb := nb) c hfs hin hinI hKY hAY
    hcls hsec hrY hbxY hbpY hspY hS hlo hfb (by rw [q _ hfb]; exact htc) hC
    (fun i hi => by
      rw [O _ _ (by rw [add_n _ _ (by omega)]; omega)]
      exact hn i hi) hfn
    (by rw [d _ hf24]; exact h1) hf1
    (by rw [q _ (n8 _ (by omega))]; exact hgm) (by rw [d _ (n4 _ (by omega))]; exact hfc)
    (fun k hk => by rw [q _ (n8 _ (by omega))]; exact hfz k hk)
    (fun i i1 i2 => by rw [q _ (n8 _ (by omega))]; exact hbk i i1 i2)
    (fun i i1 i2 => by rw [q _ (n8 _ (by omega))]; exact hlb i i1 i2)
    (by rw [q _ (n8 _ (by omega))]; exact htb) (by rw [q _ (n8 _ (by omega))]; exact hun)
    (by rw [d _ (n4 _ (by omega))]; exact hm0) (by rw [d _ (n4 _ (by omega))]; exact hm1)
    (by rw [d _ (n4 _ (by omega))]; exact hm2) (by rw [d _ (n4 _ (by omega))]; exact hm3)
    hW hgf htf hsw hT hTS htw hrw hpb (by rw [d _ (n4 _ (by omega))]; exact hp0)
    (by rw [q _ (n8 _ (by omega))]; exact htop) (by rw [q _ hT8]; exact hsz)
    (by rw [q _ (n8 _ (by omega))]; exact hsm) hle hge hin₂ h₂ hra' ?_
  intro M Z t' hKZ hAZ hM hrZ haxZ ⟨spZ, bxZ, bpZ, r12Z⟩ ⟨r13Z, r14Z, r15Z⟩
  obtain ⟨b1, b2, b3, -, -⟩ := Mal.regs3 X.cpu.gpr V (by omega) (by omega)
  rw [hrsp, s192] at b1
  rw [hrsp, s200] at b2
  rw [hrsp, s208] at b3
  refine k M Z t' hKZ hAZ (fun a ha => ?_) hrZ haxZ spZ (bxZ.trans b1) (bpZ.trans b2) (r12Z.trans b3)
    (r13Z.trans h13) (r14Z.trans h14) (r15Z.trans h15)
  rw [hM a (by omega)]
  unfold VspN
  exact Mhi.vst_eq _ _ _ _ _ (Mhi.vst_eq _ _ _ _ _ (Mhi.vst_eq _ _ _ _ _ (Vm_out V hrsp hS (by omega))))

end FV7z.Mnx
