import FV7z.Mhi.Tail
import FV7z.Mhi.HoldsM
import FV7z.Im5.RunA
/-!
# `malloc_hook_ini`: from the return of `tcache_init` to the return address, `n ≤ 4104` (PLAN.md G3, `malloc`)

- `VspN_hd`, `VspN_far`, `VspN_frm`: the size word after the split; the bytes outside the frame of `_int_malloc`
  (`VspN_frm` through its frame `Im2.Fr`).
- `mhi_tailn`: `vc_236m` (`k ≤ 65`) or `vc_236l` (`k ≥ 66`, no tcache bin), `vc_99`, the `call` of `_int_malloc`
  (`Im5.im_secondA`), `vc_130m`, `vc_180` and the `ret`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at add_n)
open FV7z.Im2 (VspN VspN_rd V2n V2n_out)
open FV7z.Im5 (ClsA im_secondA)
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

/-- The chunk's size word after the split: `nb ||| 1`. -/
theorem VspN_hd {T szw nb : Addr} (V : Addr → Byte) (hT : T.toNat + nb.toNat + 16 < 2 ^ 64) (h8 : 8 ≤ nb.toNat) :
    rdq(VspN T szw nb V, T + 8#64) = nb ||| 1#64 := by
  have e8 : (T + 8#64).toNat = T.toNat + 8 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e72 : (T + nb + 8#64).toNat = T.toNat + nb.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  unfold VspN
  rw [rd_Vst _ _ _ _ _ (by rw [l, e72]; omega) (by omega) (by rw [l, e72]; omega),
    rd_Vst_self _ _ _ (l _) (by omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- Outside the frame of `_int_malloc`, the bytes after the second call are those of the split on the bytes
before. -/
theorem VspN_far {S T szw nb : Addr} (g : Gprs) (n : Addr) (V : Addr → Byte) (r : List Byte) (hr : r.length = 8)
    (hS : S.toNat + 256 < 2 ^ 64) {a : Addr} (ha : a.toNat < S.toNat + 8 ∨ S.toNat + 192 ≤ a.toNat) :
    VspN T szw nb (V2n S g n nb (Vst V (S + 184#64) r)) a = VspN T szw nb V a := by
  have e : V2n S g n nb (Vst V (S + 184#64) r) a = V a := by
    rw [V2n_out S g n nb _ hS (by omega), Vst_out _ _ _ _ (by rw [hr, add_n _ _ (by omega)]; omega)
      (by rw [hr, add_n _ _ (by omega)]; omega)]
  unfold VspN
  exact vst_eq _ _ _ _ _ (vst_eq _ _ _ _ _ (vst_eq _ _ _ _ _ e))

/-- Outside the frame of `_int_malloc` (and its return address), the bytes after the second call are those of the
split on the bytes before: the frame `Im2.Fr` of the call. -/
theorem VspN_frm {S T szw nb : Addr} {g : Gprs} {V M : Addr → Byte} {r : List Byte} (hr : r.length = 8)
    (hS : S.toNat + 256 < 2 ^ 64) (hfr : Im2.Fr S g (Vst V (S + 184#64) r) M) {a : Addr}
    (ha : a.toNat < S.toNat + 8 ∨ S.toNat + 192 ≤ a.toNat) :
    VspN T szw nb M a = VspN T szw nb V a := by
  have e : M a = V a := by
    rw [hfr.out a (by omega), Vst_out _ _ _ _ (by rw [hr, add_n _ _ (by omega)]; omega)
      (by rw [hr, add_n _ _ (by omega)]; omega)]
  unfold VspN
  exact vst_eq _ _ _ _ _ (vst_eq _ _ _ _ _ (vst_eq _ _ _ _ _ e))

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- `mhi_tail` for every request `n ≤ 4104` (`nb` its chunk size, `Im5.ClsA`): from offset 236 (`rbx` the tcache
index of `nb`, `rbp` = `n`) to the return address with `T + 16` in `rax`. -/
theorem mhi_tailn {fb S T szw sm C n nb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L mhi_at mhi) (hinI : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hcls : ClsA n nb)
    (hrip : X.cpu.rip = mhi_at.add 236) (hbx : X.cpu.gpr.rbx = (nb + 18446744073709551599#64) >>> 4)
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
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨kb, hk1, hk2, hnbk⟩ := hcls.cases
  have hnbt := hcls.bnd
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  have htf' : ∀ i < 8, Foot F.data (Addr.add (7940592#64) i) :=
    fun i hi => hWd _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  -- from 99 on, both ways
  suffices K : ∀ (Y₁ : State) (t₁ : Nat), KeptW Wl s₀ Y₁ → Agree F Y₁.proc.mm.mem V → Y₁.cpu.rip = mhi_at.add 99 →
      Y₁.cpu.gpr.rsp = S + 192#64 → Y₁.cpu.gpr.rbp = n → GoG prof L o gev gP gE Y₁ t₁ by
    -- 236 → 99: the tcache bin `kb - 2` (`kb ≤ 65`) empty, or none (`kb ≥ 66`)
    by_cases h65 : kb ≤ 65
    · refine (c_236 prof fb).run c hfs hin _ hK hA hrip
        (vc_236m hk1 h65 (by rw [hbx, hnbk]) htb htc hC hn htf' htf hfn) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hv₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      rw [hv₁] at hA₁
      exact K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact hrsp) (by rw [hg₁]; exact hbp)
    · refine (c_236 prof fb).run c hfs hin _ hK hA hrip
        (vc_236l (by omega) hk2 (by rw [hbx, hnbk]) htb htf') ?_
      rintro j' g fl V₁ ⟨rfl, rfl, hv₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
      rw [hv₁] at hA₁
      exact K Y₁ t₁ hK₁ hA₁ hr₁ (by rw [hg₁]; exact hrsp) (by rw [hg₁]; exact hbp)
  intro Y₁ t₁ hK₁ hA₁ hr₁ sp₁ bp₁
  -- 99 → 125
  refine (c_99 prof fb).run c hfs hin _ hK₁ hA₁ hr₁ (vc_99 h1 hf1) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hv₂⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  rw [hv₂] at hA₂
  have esp : Y₂.cpu.gpr.rsp = S + 192#64 := by rw [hg₂]; exact sp₁
  have e184 : S + 192#64 - 8 = S + 184#64 := by bv_omega
  -- the call
  refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_125 _) hinI (Imm.lt_len (j := 0) (by decide)) tgt_125
    (by rw [esp, e184]; exact off_ft hsw 184 rfl (by decide)) ?_
  rintro Z₀ t₀ hK₀ hA₀ ⟨hr₀, hg₀⟩
  rw [esp, e184] at hA₀
  -- `_int_malloc`
  have l8 : (toBytesLE (mhi_at.add (125 + 5)) 8).length = 8 := toBytesLE_length _ _
  have s184 : (S + 184#64).toNat = S.toNat + 184 := add_n _ _ (by omega)
  have P : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ S.toNat →
      List.map (Vst V (S + 184#64) (toBytesLE (mhi_at.add (125 + 5)) 8)) (byteAddrs x m) =
        List.map V (byteAddrs x m) := fun x m h =>
    rd_Vst _ _ _ _ _ (by rw [l8, s184]; omega) (by omega) (.inr (by rw [s184]; omega))
  have q : ∀ x : Addr, x.toNat + 8 ≤ S.toNat → rdq(Vst V (S + 184#64) (toBytesLE (mhi_at.add (125 + 5)) 8), x) =
      rdq(V, x) := fun x h => congrArg (ofBytesLE 64) (P x 8 h)
  have d : ∀ x : Addr, x.toNat + 4 ≤ S.toNat → rdd(Vst V (S + 184#64) (toBytesLE (mhi_at.add (125 + 5)) 8), x) =
      rdd(V, x) := fun x h => congrArg (ofBytesLE 32) (P x 4 h)
  have n8 : ∀ (x : Nat), x + 8 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 8 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have n4 : ∀ (x : Nat), x + 4 ≤ S.toNat → (BitVec.ofNat 64 x).toNat + 4 ≤ S.toNat := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have hT8 : (T + 8#64).toNat + 8 ≤ S.toNat := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine im_secondA (S := S) (T := T) (szw := szw) (sm := sm) (n := n) c hfs hinI hK₀ hA₀ hr₀
    (by rw [hg₀]; show Y₂.cpu.gpr.rsp - 8 = _; rw [esp, e184])
    (by rw [hg₀, hg₂]; show Y₁.cpu.gpr.rbp = _; exact bp₁)
    (by rw [hg₀, hg₂]; rfl) hcls hS hlo hfb
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
    hin (lt_len (j := 125 + 5) (by decide)) (by
      rw [rd_Vst_self _ _ _ l8 (by rw [s184]; omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  rintro M Z₁ t₃ hfr hK₃ hA₃ hr₃ hax₃ ⟨sp₃, bx₃, bp₃, r12₃, -, -, -⟩
  have hT' : T.toNat + nb.toNat + 16 < 2 ^ 64 := by omega
  -- the bytes above the frame
  have FAR : ∀ (x : Addr) (m : Nat), S.toNat + 192 ≤ x.toNat → x.toNat + m ≤ 2 ^ 64 →
      List.map (VspN T szw nb M) (byteAddrs x m) = List.map V (byteAddrs x m) := fun x m h1 h2 => by
    rw [← VspN_rd (T := T) (szw := szw) (nb := nb) V hT' h2 (.inr (by omega)) (.inr (by omega)) (by omega)]
    exact rd_eq h2 fun a ha _ => VspN_frm l8 hS hfr (.inr (by omega))
  -- 130 → 180
  have e8 : T + 16#64 + 18446744073709551608#64 = T + 8#64 := by bv_omega
  have hT0 : T + 16#64 ≠ 0#64 := fun h => by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    simp at this
    omega
  refine (c_130 prof fb).run c hfs hin _ hK₃ hA₃ (by rw [hr₃])
    (vc_130m hk1 (by omega) (by rw [hax₃]; exact hT0) (by rw [hax₃, e8, ← hnbk]; exact VspN_hd _ hT' (by omega))
      (by rw [hax₃, e8]; exact fun i hi => c.hws _ (htw i hi))) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hv₄⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  rw [hv₄] at hA₄
  have sp₄ : Y₄.cpu.gpr.rsp = S + 192#64 := by rw [hg₄]; exact sp₃
  -- 180 → 187
  refine (c_180 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
    (vc_180 (by rw [sp₄]; exact fun i hi => c.hws _ (off_ft hsw 192 rfl (by decide) i hi))) ?_
  rintro j' g fl V₅ ⟨rfl, hv₅, ax₅, sp₅, bx₅, bp₅, r12₅⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
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
  refine c.s_ret hK₅ hA₅ hin (lt_len (by decide)) hr₅ (ret_187 _)
    (by rw [sp₅]; exact fun i hi => c.hws _ (off_ft hsw 216 rfl (by decide) i hi)) hin₂ h₂
    (by rw [sp₅, FAR _ _ (by omega) (by omega)]; exact hra) ?_
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k _ Z t' hK' hA' (fun a ha => VspN_frm l8 hS hfr ha) hr'
    (by rw [hg']; exact ax₅.trans (by rw [hg₄]; exact hax₃))
    ⟨by rw [hg']; show Y₅.cpu.gpr.rsp + 8 = _; rw [sp₅]; bv_omega, ?_, ?_, ?_⟩
  · rw [hg']
    exact bx₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))
  · rw [hg']
    exact bp₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))
  · rw [hg']
    exact r12₅.trans (congrArg (ofBytesLE 64) (FAR _ _ (by omega) (by omega)))

end FV7z.Mhi
