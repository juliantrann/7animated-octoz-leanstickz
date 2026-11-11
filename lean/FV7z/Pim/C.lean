import FV7z.Pim.CVc
/-!
# `__pthread_initialize_minimal_internal`: the static TLS block's size and the stacks' default size

`pim_c`: the third stretch of the function at `0x6000b0`, offsets 352 to 545, over the verification conditions of
`Pim/CVc.lean`, in two parts (`pim_c1` to the call of `__getrlimit`, `pim_c2` from it): one proof of the whole
stretch passes the memory the build gives a file.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Sga (vo vr vs)
open FV7z.Raf (off_ft)
namespace FV7z.Pim

variable {F : Footprint} {Wl : List Rgn}

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

set_option maxHeartbeats 1600000 in
/-- From offset 352 to the call of `__getrlimit`: `_dl_get_tls_static_info`, the alignment, the `div`, the two
variables. -/
theorem pim_c1 {fb : Addr} {g₀ : Gprs} {G : Addr → Byte} {r12 rbp cn : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pim_at pim)
    (hinG : CodeIn L Gts.gts_at Gts.gts) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pim_at.add 352) (hL : Lay F Wl g₀.rsp fb) (hF : Fr G V g₀.rsp r12 rbp cn)
    (hsp : X.cpu.gpr.rsp = g₀.rsp - 216#64)
    (k : ∀ V' Z t' (am tv : BitVec 64), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Fr (MemC G am tv) V' g₀.rsp r12 rbp cn → Z.cpu.rip = pim_at.add 448 → Kp X.cpu.gpr Z.cpu.gpr →
      Z.cpu.gpr.rdi = BitVec.setWidth 64 3#32 → Z.cpu.gpr.rsi = g₀.rsp - 200#64 → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsp' := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := g₀.rsp.isLt
  have gl : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 → ∀ i < n, Foot Wl (Addr.add x i) :=
    fun x n h1 h2 => hL.gl h1 h2
  have gd : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 →
      ∀ i < n, Foot F.data (Addr.add x i) := fun x n h1 h2 i hi => hL.hws _ (hL.gl h1 h2 i hi)
  have st : ∀ (d n : Nat) (x : Addr), x = g₀.rsp - 552#64 + BitVec.ofNat 64 d → d + n ≤ 552 →
      ∀ i < n, Foot Wl (Addr.add x i) := fun d n x hx hd => off_ft hL.hst d hx hd
  -- the arguments
  refine (c_352 prof fb).run c hfs hin _ hK hA hrip vc_352 ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have k1 : Kp X.cpu.gpr Y₁.cpu.gpr := by
    rw [hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsp₁ : Y₁.cpu.gpr.rsp = g₀.rsp - 216#64 := k1.rsp.trans hsp
  refine c.s_call hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_364 _) hinG (Gts.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp₁]
    exact st 328 8 _ (by bv_omega) (by decide) i hi
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁, show g₀.rsp - 216#64 - 8 = g₀.rsp - 224#64 from by bv_omega] at hA₂ hg₂
  have hdi₂ : Y₂.cpu.gpr.rdi = 8027712#64 := by rw [hg₂, hg₁]; rfl
  have hsi₂ : Y₂.cpu.gpr.rsi = g₀.rsp - 208#64 := by
    rw [hg₂, hg₁]
    show X.cpu.gpr.rsp + 8#64 = _
    rw [hsp]
    bv_omega
  -- `_dl_get_tls_static_info`
  refine Gts.gts_ok c hinG hK₂ hA₂ hr₂ (gd _ 8 (by decide) (by decide)) (gd _ 8 (by decide) (by decide))
    (by rw [hdi₂]; exact gl _ 8 (by decide) (by decide))
    (by rw [hsi₂]; exact st 344 8 _ (by bv_omega) (by decide)) ?_
  intro Y₃ t₃ hK₃ hA₃ hr₃ hg₃
  unfold Gts.V2 Gts.V1 at hA₃
  rw [hdi₂, hsi₂] at hA₃
  have hF₂ : Fr G (Vst V₁ (g₀.rsp - 224#64) (toBytesLE (pim_at.add (364 + 5)) 8)) g₀.rsp r12 rbp cn :=
    hF.lo hL.hsp (by ln) (by bv_omega) (by bv_omega)
  have e1 : rdq(Vst V₁ (g₀.rsp - 224#64) (toBytesLE (pim_at.add (364 + 5)) 8), 7938736#64) = rdq(G, 7938736#64) :=
    congrArg (ofBytesLE 64) (hF₂.rd (by decide) (by bv_omega))
  rw [e1] at hA₃
  obtain ⟨V₃, hA₃, hF₃, hra₃⟩ : ∃ V₃, Agree F Y₃.proc.mm.mem V₃ ∧
      Fr (Vst G (8027712#64) (toBytesLE rdq(G, 7938736#64) 8)) V₃ g₀.rsp r12 rbp cn ∧
      rdq(V₃, g₀.rsp - 224#64) = pim_at.add 369 := by
    refine ⟨_, hA₃, ?_, ?_⟩
    · exact (hF₂.gl hL.hsp (by ln) (by decide) (by bv_omega)).lo hL.hsp (by ln) (by bv_omega) (by bv_omega)
    · rw [vr (by ln) (by bv_omega) (by bv_omega) (by bv_omega), vr (by ln) (by bv_omega) (by bv_omega) (by bv_omega),
        vs (by ln) (by bv_omega)]
      exact ofBytesLE_toBytesLE (n := 8) rfl _
  have hsp₃ : Y₃.cpu.gpr.rsp = g₀.rsp - 224#64 := by rw [hg₃, hg₂]; rfl
  refine c.s_ret hK₃ hA₃ hinG (Gts.lt_len (by decide)) hr₃ (Gts.ret_24 _) (fun i hi => ?_) hin (j₂ := 369)
    (lt_len (by decide)) ?_ ?_
  · rw [hsp₃]
    exact hL.hws _ (st 328 8 _ (by bv_omega) (by decide) i hi)
  · rw [hsp₃]
    exact hra₃
  rintro Y₄ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  have k4 : Kp Y₁.cpu.gpr Y₄.cpu.gpr := by
    rw [hg₄, hg₃, hg₂]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    show g₀.rsp - 224#64 + 8 = Y₁.cpu.gpr.rsp
    rw [hsp₁]
    bv_omega
  have hsp₄ : Y₄.cpu.gpr.rsp = g₀.rsp - 216#64 := k4.rsp.trans hsp₁
  -- the alignment
  refine (c_369 prof fb).run c hfs hin _ hK₄ hA₄ hr₄
    (vc_369 (by rw [hsp₄]; exact fun i hi => hL.hws _ (st 344 8 _ (by bv_omega) (by decide) i hi))
      (by rw [hsp₄]; exact st 344 8 _ (by bv_omega) (by decide))) ?_
  rintro j' g fl V₅ ⟨rfl, al, am, hal, rfl, hV⟩ Y₅ t₅ hK₅ hA₅ hr₅ hg₅ -
  have hF₅ : Fr (Vst G (8027712#64) (toBytesLE rdq(G, 7938736#64) 8)) V₅ g₀.rsp r12 rbp cn := by
    rcases hV with rfl | rfl
    · exact hF₃
    · rw [hsp₄]
      exact hF₃.lo hL.hsp (by ln) (by bv_omega) (by bv_omega)
  have k5 : Kp Y₄.cpu.gpr Y₅.cpu.gpr := by
    rw [hg₅]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hcx₅ : Y₅.cpu.gpr.rcx = al := by rw [hg₅]
  have hax₅ : Y₅.cpu.gpr.rax = am := by rw [hg₅]
  -- `__static_tls_align_m1`
  refine (c_403 prof fb).run c hfs hin _ hK₅ hA₅ hr₅
    (vc_403 (gl _ 8 (by decide) (by decide)) (gd _ 8 (by decide) (by decide))) ?_
  rintro j' g fl V₆ ⟨rfl, ax, rfl, rfl⟩ Y₆ t₆ hK₆ hA₆ hr₆ hg₆ -
  rw [hax₅] at hA₆
  have k6 : Kp Y₅.cpu.gpr Y₆.cpu.gpr := by
    rw [hg₆]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `div`
  refine c.s_div64 hK₆ hA₆ hin (lt_len (by decide)) hr₆ (div_434 _) (by rw [hg₆]; rfl) ?_ ?_
  · show (Y₆.cpu.gpr.get (regOf 1)).setWidth 64 ≠ 0
    rw [hg₆]
    show (Y₅.cpu.gpr.rcx).setWidth 64 ≠ 0
    rw [hcx₅, BitVec.setWidth_eq]
    exact hal
  rintro Y₇ t₇ hK₇ hA₇ ⟨hr₇, hg₇⟩
  have k7 : Kp Y₆.cpu.gpr Y₇.cpu.gpr := by
    rw [hg₇]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- `__static_tls_size`
  refine (c_437 prof fb).run c hfs hin _ hK₇ hA₇ hr₇ (vc_437 (gl _ 8 (by decide) (by decide))) ?_
  rintro j' g fl V₈ ⟨rfl, tv, rfl, rfl⟩ Y₈ t₈ hK₈ hA₈ hr₈ hg₈ -
  have k8 : Kp Y₇.cpu.gpr Y₈.cpu.gpr := by
    rw [hg₈]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have k18 : Kp X.cpu.gpr Y₈.cpu.gpr := ((((k1.trans k4).trans k5).trans k6).trans k7).trans k8
  have hsp₈ : Y₈.cpu.gpr.rsp = g₀.rsp - 216#64 := k18.rsp.trans hsp
  have hdi₈ : Y₈.cpu.gpr.rdi = BitVec.setWidth 64 3#32 := by rw [hg₈, hg₇, hg₆]; rfl
  have hsi₈ : Y₈.cpu.gpr.rsi = g₀.rsp - 200#64 := by
    rw [hg₈, hg₇, hg₆]
    show Y₅.cpu.gpr.rsp + 16#64 = _
    rw [k5.rsp.trans hsp₄]
    bv_omega
  have hF₈ : Fr (MemC G am tv) (Vst (Vst V₅ (8027696#64) (toBytesLE am 8)) (8027712#64) (toBytesLE tv 8)) g₀.rsp
      r12 rbp cn :=
    (hF₅.gl hL.hsp (by ln) (by decide) (by bv_omega)).gl hL.hsp (by ln) (by decide) (by bv_omega)
  exact k _ Y₈ t₈ am tv hK₈ hA₈ hF₈ hr₈ k18 hdi₈ hsi₈

set_option maxHeartbeats 1600000 in
/-- From the call of `__getrlimit (RLIMIT_STACK, sp - 200)` to offset 545: the limit, the default stack's size in
the frame. -/
theorem pim_c2 {fb : Addr} {g₀ : Gprs} {G : Addr → Byte} {r12 rbp cn am tv : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pim_at pim)
    (hinR : CodeIn L Grl.grl_at Grl.grl) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = pim_at.add 448) (hL : Lay F Wl g₀.rsp fb) (htop : g₀.rsp.toNat ≤ userPtrMax prof.feat)
    (hF : Fr (MemC G am tv) V g₀.rsp r12 rbp cn) (hsp : X.cpu.gpr.rsp = g₀.rsp - 216#64)
    (hdi : X.cpu.gpr.rdi = BitVec.setWidth 64 3#32) (hsi : X.cpu.gpr.rsi = g₀.rsp - 200#64)
    (k : ∀ V' g' Z t' (sz : BitVec 64), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Fr (MemC G am tv) V' g₀.rsp r12 rbp cn → rdq(V', g₀.rsp - 200#64) = sz → Z.cpu.rip = pim_at.add 545 →
      Z.cpu.gpr = g' → Kp X.cpu.gpr g' → g'.rax = 0 → g'.rdx = 1 →
      GoG prof L o (gev ++ [rlEv g₀.rsp X.cpu.gpr.r8 X.cpu.gpr.r9 (s₀.proc.signal.rlimits ⟨3, by decide⟩).bytes])
        gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hsp' := hL.hsp
  have hfb := hL.hfb
  have hlo := hL.hlo
  have hlt := g₀.rsp.isLt
  have gl : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 → ∀ i < n, Foot Wl (Addr.add x i) :=
    fun x n h1 h2 => hL.gl h1 h2
  have gd : ∀ (x : Addr) (n : Nat), 0x777000 ≤ x.toNat → x.toNat + n ≤ 0x7a9000 →
      ∀ i < n, Foot F.data (Addr.add x i) := fun x n h1 h2 i hi => hL.hws _ (hL.gl h1 h2 i hi)
  have st : ∀ (d n : Nat) (x : Addr), x = g₀.rsp - 552#64 + BitVec.ofNat 64 d → d + n ≤ 552 →
      ∀ i < n, Foot Wl (Addr.add x i) := fun d n x hx hd => off_ft hL.hst d hx hd
  refine c.s_call hK hA hin (lt_len (by decide)) hrip (call_448 _) hinR (Grl.lt_len (by decide)) (by decide)
    (fun i hi => ?_) ?_
  · rw [hsp]
    exact st 328 8 _ (by bv_omega) (by decide) i hi
  rintro Y₉ t₉ hK₉ hA₉ ⟨hr₉, hg₉⟩
  rw [hsp, show g₀.rsp - 216#64 - 8 = g₀.rsp - 224#64 from by bv_omega] at hA₉ hg₉
  have hdi₉ : Y₉.cpu.gpr.rdi = BitVec.setWidth 64 3#32 := by rw [hg₉]; exact hdi
  have hsi₉ : Y₉.cpu.gpr.rsi = g₀.rsp - 200#64 := by rw [hg₉]; exact hsi
  have e8 : Y₉.cpu.gpr.r8 = X.cpu.gpr.r8 := by rw [hg₉]; rfl
  have e9 : Y₉.cpu.gpr.r9 = X.cpu.gpr.r9 := by rw [hg₉]; rfl
  -- `__getrlimit (RLIMIT_STACK, sp - 200)`
  refine Grl.grl_ok c hinR hK₉ hA₉ hr₉ (r := 3) (by decide) (by rw [hdi₉]; rfl) (by rw [hsi₉]; bv_omega)
    (by rw [hsi₉]; exact Nat.le_trans (by bv_omega) htop)
    (by rw [hsi₉]; exact st 352 16 _ (by bv_omega) (by decide)) ?_
  intro rc r11 Y₁₀ t₁₀ hK₁₀ hA₁₀ hr₁₀ hg₁₀
  have hev : Grl.grlEv Y₉.cpu.gpr (s₀.proc.signal.rlimits ⟨3, by decide⟩).bytes =
      rlEv g₀.rsp X.cpu.gpr.r8 X.cpu.gpr.r9 (s₀.proc.signal.rlimits ⟨3, by decide⟩).bytes := by
    show (⟨302, [0, (Y₉.cpu.gpr.rdi.setWidth 32).setWidth 64, 0, Y₉.cpu.gpr.rsi, Y₉.cpu.gpr.r8, Y₉.cpu.gpr.r9], 0, [],
      _⟩ : Event) = _
    rw [hdi₉, hsi₉, e8, e9]
    rfl
  rw [hev]
  rw [hsi₉] at hA₁₀
  have hsp₁₀ : Y₁₀.cpu.gpr.rsp = g₀.rsp - 224#64 := by rw [hg₁₀, hg₉]; rfl
  refine c.s_ret hK₁₀ hA₁₀ hinR (Grl.lt_len (by decide)) hr₁₀ (Grl.ret_28 _) (fun i hi => ?_) hin (j₂ := 453)
    (lt_len (by decide)) ?_ ?_
  · rw [hsp₁₀]
    exact hL.hws _ (st 328 8 _ (by bv_omega) (by decide) i hi)
  · rw [hsp₁₀, vr (Rlimit.bytes_length _) (by bv_omega) (by bv_omega) (by bv_omega), vs (by ln) (by bv_omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  rintro Y₁₁ t₁₁ hK₁₁ hA₁₁ ⟨hr₁₁, hg₁₁⟩
  have hF₁₁ : Fr (MemC G am tv) (Vst (Vst V (g₀.rsp - 224#64) (toBytesLE (pim_at.add (448 + 5)) 8))
      (g₀.rsp - 200#64) (s₀.proc.signal.rlimits ⟨3, by decide⟩).bytes) g₀.rsp r12 rbp cn :=
    (hF.lo hL.hsp (by ln) (by bv_omega) (by bv_omega)).lo hL.hsp (Rlimit.bytes_length _) (by bv_omega)
      (by bv_omega)
  have k11 : Kp X.cpu.gpr Y₁₁.cpu.gpr := by
    rw [hg₁₁, hg₁₀, hg₉]
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    show g₀.rsp - 224#64 + 8 = X.cpu.gpr.rsp
    rw [hsp]
    bv_omega
  have hsp₁₁ : Y₁₁.cpu.gpr.rsp = g₀.rsp - 216#64 := k11.rsp.trans hsp
  -- the limit
  refine (c_453 prof fb).run c hfs hin _ hK₁₁ hA₁₁ hr₁₁
    (vc_453 (by rw [hsp₁₁]; exact fun i hi => hL.hws _ (st 352 8 _ (by bv_omega) (by decide) i hi))) ?_
  rintro j' g fl V₁₂ ⟨rfl, ax', cx, dx, rfl, rfl⟩ Y₁₂ t₁₂ hK₁₂ hA₁₂ hr₁₂ hg₁₂ -
  have k12 : Kp Y₁₁.cpu.gpr Y₁₂.cpu.gpr := by
    rw [hg₁₂]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsp₁₂ : Y₁₂.cpu.gpr.rsp = g₀.rsp - 216#64 := k12.rsp.trans hsp₁₁
  -- the default size
  refine (c_492 prof fb).run c hfs hin _ hK₁₂ hA₁₂ hr₁₂
    (vc_492 (gd _ 8 (by decide) (by decide)) (gd _ 8 (by decide) (by decide))
      (by rw [hsp₁₂]; exact st 352 8 _ (by bv_omega) (by decide))) ?_
  rintro j' g fl V₁₃ ⟨rfl, sz, rfl, rfl⟩ Y₁₃ t₁₃ hK₁₃ hA₁₃ hr₁₃ hg₁₃ -
  rw [hsp₁₂, show g₀.rsp - 216#64 + 16#64 = g₀.rsp - 200#64 from by bv_omega] at hA₁₃
  have k13 : Kp Y₁₂.cpu.gpr Y₁₃.cpu.gpr := by
    rw [hg₁₃]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have kk : Kp X.cpu.gpr Y₁₃.cpu.gpr := (k11.trans k12).trans k13
  refine k _ _ Y₁₃ t₁₃ sz hK₁₃ hA₁₃ (hF₁₁.lo hL.hsp (by ln) (by bv_omega) (by bv_omega)) ?_ hr₁₃ rfl kk
    (by rw [hg₁₃]; rfl) (by rw [hg₁₃]; rfl)
  rw [vs (by ln) (by bv_omega)]
  exact ofBytesLE_toBytesLE (n := 8) rfl _

/-- From offset 352 to offset 545: the sizes computed, the default stack's size `sz` in the frame. -/
theorem pim_c {fb : Addr} {g₀ : Gprs} {G : Addr → Byte} {r12 rbp cn : BitVec 64}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L pim_at pim)
    (hinG : CodeIn L Gts.gts_at Gts.gts) (hinR : CodeIn L Grl.grl_at Grl.grl) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = pim_at.add 352) (hL : Lay F Wl g₀.rsp fb)
    (htop : g₀.rsp.toNat ≤ userPtrMax prof.feat) (hF : Fr G V g₀.rsp r12 rbp cn) (hR : Rg g₀ X.cpu.gpr)
    (k : ∀ V' g' Z t' (am tv sz : BitVec 64), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
      Fr (MemC G am tv) V' g₀.rsp r12 rbp cn → rdq(V', g₀.rsp - 200#64) = sz → Z.cpu.rip = pim_at.add 545 →
      Z.cpu.gpr = g' → Rg g₀ g' → g'.rax = 0 → g'.rdx = 1 →
      GoG prof L o (gev ++ [rlEv g₀.rsp X.cpu.gpr.r8 X.cpu.gpr.r9 (s₀.proc.signal.rlimits ⟨3, by decide⟩).bytes])
        gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨hsp, hbp, h12, hbx, h13, h14, h15⟩ := hR
  refine pim_c1 c hfs hin hinG hK hA hrip hL hF hsp ?_
  intro V₁ Z₁ t₁ am tv hK₁ hA₁ hF₁ hr₁ kp hdi hsi
  rw [← kp.r8, ← kp.r9] at k
  refine pim_c2 c hfs hin hinR hK₁ hA₁ hr₁ hL htop hF₁ (kp.rsp.trans hsp) hdi hsi ?_
  intro V₂ g₂ Z₂ t₂ sz hK₂ hA₂ hF₂ hsz hr₂ hg₂ kp₂ hax hdx
  have kk := kp.trans kp₂
  exact k V₂ g₂ Z₂ t₂ am tv sz hK₂ hA₂ hF₂ hsz hr₂ hg₂
    ⟨kk.rsp.trans hsp, kk.rbp.trans hbp, kk.r12.trans h12, kk.rbx.trans hbx, kk.r13.trans h13, kk.r14.trans h14,
      kk.r15.trans h15⟩ hax hdx

end FV7z.Pim
