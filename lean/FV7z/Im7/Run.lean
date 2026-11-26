import FV7z.Im7.Va
import FV7z.Im7.Vb
import FV7z.Im7.Idx
import FV7z.Im5.Cls
/-!
# `_int_malloc`: the second call for every request `4105 ≤ n ≤ 2 ^ 32` (PLAN.md G3, `malloc`)

- `ixA` … `ixCc`: the index stored at `rsp + 0x28` on each way is `lix nb`.
- `clsG`: the facts of `request2size` for such a request.
- `from512`: from 512 with the index `lix nb` (`vcBall`) to 2549, then `Im2.im_from2549`.
- `im_secondG`: by the way `nb` takes (`vcA` … `vcCc`) to 512, then `from512`; `secG`: as `Im5.SecA`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at)
open FV7z.Im2 (VspN and_m16)
open FV7z.Sbrk (rd_eq)
namespace FV7z.Im7
variable {F : Footprint} {Wl : List Rgn}

/-- `lix m` on the way of `PaA`. -/
theorem lixA {m : Nat} (h1 : 48 < m / 64) (h2 : m / 512 ≤ 20) : lix m = 91 + m / 512 := by
  unfold lix; repeat' split
  all_goals omega

theorem lixB {m : Nat} (h1 : 20 < m / 512) (h2 : m / 4096 ≤ 10) : lix m = 110 + m / 4096 := by
  unfold lix; repeat' split
  all_goals omega

theorem lixCa {m : Nat} (h1 : 10 < m / 4096) (h2 : m / 32768 < 5) : lix m = 119 + m / 32768 := by
  unfold lix; repeat' split
  all_goals omega

theorem lixCb {m : Nat} (h1 : 5 ≤ m / 32768) (h2 : m ≤ 786431) : lix m = 124 + m / 262144 := by
  unfold lix; repeat' split
  all_goals omega

theorem lixCc {m : Nat} (h2 : 786431 < m) : lix m = 126 := by
  unfold lix; repeat' split
  all_goals omega

theorem ixA {nb : BitVec 64} (h1 : 48 < nb.toNat / 64) (h2 : nb.toNat / 512 ≤ 20) :
    BitVec.setWidth 32 (nb >>> 9) + 91#32 = BitVec.ofNat 32 (lix nb.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [lixA h1 h2, BitVec.toNat_add, BitVec.toNat_setWidth, shr_nat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem ixB {nb : BitVec 64} (h1 : 20 < nb.toNat / 512) (h2 : nb.toNat / 4096 ≤ 10) :
    BitVec.setWidth 32 (nb >>> 12 + 110#64) = BitVec.ofNat 32 (lix nb.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [lixB h1 h2, BitVec.toNat_add, BitVec.toNat_setWidth, shr_nat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem ixCa {nb : BitVec 64} (h1 : 10 < nb.toNat / 4096) (h2 : nb.toNat / 32768 < 5) :
    BitVec.setWidth 32 (nb >>> 15 + 119#64) = BitVec.ofNat 32 (lix nb.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [lixCa h1 h2, BitVec.toNat_add, BitVec.toNat_setWidth, shr_nat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem ixCb {nb : BitVec 64} (h1 : 5 ≤ nb.toNat / 32768) (h2 : nb.toNat ≤ 786431) :
    BitVec.setWidth 32 (nb >>> 18 + 124#64) = BitVec.ofNat 32 (lix nb.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [lixCb h1 h2, BitVec.toNat_add, BitVec.toNat_setWidth, shr_nat, BitVec.toNat_ofNat, Nat.reducePow]
  omega

theorem ixCc {nb : BitVec 64} (h2 : 786431 < nb.toNat) : (126#32 : BitVec 32) = BitVec.ofNat 32 (lix nb.toNat) := by
  rw [lixCc h2]

/-- `nb >>> k` as a division, for the flag lemmas. -/
theorem shr6 (x : BitVec 64) : (x >>> 6).toNat = x.toNat / 64 := shr_nat x 6
theorem shr9 (x : BitVec 64) : (x >>> 9).toNat = x.toNat / 512 := shr_nat x 9
theorem shr12 (x : BitVec 64) : (x >>> 12).toNat = x.toNat / 4096 := shr_nat x 12
theorem shr15 (x : BitVec 64) : (x >>> 15).toNat = x.toNat / 32768 := shr_nat x 15

/-- The comparison of `tc = (nb - 17) >> 4` with `mp_.tcache_bins` (64) at 1099. -/
theorem tcb {nb : BitVec 64} (h : 4112 < nb.toNat) :
    decide (64 < ((nb + 18446744073709551599#64) >>> 4).toNat) = true := by
  have hl := nb.isLt
  have e : (nb + 18446744073709551599#64).toNat = nb.toNat - 17 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [shr_nat, e]
  exact decide_eq_true (show 64 < (nb.toNat - 17) / 16 by omega)

/-- `request2size` of `4105 ≤ n ≤ 2 ^ 32`. -/
theorem clsG {n : Addr} (h1 : 4105 ≤ n.toNat) (h2 : n.toNat ≤ 2 ^ 32) :
    n.msb = false ∧ decide ((n + 23#64).toNat < 31) = false ∧ decide (n + 23#64 = 31#64) = false ∧
    (n + 23#64 &&& 18446744073709551600#64).toNat = (n.toNat + 23) / 16 * 16 := by
  have e : (n + 23#64).toNat = n.toNat + 23 := by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine ⟨?_, decide_eq_false (by omega), decide_eq_false (fun h => by rw [h, BitVec.toNat_ofNat] at e; omega), ?_⟩
  · rw [BitVec.msb_eq_decide]; exact decide_eq_false (by show ¬ (2 ^ 63 ≤ n.toNat); omega)
  · rw [and_m16, e]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- From 512 on the second call, the index `lix nb` at `rsp + 0x28`: `vcBall` to 2549, then `Im2.im_from2549`. -/
theorem from512 {fb S T szw sm nb : Addr} {G : Gprs} {V₁ : Addr → Byte} {Y : State} {t₁ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem V₁) (hr : Y.cpu.rip = imm_at.add 512)
    (hbx : Y.cpu.gpr.rbx = 7940672#64) (h13 : Y.cpu.gpr.r13 = nb) (hsp : Y.cpu.gpr.rsp = S)
    (hix : rdd(V₁, S + 40#64) = BitVec.ofNat 32 (lix nb.toNat)) (hF : Im2.Fr S G V V₁)
    (hn1 : 4112 < nb.toNat) (hn2 : nb.toNat ≤ 2 ^ 33)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat) (hfc : rdd(V, 7940680#64) = 0)
    (hlb : ∀ i, 64 ≤ i → i ≤ 126 →
      rdq(V, BitVec.ofNat 64 (7940768 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64) (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 192, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + nb.toNat + 16 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i))
    (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : nb.toNat + 32 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 184#64) = e₂.add j₂)
    (k : ∀ M Z t', Im2.Fr S G V M → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VspN T szw nb M) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = G.rbx ∧ Z.cpu.gpr.rbp = G.rbp ∧
        Z.cpu.gpr.r12 = G.r12 ∧ Z.cpu.gpr.r13 = G.r13 ∧ Z.cpu.gpr.r14 = G.r14 ∧ Z.cpu.gpr.r15 = G.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₁ := by
  have hs184 : ∀ i < 184, Foot Wl (Addr.add S i) := fun i hi => hsw i (by omega)
  have hsd : ∀ i < 184, Foot F.data (Addr.add S i) := fun i hi => c.hws _ (hs184 i hi)
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  have T2 : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ S.toNat →
      List.map V₁ (byteAddrs x m) = List.map V (byteAddrs x m) := fun x m h =>
    rd_eq (by omega) fun a _ h2 => hF.out a (.inl (by omega))
  have hI1 := lix_ge hn1
  have hI2 : lix nb.toNat ≤ 126 := (lix_le _).resolve_right (by omega)
  have hbin : rdq(V₁, BitVec.ofNat 64 (7940768 + 16 * lix nb.toNat)) =
      BitVec.ofNat 64 (7940752 + 16 * lix nb.toNat) :=
    (congrArg (ofBytesLE 64) (T2 _ 8 (by rw [BitVec.toNat_ofNat]; omega))).trans (hlb _ (by omega) hI2)
  have hfc' : rdd(V₁, 7940680#64) = 0 :=
    (congrArg (ofBytesLE 32) (T2 _ 4 (by rw [BitVec.toNat_ofNat]; omega))).trans hfc
  have htc' : rdq(V₁, fb + 18446744073709551576#64) ≠ 0#64 := by
    rw [congrArg (ofBytesLE 64) (T2 _ 8 hfb)]; exact htc
  have htb' : rdq(V₁, 7940592#64) = 64#64 :=
    (congrArg (ofBytesLE 64) (T2 _ 8 (by rw [BitVec.toNat_ofNat]; omega))).trans htb
  have hun' : rdq(V₁, 7940792#64) = 7940768#64 :=
    (congrArg (ofBytesLE 64) (T2 _ 8 (by rw [BitVec.toNat_ofNat]; omega))).trans hun
  have hm3' : rdd(V₁, 7942828#64) = 0 :=
    (congrArg (ofBytesLE 32) (T2 _ 4 (by rw [BitVec.toNat_ofNat]; omega))).trans hm3
  refine (c_512 prof fb).run c hfs hin _ hK hA hr
    (vcBall hI1 hI2 hbx h13 hsp hix hF (dlt (by omega)) (deq (by omega)) (tcb hn1) hS hlo hfb hfc' hbin htc' htb'
      hun' hm3' hWd htf hs184 hsd) ?_
  rintro j₂' g₂ f₂ V₂ ⟨rfl, h₂'⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ hf₂
  refine (c_1115 prof fb).run c hfs hin _ hK₂ hA₂ hr₂ (by rw [hg₂, hf₂]; exact h₂') ?_
  rintro j₃ g₃ f₃ V₃ ⟨rfl, h₃⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ hf₃
  refine (c_2012 prof fb).run c hfs hin _ hK₃ hA₃ hr₃ (by rw [hg₃, hf₃]; exact h₃) ?_
  rintro j₄ g₄ f₄ V₄ ⟨rfl, hbx₄, h13₄, hsp₄, hfr⟩ Y₄ t₄ hK₄ hA₄ hr₄ hg₄ -
  exact Im2.im_from2549 c hfs hin hK₄ hA₄ hr₄ (by rw [hg₄]; exact hbx₄) (by rw [hg₄]; exact h13₄)
    (by rw [hg₄]; exact hsp₄) hfr (by omega) hS hW hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge
    hin₂ h₂ hra (fun Z t' => k V₄ Z t' hfr)

/-- `_int_malloc` on the second call for every request `4105 ≤ n ≤ 2 ^ 32`: the hypotheses of `Im5.SecA`. -/
theorem im_secondG {fb S T szw sm n nb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at)
    (hrsp : X.cpu.gpr.rsp = S + 184#64) (hsi : X.cpu.gpr.rsi = n) (hdi : X.cpu.gpr.rdi = 7940672#64)
    (hn1 : 4105 ≤ n.toNat) (hn2 : n.toNat ≤ 2 ^ 32) (hnb : n + 23#64 &&& 18446744073709551600#64 = nb)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64) (hfc : rdd(V, 7940680#64) = 0)
    (hlb : ∀ i, 64 ≤ i → i ≤ 126 →
      rdq(V, BitVec.ofNat 64 (7940768 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64) (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 192, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + nb.toNat + 16 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i))
    (hrw : ∀ i < 8, Foot Wl (Addr.add (T + nb + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat)
    (hge : nb.toNat + 32 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 184#64) = e₂.add j₂)
    (k : ∀ M Z t', Im2.Fr S X.cpu.gpr V M → KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VspN T szw nb M) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  obtain ⟨m, d1, d2, hv⟩ := clsG hn1 hn2
  rw [hnb] at hv
  have hs184 : ∀ i < 184, Foot Wl (Addr.add S i) := fun i hi => hsw i (by omega)
  have hsd : ∀ i < 184, Foot F.data (Addr.add S i) := fun i hi => c.hws _ (hs184 i hi)
  have K : ∀ {Y : State} {t₁ : Nat} {V₁ : Addr → Byte}, KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V₁ →
      Y.cpu.rip = imm_at.add 512 → Y.cpu.gpr.rbx = 7940672#64 → Y.cpu.gpr.r13 = nb → Y.cpu.gpr.rsp = S →
      rdd(V₁, S + 40#64) = BitVec.ofNat 32 (lix nb.toNat) → Im2.Fr S X.cpu.gpr V V₁ →
      GoG prof L o gev gP gE Y t₁ := fun hK₁ hA₁ hr₁ hbx h13 hsp hix hF =>
    from512 c hfs hin hK₁ hA₁ hr₁ hbx h13 hsp hix hF (by omega) (by omega) hS hlo hfb hfc hlb htc htb hun hm3 hW
      htf hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge hin₂ h₂ hra k
  have c320 : decide (nb.toNat < 128) = false := dlt (by omega)
  have z320 : decide (nb = 128#64) = false := deq (by omega)
  have c340 : decide (nb.toNat < 1023) = false := dlt (by omega)
  have z340 : decide (nb = 1023#64) = false := deq (by omega)
  have c476 : decide ((nb >>> 6).toNat < 48) = false := dlt (by rw [shr6]; omega)
  have z476 : decide (nb >>> 6 = 48#64) = false := deq (by rw [shr6]; omega)
  have hrip' : X.cpu.rip = imm_at.add 0 := by rw [hrip]; rfl
  by_cases pA : nb.toNat / 512 ≤ 20
  · refine (c_0 prof fb).run c hfs hin _ hK hA hrip'
      (vcA hrsp hsi hdi m d1 d2 hnb c320 z320 c340 z340 (dlt' (by omega)) c476 z476 rfl rfl
        (dle (by rw [shr9]; omega)) hS hlo hgm hgf hs184 hsd) ?_
    rintro j₁ g₁ f₁ V₁ ⟨rfl, hbx, h13, hsp, hix, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    exact K hK₁ hA₁ hr₁ hbx h13 hsp (hix.trans (ixA (by omega) pA)) hF
  have c486 : decide ((nb >>> 9).toNat < 20) = false := dlt (by rw [shr9]; omega)
  have z486 : decide (nb >>> 9 = 20#64) = false := deq (by rw [shr9]; omega)
  by_cases pB : nb.toNat / 4096 ≤ 10
  · refine (c_0 prof fb).run c hfs hin _ hK hA hrip'
      (vcB hrsp hsi hdi m d1 d2 hnb c320 z320 c340 z340 (dlt' (by omega)) c476 z476 c486 z486 rfl rfl
        (dle (by rw [shr12]; omega)) hS hlo hgm hgf hs184 hsd) ?_
    rintro j₁ g₁ f₁ V₁ ⟨rfl, hbx, h13, hsp, hix, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    exact K hK₁ hA₁ hr₁ hbx h13 hsp (hix.trans (ixB (by omega) pB)) hF
  have c497 : decide ((nb >>> 12).toNat < 10) = false := dlt (by rw [shr12]; omega)
  have z497 : decide (nb >>> 12 = 10#64) = false := deq (by rw [shr12]; omega)
  by_cases pCa : nb.toNat / 32768 < 5
  · refine (c_0 prof fb).run c hfs hin _ hK hA hrip'
      (vcCa hrsp hsi hdi m d1 d2 hnb c320 z320 c340 z340 (dlt' (by omega)) c476 z476 c486 z486 c497 z497
        (dlt' (by rw [shr15]; omega)) hS hlo hgm hgf hs184 hsd) ?_
    rintro j₁ g₁ f₁ V₁ ⟨rfl, hbx, h13, hsp, hix, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    exact K hK₁ hA₁ hr₁ hbx h13 hsp (hix.trans (ixCa (by omega) pCa)) hF
  have c2192 : decide ((nb >>> 15).toNat < 5) = false := dlt (by rw [shr15]; omega)
  by_cases pCb : nb.toNat ≤ 786431
  · refine (c_0 prof fb).run c hfs hin _ hK hA hrip'
      (vcCb hrsp hsi hdi m d1 d2 hnb c320 z320 c340 z340 rfl rfl (dle (by omega)) c476 z476 c486 z486 c497 z497
        c2192 hS hlo hgm hgf hs184 hsd) ?_
    rintro j₁ g₁ f₁ V₁ ⟨rfl, hbx, h13, hsp, hix, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    exact K hK₁ hA₁ hr₁ hbx h13 hsp (hix.trans (ixCb (by omega) pCb)) hF
  · refine (c_0 prof fb).run c hfs hin _ hK hA hrip'
      (vcCc hrsp hsi hdi m d1 d2 hnb c320 z320 c340 z340 (dlt (by omega)) (deq (by omega)) c476 z476 c486 z486
        c497 z497 c2192 hS hlo hgm hgf hs184 hsd) ?_
    rintro j₁ g₁ f₁ V₁ ⟨rfl, hbx, h13, hsp, hix, hF⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
    subst hg₁
    exact K hK₁ hA₁ hr₁ hbx h13 hsp (hix.trans (ixCc (by omega))) hF

/-- Every request `4105 ≤ n ≤ 2 ^ 32`: `im_secondG`. -/
theorem secG {n nb : Addr} (h1 : 4105 ≤ n.toNat) (h2 : n.toNat ≤ 2 ^ 32)
    (h : n + 23#64 &&& 18446744073709551600#64 = nb) : Im5.SecA n nb := by
  intro prof F Wl L s₀ X o t gev gP gE V fb S T szw sm c hfs hin hK hA hrip hrsp hsi hdi hS hlo hfb hgm hfc hfz
    hbk hlb htc htb hun hm0 hm1 hm2 hm3
  exact im_secondG c hfs hin hK hA hrip hrsp hsi hdi h1 h2 h hS hlo hfb hgm hfc hlb htc htb hun hm3

end FV7z.Im7
