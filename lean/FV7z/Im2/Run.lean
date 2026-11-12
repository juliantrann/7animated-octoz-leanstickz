import FV7z.Im2.Top
/-!
# `_int_malloc`: from the entry to the return address, the second call (PLAN.md G3, `malloc`)

- `V2_out`, `V2_lo`, `V2_regs`, `V2_ra`: the bytes of `V2` outside the frame, the six registers read back and the
  return address.
- `im_second`: `vc_0`, `vc_1115`, `vc_2549` and the `ret`: from the entry with 50 bytes asked for to the return
  address, the top split, `T + 16` in `rax`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at rd_off rd_off_self add_n stk_in ret_950 lt_len)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

theorem V2_out (S : Addr) (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) {x : Addr}
    (h : x.toNat < S.toNat + 8 ∨ S.toNat + 184 ≤ x.toNat) : V2 S g V x = V x := by
  unfold V2 V1
  repeat rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)
    (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)]

theorem V2_lo {S x : Addr} {n : Nat} (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (h : x.toNat + n ≤ S.toNat + 8) : List.map (V2 S g V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
  rd_eq (by omega) fun _ _ h2 => V2_out S g V hS (.inl (by omega))

theorem V2_ra (S : Addr) (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    rdq(V2 S g V, S + 184#64) = rdq(V, S + 184#64) :=
  congrArg (ofBytesLE 64) (rd_eq (by rw [add_n _ _ (by omega)]; omega) fun _ h _ =>
    V2_out S g V hS (.inr (by rw [add_n _ _ (by omega)] at h; omega)))

theorem V2_regs (S : Addr) (g : Gprs) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    rdq(V2 S g V, S + 136#64) = g.rbx ∧ rdq(V2 S g V, S + 144#64) = g.rbp ∧ rdq(V2 S g V, S + 152#64) = g.r12 ∧
      rdq(V2 S g V, S + 160#64) = g.r13 ∧ rdq(V2 S g V, S + 168#64) = g.r14 ∧
      rdq(V2 S g V, S + 176#64) = g.r15 := by
  simp only [V2, V1, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
    Nat.reduceLeDiff, or_true, and_self]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- From the entry of `_int_malloc` on the second call (`malloc(50)` in `malloc_hook_ini`: `av` the main arena,
`nb` 64) to its return address: fastbin 2, smallbin 4, the unsorted bin and the binmap empty, the tcache there, the
top `T` big enough; the top is split, `T + 16` is returned, the six registers come back. -/
theorem im_second {fb S T szw sm : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at)
    (hrsp : X.cpu.gpr.rsp = S + 184#64) (hsi : X.cpu.gpr.rsi = 50#64) (hdi : X.cpu.gpr.rdi = 7940672#64)
    (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : 64 ≤ (rdq(V, 8013224#64)).toNat) (hf2 : rdq(V, 7940704#64) = 0#64)
    (hsb : rdq(V, 7940840#64) = 7940816#64)
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hgf : ∀ i < 8, Foot F.data (Addr.add (8013224#64) i))
    (htf : ∀ i < 8, Foot F.data (Addr.add (fb + 18446744073709551576#64) i))
    (hsw : ∀ i < 192, Foot Wl (Addr.add S i))
    (hT : 8029888 ≤ T.toNat) (hTS : T.toNat + 80 ≤ S.toNat)
    (htw : ∀ i < 8, Foot Wl (Addr.add (T + 8#64) i)) (hrw : ∀ i < 8, Foot Wl (Addr.add (T + 64#64 + 8#64) i))
    (hpb : ∀ i < 4, Foot F.data (Addr.add (8013220#64) i)) (hp0 : rdd(V, 8013220#64) = 0)
    (htop : rdq(V, 7940768#64) = T) (hsz : rdq(V, T + 8#64) = szw) (hsm : rdq(V, 7942856#64) = sm)
    (hle : (szw &&& 18446744073709551608#64).toNat ≤ sm.toNat) (hge : 96 ≤ (szw &&& 18446744073709551608#64).toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 184#64) = e₂.add j₂)
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vsp T szw (V2 S X.cpu.gpr V)) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs184 : ∀ i < 184, Foot Wl (Addr.add S i) := fun i hi => hsw i (by omega)
  have hsd : ∀ i < 184, Foot F.data (Addr.add S i) := fun i hi => c.hws _ (hs184 i hi)
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [hrip]; rfl)
    (vc_0 hrsp hsi hdi hS hlo hfb hgm hf2 hsb htc htb hWd hgf htf hs184) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
  have T2 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ S.toNat →
      List.map (V2 S X.cpu.gpr V) (byteAddrs x n) = List.map V (byteAddrs x n) := fun x n h =>
    V2_lo _ _ hS (by omega)
  refine (c_1115 prof fb).run c hfs hin _ hK₁ hA₁ hr₁
    (by rw [hg₁]; exact vc_1115 hS hlo hun hm0 hm1 hm2 hm3 hWd hs184 hsd) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
  refine (c_2549 prof fb).run c hfs hin _ hK₂ hA₂ hr₂
    (vc_2549 (sm := sm) (by rw [hg₂]) (by rw [hg₂]) hT (by rw [hg₂]; exact hTS) (by rw [hg₂]; exact hS) hWd
      (fun i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
      (fun i hi => c.hws _ (htw i hi)) htw hrw (by rw [hg₂]; exact hsd) hpb
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact hp0)
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact htop)
      (by rw [T2 _ _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hsz)
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact hsm) hle hge) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hax₃, hsp₃, hbx, hbp, h12, h13, h14, h15⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst hg₃
  obtain ⟨R1, R2, R3, R4, R5, R6⟩ := V2_regs S X.cpu.gpr V hS
  have esp : Y₂.cpu.gpr.rsp = S := by rw [hg₂]
  rw [esp] at hsp₃ hbx hbp h12 h13 h14 h15
  refine c.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_950 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₃]
    exact c.hws _ (off_ft hsw 184 rfl (by decide) i hi)
  · rw [hsp₃]
    have e : (S + 184#64).toNat = S.toNat + 184 := add_n _ _ (by omega)
    rw [congrArg (ofBytesLE 64) (Vsp_rd _ (by omega) (by omega) (.inr (by omega)) (.inr (by omega))),
      V2_ra _ _ _ hS]
    exact hra
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k Z t' hK' hA' hr' (by rw [hg']; exact hax₃) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg']
    show Y₃.cpu.gpr.rsp + 8 = _
    rw [hsp₃]
    bv_omega
  · rw [hg']; exact hbx.trans R1
  · rw [hg']; exact hbp.trans R2
  · rw [hg']; exact h12.trans R3
  · rw [hg']; exact h13.trans R4
  · rw [hg']; exact h14.trans R5
  · rw [hg']; exact h15.trans R6

end FV7z.Im2
