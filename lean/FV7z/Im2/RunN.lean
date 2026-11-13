import FV7z.Im2.Run
import FV7z.Im2.HeadN
import FV7z.Im3.Holds
import FV7z.Im4.Holds
import FV7z.Im4.R1115
import FV7z.Im2.Frame
/-!
# `_int_malloc`: the second call for every request `n ≤ 1000` (PLAN.md G3, `malloc`)

- `V2n_out`, `V2n_lo`, `V2n_regs`, `V2n_ra`: the bytes of `V2n` outside the frame, the six registers read back and
  the return address.
- `im_from2549`: from 2549 to the return address, the bytes there with the frame `Fr` (`Im2.Frame`): `vc_2549n` and
  the `ret`, whatever way the size took.
- `im_secondn`: `vc_0n` (`Im3.vc_0s` for `n ≤ 8`, `Im4.vc_0m` for `121 ≤ n ≤ 1000`), `Im4.vc_1115g`, `im_from2549`
  (`Fr.v2n`); `nb` with `Im3.Cls`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Sbrk (rd_eq)
open FV7z.Imm (imm imm_at rd_off rd_off_self add_n stk_in ret_950 lt_len)
namespace FV7z.Im2
variable {F : Footprint} {Wl : List Rgn}

theorem V2n_out (S : Addr) (g : Gprs) (n nb : Addr) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) {x : Addr}
    (h : x.toNat < S.toNat + 8 ∨ S.toNat + 184 ≤ x.toNat) : V2n S g n nb V x = V x := by
  unfold V2n V1n
  repeat rw [Vst_out _ _ _ _ (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)
    (by rw [toBytesLE_length, add_n _ _ (by omega)]; omega)]

theorem V2n_lo {S x : Addr} {m : Nat} (g : Gprs) (n nb : Addr) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64)
    (h : x.toNat + m ≤ S.toNat + 8) : List.map (V2n S g n nb V) (byteAddrs x m) = List.map V (byteAddrs x m) :=
  rd_eq (by omega) fun _ _ h2 => V2n_out S g n nb V hS (.inl (by omega))

theorem V2n_ra (S : Addr) (g : Gprs) (n nb : Addr) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    rdq(V2n S g n nb V, S + 184#64) = rdq(V, S + 184#64) :=
  congrArg (ofBytesLE 64) (rd_eq (by rw [add_n _ _ (by omega)]; omega) fun _ h _ =>
    V2n_out S g n nb V hS (.inr (by rw [add_n _ _ (by omega)] at h; omega)))

theorem V2n_regs (S : Addr) (g : Gprs) (n nb : Addr) (V : Addr → Byte) (hS : S.toNat + 256 < 2 ^ 64) :
    rdq(V2n S g n nb V, S + 136#64) = g.rbx ∧ rdq(V2n S g n nb V, S + 144#64) = g.rbp ∧
      rdq(V2n S g n nb V, S + 152#64) = g.r12 ∧ rdq(V2n S g n nb V, S + 160#64) = g.r13 ∧
      rdq(V2n S g n nb V, S + 168#64) = g.r14 ∧ rdq(V2n S g n nb V, S + 176#64) = g.r15 := by
  simp only [V2n, V1n, rd_off _ hS, rd_off_self _ hS, toBytesLE_length, ofBytesLE_toBytesLE, Nat.reduceAdd,
    Nat.reduceLeDiff, or_true, and_self]

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

/-- From offset 2549 of `_int_malloc` to its return address, whatever way the size took: `av` (the main arena) in
`rbx`, `nb` in `r13`, `S` in `rsp`, the bytes `M` with the frame `Fr S G V M` (`G` the registers and `V` the bytes at
the entry); the top `T` split, `T + 16` returned, the six registers of `G` back. -/
theorem im_from2549 {fb S T szw sm nb : Addr} {G : Gprs} {M : Addr → Byte} {Y : State} {t₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L imm_at imm)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem M) (hr : Y.cpu.rip = imm_at.add 2549)
    (hbx : Y.cpu.gpr.rbx = 7940672#64) (h13 : Y.cpu.gpr.r13 = nb) (hsp : Y.cpu.gpr.rsp = S) (hfr : Fr S G V M)
    (h32 : 32 ≤ nb.toNat) (hnb : nb.toNat ≤ 8192) (hS : S.toNat + 256 < 2 ^ 64)
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
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
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (VspN T szw nb M) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = G.rbx ∧ Z.cpu.gpr.rbp = G.rbp ∧
        Z.cpu.gpr.r12 = G.r12 ∧ Z.cpu.gpr.r13 = G.r13 ∧ Z.cpu.gpr.r14 = G.r14 ∧ Z.cpu.gpr.r15 = G.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t₂ := by
  have hsd : ∀ i < 184, Foot F.data (Addr.add S i) := fun i hi => c.hws _ (hsw i (by omega))
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  have T2 : ∀ (x : Addr) (m : Nat), x.toNat + m ≤ S.toNat →
      List.map M (byteAddrs x m) = List.map V (byteAddrs x m) := fun x m h =>
    rd_eq (by omega) fun a _ h2 => hfr.out a (.inl (by omega))
  refine (c_2549 prof fb).run c hfs hin _ hK hA hr
    (vc_2549n (sm := sm) hbx h13 h32 hnb hT (by rw [hsp]; omega) (by rw [hsp]; exact hS) hWd
      (fun i hi => hW _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
      (fun i hi => c.hws _ (htw i hi)) htw hrw (by rw [hsp]; exact hsd) hpb
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact hp0)
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact htop)
      (by rw [T2 _ _ (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)]; exact hsz)
      (by rw [T2 _ _ (by rw [BitVec.toNat_ofNat]; omega)]; exact hsm) hle hge) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hax₃, hsp₃, hbx₃, hbp, h12, h13₃, h14, h15⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
  subst hg₃
  rw [hsp] at hsp₃ hbx₃ hbp h12 h13₃ h14 h15
  refine c.s_ret hK₃ hA₃ hin (lt_len (by decide)) hr₃ (ret_950 _) (fun i hi => ?_) hin₂ h₂ ?_ ?_
  · rw [hsp₃]
    exact c.hws _ (off_ft hsw 184 rfl (by decide) i hi)
  · rw [hsp₃]
    have e : (S + 184#64).toNat = S.toNat + 184 := add_n _ _ (by omega)
    rw [congrArg (ofBytesLE 64) (VspN_rd _ (by omega) (by omega) (.inr (by omega)) (.inr (by omega)) (by omega)),
      congrArg (ofBytesLE 64) (rd_eq (by rw [e]; omega) fun a h _ => hfr.out a (.inr (by rw [e] at h; omega)))]
    exact hra
  rintro Z t' hK' hA' ⟨hr', hg'⟩
  refine k Z t' hK' hA' hr' (by rw [hg']; exact hax₃) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg']
    show Y₃.cpu.gpr.rsp + 8 = _
    rw [hsp₃]
    bv_omega
  · rw [hg']; exact hbx₃.trans hfr.bx
  · rw [hg']; exact hbp.trans hfr.bp
  · rw [hg']; exact h12.trans hfr.r12
  · rw [hg']; exact h13₃.trans hfr.r13
  · rw [hg']; exact h14.trans hfr.r14
  · rw [hg']; exact h15.trans hfr.r15

/-- `im_second` for every request `n ≤ 1000` (`nb` its chunk size, `Im3.Cls`, a fastbin or smallbin size): from the
entry of `_int_malloc` on the second call (`av` the main arena) to its return address: the fastbins and the smallbins
(sizes 32 … 1008), the unsorted bin and the binmap empty, the tcache there, the top `T` big enough; the top is split,
`T + 16` is returned, the six registers come back. -/
theorem im_secondn {fb S T szw sm n nb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb)
    (hin : CodeIn L imm_at imm) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = imm_at)
    (hrsp : X.cpu.gpr.rsp = S + 184#64) (hsi : X.cpu.gpr.rsi = n) (hdi : X.cpu.gpr.rdi = 7940672#64)
    (hcls : Im3.Cls n nb) (hS : S.toNat + 256 < 2 ^ 64) (hlo : 8029888 ≤ S.toNat)
    (hfb : (fb + 18446744073709551576#64).toNat + 8 ≤ S.toNat)
    (hgm : rdq(V, 8013224#64) = 128#64)
    (hfz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64)
    (hbk : ∀ i, 2 ≤ i → i ≤ 63 →
      rdq(V, BitVec.ofNat 64 (7940776 + 16 * i)) = BitVec.ofNat 64 (7940752 + 16 * i))
    (htc : rdq(V, fb + 18446744073709551576#64) ≠ 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hun : rdq(V, 7940792#64) = 7940768#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
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
    (k : ∀ Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem
      (VspN T szw nb (V2n S X.cpu.gpr n nb V)) → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr.rax = T + 16#64 →
      (Z.cpu.gpr.rsp = S + 192#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12 ∧ Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hcase := hcls.cases
  obtain ⟨hn32, hn1008⟩ := hcls.bnd
  have hs184 : ∀ i < 184, Foot Wl (Addr.add S i) := fun i hi => hsw i (by omega)
  have hsd : ∀ i < 184, Foot F.data (Addr.add S i) := fun i hi => c.hws _ (hs184 i hi)
  have hWd : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a := fun a h1 h2 => c.hws _ (hW a h1 h2)
  -- from 1115 on, both ways
  have K : ∀ (Y : State) (t₁ : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (V1n S X.cpu.gpr nb V) →
      Y.cpu.rip = imm_at.add 1115 → Y.cpu.gpr = G1n S X.cpu.gpr n nb → GoG prof L o gev gP gE Y t₁ := by
    intro Y t₁ hK₁ hA₁ hr₁ hg₁
    refine (c_1115 prof fb).run c hfs hin _ hK₁ hA₁ hr₁
      (by rw [hg₁]; exact Im4.vc_1115g hcase hS hlo hun hm0 hm1 hm2 hm3 hWd hs184 hsd) ?_
    rintro j' g fl V₂ ⟨rfl, hbx₂, h13₂, hsp₂, rfl⟩ Y₂ t₂ hK₂ hA₂ hr₂ hg₂ -
    exact im_from2549 c hfs hin hK₂ hA₂ hr₂ (by rw [hg₂]; exact hbx₂) (by rw [hg₂]; exact h13₂)
      (by rw [hg₂]; exact hsp₂)
      (Fr.v2n S X.cpu.gpr n nb V hS) (by omega) (by omega) hS hW hsw hT hTS htw hrw hpb hp0 htop hsz hsm hle hge
      hin₂ h₂ hra k
  rcases hcls with ⟨hn, hn', rfl⟩ | ⟨hn, rfl⟩
  · by_cases h120 : n.toNat ≤ 120
    · refine (c_0 prof fb).run c hfs hin _ hK hA (by rw [hrip]; rfl)
        (vc_0n hrsp hsi hdi hn h120 hS hlo hfb hgm hfz (fun i i1 i2 => hbk i i1 (by omega)) htc htb hWd hgf htf
          hs184) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
      exact K Y t₁ hK₁ hA₁ hr₁ hg₁
    · refine (Im4.c_0 prof fb).run c hfs hin _ hK hA (by rw [hrip]; rfl)
        (Im4.vc_0m hrsp hsi hdi (by omega) hn' hS hlo hfb hgm hbk htc htb hWd hgf htf hs184) ?_
      rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
      exact K Y t₁ hK₁ hA₁ hr₁ hg₁
  · refine (Im3.c_0 prof fb).run c hfs hin _ hK hA (by rw [hrip]; rfl)
      (Im3.vc_0s rfl hrsp hsi hdi hn hS hlo hfb hgm hfz (fun i i1 i2 => hbk i i1 (by omega)) htc htb hWd hgf htf
        hs184) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y t₁ hK₁ hA₁ hr₁ hg₁ -
    exact K Y t₁ hK₁ hA₁ hr₁ hg₁

end FV7z.Im2
