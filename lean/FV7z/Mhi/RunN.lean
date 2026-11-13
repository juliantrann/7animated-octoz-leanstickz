import FV7z.Mhi.Run
import FV7z.Mhi.TailN
import FV7z.Mhi.HeadN
import FV7z.Im5.RunA
/-!
# `malloc_hook_ini (n)` for `n ≤ 4104`, the whole run (PLAN.md G3, `malloc`)

- `sz_okn`: the top after the first `_int_malloc` has at least 1040 bytes and at least `mp_.top_pad + 32`.
- `cXn`, `t72n`: offsets of the 64 tcache counts and of the split.
- `mhi_okn`: `mhi_headn`, `Tci.tci_ok`, `mhi_tailn`: as `mhi_ok`, the top split for `nb` bytes (`VspN`, `nb` the
  chunk size of `n`, `Im5.ClsA`), the fastbins 0 at the entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr corr2 size smEv smEv2)
open FV7z.Imm (imm imm_at Out add_n)
open FV7z.Im2 (Vsp VspN)
open FV7z.Tci (K5 mt)
namespace FV7z.Mhi
variable {F : Footprint} {Wl : List Rgn}

/-- `sz_ok` with the lower bounds 1040 and `pad + 32` (the split of up to 1008, or `pad`, bytes leaves a chunk). -/
theorem sz_okn {b pad sm : Addr} (hb : b.toNat < 2 ^ 47) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47)
    (hsm : sm.toNat < 2 ^ 47) :
    (Sz b pad &&& 18446744073709551608#64).toNat ≤ (sm + size pad 656#64 + C2 b pad).toNat ∧
      1040 ≤ (Sz b pad &&& 18446744073709551608#64).toNat ∧
      pad.toNat + 32 ≤ (Sz b pad &&& 18446744073709551608#64).toNat := by
  have hR : (size pad 656#64).toNat = (4127 + pad.toNat + 656) / 4096 * 4096 :=
    Smm.size_toNat (pad := pad) (nb := 656#64) (by show 656 + pad.toNat + 4127 < 2 ^ 47; omega)
  have hc := Smm.corr_toNat b
  have h2 := Smm.corr2_toNat b (corr b) (size pad 656#64) (by omega)
  show ((((b + size pad 656#64 - (b + corr b) + corr2 b (corr b) (size pad 656#64) ||| 1#64)
      &&& 18446744073709551608#64) - 656#64 ||| 1#64) &&& 18446744073709551608#64).toNat ≤
      (sm + size pad 656#64 + corr2 b (corr b) (size pad 656#64)).toNat ∧
    1040 ≤ ((((b + size pad 656#64 - (b + corr b) + corr2 b (corr b) (size pad 656#64) ||| 1#64)
      &&& 18446744073709551608#64) - 656#64 ||| 1#64) &&& 18446744073709551608#64).toNat ∧
    pad.toNat + 32 ≤ ((((b + size pad 656#64 - (b + corr b) + corr2 b (corr b) (size pad 656#64) ||| 1#64)
      &&& 18446744073709551608#64) - 656#64 ||| 1#64) &&& 18446744073709551608#64).toNat
  generalize corr2 b (corr b) (size pad 656#64) = C at *
  generalize size pad 656#64 = R at *
  generalize corr b = c at *
  have hv : (b + R - (b + c) + C).toNat = R.toNat + C.toNat - c.toNat := by bv_omega
  have hs : (sm + R + C).toNat = sm.toNat + R.toNat + C.toNat := by bv_omega
  have hy : ((b + R - (b + c) + C ||| 1#64) &&& 18446744073709551608#64).toNat =
      (R.toNat + C.toNat - c.toNat) / 8 * 8 := by rw [or1_m8, hv]
  rw [or1_m8, sub656 _ _ hy (by omega), hs]
  omega

/-- The tcache counts of the 64 bins. -/
theorem cXn {b : Addr} (hb : b.toNat < 2 ^ 47) (i : Nat) (hi : i < 64) :
    (b + corr b + 16#64 + BitVec.ofNat 64 (2 * i)).toNat = b.toNat + (corr b).toNat + 16 + 2 * i := by
  have := (mt b hb).2.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, (mt b hb).1]; omega

/-- The size word after the split of `nb` bytes. -/
theorem t72n {b nb : Addr} (hb : b.toNat < 2 ^ 47) (h : nb.toNat ≤ 4112) :
    (Tp b + nb + 8#64).toNat = b.toNat + (corr b).toNat + 664 + nb.toNat := by
  have := Smm.corr_toNat b
  show (b + corr b + 656#64 + nb + 8#64).toNat = _
  bv_omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

set_option maxHeartbeats 2000000 in
/-- `mhi_ok` for every request `n ≤ 4104`: `_int_malloc` splits the top for `nb` bytes (`VspN`, `nb` the chunk size
of `n`, `Im5.ClsA`; `nb ≤ 1008` or `nb ≤ mp_.top_pad`); the fastbins are 0 at the entry. -/
theorem mhi_okn {lim : Nat} {b fsb S n nb : Addr} {ks : Kst} {pad sm mx : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hin : CodeIn L mhi_at mhi) (hinP : CodeIn L Pmi.pmi_at Pmi.pmi)
    (hinG : CodeIn L Tgv.tgv_at Tgv.tgv) (hinT : CodeIn L Tci.tci_at Tci.tci) (hinI : CodeIn L imm_at imm)
    (hinS : CodeIn L Smm.smm_at Smm.smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinK : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mhi_at)
    (hrsp : X.cpu.gpr.rsp = S + 232#64) (hdi : X.cpu.gpr.rdi = n) (hcls : Im5.ClsA n nb)
    (hsp : 8029888 + 168 ≤ S.toNat) (hS : S.toNat + 512 < 2 ^ 64)
    (hst : ∀ i < 408, Foot Wl (Addr.add (S - 168) i))
    (hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a)
    (hhk : ∀ i < 8, Foot Wl (Addr.add (8013152#64) i))
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot Wl (Addr.add (7944640#64) i))
    (hpb : ∀ i < 4, Foot Wl (Addr.add (8013220#64) i)) (hgmf : ∀ i < 8, Foot Wl (Addr.add (8013224#64) i))
    (hft : ∀ i < 8, Foot Wl (Addr.add (fsb + 18446744073709551576#64) i))
    (hfa : ∀ i < 8, Foot Wl (Addr.add (fsb + 18446744073709551592#64) i))
    (hfm : ∀ i < 4, Foot Wl (Addr.add (fsb + 24#64) i))
    (hfl : ∀ i < 8, Foot F.data (Addr.add (fsb + 40#64) i))
    (hfs1 : ∀ i < 1, Foot F.data (Addr.add (fsb + 18446744073709551584#64) i))
    (hfs : 8029888 + 40 ≤ fsb.toNat) (hfb : fsb.toNat + 48 ≤ b.toNat)
    (hmi : (rdd(V, 7940484#64)).msb = true)
    (h32 : ∀ d ∈ Pmi.t32, Tgv.Unset F V d) (h64 : ∀ d ∈ Pmi.t64, Tgv.UnsetW F V d)
    (hsd : ofBytesLE 8 ((byteAddrs (fsb + 18446744073709551584#64) 1).map V) = 0#8)
    (hmt : rdd(V, fsb + 24#64) = 0) (hlk : rdd(V, 7940672#64) = 0)
    (htc : rdq(V, fsb + 18446744073709551576#64) = 0#64)
    (hfz : ∀ k < 7, rdq(V, BitVec.ofNat 64 (7940688 + 8 * k)) = 0#64) (htb : rdq(V, 7940592#64) = 64#64)
    (hm0 : rdd(V, 7942816#64) = 0) (hm1 : rdd(V, 7942820#64) = 0) (hm2 : rdd(V, 7942824#64) = 0)
    (hm3 : rdd(V, 7942828#64) = 0)
    (hps : rdq(V, 7943128#64) = 4096#64) (hthr : 656 < (rdq(V, 7940528#64)).toNat)
    (hsz : rdq(V, 7940776#64) = 0#64)
    (hpad : rdq(V, 7940520#64) = pad) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47)
    (hfl' : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b) (hml0 : rdd(V, 7944640#64) = 0)
    (hk0 : rdq(V, 8013152#64) = 0#64) (hsm : rdq(V, 7942856#64) = sm) (hsb : rdq(V, 7940584#64) = 0#64)
    (hmx : rdq(V, 7942864#64) = mx) (hms : mx.toNat ≤ sm.toNat) (hsu : sm.toNat < 2 ^ 47)
    (hp0 : rdd(V, 8013220#64) = 0)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlim : pageUp (b + size pad 656#64).toNat / 4096 ≤ lim)
    (hbl : 8029888 ≤ b.toNat)
    (hbs : (b + size pad 656#64).toNat + 4096 + 168 ≤ S.toNat)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096))
    (hpd : nb.toNat ≤ 1008 ∨ nb.toNat ≤ pad.toNat)
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + nb.toNat + 16 →
      Foot (N ++ Wl) a)
    (hz : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < pageUp b.toNat / 4096 * 4096 → V a = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 232#64) = e₂.add j₂)
    (k : ∀ (Vd V₁ M : Addr → Byte) (evs : List Event) (s₁ Z : State) (t' : Nat),
      Seg prof (withNew F N) (N ++ Wl) L s₁ o →
      Base s₁ lim (b + size pad 656#64 + C2 b pad) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem M →
      Pmi.Dat fsb (S + 200#64) 1 (Vh (S + 232#64) X.cpu.gpr V) Vd →
      Out (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) V₁ b 656#64 (size pad 656#64) (C2 b pad) sm
        (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096)
        (S.toNat - 168) (S.toNat + 200) →
      (∀ a : Addr, a.toNat < S.toNat + 24 ∨ S.toNat + 208 ≤ a.toNat →
        M a = VspN (Tp b) (Sz b pad) nb (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)) a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = Tp b + 16#64 →
      (Z.cpu.gpr.rsp = S + 240#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12) →
      (Z.cpu.gpr.r13 = X.cpu.gpr.r13 ∧ Z.cpu.gpr.r14 = X.cpu.gpr.r14 ∧ Z.cpu.gpr.r15 = X.cpu.gpr.r15) →
      (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = b ∧ g₂.r14 = size pad 656#64 ∧
        (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂])) →
      GoG prof L o (gev ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hb47 : b.toNat < 2 ^ 47 := by omega
  obtain ⟨hle, hge, hgp⟩ := sz_okn hb47 hnb hsu
  obtain ⟨hn32, hn4112⟩ := hcls.bnd
  obtain ⟨a232, e200, m64, a200, a208, a16, q208, q16, q232, q240, p1, p2, p3, q24⟩ := sof S hS (by omega)
  have h656 : (656#64 : BitVec 64).toNat = 656 := rfl
  have hsn := Smm.size_toNat (pad := pad) (nb := 656#64) (by rw [h656]; omega)
  have hbR : (b + size pad 656#64).toNat = b.toNat + (size pad 656#64).toNat := by
    rw [BitVec.toNat_add]
    omega
  have hhi : b.toNat + 688 ≤ pageUp (b + size pad 656#64).toNat / 4096 * 4096 ∧
      pageUp (b + size pad 656#64).toNat / 4096 * 4096 + 168 ≤ S.toNat := by
    unfold pageUp
    omega
  have hlo : b.toNat ≤ pageUp b.toNat / 4096 * 4096 := by unfold pageUp; omega
  have hf40 := f40 fsb (by omega)
  have hf32 := f32 fsb (by omega)
  have hf24 := Tci.f24 fsb (by omega)
  have hfp := f24' fsb (by omega)
  have hclh : (9 ≤ n.toNat ∧ n.toNat ≤ 4104 ∧ n + 23#64 &&& 18446744073709551600#64 = nb) ∨
      (n.toNat ≤ 8 ∧ nb = 32#64) := by
    rcases hcls with (⟨h1, h2, h3⟩ | h) | ⟨h1, h2, h3⟩
    · exact .inl ⟨h1, by omega, h3⟩
    · exact .inr h
    · exact .inl ⟨by omega, h2, h3⟩
  refine mhi_headn c hB.fsb hin hinP hinG hinT hK hA hrip hdi hclh (by rw [hrsp, a232]; omega) (by omega)
    (by rw [hrsp, a232]; omega) (by rw [hrsp, m64]; exact off_ft hst 336 rfl (by decide)) hfl hfa hW hgmf
    (fun i hi => c.hws _ (hft i hi)) hfs1 hmi h32 h64 htc hsd ?_
  rintro Vd Z₀ t₀ hK₀ hA₀ hD hr₀ sp₀ bx₀ bp₀ ⟨r12₀, r13₀, r14₀, r15₀⟩
  rw [hrsp, e200] at hA₀ hD sp₀
  have l8 : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  have hpg : pageUp b.toNat / 4096 * 4096 + 168 ≤ S.toNat := by unfold pageUp; omega
  have hcu : curbrk.toNat = 8014904 := by decide
  -- the bytes at the entry of `tcache_init`
  have TV : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ S.toNat + 200 →
      List.map (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) (byteAddrs x n) =
        List.map Vd (byteAddrs x n) := fun x n h =>
    rd_Vst _ _ _ _ _ (by rw [l8, a200]; omega) (by omega) (.inr (by rw [a200]; omega))
  have W2 : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ S.toNat + 168 →
      (∀ m, x.toNat ≤ m → m < x.toNat + n → ¬ Pmi.Wr fsb m ∧ (m < 7940656 ∨ 7940664 ≤ m)) →
      List.map (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) (byteAddrs x n) =
        List.map V (byteAddrs x n) := fun x n h hw =>
    (TV x n (by omega)).trans (rd_eq (by omega) fun a a1 a2 =>
      (hD.out a (by rw [a200]; omega) (hw _ a1 a2).1).trans
        (Vh_out _ _ _ (by rw [a232]; omega) (by rw [a232]; omega) (hw _ a1 a2).2))
  have tn : ∀ x : Nat, x < 2 ^ 64 → (BitVec.ofNat 64 x).toNat = x := fun x h => by
    rw [BitVec.toNat_ofNat]; omega
  have W1 : ∀ (x n : Nat), x + n ≤ S.toNat + 168 →
      (∀ m, x ≤ m → m < x + n → ¬ Pmi.Wr fsb m ∧ (m < 7940656 ∨ 7940664 ≤ m)) →
      List.map (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) (byteAddrs (BitVec.ofNat 64 x) n) =
        List.map V (byteAddrs (BitVec.ofNat 64 x) n) := fun x n h hw =>
    W2 _ _ (by rw [tn x (by omega)]; omega) fun m h1 h2 => hw m (by rw [tn x (by omega)] at h1; exact h1)
      (by rw [tn x (by omega)] at h2; exact h2)
  have T1 : ∀ (x n : Nat), x + n ≤ S.toNat + 200 →
      List.map (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) (byteAddrs (BitVec.ofNat 64 x) n) =
        List.map Vd (byteAddrs (BitVec.ofNat 64 x) n) := fun x n h =>
    TV _ _ (by rw [tn x (by omega)]; omega)
  refine Tci.tci_ok (pad := pad) (sm := sm) (mx := mx) (N := N) c hB hinT hinI hinS hinD hinK hinb hK₀ hA₀ hr₀ sp₀
    hsp (by omega) (fun i hi => hst i (by omega)) hW hhk hcur hml hpb (fun i hi => c.hws _ (hgmf i hi)) hft hfa hfm
    hfs (by omega)
    (by rw [congrArg (ofBytesLE 64) (TV _ 8 (by rw [hf24]; omega))]; exact hD.tls)
    (by
      rw [congrArg (ofBytesLE 32) (W2 _ 4 (by rw [hfp]; omega) fun m h1 h2 =>
        ⟨by unfold Pmi.Wr; rw [hfp] at h1 h2; omega, by rw [hfp] at h1; omega⟩)]
      exact hmt)
    (by rw [congrArg (ofBytesLE 32) (W1 7940672 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hlk)
    (by rw [congrArg (ofBytesLE 64) (T1 8013224 8 (by omega)), hD.gmf]; decide)
    (by rw [congrArg (ofBytesLE 64) (T1 7941432 8 (by omega))]; exact (hD.bins 40 (by decide)).2)
    (by
      rw [congrArg (ofBytesLE 64) (W2 _ 8 (by rw [hf40]; omega) fun m h1 h2 =>
        ⟨by unfold Pmi.Wr; rw [hf40] at h1 h2; omega, by rw [hf40] at h1; omega⟩)]
      exact htc)
    (by rw [congrArg (ofBytesLE 64) (T1 7940792 8 (by omega))]; exact (hD.bins 0 (by decide)).2)
    (by rw [congrArg (ofBytesLE 32) (W1 7942820 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hm1)
    (by rw [congrArg (ofBytesLE 32) (W1 7942824 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hm2)
    (by rw [congrArg (ofBytesLE 32) (W1 7942828 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hm3)
    (by rw [congrArg (ofBytesLE 64) (W1 7943128 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hps)
    (by rw [congrArg (ofBytesLE 64) (W1 7940528 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hthr)
    (by rw [congrArg (ofBytesLE 64) (T1 7940768 8 (by omega))]; exact hD.top)
    (by rw [congrArg (ofBytesLE 64) (W1 7940776 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hsz)
    (by rw [congrArg (ofBytesLE 64) (W1 7940520 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hpad) hnb
    (by rw [W1 7940676 1 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩]; exact hfl')
    (by rw [congrArg (ofBytesLE 32) (T1 7940680 4 (by omega))]; exact hD.flg)
    (by rw [congrArg (ofBytesLE 64) (W1 7942872 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hmc)
    (by
      rw [congrArg (ofBytesLE 64) (W2 _ 8 (by rw [hcu]; omega) fun m h1 h2 =>
        ⟨by unfold Pmi.Wr; rw [hcu] at h1 h2; omega, by rw [hcu] at h1; omega⟩)]
      exact hcb)
    (by rw [congrArg (ofBytesLE 32) (W1 7944640 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hml0)
    (by rw [congrArg (ofBytesLE 64) (W1 8013152 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hk0)
    (by rw [congrArg (ofBytesLE 64) (W1 7942856 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hsm)
    (by rw [congrArg (ofBytesLE 64) (W1 7940584 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hsb)
    (by rw [congrArg (ofBytesLE 64) (W1 7942864 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hmx) hms hsu
    (by rw [congrArg (ofBytesLE 32) (W1 8013220 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hp0)
    hmg hlim hbl hbs hN (fun a h1 h2 => hh a h1 (by omega))
    (fun a h1 h2 => by
      rw [Vst_out _ _ _ _ (by rw [l8, a200]; omega) (.inl (by rw [a200]; omega)),
        hD.out a (by rw [a200]; omega) (by unfold Pmi.Wr; omega),
        Vh_out _ _ _ (by rw [a232]; omega) (by rw [a232]; omega) (by omega)]
      exact hz a h1 h2)
    hin (lt_len (j := 231 + 5) (by decide))
    (by rw [rd_Vst_self _ _ _ (l8 _) (by rw [a200]; omega)]; exact ofBytesLE_toBytesLE (n := 8) rfl _) ?_
  intro V₁ g₁ g₂ evs s₁ Z t' c' hB' hK' hA' hr' ⟨spZ, bpZ, k5⟩ hO hcz hg1 hg2 hev
  obtain ⟨-, hab, hc16, -⟩ := mt b hb47
  obtain ⟨t0, t8, -, -, -⟩ := tof b hb47
  obtain ⟨u1, u2, u3, -⟩ := r4 (S + 232#64) (by rw [a232]; omega)
  have hM0 : b + corr b + 16#64 ≠ 0 := fun h => by
    have h' := congrArg BitVec.toNat h
    rw [(mt b hb47).1, show (0 : BitVec 64).toNat = 0 from rfl] at h'
    omega
  -- reads after `tcache_init`
  have MV : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 → (x.toNat + n ≤ fsb.toNat - 40 ∨ fsb.toNat - 32 ≤ x.toNat) →
      List.map (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)) (byteAddrs x n) =
        List.map V₁ (byteAddrs x n) := fun x n h1 h2 =>
    rd_Vst _ _ _ _ _ (by rw [l8, hf40]; omega) h1 (by rw [l8, hf40]; omega)
  have OS : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ b.toNat →
      (∀ m, x.toNat ≤ m → m < x.toNat + n → ¬ (7940584 ≤ m ∧ m < 7940592) ∧ ¬ (7940768 ≤ m ∧ m < 7940776) ∧
        ¬ (7942856 ≤ m ∧ m < 7942872) ∧ ¬ (8014904 ≤ m ∧ m < 8014912)) →
      List.map V₁ (byteAddrs x n) =
        List.map (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) (byteAddrs x n) := fun x n h hw =>
    rd_eq (by omega) fun a a1 a2 => hO.same a (by omega) (by omega) (hw _ a1 a2).2.2.2 (hw _ a1 a2).1
      (hw _ a1 a2).2.1 (hw _ a1 a2).2.2.1 (by omega) (by rw [h656]; omega)
  have HI : ∀ (x : Addr) (n : Nat), S.toNat + 208 ≤ x.toNat → x.toNat + n ≤ 2 ^ 64 →
      List.map (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)) (byteAddrs x n) =
        List.map (Vh (S + 232#64) X.cpu.gpr V) (byteAddrs x n) := fun x n h1 h2 =>
    rd_eq h2 fun a a1 a2 => by
      rw [Vst_out _ _ _ _ (by rw [l8, hf40]; omega) (.inr (by rw [l8, hf40]; omega)),
        hO.same a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [h656]; omega),
        Vst_out _ _ _ _ (by rw [l8, a200]; omega) (.inr (by rw [l8, a200]; omega))]
      exact hD.out a (by rw [a200]; omega) (by unfold Pmi.Wr; omega)
  have E1 : ∀ (x n : Nat), x + n ≤ 7940656 ∨ (7940664 ≤ x ∧ x + n ≤ 8013220 + 4) →
      (∀ m, x ≤ m → m < x + n → ¬ Pmi.Wr fsb m ∧ ¬ (7940584 ≤ m ∧ m < 7940592) ∧ ¬ (7940768 ≤ m ∧ m < 7940776) ∧
        ¬ (7942856 ≤ m ∧ m < 7942872)) →
      List.map (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8))
        (byteAddrs (BitVec.ofNat 64 x) n) = List.map V (byteAddrs (BitVec.ofNat 64 x) n) := fun x n h hw => by
    have hx := tn x (by omega)
    rw [MV _ _ (by rw [hx]; omega) (.inl (by rw [hx]; omega)),
      OS _ _ (by rw [hx]; omega) fun m h1 h2 => by
        rw [hx] at h1 h2
        exact ⟨(hw m h1 h2).2.1, (hw m h1 h2).2.2.1, (hw m h1 h2).2.2.2, by omega⟩]
    exact W1 x n (by omega) fun m h1 h2 => ⟨(hw m h1 h2).1, by omega⟩
  have D1 : ∀ (x n : Nat), x + n ≤ 8013232 →
      (∀ m, x ≤ m → m < x + n → ¬ (7940584 ≤ m ∧ m < 7940592) ∧ ¬ (7940768 ≤ m ∧ m < 7940776) ∧
        ¬ (7942856 ≤ m ∧ m < 7942872)) →
      List.map (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8))
        (byteAddrs (BitVec.ofNat 64 x) n) = List.map Vd (byteAddrs (BitVec.ofNat 64 x) n) := fun x n h hw => by
    have hx := tn x (by omega)
    rw [MV _ _ (by rw [hx]; omega) (.inl (by rw [hx]; omega)),
      OS _ _ (by rw [hx]; omega) fun m h1 h2 => by
        rw [hx] at h1 h2
        exact ⟨(hw m h1 h2).1, (hw m h1 h2).2.1, (hw m h1 h2).2.2, by omega⟩]
    exact T1 x n (by omega)
  have cX := cXn hb47
  have t72n := t72n (b := b) hb47 hn4112
  refine mhi_tailn (S := S + 16#64) (T := Tp b) (szw := Sz b pad) (sm := sm + size pad 656#64 + C2 b pad)
    (C := b + corr b + 16#64) c' hB'.fsb hin hinI hK' hA' hcls (Im5.secA hcls) hr'
    (k5.1.trans bx₀) (bpZ.trans bp₀)
    (spZ.trans q208)
    (by rw [a16]; omega) (by rw [a16]; omega) (by rw [hf40, a16]; omega)
    (by rw [rd_Vst_self _ _ _ (l8 _) (by rw [hf40]; omega)]; exact ofBytesLE_toBytesLE (n := 8) rfl _) hM0
    (fun i hi => by
      have c4 := cX i hi
      rw [MV _ 2 (by rw [c4]; omega) (.inr (by rw [c4]; omega))]
      exact z16 fun j hj => hcz _ (by rw [Tci.at_add _ _ (by rw [c4]; omega), c4]; omega)
        (by rw [Tci.at_add _ _ (by rw [c4]; omega), c4]; omega))
    (fun i hi j hj => by
      have c4 := cX i hi
      exact c'.hws _ (hh _ (by rw [Tci.at_add _ _ (by rw [c4]; omega), c4]; omega)
        (by rw [Tci.at_add _ _ (by rw [c4]; omega), c4]; omega)))
    (by
      rw [congrArg (ofBytesLE 32) (MV _ 4 (by rw [hfp]; omega) (.inr (by rw [hfp]; omega))),
        congrArg (ofBytesLE 32) (OS _ 4 (by rw [hfp]; omega) fun m h1 h2 => by rw [hfp] at h1 h2; omega),
        congrArg (ofBytesLE 32) (W2 _ 4 (by rw [hfp]; omega) fun m h1 h2 =>
          ⟨by unfold Pmi.Wr; rw [hfp] at h1 h2; omega, by rw [hfp] at h1; omega⟩)]
      exact hmt)
    (fun i hi => c'.hws _ (foot_append_iff.2 (.inr (hfm i hi))))
    (by rw [congrArg (ofBytesLE 64) (D1 8013224 8 (by omega) fun m h1 h2 => by omega)]; exact hD.gmf)
    (by rw [congrArg (ofBytesLE 32) (D1 7940680 4 (by omega) fun m h1 h2 => by omega)]; exact hD.flg)
    (fun k hk => by
      rw [congrArg (ofBytesLE 64) (E1 (7940688 + 8 * k) 8 (by omega) fun m h1 h2 =>
        ⟨by unfold Pmi.Wr; omega, by omega⟩)]
      exact hfz k hk)
    (fun i i1 i2 => by
      rw [congrArg (ofBytesLE 64) (D1 (7940776 + 16 * i) 8 (by omega) fun m h1 h2 => by omega)]
      have hb := (hD.bins (i - 1) (by omega)).2
      rw [show 7940792 + 16 * (i - 1) = 7940776 + 16 * i by omega,
        show 7940768 + 16 * (i - 1) = 7940752 + 16 * i by omega] at hb
      exact hb)
    (fun i i1 i2 => by
      rw [congrArg (ofBytesLE 64) (D1 (7940768 + 16 * i) 8 (by omega) fun m h1 h2 => by omega)]
      have hb := (hD.bins (i - 1) (by omega)).1
      rw [show 7940784 + 16 * (i - 1) = 7940768 + 16 * i by omega,
        show 7940768 + 16 * (i - 1) = 7940752 + 16 * i by omega] at hb
      exact hb)
    (by rw [congrArg (ofBytesLE 64) (E1 7940592 8 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact htb)
    (by rw [congrArg (ofBytesLE 64) (D1 7940792 8 (by omega) fun m h1 h2 => by omega)]
        exact (hD.bins 0 (by decide)).2)
    (by rw [congrArg (ofBytesLE 32) (E1 7942816 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hm0)
    (by rw [congrArg (ofBytesLE 32) (E1 7942820 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hm1)
    (by rw [congrArg (ofBytesLE 32) (E1 7942824 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hm2)
    (by rw [congrArg (ofBytesLE 32) (E1 7942828 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hm3)
    (fun a h1 h2 => foot_append_iff.2 (.inr (hW a h1 h2)))
    (fun i hi => c'.hws _ (foot_append_iff.2 (.inr (hgmf i hi))))
    (fun i hi => c'.hws _ (foot_append_iff.2 (.inr (hft i hi))))
    (off_ft (fun i hi => foot_append_iff.2 (.inr (hst i hi))) 184 q16 (by decide))
    (by rw [t0]; omega) (by rw [t0, a16]; omega)
    (rng hh _ 8 (by rw [t8, hab]; omega) (by rw [t8, hab]; omega) (by rw [t8]; omega))
    (rng hh _ 8 (by rw [t72n, hab]; omega) (by rw [t72n, hab]; omega) (by rw [t72n]; omega))
    (fun i hi => c'.hws _ (foot_append_iff.2 (.inr (hpb i hi))))
    (by rw [congrArg (ofBytesLE 32) (E1 8013220 4 (by omega) fun m h1 h2 => ⟨by unfold Pmi.Wr; omega, by omega⟩)]
        exact hp0)
    (by rw [congrArg (ofBytesLE 64) (MV _ 8 (by decide) (.inl (by simp only [BitVec.toNat_ofNat]; omega)))]
        exact hO.top)
    (by rw [congrArg (ofBytesLE 64) (MV _ 8 (by rw [t8]; omega) (.inr (by rw [t8]; omega)))]; exact hO.tsz)
    (by rw [congrArg (ofBytesLE 64) (MV _ 8 (by decide) (.inl (by simp only [BitVec.toNat_ofNat]; omega)))]
        exact hO.sys)
    hle (by omega) hin₂ h₂
    (by
      rw [q232, congrArg (ofBytesLE 64) (HI _ 8 (by rw [a232]; omega) (by rw [a232]; omega)),
        congrArg (ofBytesLE 64) (rd_eq (V := V) (by rw [a232]; omega) fun a a1 a2 =>
          Vh_hi _ _ _ (by rw [a232]; omega) a1)]
      exact hra) ?_
  rintro M Z' t'' hK'' hA'' hM hr'' hax ⟨sp, bx, bp, r12⟩ ⟨r13', r14', r15'⟩
  obtain ⟨v1, v2, v3⟩ := Vh_regs (S + 232#64) X.cpu.gpr V (by rw [a232]; omega)
  refine k Vd V₁ M evs s₁ Z' t'' c' hB' hK'' hA'' hD hO (fun a ha => hM a (by rw [a16]; omega)) hr'' hax
    ⟨sp.trans q240, ?_, ?_, ?_⟩
    ⟨r13'.trans (k5.2.2.1.trans r13₀), r14'.trans (k5.2.2.2.1.trans r14₀), r15'.trans (k5.2.2.2.2.trans r15₀)⟩
    ⟨g₁, g₂, hg1, hg2.1, hg2.2, hev⟩
  · rw [bx, p1, congrArg (ofBytesLE 64) (HI _ 8 (by rw [u3, a232]; omega) (by rw [u3, a232]; omega))]
    exact v1
  · rw [bp, p2, congrArg (ofBytesLE 64) (HI _ 8 (by rw [u2, a232]; omega) (by rw [u2, a232]; omega))]
    exact v2
  · rw [r12, p3, congrArg (ofBytesLE 64) (HI _ 8 (by rw [u1, a232]; omega) (by rw [u1, a232]; omega))]
    exact v3

end FV7z.Mhi
