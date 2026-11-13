import FV7z.Mal.Run
import FV7z.Mhi.RunN
/-!
# The first `malloc (n)` of the process for `n ≤ 120` (PLAN.md G3, `malloc`)

- `mal_firstn`: `mal_first` with `Mhi.mhi_okn`.
- `Nr_hhn`: `Nr_hh` up to 144 bytes above the first chunk.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr corr2 size smEv smEv2)
open FV7z.Imm (imm imm_at Out add_n)
open FV7z.Im2 (Vsp VspN)
namespace FV7z.Mal
open FV7z.Mhi (Tp C2 Sz Vh mhi mhi_at)
variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

set_option maxHeartbeats 2000000 in
/-- `mal_first` for every request `n ≤ 120` (`Mhi.mhi_okn`): the top split for `nb` bytes, `nb` the chunk size of `n`
(`Im3.Cls`). -/
theorem mal_firstn {lim : Nat} {b fsb S n nb : Addr} {ks : Kst} {pad sm mx : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hin : CodeIn L mal_at mal) (hinH : CodeIn L mhi_at mhi)
    (hinP : CodeIn L Pmi.pmi_at Pmi.pmi)
    (hinG : CodeIn L Tgv.tgv_at Tgv.tgv) (hinT : CodeIn L Tci.tci_at Tci.tci) (hinI : CodeIn L imm_at imm)
    (hinS : CodeIn L Smm.smm_at Smm.smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinK : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mal_at)
    (hhook : rdq(V, 7940656#64) = mhi_at)
    (hrsp : X.cpu.gpr.rsp = S + 232#64) (hdi : X.cpu.gpr.rdi = n) (hcls : Im3.Cls n nb)
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
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 144 → Foot (N ++ Wl) a)
    (hz : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < pageUp b.toNat / 4096 * 4096 → V a = 0)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, S + 232#64) = e₂.add j₂)
    (k : ∀ (Vd V₁ M : Addr → Byte) (evs : List Event) (s₁ Z : State) (t' : Nat),
      Seg prof (withNew F N) (N ++ Wl) L s₁ o →
      Base s₁ lim (b + size pad 656#64 + C2 b pad) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem M →
      Pmi.Dat fsb (S + 200#64) 1 (Vh (S + 232#64) X.cpu.gpr (Vm X.cpu.gpr V)) Vd →
      Out (Vst Vd (S + 200#64) (toBytesLE (mhi_at.add (231 + 5)) 8)) V₁ b 656#64 (size pad 656#64) (C2 b pad) sm
        (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096)
        (S.toNat - 168) (S.toNat + 200) →
      (∀ a : Addr, a.toNat < S.toNat + 24 ∨ S.toNat + 208 ≤ a.toNat →
        M a = VspN (Tp b) (Sz b pad) nb (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)) a) →
      Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rax = Tp b + 16#64 →
      (Z.cpu.gpr.rsp = S + 240#64 ∧ Z.cpu.gpr.rbx = X.cpu.gpr.rbx ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rbp ∧
        Z.cpu.gpr.r12 = X.cpu.gpr.r12) →
      (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = b ∧ g₂.r14 = size pad 656#64 ∧
        (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂])) →
      GoG prof L o (gev ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hb47 : b.toNat < 2 ^ 47 := by omega
  have a232 := t232 S hS
  have hsp' : X.cpu.gpr.rsp.toNat = S.toNat + 232 := by rw [hrsp]; exact a232
  have VL : ∀ a : Addr, a.toNat < S.toNat + 208 ∨ S.toNat + 232 ≤ a.toNat → Vm X.cpu.gpr V a = V a :=
    fun a ha => Vm_out _ _ (by omega) (by omega)
  have R : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ S.toNat + 208 →
      List.map (Vm X.cpu.gpr V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n h => rd_eq (by omega) (fun a _ h2 => VL a (.inl (by omega)))
  have Rc : ∀ (x : Addr) (n : Nat), x.toNat < 8029888 → n ≤ 8 →
      List.map (Vm X.cpu.gpr V) (byteAddrs x n) = List.map V (byteAddrs x n) :=
    fun x n h1 h2 => R x n (by omega)
  obtain ⟨f24, f32, f40⟩ := fofs fsb (by omega) (by omega)
  obtain ⟨hpg, hbS⟩ := bnd hb47 hnb hbs
  have ho : ∀ a : Addr, ¬ (S.toNat + 208 ≤ a.toNat ∧ a.toNat < S.toNat + 232) → Vm X.cpu.gpr V a = V a :=
    fun a ha => VL a (by omega)
  have g32 : ∀ d ∈ Pmi.t32, (Tgv.ent d).toNat + 48 ≤ 7940484 := fun d hd => by
    simp only [Pmi.t32, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  have g64 : ∀ d ∈ Pmi.t64, (Tgv.ent d).toNat + 48 ≤ 7940484 := fun d hd => by
    simp only [Pmi.t64, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hfh : ∀ i < 8, Foot F.data (Addr.add (7940656#64) i) := fun i hi =>
    c.hws _ (Mhi.rng hW (7940656#64) 8 (by decide) (by decide) (by decide) i hi)
  refine mal_hook c hin hK hA hrip hinH (Mhi.lt_len (j := 0) (by decide)) (by rw [hhook, addr_add_zero])
    (by decide) hfh (by omega) (by omega) (by rw [hrsp]; exact off_ft hst 376 (sp376 S) (by omega)) ?_
  intro Z t' hKZ hAZ hrZ hgZ
  rw [addr_add_zero] at hrZ
  refine Mhi.mhi_okn (V := Vm X.cpu.gpr V) c hB hinH hinP hinG hinT hinI hinS hinD hinK hinb hKZ hAZ hrZ
    (by rw [hgZ]; exact hrsp) (by rw [hgZ]; exact hdi) hcls hsp hS hst hW hhk hcur hml hpb hgmf hft hfa hfm
    hfl hfs1 hfs hfb (by rw [Rc (7940484#64) 4 (by decide) (by decide)]; exact hmi)
    (fun d hd => (h32 d hd).out (by have := g32 d hd; omega) (by omega) ho)
    (fun d hd => (h64 d hd).out (by have := g64 d hd; omega) (by omega) ho)
    (by rw [R (fsb + 18446744073709551584#64) 1 (by rw [f32]; omega)]; exact hsd)
    (by rw [R (fsb + 24#64) 4 (by rw [f24]; omega)]; exact hmt)
    (by rw [Rc (7940672#64) 4 (by decide) (by decide)]; exact hlk)
    (by rw [R (fsb + 18446744073709551576#64) 8 (by rw [f40]; omega)]; exact htc)
    (fun k hk => by
      rw [Rc (BitVec.ofNat 64 (7940688 + 8 * k)) 8 (by rw [BitVec.toNat_ofNat]; omega) (by decide)]
      exact hfz k hk)
    (by rw [Rc (7940592#64) 8 (by decide) (by decide)]; exact htb)
    (by rw [Rc (7942816#64) 4 (by decide) (by decide)]; exact hm0)
    (by rw [Rc (7942820#64) 4 (by decide) (by decide)]; exact hm1)
    (by rw [Rc (7942824#64) 4 (by decide) (by decide)]; exact hm2)
    (by rw [Rc (7942828#64) 4 (by decide) (by decide)]; exact hm3)
    (by rw [Rc (7943128#64) 8 (by decide) (by decide)]; exact hps)
    (by rw [Rc (7940528#64) 8 (by decide) (by decide)]; exact hthr)
    (by rw [Rc (7940776#64) 8 (by decide) (by decide)]; exact hsz)
    (by rw [Rc (7940520#64) 8 (by decide) (by decide)]; exact hpad) hnb
    (by rw [Rc (7940676#64) 1 (by decide) (by decide)]; exact hfl')
    (by rw [Rc (7942872#64) 8 (by decide) (by decide)]; exact hmc)
    (by rw [Rc (curbrk) 8 (by decide) (by decide)]; exact hcb)
    (by rw [Rc (7944640#64) 4 (by decide) (by decide)]; exact hml0)
    (by rw [Rc (8013152#64) 8 (by decide) (by decide)]; exact hk0)
    (by rw [Rc (7942856#64) 8 (by decide) (by decide)]; exact hsm)
    (by rw [Rc (7940584#64) 8 (by decide) (by decide)]; exact hsb)
    (by rw [Rc (7942864#64) 8 (by decide) (by decide)]; exact hmx) hms hsu
    (by rw [Rc (8013220#64) 4 (by decide) (by decide)]; exact hp0)
    hmg hlim hbl hbs hN hh (fun a h1 h2 => by rw [VL a (.inl (by omega))]; exact hz a h1 h2) hin₂ h₂
    (by rw [rd_eq (x := S + 232#64) (n := 8) (by omega) (fun a h1 _ => VL a (.inr (by omega)))]; exact hra) ?_
  intro Vd V₁ M evs s₁ Z' t'' hc hB' hK' hA' hD hO hM hr hax hregs hev
  rw [hgZ] at hD hregs
  exact k Vd V₁ M evs s₁ Z' t'' hc hB' hK' hA' hD hO hM hr hax hregs hev

/-- `Nr_hh` up to 144 bytes above the first chunk (the split of up to 128 bytes). -/
theorem Nr_hhn {b pad : Addr} {Wl : List Rgn} (hb : b.toNat < 2 ^ 47) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47)
    (hw : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < pageUp b.toNat / 4096 * 4096 → Foot Wl a) :
    ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 144 →
      Foot (Nr b pad ++ Wl) a := by
  intro a h1 h2
  have hc : (corr b).toNat < 16 := by rw [Smm.corr_toNat]; omega
  have ec : (b + corr b).toNat = b.toNat + (corr b).toNat := by bv_omega
  rw [ec] at h1 h2
  by_cases hlt : a.toNat < pageUp b.toNat / 4096 * 4096
  · exact foot_append_iff.2 (.inr (hw a (by omega) hlt))
  · refine foot_append_iff.2 (.inl ⟨_, List.mem_singleton_self _, ?_⟩)
    obtain ⟨e, hR⟩ := brk_up (pad := pad) hb hnb
    show (BitVec.ofNat 64 (pageUp b.toNat / 4096 * 4096)).toNat ≤ a.toNat ∧
      a.toNat < (BitVec.ofNat 64 (pageUp b.toNat / 4096 * 4096)).toNat +
        (pageUp (b + size pad 656#64).toNat / 4096 * 4096 - pageUp b.toNat / 4096 * 4096)
    rw [pg_toNat hb, e]
    unfold pageUp at hlt ⊢
    omega

end FV7z.Mal
