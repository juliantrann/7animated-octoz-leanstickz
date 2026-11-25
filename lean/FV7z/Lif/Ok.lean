import FV7z.Lif.Nb
import FV7z.Ndi.Hpa
/-!
# `__libc_init_first` with `_dl_non_dynamic_init` (PLAN.md G3, startup)

`lif_ok`: `__libc_init_first` from its entry to its return address, `Lif.lif_a` to the `call` of
`_dl_non_dynamic_init` (`sp` its stack pointer, the entry's `rsp` less 152), `ndi_ok`, then `Lif.lif_nb`. The
hypotheses of `ndi_ok` are kept on the bytes `W` and the registers `gY` at its entry; the bytes at its return are
`NdiRet` of `W`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Smm (corr size smEv smEv2)
open FV7z.Mhi (Tp C2 Sz)
open FV7z.Mal (MPre After Hp GlR)
open FV7z.Gor (MCx Vg Vg_lo Lo nbOf nbOf_bnd lay foot_wn foot_wnN gEv gor_at gor)
namespace FV7z.Ndi

set_option maxRecDepth 8192

/-- The bytes `W₂` at the return of `_dl_non_dynamic_init` from those at its entry `W` (`ndi_ok`'s continuation):
`lV (bV U m)` outside the scratch below `sp`, `U` the bytes `hV W' …` on the image, the GOT page, from `sp` up and on
the brk below the TLS block, `W'` the entry's (`fV`) below the break and where `Cx` reads. -/
def NdiRet (W : Addr → Byte) (sp : Addr) (g : Gprs) (b fsb : Addr) (W₂ : Addr → Byte) : Prop :=
  ∃ (W' U : Addr → Byte) (m : Nat) (r : Addr), Eqo sp W₂ (lV (bV U m)) ∧
    (∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
      Mal.Kf fsb a) → U a = hV W' r 4194368#64 8#64 a) ∧
    (∀ a : Addr, Lo b fsb a → W' a = fV W sp g a) ∧ Same sp (fV W sp g) W'

theorem s152 (sp : Addr) : sp + 152#64 - 32#64 = sp + 120#64 := by bv_omega

/-- The return address `__libc_init_first` leaves for `_dl_non_dynamic_init`, through the stores of its prologue. -/
theorem lif_ret {V W : Addr → Byte} {g gY : Gprs} {sp : Addr} (hR : g.rsp = sp + 152#64)
    (hs : sp.toNat + 160 ≤ 2 ^ 64)
    (hW : W = Vst (Lif.LifMem V g) (g.rsp - 32#64) (toBytesLE (Lif.lif_at.add 70) 8)) :
    rdq(fV W sp gY, sp + 120#64) = Lif.lif_at.add 70 := by
  have s120 : (sp + 120#64).toNat = sp.toNat + 120 := by bv_omega
  have e : g.rsp - 32#64 = sp + 120#64 := by rw [hR]; exact s152 sp
  have q : rdq(fV W sp gY, sp + 120#64) = rdq(W, sp + 120#64) := Lif.rq_congr fun i hi => by
    have := toNat_add_of_fits (a := sp + 120#64) (n := 8) hi (by omega)
    exact fV_out (by omega) (.inr (by omega))
  rw [q, hW, e, FV7z.Sga.vs (toBytesLE_length _ _) (by omega)]
  exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _

/-- `Hp` of the bytes `U` at the end of `_dl_non_dynamic_init`'s body, on the bytes after `__libc_init_first`'s
`__init_misc` and `__libc_init_secure`'s TLS stores: `Hp` reads below `hi`, apart from the scratch, the variables `nv`,
`__init_misc`'s two words and the TLS words below the tcache. -/
theorem hp_lif {F : Footprint} {Wl : List Rgn} {fb : Addr} {hi m n : Nat} {U W₂ : Addr → Byte} {sp a0 s : Addr}
    {g : Gprs} {ca cb cc : BitVec 64} (h : Hp F Wl fb hi m U) (hm : 16 ≤ m) (hsp : hi + 72 ≤ sp.toNat)
    (hg : g.rsp = sp + 128#64) (hs : sp.toNat + 128 < 2 ^ 64) (hE : Eqo sp W₂ (lV (bV U n))) :
    Hp F Wl fb hi m (Cti.CtMem (Lif.bcV W₂ g a0 s) fb ca cb cc) := by
  obtain ⟨C, T, hf1, hf2, hc1, hc2, hT, hTh, hhi, -, -, hW⟩ := h.cut hm
  have e48 : (fb - 48#64).toNat = fb.toNat - 48 := by bv_omega
  have e56 : (fb - 56#64).toNat = fb.toNat - 56 := by bv_omega
  have e64 : (fb - 64#64).toNat = fb.toNat - 64 := by bv_omega
  have hgr : g.rsp.toNat = sp.toNat + 128 := by rw [hg, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  refine hW _ fun a ha => ?_
  unfold Mal.HpF Mal.GlF at ha
  unfold Cti.CtMem
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e64]; omega) (by rw [toBytesLE_length, e64]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e56]; omega) (by rw [toBytesLE_length, e56]; omega),
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, e48]; omega) (by rw [toBytesLE_length, e48]; omega),
    Lif.bcV_out (by omega) (by omega) (by omega), hE a (by unfold Scr; omega)]
  refine lV_gk (bV_gk U n) a ?_
  cases hv : nv a.toNat
  · rfl
  · simp only [nv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hv
    omega

variable {prof : Profile} {F : Footprint} {Wl N : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64}

set_option maxHeartbeats 1600000 in
/-- `__libc_init_first (argc, argv, envp)` from its entry to its return address: `Lif.lif_a`, `ndi_ok`,
`Lif.lif_nb`. -/
theorem lif_ok {pl pc ip cpy : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {W V : Addr → Byte} {sp : Addr}
    {gY : Gprs}
    -- `Lif.lif_a`
    (hinL : CodeIn L Lif.lif_at Lif.lif) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = Lif.lif_at) (hR : X.cpu.gpr.rsp = sp + 152#64)
    (hst0 : ∀ i < 32, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32#64) i)) (hsp0 : 0x7a9000 + 32 ≤ X.cpu.gpr.rsp.toNat)
    (l1 : ∀ i < 2, Foot F.data (Addr.add 7945344#64 i)) (l2 : ∀ i < 2, Foot F.data (Addr.add 7943116#64 i))
    (lw : ∀ i < 4, Foot Wl (Addr.add 7944640#64 i)) (la : ∀ i < 4, Foot Wl (Addr.add 8029640#64 i))
    (lb : ∀ i < 8, Foot Wl (Addr.add 8029648#64 i)) (lE : ∀ i < 8, Foot Wl (Addr.add 8013720#64 i))
    (hfw : rdw(V, 7945344#64) = rdw(V, 7943116#64))
    (hW : W = Vst (Lif.LifMem V X.cpu.gpr) (X.cpu.gpr.rsp - 32#64) (toBytesLE (Lif.lif_at.add 70) 8))
    (hgY : gY = (Lif.lifG X.cpu.gpr rdw(V, 7945344#64)).set 4 (X.cpu.gpr.rsp - 32#64))
    -- `ndi_ok`
    (c : Seg prof F Wl L s₀ o) (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx)
    (cx : Cx prof F Wl L o pl pc Pm E (fV W sp gY) sp) (hgo : CodeIn L gor_at gor)
    (hsn : sp.toNat + 128 ≤ 2 ^ 64) (htop : sp.toNat ≤ userPtrMax prof.feat)
    (hpw : ∀ i < 40, Foot Wl (Addr.add (sp + 80#64) i))
    (hst : ∀ i < 4136, Foot Wl (Addr.add (sp - 8#64 - 4136#64) i))
    (hsm : ∀ i < 408, Foot Wl (Addr.add (sp - 8#64 - 4136#64 - 240#64 - 168) i))
    (hlo : 8029888 + 408 + 4144 ≤ sp.toNat)
    (hbs : (b + size pad 656#64).toNat + 4096 + 408 + 4144 ≤ sp.toNat)
    (hbuf : ∀ i < 4096, Foot F.data (Addr.add (sp - 8#64 - 4136#64) i))
    (hfr : ∀ i < 40, Foot F.data (Addr.add (sp - 8#64 - 32#64) i))
    (hpf : ∀ i < 16, Foot F.data (Addr.add 7366691#64 i))
    (hpn : ∀ i < 14, nV W sp gY (Addr.add 7366691#64 i) ≠ 0)
    (hpz : nV W sp gY (Addr.add 7366691#64 14) = 0)
    (hpp : (byteAddrs 7366691#64 14).map (nV W sp gY) = Gor.pse)
    (hof : ∀ i < 8, Foot F.data (Addr.add (8029440#64) i)) (hoz : rdq(nV W sp gY, 8029440#64) = 0#64)
    (hps : ProcSelfExe o) (hpre : MPre F (nV W sp gY) b fsb pad sm mx)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (h1 : rdq(fV W sp gY, 8029448#64) = 0#64) (h2 : rdq(fV W sp gY, 8029568#64) = 4194368#64)
    (h3 : rdq(fV W sp gY, 8029592#64) = 8#64) (h4 : rdq(fV W sp gY, 8029424#64) = 0#64)
    (h5 : rdd(fV W sp gY, 7937248#64) = 0#32)
    (ke : ∀ r, (∃ t₀, o t₀ (.readlink none Gor.pse) = r ∧ ∀ x, r = .procExe x → pathMax ≤ x.bytes.length) →
      ∀ Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Gor.frV (nV W sp gY) { gY with rsp := sp - 8#64 }) →
      Z.cpu.rip = gor_at.add 271 → Z.cpu.gpr.rax = 18446744073709551615#64 → Z.cpu.gpr.rsp = sp - 8#64 →
      Z.cpu.gpr.rbx = gY.rbx → Z.cpu.gpr.rbp = gY.rbp → Z.cpu.gpr.r12 = gY.r12 →
      Z.cpu.gpr.r13 = gY.r13 → Z.cpu.gpr.r14 = gY.r14 → Z.cpu.gpr.r15 = gY.r15 →
      GoG prof L o (gev ++ [gEv { gY with rsp := sp - 8#64 } r]) gP gE Z t')
    -- `ndi_pc`, of the bytes at the entry
    (hin : CodeIn L Ipa.ipa_at Ipa.ipa) (hinh : CodeIn L Hwc.hwc_at Hwc.hwc)
    {mlc sl ms : List Byte} {Pq Pk Ps : (Addr → Byte) → Prop}
    (hcpq : Gor.PcpyAt prof L o 4198592#64 Pq)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length)
    (hinX : CodeIn L Mnx.mnx_at Mnx.mnx) (hinI : CodeIn L Imm.imm_at Imm.imm)
    (hinl : CodeIn L 4198664#64 sl) (hl0 : 0 < sl.length) (hlenA : Str.LenAt prof L o 4198664#64 Pk)
    (hinz : CodeIn L 4198528#64 ms) (hz0 : 0 < ms.length) (hset : Ipa.SetAt prof L o 4198528#64 Ps)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {hw : Addr} {cnt Ec H sz : Nat}
    (hn : hw = 2#64 ∧ cnt = 3 ∧ Ec = 8 ∧ H = 4 ∧ sz = 151 ∨ hw = 6#64 ∧ cnt = 4 ∧ Ec = 16 ∧ H = 8 ∧ sz = 320)
    (hPq : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W₁ a = fV W sp gY a) → Pq W₁)
    (hPk : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → ¬ Hv a → W₁ a = fV W sp gY a) → Pk W₁)
    (hPs : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W₁ a = fV W sp gY a) → Ps W₁)
    (he : 8388872 + 408 ≤ sp.toNat) (hal : (sp + 18446744073709551504#64) &&& 15#64 = 0#64)
    (hFs : ∀ a : Addr, sp.toNat - 408 ≤ a.toNat → a.toNat < sp.toNat → Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, fV W sp gY (Addr.add 7288953#64 k) ≠ 0)
    (hx1z : fV W sp gY (Addr.add 7288953#64 6) = 0)
    (hx2 : ∀ k < 8, fV W sp gY (Addr.add 7288962#64 k) ≠ 0)
    (hx2z : fV W sp gY (Addr.add 7288962#64 8) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hU : Tgv.UnsetW F (fV W sp gY) 11#64) (hm6 : rdq(fV W sp gY, Tgv.ent 11#64 + 32#64) = 6#64)
    (hhw : rdq(fV W sp gY, 8014536#64) = hw) (hfh : ∀ i < 8, Foot F.data (Addr.add 8014536#64 i))
    (hfm : ∀ i < 8, Foot F.data (Addr.add 8029424#64 i)) (hpl0 : rdq(fV W sp gY, 8029520#64) = 0#64)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add 8029520#64 i)) (hf2 : ∀ i < 8, Foot F.data (Addr.add 8029512#64 i))
    (hWb : ∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (hfN : ∀ x : Addr, 7937688 ≤ x.toNat → x.toNat < 7937696 → Foot F.data x)
    (hW7a : ∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a)
    (hW7b : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (hlenV : ∀ k < 3, rdq(fV W sp gY, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (Ipa.lA k))
    (hslV : ∀ k < 3, ofBytesLE 8 (List.map (fV W sp gY) (byteAddrs (BitVec.ofNat 64 (Ipa.sA k)) 1)) = 47#8)
    {G : Footprint} {Wl' : List Rgn} {q : Addr} {m : Nat}
    (hpl : Pl (fV W sp gY) F sp q m)
    (hid : CodeIn L Dpr.dpr_at Dpr.dpr) (him : CodeIn L Mpr.mpr_at Mpr.mpr)
    (hfp : ∀ x : Addr, 4194368 ≤ x.toNat → x.toNat < 4194816 → Foot F.data x) (hph : Ph (fV W sp gY))
    (hpgs : rdq(fV W sp gY, 7943128#64) = 4096#64) (hla : rdq(fV W sp gY, 7943392#64) = 0#64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hGo : G.own = []) (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot (N ++ F.writes) a ∧ inPages 0x777 27 (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot (N ++ F.writes) a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hlG : ∀ i < 24, Foot G.data (Addr.add (sp - 24#64) i))
    (hl : ∀ i < 48, Foot G.data (Addr.add (sp + 80#64) i))
    -- `Lif.lif_nb`
    {lp ct a0 : Addr} {ca cb cc : BitVec 64} {n : Nat} {pr : List Byte} {Pr : (Addr → Byte) → Prop}
    (hinS : CodeIn L Ims.ims_at Ims.ims) (hci : CodeIn L Cti.cti_at Cti.cti)
    (hir : CodeIn L 4198480#64 pr) (hr0 : 0 < pr.length) (hrchr : Str.RchrAt prof L o 4198480#64 Pr)
    (hbk : fsb.toNat ≤ b.toNat) (hfl : 8032256 + 112 ≤ fsb.toNat) (hfsp : fsb.toNat + 72 ≤ sp.toNat)
    (hs : sp.toNat + 160 ≤ 2 ^ 64)
    (hst₂ : ∀ i < 40, Foot Wl' (Addr.add (sp + 128#64 - 40#64) i))
    (hl₂ : ∀ i < 32, Foot G.data (Addr.add (sp + 128#64) i))
    (hgl : ∀ i < 16, Foot Wl' (Addr.add 7942968#64 i))
    (hsi : gY.r12 ≠ 0) (fa : ∀ i < 8, Foot G.data (Addr.add gY.r12 i))
    (ha0 : rdq(W, gY.r12) = a0) (hnz : a0 ≠ 0) (hrs : sp.toNat + 128 ≤ gY.r12.toNat)
    (hr8 : gY.r12.toNat + 8 ≤ 2 ^ 64)
    (nfit : a0.toNat + n < 2 ^ 64) (nnz : ∀ k < n, W (Addr.add a0 k) ≠ 0) (nz : W (Addr.add a0 n) = 0)
    (hns : sp.toNat + 128 ≤ a0.toNat)
    (npg : ∀ x : Addr, a0.toNat / 4096 ≤ x.toNat / 4096 → x.toNat / 4096 ≤ (a0.toNat + n) / 4096 → Foot G.data x)
    (hPr : ∀ W₁ : Addr → Byte, (∀ a : Addr, (a.toNat < 7937208 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480) →
      W₁ a = W a) → Pr W₁)
    (hlp : rdq(W, fsb - 112#64) = lp) (hct : rdq(W, lp) = ct) (ha : rdq(W, ct + 64#64) = ca)
    (hb : rdq(W, ct + 72#64) = cb) (hc : rdq(W, ct + 88#64) = cc)
    (hlg : 7937720 ≤ lp.toNat ∧ lp.toNat + 8 ≤ 7940480) (hcg : ct.toNat + 96 ≤ 7937208)
    (f1 : ∀ i < 8, Foot G.data ((fsb - 112#64).add i)) (f2 : ∀ i < 8, Foot G.data (Addr.add lp i))
    (f3 : ∀ i < 32, Foot G.data ((ct + 64#64).add i)) (fw : ∀ i < 24, Foot Wl' ((fsb - 64#64).add i))
    {e₃ : Addr} {code₃ : List Byte} (hin₃ : CodeIn L e₃ code₃) {j₃ : Nat} (h₃ : j₃ < code₃.length)
    (hra : rdq(W, sp + 152#64) = e₃.add j₃)
    (k : ∀ (x : ExePath) (evs : List Event) (s₂ Z₁ Z : State) (t' : Nat) (s : Addr) (W₂ : Addr → Byte),
      (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = b ∧ g₂.r14 = size pad 656#64 ∧
        (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂])) →
      Seg prof G Wl' L s₂ o → Base s₂ lim (b + size pad 656#64 + C2 b pad) fsb ks → NdiRet W sp gY b fsb W₂ →
      Z₁.cpu.gpr.rsp = sp + 128#64 → Z₁.cpu.gpr.rbp = gY.rbp → Z₁.cpu.gpr.r12 = gY.r12 →
      Z₁.cpu.gpr.r13 = gY.r13 →
      KeptW Wl' s₂ Z → Agree G Z.proc.mm.mem (Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr a0 s) fsb ca cb cc) →
      Hp (withNew F N) (N ++ Wl) fsb (sp.toNat - 4144) (1072 * 0 + 73840)
        (Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr a0 s) fsb ca cb cc) →
      Ims.Short W a0 n s → Z.cpu.rip = e₃.add j₃ → Z.cpu.gpr.rsp = sp + 160#64 →
      Z.cpu.gpr.rbx = gY.rbx → Z.cpu.gpr.rbp = rdq(W, sp + 128#64) →
      Z.cpu.gpr.r12 = rdq(W, sp + 136#64) → Z.cpu.gpr.r13 = rdq(W, sp + 144#64) →
      Z.cpu.gpr.r14 = gY.r14 → Z.cpu.gpr.r15 = gY.r15 →
      GoG prof L o (gev ++ [gEv { gY with rsp := sp - 8#64 } (.procExe x)] ++ evs ++ [ndiEv]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine Lif.lif_a (e₂ := ndi_at) (code₂ := ndi) c hinL cx.hin (by rw [ndi_length]; decide) rfl hK hA hrip hst0
    hsp0 l1 l2 lw la lb lE hfw ?_
  intro Y t₁ hKY hAY hrY hgY'
  rw [← hW] at hAY
  have hYs : Y.cpu.gpr.rsp = sp + 120#64 := by
    rw [hgY']
    show X.cpu.gpr.rsp - 32#64 = sp + 120#64
    rw [hR, s152]
  have hg : Y.cpu.gpr = gY := hgY'.trans hgY.symm
  subst hg
  refine ndi_ok (ip := ip) (X := Y) (W := W) (sp := sp) (e₂ := Lif.lif_at) (code₂ := Lif.lif) (j₂ := 70) c mc cx hgo
    hsn htop
    hpw hst hsm hlo hbs hbuf hfr hpf hpn hpz hpp hof hoz hps hpre hinc hc0 hcpy h1 h2 h3 h4 h5 hKY hAY
    (by rw [addr_add_zero]; exact hrY) hYs ke hin hinh hcpq hinm hm0 hinX hinI hinl hl0 hlenA hinz hz0 hset hint hn
    hPq hPk hPs he hal hFs hpg hx1 hx1z hx2 hx2z htls hU hm6 hhw hfh hfm hpl0 hf1 hf2 hWb hfN hW7a hW7b hFR hlenV
    hslV hpl hid him hfp hph hpgs hla hmg hGo hGc hfit hGw hGr hcode hww hlG hl hinL
    (by rw [Lif.lif_length]; decide) (lif_ret hR hs hW) ?_
  intro x nn ss Vc M W' evs gg U s₂ Z t' W₂ _ _ _ _ _ _ _ _ _ _ hLo hSame hev hUr hHp hc₂ hB hK₂ hA₂ hE hr₂ hs₂ hbx hbp
    h12 h13 h14 h15
  refine Lif.lif_nb (lp := lp) (ct := ct) (a := ca) (b := cb) (cc := cc) (a0 := a0) (n := n) (g := Y.cpu.gpr) hc₂
    hB.fsb hinL hinS hci hir hr0 hrchr hK₂ hA₂ hr₂ hs₂ hE hUr hLo hSame hbk hfl hfsp hs (by rw [hs₂]; exact hst₂)
    (by rw [hs₂]; exact hl₂) hgl (by rw [h12]; exact hsi) (by rw [h12]; exact fa) (by rw [h12]; exact ha0) hnz
    (by rw [h12]; exact hrs) (by rw [h12]; exact hr8) nfit nnz nz hns npg hPr hlp hct ha hb hc hlg hcg f1 f2 f3 fw
    hin₃ h₃ hra ?_
  intro Zf t'' s' hKf hAf hSh hrf hsf hbxf hbpf h12f h13f h14f h15f
  exact k x evs s₂ Z Zf t'' s' W₂ hev hc₂ hB ⟨W', U, m, Tp b + 16#64, hE, hUr, hLo, hSame⟩ hs₂ hbp h12 h13 hKf hAf
    (hp_lif hHp (by omega) (by omega) hs₂ (by omega) hE) hSh hrf hsf (hbxf.trans hbx) hbpf h12f h13f
    (h14f.trans h14) (h15f.trans h15)

end FV7z.Ndi
