/-
`_dl_non_dynamic_init` whole: `ndi_ab` (entry → `_dl_get_origin` → `ndi_b`, up to the `call` of `_dl_init_paths`)
then `ndi_pc` (`_dl_init_paths (NULL)`, `ndi_c`, the return). The facts `ndi_pc` needs of the bytes after the first
`malloc` (`W'`) are stated of the bytes at the entry (`fV W sp g`) and moved: `W'` is `fV W sp g` from `sp` on and on
`Lo` (`ndi_ab`), the footprints grow by the new heap pages (`withNew F N`, `N ++ Wl`). The one fact not moved is the
precondition `Pa` of the second `malloc`: it is asked of every `W₁` that agrees with `M`, the bytes `Mal.After` gives,
below the frame of `_dl_init_paths` off the copied directory.
-/
import FV7z.Ndi.Org
import FV7z.Ndi.Bc

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Smm (corr size smEv smEv2)
open FV7z.Mhi (Tp C2)
open FV7z.Mal (MPre After)
open FV7z.Gor (MCx Vg Lo nbOf gEv gor_at gor)

namespace FV7z.Ndi

/-- A byte of a literal run `x, …, x + k` is below `m` when the run ends below it. -/
theorem ad_lt {x k m : Nat} (hk : x + k < m) (hm : m ≤ 2 ^ 64) : (Addr.add (BitVec.ofNat 64 x) k).toNat < m := by
  rw [toNat_add_of_fits (n := k + 1) (by omega) (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

/-- The eight bytes at `x` read the same from bytes that agree there. -/
theorem rq_of {V V' : Addr → Byte} {x : Addr} (hx : x.toNat + 8 ≤ 2 ^ 64)
    (h : ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + 8 → V' a = V a) : rdq(V', x) = rdq(V, x) :=
  congrArg (ofBytesLE 64) (Sbrk.rd_eq hx h)

theorem sA_lt {k : Nat} (hk : k < 3) : Ipa.sA k < 7364131 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> decide

/-- The bytes of `n` from `x` in `R` as a range. -/
theorem of_add {R : List Rgn} {x : Addr} {n : Nat} (h : ∀ i < n, Foot R (Addr.add x i)) (hx : x.toNat + n ≤ 2 ^ 64) :
    ∀ a : Addr, x.toNat ≤ a.toNat → a.toNat < x.toNat + n → Foot R a := fun a h1 h2 => by
  have := a.isLt
  have e : Addr.add x (a.toNat - x.toNat) = a := by
    apply BitVec.eq_of_toNat_eq
    simp only [Addr.add]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact e ▸ h _ (by omega)
theorem s4144 {sp : Addr} (h : 4144 ≤ sp.toNat) : (sp - 8#64 - 4136#64).toNat = sp.toNat - 4144 := by bv_omega
theorem ent6 : (Tgv.ent 11#64 + 32#64).toNat = 7936232 := by rw [Hwc.eent]; decide

variable {F : Footprint} {Wl N : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
/-- `_dl_non_dynamic_init` from its entry (bytes `W`, `rsp = sp + 120`) to its caller: `ndi_ab` then `ndi_pc`. The
caller's continuation gets what `ndi_ab` gives of the bytes `W'` after `_dl_get_origin` (the path `x`, the `malloc (n)`
and its `Mal.After` bytes `M`, the copied directory of `s` bytes at `Tp b + 16`) and what `ndi_pc` gives after
`_dl_init_paths` and the platform loop; the registers are the caller's. -/
theorem ndi_all {pl pc ip cpy : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {W : Addr → Byte} {sp : Addr}
    (c : Seg prof F Wl L s₀ o) (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx)
    (cx : Cx prof F Wl L o pl pc Pm E (fV W sp X.cpu.gpr) sp) (hgo : CodeIn L gor_at gor)
    (hsn : sp.toNat + 128 ≤ 2 ^ 64) (htop : sp.toNat ≤ userPtrMax prof.feat)
    (hpw : ∀ i < 40, Foot Wl (Addr.add (sp + 80#64) i))
    (hst : ∀ i < 4136, Foot Wl (Addr.add (sp - 8#64 - 4136#64) i))
    (hsm : ∀ i < 408, Foot Wl (Addr.add (sp - 8#64 - 4136#64 - 240#64 - 168) i))
    (hlo : 8029888 + 408 + 4144 ≤ sp.toNat)
    (hbs : (b + size pad 656#64).toNat + 4096 + 408 + 4144 ≤ sp.toNat)
    (hbuf : ∀ i < 4096, Foot F.data (Addr.add (sp - 8#64 - 4136#64) i))
    (hfr : ∀ i < 40, Foot F.data (Addr.add (sp - 8#64 - 32#64) i))
    (hpf : ∀ i < 16, Foot F.data (Addr.add 7366691#64 i))
    (hpn : ∀ i < 14, nV W sp X.cpu.gpr (Addr.add 7366691#64 i) ≠ 0)
    (hpz : nV W sp X.cpu.gpr (Addr.add 7366691#64 14) = 0)
    (hpp : (byteAddrs 7366691#64 14).map (nV W sp X.cpu.gpr) = Gor.pse)
    (hof : ∀ i < 8, Foot F.data (Addr.add (8029440#64) i)) (hoz : rdq(nV W sp X.cpu.gpr, 8029440#64) = 0#64)
    (hps : ProcSelfExe o) (hpre : MPre F (nV W sp X.cpu.gpr) b fsb pad sm mx)
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : Gor.PcpyAt prof L o 4198592#64 Pm)
    (h1 : rdq(fV W sp X.cpu.gpr, 8029448#64) = 0#64) (h2 : rdq(fV W sp X.cpu.gpr, 8029568#64) = 4194368#64)
    (h3 : rdq(fV W sp X.cpu.gpr, 8029592#64) = 8#64) (h4 : rdq(fV W sp X.cpu.gpr, 8029424#64) = 0#64)
    (h5 : rdd(fV W sp X.cpu.gpr, 7937248#64) = 0#32)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hrip : X.cpu.rip = ndi_at.add 0)
    (hsp : X.cpu.gpr.rsp = sp + 120#64)
    (ke : ∀ r Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Gor.frV (nV W sp X.cpu.gpr) { X.cpu.gpr with rsp := sp - 8#64 }) →
      Z.cpu.rip = gor_at.add 271 → Z.cpu.gpr.rax = 18446744073709551615#64 → Z.cpu.gpr.rsp = sp - 8#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv { X.cpu.gpr with rsp := sp - 8#64 } r]) gP gE Z t')
    -- `ndi_pc`, of the bytes at the entry
    (hin : CodeIn L Ipa.ipa_at Ipa.ipa) (hinh : CodeIn L Hwc.hwc_at Hwc.hwc)
    {mlc sl ms : List Byte} {Pq Pk Ps : (Addr → Byte) → Prop}
    {Pa : Nat → (Addr → Byte) → Prop} {ka : Nat}
    (hcpq : Gor.PcpyAt prof L o 4198592#64 Pq)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length)
    (hmal : Mal.At prof (withNew F N) (N ++ Wl) L o fsb (sp.toNat - 4144) 6500704#64 Pa)
    {mb : Nat} (hmb : 16 ≤ mb)
    (hPaH : ∀ k W, Pa k W ↔ Mal.Hp (withNew F N) (N ++ Wl) fsb (sp.toNat - 4144) (1072 * k + mb) W)
    (hinl : CodeIn L 4198664#64 sl) (hl0 : 0 < sl.length) (hlenA : Str.LenAt prof L o 4198664#64 Pk)
    (hinz : CodeIn L 4198528#64 ms) (hz0 : 0 < ms.length) (hset : Ipa.SetAt prof L o 4198528#64 Ps)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {hw : Addr} {cnt Ec H sz : Nat}
    (hn : hw = 2#64 ∧ cnt = 3 ∧ Ec = 8 ∧ H = 4 ∧ sz = 151 ∨ hw = 6#64 ∧ cnt = 4 ∧ Ec = 16 ∧ H = 8 ∧ sz = 320)
    (hPq : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W₁ a = fV W sp X.cpu.gpr a) → Pq W₁)
    (hPa : ∀ (x : ExePath) (n s : Nat) (Vc M : Addr → Byte) (g : Gprs), x.bytes.length < 4096 → 2 ≤ n → n ≤ 4097 →
      1 ≤ s → s + 1 ≤ n → g.rsp = sp - 8#64 - 4136#64 - 8 →
      (∀ a : Addr, a.toNat < sp.toNat - 8 - 4144 ∨ sp.toNat - 8 - 4136 ≤ a.toNat →
        Vc a = Vg (nV W sp X.cpu.gpr) { X.cpu.gpr with rsp := sp - 8#64 } x a) →
      After fsb (sp - 8#64 - 4136#64 - 240#64) b pad sm (nbOf n) g Vc M →
      ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < sp.toNat - 408 →
        (a.toNat < (Tp b + 16#64).toNat ∨ (Tp b + 16#64).toNat + s + 1 ≤ a.toNat) →
        (a.toNat < sp.toNat - 8 - 4144 ∨ sp.toNat - 8 - 4136 ≤ a.toNat) →
        (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a → W₁ a = M a) → Pa (ka + 3) W₁)
    (hPk : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → ¬ Hv a → W₁ a = fV W sp X.cpu.gpr a) → Pk W₁)
    (hPs : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W₁ a = fV W sp X.cpu.gpr a) → Ps W₁)
    (he : 8388872 + 408 ≤ sp.toNat) (hal : (sp + 18446744073709551504#64) &&& 15#64 = 0#64)
    (hFs : ∀ a : Addr, sp.toNat - 408 ≤ a.toNat → a.toNat < sp.toNat → Foot Wl a ∧ Foot F.data a)
    (hpg : ∀ x : Addr, 7286784 ≤ x.toNat → x.toNat < 7290880 → Foot F.data x)
    (hx1 : ∀ k < 6, fV W sp X.cpu.gpr (Addr.add 7288953#64 k) ≠ 0)
    (hx1z : fV W sp X.cpu.gpr (Addr.add 7288953#64 6) = 0)
    (hx2 : ∀ k < 8, fV W sp X.cpu.gpr (Addr.add 7288962#64 k) ≠ 0)
    (hx2z : fV W sp X.cpu.gpr (Addr.add 7288962#64 8) = 0)
    (htls : ∀ i < 3, Foot F.data ((7366106#64).add i))
    (hU : Tgv.UnsetW F (fV W sp X.cpu.gpr) 11#64) (hm6 : rdq(fV W sp X.cpu.gpr, Tgv.ent 11#64 + 32#64) = 6#64)
    (hhw : rdq(fV W sp X.cpu.gpr, 8014536#64) = hw) (hfh : ∀ i < 8, Foot F.data (Addr.add 8014536#64 i))
    (hfm : ∀ i < 8, Foot F.data (Addr.add 8029424#64 i)) (hpl0 : rdq(fV W sp X.cpu.gpr, 8029520#64) = 0#64)
    (hf1 : ∀ i < 8, Foot F.data (Addr.add 8029520#64 i)) (hf2 : ∀ i < 8, Foot F.data (Addr.add 8029512#64 i))
    (hWb : ∀ x : Addr, 7937664 ≤ x.toNat → x.toNat < 7937720 → Foot Wl x)
    (hfN : ∀ x : Addr, 7937688 ≤ x.toNat → x.toNat < 7937696 → Foot F.data x)
    (hW7a : ∀ a : Addr, 8029552 ≤ a.toNat → a.toNat < 8029560 → Foot Wl a)
    (hW7b : ∀ x : Addr, 8014920 ≤ x.toNat → x.toNat < 8014928 → Foot Wl x)
    (hFR : ∀ x : Addr, 7364040 ≤ x.toNat → x.toNat < 7364131 → Foot F.data x)
    (hlenV : ∀ k < 3, rdq(fV W sp X.cpu.gpr, BitVec.ofNat 64 (7364040 + 8 * k)) = BitVec.ofNat 64 (Ipa.lA k))
    (hslV : ∀ k < 3, ofBytesLE 8 (List.map (fV W sp X.cpu.gpr) (byteAddrs (BitVec.ofNat 64 (Ipa.sA k)) 1)) = 47#8)
    {G : Footprint} {Wl' : List Rgn} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {q : Addr} {m : Nat}
    (hpl : Pl (fV W sp X.cpu.gpr) F sp q m)
    (hid : CodeIn L Dpr.dpr_at Dpr.dpr) (him : CodeIn L Mpr.mpr_at Mpr.mpr)
    (hfp : ∀ x : Addr, 4194368 ≤ x.toNat → x.toNat < 4194816 → Foot F.data x) (hph : Ph (fV W sp X.cpu.gpr))
    (hpgs : rdq(fV W sp X.cpu.gpr, 7943128#64) = 4096#64) (hla : rdq(fV W sp X.cpu.gpr, 7943392#64) = 0#64)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hGo : G.own = []) (hGc : G.code = F.code) (hfit : ∀ r ∈ G.writes ++ G.reads, r.Fits)
    (hGw : ∀ r ∈ G.writes, ∀ a, r.Mem a → Foot (N ++ F.writes) a ∧ inPages 0x777 27 (pageOf a) = false)
    (hGr : ∀ r ∈ G.reads, ∀ a, r.Mem a → Foot (N ++ F.writes) a ∨ Foot F.reads a)
    (hcode : ∀ a, Foot F.codeRgns a → inPages 0x777 27 (pageOf a) = false)
    (hww : ∀ y, Foot Wl' y → ∃ q ∈ G.writes, q.Mem y)
    (hlG : ∀ i < 24, Foot G.data (Addr.add (sp - 24#64) i))
    (hl : ∀ i < 48, Foot G.data (Addr.add (sp + 80#64) i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length) (hret : rdq(fV W sp X.cpu.gpr, sp + 120#64) = e₂.add j₂)
    (k : ∀ (x : ExePath) (n s : Nat) (Vc M W' : Addr → Byte) (evs : List Event) (g : Gprs) (U : Addr → Byte)
      (s₂ Z : State) (t' : Nat) (W₂ : Addr → Byte), x.bytes.length < 4096 →
      2 ≤ n → n ≤ 4097 → 1 ≤ s → s + 1 ≤ n → g.rsp = sp - 8#64 - 4136#64 - 8 →
      (∀ a : Addr, a.toNat < sp.toNat - 8 - 4144 ∨ sp.toNat - 8 - 4136 ≤ a.toNat →
        Vc a = Vg (nV W sp X.cpu.gpr) { X.cpu.gpr with rsp := sp - 8#64 } x a) →
      After fsb (sp - 8#64 - 4136#64 - 240#64) b pad sm (nbOf n) g Vc M →
      W' (Addr.add (Tp b + 16#64) s) = 0 →
      (∀ a : Addr, (a.toNat < (Tp b + 16#64).toNat ∨ (Tp b + 16#64).toNat + s + 1 ≤ a.toNat) →
        (a.toNat < sp.toNat - 8 - 4144 ∨ sp.toNat - 8 - 4136 ≤ a.toNat) → W' a = M a) →
      (∀ a : Addr, Lo b fsb a → W' a = fV W sp X.cpu.gpr a) → Same sp (fV W sp X.cpu.gpr) W' →
      (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = b ∧ g₂.r14 = size pad 656#64 ∧
        (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂])) →
      (∀ a : Addr, (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480 ∨ sp.toNat ≤ a.toNat ∨
        Mal.Kf fsb a) →
        U a = hV W' (Tp b + 16#64) 4194368#64 8#64 a) →
      Mal.Hp (withNew F N) (N ++ Wl) fsb (sp.toNat - 4144) (1072 * ka + mb) U →
      Seg prof G Wl' L s₂ o → Base s₂ lim (b + size pad 656#64 + C2 b pad) fsb ks → KeptW Wl' s₂ Z →
      Agree G Z.proc.mm.mem W₂ → Eqo sp W₂ (lV (bV U m)) → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp + 128#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv { X.cpu.gpr with rsp := sp - 8#64 } (.procExe x)] ++ evs ++ [ndiEv]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have h72 := cx.h72
  have hfs := mc.hfs
  have hfb := mc.hfb
  have hown := mc.hown
  refine ndi_ab (ph := 4194368#64) (pn := 8#64) c mc cx hgo hin (by rw [Ipa.ipa_length]; decide) hsn htop hpw hst
    hsm hlo hbs hbuf hfr hpf hpn hpz hpp hof hoz hps hpre hinc hc0 hcpy h1 h2 h3 h4 h5 hK hA hrip hsp ke ?_
  intro x n s s₁ Vc M W' evs g Y t₁ W'' hx c₁ hB₁ h2n hn4 h1s hs1 hg' hVc hAf hnul hout LO SM hev hKY hAY hMY hrY
    hspY hdiY h15Y
  have HI : ∀ a : Addr, sp.toNat ≤ a.toNat → W' a = fV W sp X.cpu.gpr a := fun a h => SM a (.inl h)
  have LB : ∀ a : Addr, a.toNat < 7940480 → W' a = fV W sp X.cpu.gpr a := fun a h =>
    LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
  have LM : ∀ a : Addr, 7942872 ≤ a.toNat → a.toNat < 8013224 → W' a = fV W sp X.cpu.gpr a := fun a a1 a2 =>
    LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
  have L2 : ∀ a : Addr, 8013232 ≤ a.toNat → a.toNat < 8014904 → W' a = fV W sp X.cpu.gpr a := fun a a1 a2 =>
    LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
  have LZ : ∀ a : Addr, 8014912 ≤ a.toNat → a.toNat < 8029888 → W' a = fV W sp X.cpu.gpr a := fun a a1 a2 =>
    LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
  have RQ : ∀ d : Nat, d + 8 ≤ 128 →
      rdq(W', sp + BitVec.ofNat 64 d) = rdq(fV W sp X.cpu.gpr, sp + BitVec.ofNat 64 d) := fun d hd =>
    rq_of (by rw [tp sp d (by omega)]; omega) fun a a1 a2 => HI a (by rw [tp sp d (by omega)] at a1; omega)
  obtain ⟨r0, r1, r2, r3, r4⟩ := fV_rd W sp X.cpu.gpr hsn
  have hU' : Tgv.UnsetW (withNew F N) W' 11#64 :=
    Tgv.UnsetW.out (lo := 7937208) (hi := 2 ^ 64) (unset_foot hU fun _ => fwn hown)
      (by rw [Hwc.eent]; decide) (by omega) fun a ha => LB a (by have := a.isLt; omega)
  -- the stack from `sp - 0x1030` (`hst`, `hFs`): for the frames of `malloc`
  have WS : ∀ a : Addr, sp.toNat - 4144 ≤ a.toNat → a.toNat < sp.toNat → Foot Wl a := fun a a1 a2 => by
    by_cases hl : a.toNat < sp.toNat - 408
    · have e := s4144 (sp := sp) (by omega)
      exact of_add hst (by rw [e]; omega) a (by rw [e]; omega) (by rw [e]; omega)
    · exact (hFs a (by omega) a2).1
  have hfsp : fsb.toNat + 128 ≤ sp.toNat := by
    have hbt := mc.hB.brk_lt
    have hbl := mc.hbl
    have hsl := sp.isLt
    have hb47 : b.toNat < 2 ^ 47 := by omega
    obtain ⟨hbc, -, hT0, -, -⟩ := Gor.lay (nb := 32#64) hb47 mc.hnb mc.hpd (by decide)
    omega
  exact ndi_pc (V := W') (org := Tp b + 16#64) c₁ (Cx.mv cx hown SM) hB₁.fsb
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029568) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact h2)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029592) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact h3)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029424) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact h4)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 7937248) (n := 4) (by omega) fun a a1 a2 =>
      LB a (by omega)]; exact h5)
    hin hinh hinc hc0 hcpq hinm hm0 hmal hmb hPaH hinl hl0 hlenA hinz hz0 hset hint hn
    (fun W₁ hW => hPq W₁ fun a a1 a2 a3 => (hW a a1 a2 a3).trans (LB a a1))
    (fun W₁ hW => hPa x n s Vc M g hx h2n hn4 h1s hs1 hg' hVc hAf W₁ fun a a1 a2 a3 a4 a5 =>
      (hW a a1 a4 a5).trans (hout a a2 a3))
    (fun W₁ hW => hPk W₁ fun a a1 a2 => (hW a a1 a2).trans (LB a a1))
    (fun W₁ hW => hPs W₁ fun a a1 a2 a3 => (hW a a1 a2 a3).trans (LB a a1))
    he hal (fun a a1 a2 => ⟨foot_append_iff.2 (.inr (hFs a a1 a2).1), fwn hown (hFs a a1 a2).2⟩)
    (fun a a1 a2 => foot_append_iff.2 (.inr (WS a a1 a2))) (by omega) hfsp
    (fun x a1 a2 => fwn hown (hpg x a1 a2))
    (fun k hk => by rw [LB _ (ad_lt (x := 7288953) (k := k) (by omega) (by omega))]; exact hx1 k hk)
    (by rw [LB _ (ad_lt (x := 7288953) (k := 6) (by omega) (by omega))]; exact hx1z)
    (fun k hk => by rw [LB _ (ad_lt (x := 7288962) (k := k) (by omega) (by omega))]; exact hx2 k hk)
    (by rw [LB _ (ad_lt (x := 7288962) (k := 8) (by omega) (by omega))]; exact hx2z)
    (fun i hi => fwn hown (htls i hi)) hU'
    ((rq_of (by rw [ent6]; omega) fun a a1 a2 => LB a (by rw [ent6] at a2; omega)).trans hm6)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8014536) (n := 8) (by omega) fun a a1 a2 => L2 a (by omega)
      (by omega)]; exact hhw)
    (fun i hi => fwn hown (hfh i hi)) (fun i hi => fwn hown (hfm i hi))
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029520) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact hpl0)
    (fun i hi => fwn hown (hf1 i hi)) (fun i hi => fwn hown (hf2 i hi))
    (fun x a1 a2 => foot_append_iff.2 (.inr (hWb x a1 a2))) (fun x a1 a2 => fwn hown (hfN x a1 a2))
    (fun x a1 a2 => foot_append_iff.2 (.inr (hW7a x a1 a2)))
    (fun x a1 a2 => foot_append_iff.2 (.inr (hW7b x a1 a2))) (fun x a1 a2 => fwn hown (hFR x a1 a2))
    (fun k hk => by
      rw [rd_of (V := fV W sp X.cpu.gpr) (x := 7364040 + 8 * k) (n := 8) (by omega) fun a a1 a2 => LB a (by omega)]
      exact hlenV k hk)
    (fun k hk => by
      have := sA_lt hk
      rw [rd_of (V := fV W sp X.cpu.gpr) (x := Ipa.sA k) (n := 1) (by omega) fun a a1 a2 => LB a (by omega)]
      exact hslV k hk)
    hB₁ (pl_foot (Pl.mv hpl (fun a ha => ha.elim (HI a) fun h => LB a (by omega))
      fun a a1 a2 => LZ a (by omega) (by omega)) fun _ => fwn hown) hid him
    (fun x a1 a2 => fwn hown (hfp x a1 a2)) (Ph.mv hph fun a ha => LB a (by omega)) hsn
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 7943128) (n := 8) (by omega) fun a a1 a2 => LM a (by omega)
      (by omega)]; exact hpgs)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 7943392) (n := 8) (by omega) fun a a1 a2 => LM a (by omega)
      (by omega)]; exact hla)
    hmg hGo hGc hfit hGw hGr hcode hww hlG hl hin₂ h₂ ((RQ 120 (by omega)).trans hret) hKY hAY hMY hrY hspY hdiY
    (fun U s₂ Z t' W₂ uv hHp c₂ hB₂ hK₂ hA₂ hM₂ hr₂ hs₂ hbx hbp h12 h13 h14 h15 =>
      k x n s Vc M W' evs g U s₂ Z t' W₂ hx h2n hn4 h1s hs1 hg' hVc hAf hnul hout LO SM hev uv hHp c₂ hB₂ hK₂ hA₂
        hM₂
        hr₂ hs₂ (hbx.trans ((RQ 80 (by omega)).trans r0)) (hbp.trans ((RQ 88 (by omega)).trans r1))
        (h12.trans ((RQ 96 (by omega)).trans r2)) (h13.trans ((RQ 104 (by omega)).trans r3))
        (h14.trans ((RQ 112 (by omega)).trans r4)) (h15.trans h15Y))

end FV7z.Ndi
