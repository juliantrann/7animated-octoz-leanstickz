import FV7z.Ndi.All
import FV7z.Mal.HeapA
import FV7z.Mal.Ok
/-!
# The heap at the second `malloc` of `_dl_non_dynamic_init` (PLAN.md G3, `malloc`)

`ndi_all` asks of its `Pa (ka + 3)` (the heap at the second `malloc`, three before the end of `_dl_init_paths`) only
for bytes `W₁` that agree with `M` (the bytes `Mal.After` gives after the first) below the frame of `_dl_init_paths`,
off the copied directory, the return slot of the first `malloc`, `[0x791e80, 0x791eb8)` and `Hv`. `hpa` gives it for
`Pa k = Hp … (1072 k + 73840)` and `ka = 0` (the form `Mal.Ok.at_ok` keeps): `After.hp` with the layout from `MCx`
(`Lay`), `MPre` at the call from the one at the entry (`_dl_get_origin` writes only its frame), the budget of
3232 bytes in the first `MORECORE` (at least 8192 bytes: `mp_.top_pad` at least 4112) after a first chunk of at most
4112, and what `Hp` reads apart from `Hv` and the other excluded bytes (`GlR`). `ndi_ok`: `ndi_all` with
`Mal.Ok.at_ok` and `hpa`, without `Mal.At` and `Pa`.
-/

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Smm (corr size smEv smEv2)
open FV7z.Mhi (Tp C2 Sz)
open FV7z.Mal (MPre After Hp GlR)
open FV7z.Gor (MCx Vg Vg_lo Lo nbOf nbOf_bnd lay foot_wn foot_wnN gEv gor_at gor)
namespace FV7z.Ndi

set_option maxRecDepth 8192

theorem s4384 {sp : Addr} (h : 4384 ≤ sp.toNat) : (sp - 8#64 - 4136#64 - 240#64).toNat = sp.toNat - 4384 := by
  bv_omega
theorem e232 (sp : Addr) : sp - 8#64 - 4136#64 - 8 = sp - 8#64 - 4136#64 - 240#64 + 232#64 := by bv_omega
theorem s8 {sp : Addr} (h : 8 ≤ sp.toNat) : (sp - 8#64).toNat = sp.toNat - 8 := by bv_omega

/-- The bytes of a run from `y` that fits. -/
theorem adn {y : Addr} {j : Nat} (h : y.toNat + j < 2 ^ 64) : (Addr.add y j).toNat = y.toNat + j := by
  simp only [Addr.add]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The chunk size of `malloc (n)`, `n ≤ 4104`: a multiple of 8 with the `n` bytes and a size word. -/
theorem nb_ge {n : Nat} (h : n ≤ 4104) : (nbOf n).toNat % 8 = 0 ∧ n + 8 ≤ (nbOf n).toNat := by
  unfold nbOf
  split
  · show 32 % 8 = 0 ∧ n + 8 ≤ 32
    omega
  · rw [Im2.and_m16, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

variable {prof : Profile} {F : Footprint} {Wl N : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64}

/-- `ndi_all`'s `hPa` for `Pa k = Hp (withNew F N) (N ++ Wl) fsb (sp - 4144) (1072 k + 73840)` and `ka = 0`. -/
theorem hpa (c : Seg prof F Wl L s₀ o) (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx) {V₀ : Addr → Byte}
    {gx : Gprs} {sp : Addr} (hpre : MPre F V₀ b fsb pad sm mx) (hsn : sp.toNat + 128 ≤ 2 ^ 64)
    (hlo : 8029888 + 408 + 4144 ≤ sp.toNat) (hbs : (b + size pad 656#64).toNat + 4096 + 408 + 4144 ≤ sp.toNat)
    {x : ExePath} {n s : Nat} {Vc M W₁ : Addr → Byte} {g : Gprs} (hx : x.bytes.length < 4096) (h2n : 2 ≤ n)
    (hn4 : n ≤ 4097) (hs1 : s + 1 ≤ n) (hg : g.rsp = sp - 8#64 - 4136#64 - 8)
    (hVc : ∀ a : Addr, a.toNat < sp.toNat - 8 - 4144 ∨ sp.toNat - 8 - 4136 ≤ a.toNat →
      Vc a = Vg V₀ { gx with rsp := sp - 8#64 } x a)
    (hAf : After fsb (sp - 8#64 - 4136#64 - 240#64) b pad sm (nbOf n) g Vc M)
    (hW : ∀ a : Addr, a.toNat < sp.toNat - 408 →
      (a.toNat < (Tp b + 16#64).toNat ∨ (Tp b + 16#64).toNat + s + 1 ≤ a.toNat) →
      (a.toNat < sp.toNat - 8 - 4144 ∨ sp.toNat - 8 - 4136 ≤ a.toNat) →
      (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a → W₁ a = M a) :
    Hp (withNew F N) (N ++ Wl) fsb (sp.toNat - 4144) (1072 * (0 + 3) + 73840) W₁ := by
  have hbt := mc.hB.brk_lt
  have hfs := mc.hfs
  have hfb := mc.hfb
  have hbk := mc.hbk
  have hpd := mc.hpd
  have htp := mc.htp
  have hnp := mc.hnb
  have hsl := sp.isLt
  have hb47 : b.toNat < 2 ^ 47 := by omega
  obtain ⟨-, hnb⟩ := nbOf_bnd (n := n) (by omega)
  obtain ⟨hn8, hns⟩ := nb_ge (n := n) (by omega)
  obtain ⟨hbc, hc15, hT0, hT1, hT16⟩ := lay hb47 hnp hpd hnb
  have hR : (size pad 656#64).toNat = (4127 + pad.toNat + 656) / 4096 * 4096 :=
    Smm.size_toNat (pad := pad) (nb := 656#64) (by show 656 + pad.toNat + 4127 < 2 ^ 47; omega)
  have eb : (b + size pad 656#64).toNat = b.toNat + (size pad 656#64).toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hc := Smm.corr_toNat b
  have e1 : (b + corr b).toNat = b.toNat + (corr b).toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hS := s4384 (sp := sp) (by omega)
  have hL : Mal.Lay fsb (sp - 8#64 - 4136#64 - 240#64) b pad (nbOf n) g :=
    ⟨by rw [hg]; exact e232 sp, by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega, by rw [hS]; omega, hfs, hfb,
      by rw [hS]; omega, hT1, hbc, by unfold pageUp; omega, by omega⟩
  have h8 := s8 (sp := sp) (by omega)
  have hpre' : MPre F Vc b fsb pad sm mx := hpre.lo hfs hfb fun a ha => by
    rw [hVc a (.inl (by omega)), Vg_lo (by show 8192 ≤ (sp - 8#64).toNat; rw [h8]; omega) hx
      (by show a.toNat < (sp - 8#64).toNat - 4136; rw [h8]; omega)]
  have D : ∀ a : Addr, Foot Wl a → Foot (withNew F N).data a := fun a h => foot_wn mc.hown (c.hws a h)
  have HH : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + size pad 656#64).toNat →
      Foot (N ++ Wl) a ∧ Foot (withNew F N).data a := fun a h1 h2 =>
    ⟨mc.hH a h1 h2, (foot_append_iff.1 (mc.hH a h1 h2)).elim foot_wnN (D a)⟩
  obtain ⟨hz1, -⟩ := Mhi.sz_ok (sm := sm) hb47 hnp mc.hsu
  have hz2 := Mhi.sz_big (b := b) (pad := pad) hb47 hnp
  have hA : ∀ i < 8, (Addr.add (7940656#64) i).toNat = 7940656 + i := fun i hi => by
    rw [adn (y := 7940656#64) (j := i) (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat] <;> omega
  have hC : ∀ i < 64, ∀ j < 2,
      (Addr.add (b + corr b + 16#64 + BitVec.ofNat 64 (2 * i)) j).toNat = b.toNat + (corr b).toNat + 16 + 2 * i + j :=
    fun i hi j hj => by
      rw [adn (y := b + corr b + 16#64 + BitVec.ofNat 64 (2 * i)) (j := j) (by rw [Mhi.cXn hb47 i hi]; omega),
        Mhi.cXn hb47 i hi]
  exact After.hp (F := withNew F N) (Wl := N ++ Wl) (hi := sp.toNat - 4144) (m := 1072 * (0 + 3) + 73840) (s := s + 1)
    hAf hL hpre' (fun i hi => D _ (mc.hW _ (by rw [hA i hi]; omega) (by rw [hA i hi]; omega)))
    (fun i hi j hj => (HH _ (by rw [hC i hi j hj]; omega) (by rw [hC i hi j hj]; omega)).2)
    (fun i hi => D _ (mc.hfm i hi)) (fun a a1 a2 => foot_append_iff.2 (.inr (mc.hW a a1 a2)))
    (fun i hi => D _ (mc.hgmf i hi)) (fun i hi => D _ (mc.hft i hi)) (fun i hi => D _ (mc.hpb i hi))
    hbk (by omega) hn8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun a a1 a2 => HH a (by omega) (by omega))
    fun a ha hs => hW a (by unfold GlR at ha; omega) (by rw [hT16]; omega) (.inl (by unfold GlR at ha; omega))
      (.inr (by unfold GlR at ha; omega)) (by unfold Hv; unfold GlR at ha; omega)

set_option maxHeartbeats 4000000 in
/-- `ndi_all` with `malloc` after the first call (`Mal.Ok.at_ok`) and the heap at the second (`hpa`): no `Mal.At`,
no `Pa`. -/
theorem ndi_ok {pl pc ip cpy : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {W : Addr → Byte} {sp : Addr}
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
    (ke : ∀ r, (∃ t₀, o t₀ (.readlink none Gor.pse) = r ∧ ∀ x, r = .procExe x → pathMax ≤ x.bytes.length) →
      ∀ Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Gor.frV (nV W sp X.cpu.gpr) { X.cpu.gpr with rsp := sp - 8#64 }) →
      Z.cpu.rip = gor_at.add 271 → Z.cpu.gpr.rax = 18446744073709551615#64 → Z.cpu.gpr.rsp = sp - 8#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv { X.cpu.gpr with rsp := sp - 8#64 } r]) gP gE Z t')
    -- `ndi_pc`, of the bytes at the entry
    (hin : CodeIn L Ipa.ipa_at Ipa.ipa) (hinh : CodeIn L Hwc.hwc_at Hwc.hwc)
    {mlc sl ms : List Byte} {Pq Pk Ps : (Addr → Byte) → Prop}
    (hcpq : Gor.PcpyAt prof L o 4198592#64 Pq)
    (hinm : CodeIn L 6500704#64 mlc) (hm0 : 0 < mlc.length)
    (hinX : CodeIn L Mnx.mnx_at Mnx.mnx) (hinI : CodeIn L Imm.imm_at Imm.imm)
    (hinl : CodeIn L 4198664#64 sl) (hl0 : 0 < sl.length) (hlenA : Str.LenAt prof L o 4198664#64 Pk)
    (hinz : CodeIn L 4198528#64 ms) (hz0 : 0 < ms.length) (hset : Ipa.SetAt prof L o 4198528#64 Ps)
    (hgf : Ipa.GotF F) (hdf₀ : s₀.cpu.rflags.df = false)
    (hint : CodeIn L Tgv.tgv_at Tgv.tgv)
    {hw : Addr} {cnt Ec H sz : Nat}
    (hn : hw = 2#64 ∧ cnt = 3 ∧ Ec = 8 ∧ H = 4 ∧ sz = 151 ∨ hw = 6#64 ∧ cnt = 4 ∧ Ec = 16 ∧ H = 8 ∧ sz = 320)
    (hPq : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) → ¬ Hv a →
      W₁ a = fV W sp X.cpu.gpr a) → Pq W₁)
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
      Hp (withNew F N) (N ++ Wl) fsb (sp.toNat - 4144) (1072 * 0 + 73840) U →
      Seg prof G Wl' L s₂ o → Base s₂ lim (b + size pad 656#64 + C2 b pad) fsb ks → KeptW Wl' s₂ Z →
      Agree G Z.proc.mm.mem W₂ → Eqo sp W₂ (lV (bV U m)) → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr.rsp = sp + 128#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv { X.cpu.gpr with rsp := sp - 8#64 } (.procExe x)] ++ evs ++ [ndiEv]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  exact
    ndi_all (ip := ip) (Pa := fun k W => Hp (withNew F N) (N ++ Wl) fsb (sp.toNat - 4144) (1072 * k + 73840) W)
    (ka := 0) c mc cx hgo
    hsn htop hpw hst hsm hlo hbs hbuf hfr hpf hpn hpz hpp hof hoz hps hpre hinc hc0 hcpy h1 h2 h3 h4 h5 hK hA hrip hsp
    ke hin hinh hcpq hinm hm0 (Mal.at_ok hinX hinI) (by omega) (fun _ _ => Iff.rfl) hinl hl0 hlenA hinz hz0 hset
    hgf hdf₀ hint hn
    hPq
    (fun x n s Vc M g hx h2n hn4 _ hs1 hg hVc hAf W₁ hW => hpa c mc hpre hsn hlo hbs hx h2n hn4 hs1 hg hVc hAf hW)
    hPk hPs he hal hFs hpg
    hx1 hx1z hx2 hx2z htls hU hm6 hhw hfh hfm hpl0 hf1 hf2 hWb hfN hW7a hW7b hFR hlenV hslV hpl hid him hfp hph hpgs
    hla hmg hGo hGc hfit hGw hGr hcode hww hlG hl hin₂ h₂ hret k

end FV7z.Ndi
