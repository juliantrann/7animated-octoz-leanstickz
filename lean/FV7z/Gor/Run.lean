import FV7z.Gor.Tail
import FV7z.Mal.Pre
/-!
# `_dl_get_origin` with its `malloc` (PLAN.md G3, startup)

- `nbOf`, `clsA_of`, `nbOf_bnd`: the chunk size of `malloc (n)`, `2 ≤ n ≤ 4104`.
- `lay`: the first chunk after the break `b`, below the end `b + size` of the first `MORECORE`.
- `MCx`: what `mal_firstn` needs besides the bytes below the break (`Mal.MPre`) and the stack.
- `Kd`: the caller's continuation after the `malloc` and the copy: the directory's `s` bytes and a NUL at
  `p = Tp b + 16`, the other bytes `M` (`Mal.After`) but for the slot below `B`, the saved registers back.
- `g124`, `g278`: from the `call` of `malloc` at 124 (`malloc (2)`, `"/"`) and at 278 (`malloc (s + 2)`, `mempcpy`) to
  the caller (`Kd`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Smm (corr size smEv smEv2)
open FV7z.Mhi (Tp C2 Sz Vh mhi mhi_at)
open FV7z.Mal (MPre After mal_at mal Vm)
namespace FV7z.Gor

/-- The chunk size of `malloc (n)`. -/
def nbOf (n : Nat) : Addr := if n ≤ 8 then 32#64 else BitVec.ofNat 64 n + 23#64 &&& 18446744073709551600#64

theorem clsA_of {n : Nat} (h : n ≤ 4104) : Im5.ClsA (BitVec.ofNat 64 n) (nbOf n) := by
  have e : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  unfold nbOf Im5.ClsA Im3.Cls
  split
  · exact .inl (.inr ⟨by omega, rfl⟩)
  · rcases Nat.lt_or_ge n 1001 with h' | h'
    · exact .inl (.inl ⟨by omega, by omega, rfl⟩)
    · exact .inr ⟨by omega, by omega, rfl⟩

theorem nbOf_bnd {n : Nat} (h : n ≤ 4104) : 32 ≤ (nbOf n).toNat ∧ (nbOf n).toNat ≤ 4112 := by
  obtain ⟨k, k1, k2, e⟩ := (clsA_of h).cases
  rw [e, BitVec.toNat_ofNat]
  omega

/-- The slot of the return address of a `call` with `rsp = B`, in the stack of `malloc`'s frame from `B - 240`. -/
theorem slot8 {Wl : List Rgn} {B : Addr} (hst : ∀ i < 408, Foot Wl (Addr.add (B - 240#64 - 168) i)) :
    ∀ i < 8, Foot Wl (Addr.add (B - 8) i) := fun i hi => by
  have h := hst (400 + i) (by omega)
  rwa [show Addr.add (B - 240#64 - 168) (400 + i) = Addr.add (B - 8) i by simp only [Addr.add]; bv_omega] at h

/-- The first chunk: `b + corr b` 16-aligned at most 15 above `b`, the top `Tp b` 656 above, and a chunk of up to 4112
bytes with its next size word below the end of the first `MORECORE`. -/
theorem lay {b pad nb : Addr} (hb : b.toNat < 2 ^ 47) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47) (hpd : 4112 ≤ pad.toNat)
    (hn : nb.toNat ≤ 4112) :
    b.toNat ≤ (b + corr b).toNat ∧ (b + corr b).toNat ≤ b.toNat + 15 ∧
      (b + corr b).toNat + 656 + nb.toNat + 16 ≤ (b + size pad 656#64).toNat ∧
      (Tp b).toNat = (b + corr b).toNat + 656 ∧ (Tp b + 16#64).toNat = (b + corr b).toNat + 672 := by
  have hR : (size pad 656#64).toNat = (4127 + pad.toNat + 656) / 4096 * 4096 :=
    Smm.size_toNat (pad := pad) (nb := 656#64) (by show 656 + pad.toNat + 4127 < 2 ^ 47; omega)
  have hc := Smm.corr_toNat b
  have hc16 : (corr b).toNat < 16 := by rw [hc]; omega
  have e1 : (b + corr b).toNat = b.toNat + (corr b).toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : (b + size pad 656#64).toNat = b.toNat + (size pad 656#64).toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have e3 : (Tp b).toNat = (b + corr b).toNat + 656 := by
    show (b + corr b + 656#64).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have e4 : (Tp b + 16#64).toNat = (b + corr b).toNat + 672 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, e3]; omega
  refine ⟨by omega, by omega, by omega, e3, e4⟩

theorem foot_wn {F : Footprint} {N : List Rgn} (hown : F.own = []) {a : Addr} (h : Foot F.data a) :
    Foot (withNew F N).data a := by
  simp only [Footprint.data, hown, List.append_nil] at h ⊢
  rcases foot_append_iff.1 h with h | h
  · exact foot_append_iff.2 (.inl (foot_append_iff.2 (.inr h)))
  · exact foot_append_iff.2 (.inr h)

/-- What `mal_firstn` needs besides the bytes below the break and the stack: the code, the root `Base`, the footprints
of the globals and of the new pages `N`, the bounds; `mp_.top_pad` at least 4112. -/
structure MCx (prof : Profile) (F : Footprint) (Wl N : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (lim : Nat) (b fsb : Addr) (ks : Kst) (pad sm mx : BitVec 64) : Prop where
  hB : Base s₀ lim b fsb ks
  hin : CodeIn L mal_at mal
  hinH : CodeIn L mhi_at mhi
  hinP : CodeIn L Pmi.pmi_at Pmi.pmi
  hinG : CodeIn L Tgv.tgv_at Tgv.tgv
  hinT : CodeIn L Tci.tci_at Tci.tci
  hinI : CodeIn L Imm.imm_at Imm.imm
  hinS : CodeIn L Smm.smm_at Smm.smm
  hinD : CodeIn L Dmc.dmc_at Dmc.dmc
  hinK : CodeIn L Sbrk.sbk_at Sbrk.sbk
  hinb : CodeIn L Brk.brk_at Brk.brk
  hW : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot Wl a
  hhk : ∀ i < 8, Foot Wl (Addr.add (8013152#64) i)
  hcur : ∀ i < 8, Foot Wl (Brk.curbrk.add i)
  hml : ∀ i < 4, Foot Wl (Addr.add (7944640#64) i)
  hpb : ∀ i < 4, Foot Wl (Addr.add (8013220#64) i)
  hgmf : ∀ i < 8, Foot Wl (Addr.add (8013224#64) i)
  hft : ∀ i < 8, Foot Wl (Addr.add (fsb + 18446744073709551576#64) i)
  hfa : ∀ i < 8, Foot Wl (Addr.add (fsb + 18446744073709551592#64) i)
  hfm : ∀ i < 4, Foot Wl (Addr.add (fsb + 24#64) i)
  hfl : ∀ i < 8, Foot F.data (Addr.add (fsb + 40#64) i)
  hfs1 : ∀ i < 1, Foot F.data (Addr.add (fsb + 18446744073709551584#64) i)
  hfs : 8029888 + 40 ≤ fsb.toNat
  hfb : fsb.toNat + 48 ≤ b.toNat
  hnb : 656 + pad.toNat + 4127 < 2 ^ 47
  hpd : 4112 ≤ pad.toNat
  hms : mx.toNat ≤ sm.toNat
  hsu : sm.toNat < 2 ^ 47
  hmg : ∀ t p, o t (.memFail p) = none
  hlim : pageUp (b + size pad 656#64).toNat / 4096 ≤ lim
  hbl : 8029888 ≤ b.toNat
  hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096)
  hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 4112 + 16 →
    Foot (N ++ Wl) a
  hown : F.own = []

variable {prof : Profile} {F : Footprint} {Wl N : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64}

/-- A byte below the break `b` that the first `malloc` does not write (`Mal.near`): not in `main_arena` and `mp_`,
`global_max_fast`, `__curbrk`, the TLS words below `fsb - 16`. -/
abbrev Lo (b fsb a : Addr) : Prop :=
  a.toNat < b.toNat ∧ ¬ (7940480 ≤ a.toNat ∧ a.toNat < 7943136) ∧ ¬ (8013224 ≤ a.toNat ∧ a.toNat < 8013232) ∧
    ¬ (8014904 ≤ a.toNat ∧ a.toNat < 8014912) ∧ ¬ (fsb.toNat - 40 ≤ a.toNat ∧ a.toNat < fsb.toNat - 16)

/-- The caller's continuation after the `malloc (n)` of `_dl_get_origin` and the copy of the `s` bytes of the
directory: the new root `s₁` and its `Seg`, the bytes `W` (the NUL at `p + s`, the others `M` but for `[p, p + s]` and
the slot below `B`), `M` from `Vc` (the bytes at the `call`, `Vb` but for the slot) by `Mal.After`, `M` and `Vb` the
same from `B` on; `rax = p`, `rsp = B + 4144`, the four saved registers read back from `Vb`, `r14`, `r15` kept. -/
def Kd (prof : Profile) (F : Footprint) (Wl N : List Rgn) (L : List (Addr × List Byte)) (o : Oracle) (lim : Nat)
    (b fsb : Addr) (ks : Kst) (pad sm : BitVec 64) (gev : List Event) (gP : State → Nat → List Event → Prop)
    (gE : Outcome → List Event → Prop) (Vb : Addr → Byte) (B e' : Addr) (j : Nat) (r14 r15 : Addr) : Prop :=
  ∀ (n s : Nat) (s₁ : State) (Vc M W : Addr → Byte) (evs : List Event) (Z : State) (t' : Nat) (g : Gprs),
    Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + size pad 656#64 + C2 b pad) fsb ks →
    KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem W →
    2 ≤ n → n ≤ 4097 → 1 ≤ s → s + 1 ≤ n → g.rsp = B - 8 →
    (∀ a : Addr, a.toNat < B.toNat - 8 ∨ B.toNat ≤ a.toNat → Vc a = Vb a) →
    After fsb (B - 240#64) b pad sm (nbOf n) g Vc M →
    (∀ a : Addr, B.toNat ≤ a.toNat → M a = Vb a) → (∀ a : Addr, Lo b fsb a → M a = Vb a) →
    W (Addr.add (Tp b + 16#64) s) = 0 →
    (∀ a : Addr, (a.toNat < (Tp b + 16#64).toNat ∨ (Tp b + 16#64).toNat + s + 1 ≤ a.toNat) →
      (a.toNat < B.toNat - 8 ∨ B.toNat ≤ a.toNat) → W a = M a) →
    Z.cpu.rip = e'.add j → Z.cpu.gpr.rax = Tp b + 16#64 → Z.cpu.gpr.rsp = B + 4144#64 →
    Z.cpu.gpr.rbx = rdq(Vb, B + 4104#64) → Z.cpu.gpr.rbp = rdq(Vb, B + 4112#64) →
    Z.cpu.gpr.r12 = rdq(Vb, B + 4120#64) → Z.cpu.gpr.r13 = rdq(Vb, B + 4128#64) →
    Z.cpu.gpr.r14 = r14 → Z.cpu.gpr.r15 = r15 →
    (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = b ∧ g₂.r14 = size pad 656#64 ∧
      (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂])) →
    GoG prof L o (gev ++ evs) gP gE Z t'

def pc124 : List Byte := [0xe8, 0x3f, 0x41, 0xf8, 0xff]
theorem pc124_0 : ∀ feat, Dec feat pc124 0 (FV7z.mk .call 64 [.rel 18446744073709044031] 5) := by dec_rfl
theorem w_124 : pc124 <+: gor.drop 124 := by decide +kernel
theorem call_124 (feat : Features) : Dec feat gor 124 (FV7z.mk .call 64 [.rel 18446744073709044031] 5) :=
  Dec.shift (j := 124) (k := 0) (pc124_0 feat) w_124 (Nat.zero_le _)

def pc278 : List Byte := [0xe8, 0xa5, 0x40, 0xf8, 0xff]
theorem pc278_0 : ∀ feat, Dec feat pc278 0 (FV7z.mk .call 64 [.rel 18446744073709043877] 5) := by dec_rfl
theorem w_278 : pc278 <+: gor.drop 278 := by decide +kernel
theorem call_278 (feat : Features) : Dec feat gor 278 (FV7z.mk .call 64 [.rel 18446744073709043877] 5) :=
  Dec.shift (j := 278) (k := 0) (pc278_0 feat) w_278 (Nat.zero_le _)

/-- The `call` of `malloc (n)` at `jc` (`rsp = B`) and `mal_firstn`, back at `jc + 5`: the facts on the bytes. -/
theorem gmal (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor)
    (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx)
    {X : State} {t : Nat} {Vb : Addr → Byte} {B : Addr} {n jc rel : Nat}
    (hd : Dec prof.feat gor jc (FV7z.mk .call 64 [.rel rel] 5)) (hjc : jc + 5 < 352)
    (htgt : gor_at.add (jc + 5) + BitVec.ofNat 64 rel = mal_at)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem Vb) (hrip : X.cpu.rip = gor_at.add jc)
    (hdi : X.cpu.gpr.rdi = BitVec.ofNat 64 n) (hn2 : 2 ≤ n) (hn : n ≤ 4097) (hsp : X.cpu.gpr.rsp = B)
    (hpre : MPre F Vb b fsb pad sm mx)
    (hst : ∀ i < 408, Foot Wl (Addr.add (B - 240#64 - 168) i))
    (hsl : 8029888 + 408 ≤ B.toNat) (hBt : B.toNat + 4144 ≤ 2 ^ 64)
    (hbs : (b + size pad 656#64).toNat + 4096 + 408 ≤ B.toNat)
    (k : ∀ (s₁ : State) (Vc M : Addr → Byte) (evs : List Event) (Z : State) (t' : Nat),
      Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + size pad 656#64 + C2 b pad) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem M →
      (∀ a : Addr, a.toNat < B.toNat - 8 ∨ B.toNat ≤ a.toNat → Vc a = Vb a) →
      After fsb (B - 240#64) b pad sm (nbOf n) (X.cpu.gpr.set 4 (B - 8)) Vc M →
      (∀ a : Addr, B.toNat ≤ a.toNat → M a = Vb a) →
      (∀ a : Addr, Lo b fsb a → M a = Vb a) →
      Z.cpu.rip = gor_at.add (jc + 5) → Z.cpu.gpr.rax = Tp b + 16#64 → Z.cpu.gpr.rsp = B →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = b ∧ g₂.r14 = size pad 656#64 ∧
        (evs = [smEv g₁ pad b] ∨ evs = [smEv g₁ pad b, smEv2 g₂])) →
      GoG prof L o (gev ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := mc.hB.brk_lt
  have hpd := mc.hpd
  have hbl := mc.hbl
  have hfs := mc.hfs
  have hb47 : b.toNat < 2 ^ 47 := by omega
  obtain ⟨-, hnb⟩ := nbOf_bnd (n := n) (by omega)
  obtain ⟨hbc, hc15, hT0, hT1, -⟩ := lay hb47 mc.hnb mc.hpd hnb
  have hS : (B - 240#64).toNat = B.toNat - 240 := by bv_omega
  have hb8 : (B - 8).toNat = B.toNat - 8 := by bv_omega
  have e8 : B - 240#64 + 232#64 = B - 8 := by bv_omega
  have hn64 : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  refine c.s_call hK hA hin (lt_len (by omega)) hrip hd mc.hin (by rw [Mal.mal_length]; decide) htgt
    (fun i hi => by rw [hsp]; exact slot8 hst i hi) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  rw [hsp] at hAY hgY
  have hVc : ∀ a : Addr, a.toNat < B.toNat - 8 ∨ B.toNat ≤ a.toNat →
      Vst Vb (B - 8) (toBytesLE (gor_at.add (jc + 5)) 8) a = Vb a := fun a ha =>
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega) (by rw [toBytesLE_length, hb8]; omega)
  have hp := hpre.lo mc.hfs mc.hfb fun a ha => hVc a (.inl (by omega))
  have hspY : (X.cpu.gpr.set 4 (B - 8)).rsp = B - 240#64 + 232#64 := by rw [e8]; rfl
  refine Mal.mal_firstn (n := BitVec.ofNat 64 n) (nb := nbOf n) (S := B - 240#64) (N := N) (e₂ := gor_at)
    (j₂ := jc + 5) c mc.hB mc.hin mc.hinH mc.hinP mc.hinG mc.hinT mc.hinI mc.hinS mc.hinD mc.hinK mc.hinb hKY hAY hrY
    hp.hook (by rw [hgY]; exact hspY) (by rw [hgY]; exact hdi) (clsA_of (by omega)) (by rw [hS]; omega)
    (by rw [hS]; omega) hst mc.hW mc.hhk mc.hcur mc.hml mc.hpb mc.hgmf mc.hft mc.hfa mc.hfm mc.hfl mc.hfs1 mc.hfs mc.hfb
    hp.mi hp.u32 hp.u64 hp.sd hp.mt hp.lk hp.tc hp.fz hp.tb hp.m0 hp.m1 hp.m2 hp.m3 hp.ps hp.thr hp.sz hp.hpad mc.hnb
    hp.fl hp.mc hp.cb hp.ml0 hp.k0 hp.hsm hp.sb hp.hmx mc.hms mc.hsu hp.p0 mc.hmg mc.hlim mc.hbl (by rw [hS]; omega)
    mc.hN (.inr (by omega)) (fun a h1 h2 => mc.hh a h1 (by omega)) hp.z hin (lt_len (by omega))
    (by
      rw [e8, Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by rw [hb8]; omega), ofBytesLE_toBytesLE (n := 8) rfl])
    ?_
  intro Vd V₁ M evs s₁ Z t₂ hc hB' hK' hA' hD hO hM hr hax hregs hr13 hev
  rw [hgY] at hD hregs hr13
  have hAf : After fsb (B - 240#64) b pad sm (nbOf n) (X.cpu.gpr.set 4 (B - 8))
      (Vst Vb (B - 8) (toBytesLE (gor_at.add (jc + 5)) 8)) M := ⟨Vd, V₁, hD, hO, hM⟩
  have MV : ∀ a : Addr, B.toNat ≤ a.toNat → M a = Vb a := fun a ha => by
    rw [hAf.far hspY (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; omega) mc.hfs mc.hfb (by rw [hS]; omega) hT1
      (a := a) (by rw [hS]; omega), hVc a (.inr ha)]
  have ML : ∀ a : Addr, Lo b fsb a → M a = Vb a := fun a ⟨ha, h1, h2, h3, h4⟩ => by
    rw [hAf.near hspY (by rw [hS]; omega) (by rw [hS]; omega) (by rw [hS]; omega) mc.hfs mc.hfb (by rw [hS]; omega) hT1
      hbc (a := a) ha h1 h2 h3 h4, hVc a (.inl (by omega))]
  refine k s₁ _ M evs Z t₂ hc hB' hK' hA' hVc hAf MV ML hr hax ?_ hregs.2.1 hregs.2.2.1 hregs.2.2.2 hr13.1 hr13.2.1
    hr13.2.2 hev
  rw [hregs.1, BitVec.sub_add_cancel]

/-- Bytes of `M` read as those of `Vb` from `B` on. -/
theorem rd_hi {M Vb : Addr → Byte} {B : Addr} (MV : ∀ a : Addr, B.toNat ≤ a.toNat → M a = Vb a) {x : Addr}
    (h1 : B.toNat ≤ x.toNat) (h2 : x.toNat + 8 ≤ 2 ^ 64) : rdq(M, x) = rdq(Vb, x) := by
  rw [Sbrk.rd_eq (V' := M) (V := Vb) (x := x) (n := 8) h2 fun a h _ => MV a (by omega)]

theorem off4 {B : Addr} {d : Nat} (hd : d < 4144) (h : B.toNat + 4144 ≤ 2 ^ 64) :
    (B + BitVec.ofNat 64 d).toNat = B.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- From the `call` of `malloc (2)` at 124 (`rsp = B`): `malloc`, then `"/"` and a NUL at `p` (`t129`), to the caller
(`Kd` with `n = 2`, `s = 1`). -/
theorem g124 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor)
    (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx)
    {X : State} {t : Nat} {Vb : Addr → Byte} {B e' : Addr} {code : List Byte} {j : Nat}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem Vb) (hrip : X.cpu.rip = gor_at.add 124)
    (hdi : X.cpu.gpr.rdi = BitVec.ofNat 64 2) (hsp : X.cpu.gpr.rsp = B)
    (hpre : MPre F Vb b fsb pad sm mx)
    (hst : ∀ i < 408, Foot Wl (Addr.add (B - 240#64 - 168) i))
    (hsl : 8029888 + 408 ≤ B.toNat) (hBt : B.toNat + 4144 ≤ 2 ^ 64)
    (hbs : (b + size pad 656#64).toNat + 4096 + 408 ≤ B.toNat)
    (hf : ∀ i < 40, Foot F.data (Addr.add (B + 4104#64) i))
    (hinr : CodeIn L e' code) (hj : j < code.length) (hra : rdq(Vb, B + 4136#64) = e'.add j)
    (k : Kd prof F Wl N L o lim b fsb ks pad sm gev gP gE Vb B e' j X.cpu.gpr.r14 X.cpu.gpr.r15) :
    GoG prof L o gev gP gE X t := by
  have hbt := mc.hB.brk_lt
  have hpd := mc.hpd
  have hb47 : b.toNat < 2 ^ 47 := by omega
  obtain ⟨hn1, hnb⟩ := nbOf_bnd (n := 2) (by omega)
  obtain ⟨hbc, hc15, hT0, -, hpN⟩ := lay hb47 mc.hnb mc.hpd hnb
  refine gmal c hin mc (n := 2) (call_124 _) (by omega) (by decide) hK hA hrip hdi (le_refl _) (by omega) hsp hpre
    hst hsl hBt hbs ?_
  intro s₁ Vc M evs Z t₂ hc hB' hK' hA' hVc hAf MV ML hr hax hsp' _ _ _ _ h14 h15 hev
  have hpt : (Tp b + 16#64).toNat + 2 ≤ 2 ^ 64 := by rw [hpN]; omega
  refine t129 hc hin hK' hA' hr hsp' hax (fun h => by
      have h' : (Tp b + 16#64).toNat = 0 := by rw [h]; rfl
      omega)
    (fun i hi => mc.hh _ (by rw [Tci.at_add _ _ (by omega), hpN]; omega)
      (by rw [Tci.at_add _ _ (by omega), hpN]; omega))
    hBt hpt (.inl (by rw [hpN]; omega)) (fun i hi => foot_wn mc.hown (hf i hi)) hinr hj
    (by rw [rd_hi MV (by rw [off4 (by omega) hBt]; omega) (by rw [off4 (by omega) hBt]; omega)]; exact hra) ?_
  intro Z₂ t₃ hK₂ hA₂ hr₂ hax₂ hsp₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂
  have R : ∀ d < 4136, rdq(M, B + BitVec.ofNat 64 d) = rdq(Vb, B + BitVec.ofNat 64 d) := fun d hd =>
    rd_hi MV (by rw [off4 (by omega) hBt]; omega) (by rw [off4 (by omega) hBt]; omega)
  refine k 2 1 s₁ Vc M _ evs Z₂ t₃ (X.cpu.gpr.set 4 (B - 8)) hc hB' hK₂ hA₂ (le_refl _) (by omega) (le_refl _)
    (le_refl _) rfl hVc hAf MV ML ?_ (fun a h1 _ => Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length]; omega)
      (by rw [toBytesLE_length]; omega)) hr₂ hax₂ hsp₂ (hbx₂.trans (R 4104 (by omega)))
    (hbp₂.trans (R 4112 (by omega))) (h12₂.trans (R 4120 (by omega))) (h13₂.trans (R 4128 (by omega)))
    (h14₂.trans h14) (h15₂.trans h15) hev
  rw [CpuFeat.Vst_at _ _ _ (j := 1) (by rw [toBytesLE_length]; omega) (by rw [toBytesLE_length]; omega)]
  first | rfl | decide

/-- From the `call` of `malloc (s + 2)` at 278 (`rsp = rbp = B`, `ebx = s`): `malloc`, then `mempcpy (p, B, s)` and
the NUL (`t283`), to the caller (`Kd` with `n = s + 2`). -/
theorem g278 (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gor_at gor)
    (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx)
    {X : State} {t : Nat} {Vb : Addr → Byte} {B e' : Addr} {code cpy : List Byte} {j s : Nat}
    {Pm : (Addr → Byte) → Prop}
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem Vb) (hrip : X.cpu.rip = gor_at.add 278)
    (hdi : X.cpu.gpr.rdi = BitVec.ofNat 64 (s + 2)) (hbx : X.cpu.gpr.rbx = BitVec.ofNat 64 s) (hs1 : 1 ≤ s)
    (hs : s < 4096) (hsp : X.cpu.gpr.rsp = B) (hbp : X.cpu.gpr.rbp = B)
    (hpre : MPre F Vb b fsb pad sm mx)
    (hst : ∀ i < 408, Foot Wl (Addr.add (B - 240#64 - 168) i))
    (hsl : 8029888 + 408 ≤ B.toNat) (hBt : B.toNat + 4144 ≤ 2 ^ 64)
    (hbs : (b + size pad 656#64).toNat + 4096 + 408 ≤ B.toNat)
    (hBw : ∀ i < 4096, Foot F.data (Addr.add B i)) (hf : ∀ i < 40, Foot F.data (Addr.add (B + 4104#64) i))
    (hinc : CodeIn L 4198592#64 cpy) (hc0 : 0 < cpy.length) (hcpy : PcpyAt prof L o 4198592#64 Pm)
    (hPm : ∀ W : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → W a = Vb a) → Pm W)
    (hinr : CodeIn L e' code) (hj : j < code.length) (hra : rdq(Vb, B + 4136#64) = e'.add j)
    (k : Kd prof F Wl N L o lim b fsb ks pad sm gev gP gE Vb B e' j X.cpu.gpr.r14 X.cpu.gpr.r15) :
    GoG prof L o gev gP gE X t := by
  have hbt := mc.hB.brk_lt
  have hpd := mc.hpd
  have hb47 : b.toNat < 2 ^ 47 := by omega
  have hbl := mc.hbl
  have hfs := mc.hfs
  obtain ⟨hn1, hnb⟩ := nbOf_bnd (n := s + 2) (by omega)
  obtain ⟨hbc, hc15, hT0, -, hpN⟩ := lay hb47 mc.hnb mc.hpd hnb
  have hb8 : (B - 8).toNat = B.toNat - 8 := by bv_omega
  refine gmal c hin mc (n := s + 2) (call_278 _) (by omega) (by decide) hK hA hrip hdi (by omega) (by omega) hsp hpre
    hst hsl hBt hbs ?_
  intro s₁ Vc M evs Z t₂ hc hB' hK' hA' hVc hAf MV ML hr hax hsp' hbx' hbp' _ _ h14 h15 hev
  have hpt : (Tp b + 16#64).toNat + s + 1 ≤ 2 ^ 64 := by rw [hpN]; omega
  refine t283 hc hin hK' hA' hr hsp' (hbp'.trans hbp) hax (fun h => by
      have h' : (Tp b + 16#64).toNat = 0 := by rw [h]; rfl
      omega) (hbx'.trans hbx) hs (by omega) hBt hpt (.inl (by rw [hpN]; omega))
    (fun i hi => mc.hh _ (by rw [Tci.at_add _ _ (by omega), hpN]; omega)
      (by rw [Tci.at_add _ _ (by omega), hpN]; omega))
    (fun i hi => foot_append_iff.2 (.inr (slot8 hst i hi))) (fun i hi => foot_wn mc.hown (hBw i hi))
    (fun i hi => foot_wn mc.hown (hf i hi)) hinc hc0 hcpy
    (hPm _ fun a ha => by
      rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, hb8]; omega) (.inl (by rw [hb8]; omega)),
        ML a ⟨by omega, by omega, by omega, by omega, by omega⟩]) hinr hj
    (by rw [rd_hi MV (by rw [off4 (by omega) hBt]; omega) (by rw [off4 (by omega) hBt]; omega)]; exact hra) ?_
  intro Z₂ t₃ W hK₂ hA₂ _ hnul hout hr₂ hax₂ hsp₂ hbx₂ hbp₂ h12₂ h13₂ h14₂ h15₂
  have R : ∀ d < 4136, rdq(M, B + BitVec.ofNat 64 d) = rdq(Vb, B + BitVec.ofNat 64 d) := fun d hd =>
    rd_hi MV (by rw [off4 (by omega) hBt]; omega) (by rw [off4 (by omega) hBt]; omega)
  exact k (s + 2) s s₁ Vc M W evs Z₂ t₃ (X.cpu.gpr.set 4 (B - 8)) hc hB' hK₂ hA₂ (by omega) (by omega) hs1
    (by omega) rfl hVc hAf MV ML hnul hout hr₂ hax₂ hsp₂ (hbx₂.trans (R 4104 (by omega)))
    (hbp₂.trans (R 4112 (by omega))) (h12₂.trans (R 4120 (by omega))) (h13₂.trans (R 4128 (by omega)))
    (h14₂.trans h14) (h15₂.trans h15) hev

end FV7z.Gor
