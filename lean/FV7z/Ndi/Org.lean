import FV7z.Ndi.Head
import FV7z.Ndi.Mv
import FV7z.Gor.Ok
/-!
# `_dl_non_dynamic_init`: from its entry to `_dl_init_paths`, through `_dl_get_origin` (PLAN.md G3, startup)

`ndi_ab`: `ndi_a` (the prologue, the `call`), `Gor.gor_ok` (`readlink`, the first `malloc`, the copy of the
directory to `p = Tp b + 16`), then `ndi_b` on the bytes `W'` after the return, with `Cx.mv`: what `Cx` reads is not
written by `_dl_get_origin` (`Same`), as the bytes from `sp` on are the stack above its frame and the bytes below the
break that `malloc` does not write are as before (`Lo`).

- `nV W sp g`: the bytes at the entry of `_dl_get_origin`, `W` with the five pushes (`fV`) and the return address.
- `ke` (`readlink` failing, `rax = -1` at the `ret` of `_dl_get_origin`) is left to the caller.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Smm (corr size smEv smEv2)
open FV7z.Mhi (Tp C2)
open FV7z.Mal (MPre After)
open FV7z.Gor (gor_ok MCx Vg Vg_lo Vg_hi Lo lay nbOf nbOf_bnd gEv gor_at gor gor_length)
namespace FV7z.Ndi

/-- The bytes at the entry of `_dl_get_origin`: the five pushes, the return address `ndi_at + 21` at `sp - 8`. -/
def nV (W : Addr → Byte) (sp : Addr) (g : Gprs) : Addr → Byte :=
  Vst (fV W sp g) (sp - 8#64) (toBytesLE (ndi_at.add 21) 8)

theorem m8 (sp : Addr) (h : 8 ≤ sp.toNat) : (sp - 8#64).toNat = sp.toNat - 8 := by bv_omega
theorem p8 (sp : Addr) : sp - 8#64 + 8#64 = sp := by bv_omega

/-- Below the pushes, `fV` is the bytes it was given. -/
theorem fV_lo {V : Addr → Byte} {sp : Addr} {g : Gprs} (hsn : sp.toNat + 128 ≤ 2 ^ 64) {a : Addr}
    (ha : a.toNat < sp.toNat + 80) : fV V sp g a = V a := by
  have o : ∀ (U : Addr → Byte) (k : Nat) (w : BitVec 64), 80 ≤ k → k ≤ 112 →
      Vst U (sp + BitVec.ofNat 64 k) (toBytesLE w 8) a = U a := fun U k w h1 h2 =>
    Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, qn sp k (by omega)]; omega)
      (.inl (by rw [qn sp k (by omega)]; omega))
  unfold fV
  rw [o _ 80 _ (by omega) (by omega), o _ 88 _ (by omega) (by omega), o _ 96 _ (by omega) (by omega),
    o _ 104 _ (by omega) (by omega), o _ 112 _ (by omega) (by omega)]

/-- Off the return address, `nV` is `fV`. -/
theorem nV_fV {W : Addr → Byte} {sp : Addr} {g : Gprs} (h8 : 8 ≤ sp.toNat) (hsn : sp.toNat + 128 ≤ 2 ^ 64)
    {a : Addr} (ha : a.toNat < sp.toNat - 8 ∨ sp.toNat ≤ a.toNat) : nV W sp g a = fV W sp g a := by
  unfold nV
  rw [Tun.Vst_out _ _ _ _ (by rw [toBytesLE_length, m8 sp h8]; omega)
    (by rw [toBytesLE_length, m8 sp h8]; omega)]

variable {F : Footprint} {Wl N : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {lim : Nat} {b fsb : Addr} {ks : Kst} {pad sm mx : BitVec 64}

/-- From the entry of `_dl_non_dynamic_init` (bytes `W`, `rsp = sp + 120`) to the first instruction of
`_dl_init_paths`: `_dl_get_origin` gives `p = Tp b + 16` (the directory of `/proc/self/exe`, NUL ended, in the first
chunk of the heap) and the bytes `W'`, which are `fV W sp g` from `sp` on and below the break where `malloc` does not
write; `ndi_b` then stores `p` as the main map's `l_origin` (`hV`). -/
theorem ndi_ab {pl pc ip cpy : List Byte} {Pm : (Addr → Byte) → Prop} {E : Ev} {W : Addr → Byte} {sp : Addr}
    {ph pn : BitVec 64} (c : Seg prof F Wl L s₀ o) (mc : MCx prof F Wl N L s₀ o lim b fsb ks pad sm mx)
    (cx : Cx prof F Wl L o pl pc Pm E (fV W sp X.cpu.gpr) sp) (hgo : CodeIn L gor_at gor)
    (hip : CodeIn L 6981872#64 ip) (hp0 : 0 < ip.length)
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
    (h1 : rdq(fV W sp X.cpu.gpr, 8029448#64) = 0#64) (h2 : rdq(fV W sp X.cpu.gpr, 8029568#64) = ph)
    (h3 : rdq(fV W sp X.cpu.gpr, 8029592#64) = pn) (h4 : rdq(fV W sp X.cpu.gpr, 8029424#64) = 0#64)
    (h5 : rdd(fV W sp X.cpu.gpr, 7937248#64) = 0#32)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem W) (hrip : X.cpu.rip = ndi_at.add 0)
    (hsp : X.cpu.gpr.rsp = sp + 120#64)
    (ke : ∀ r Z t', KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem (Gor.frV (nV W sp X.cpu.gpr) { X.cpu.gpr with rsp := sp - 8#64 }) →
      Z.cpu.rip = gor_at.add 271 → Z.cpu.gpr.rax = 18446744073709551615#64 → Z.cpu.gpr.rsp = sp - 8#64 →
      Z.cpu.gpr.rbx = X.cpu.gpr.rbx → Z.cpu.gpr.rbp = X.cpu.gpr.rbp → Z.cpu.gpr.r12 = X.cpu.gpr.r12 →
      Z.cpu.gpr.r13 = X.cpu.gpr.r13 → Z.cpu.gpr.r14 = X.cpu.gpr.r14 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv { X.cpu.gpr with rsp := sp - 8#64 } r]) gP gE Z t')
    (k : ∀ (x : ExePath) (n s : Nat) (s₁ : State) (Vc M W' : Addr → Byte) (evs : List Event) (g : Gprs)
      (Z : State) (t' : Nat) (W'' : Addr → Byte), x.bytes.length < 4096 →
      Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + size pad 656#64 + C2 b pad) fsb ks →
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
      KeptW (N ++ Wl) s₁ Z →
      Agree (withNew F N) Z.proc.mm.mem (Vst W'' (sp - 8#64) (toBytesLE (ndi_at.add 2063) 8)) →
      Eqo sp W'' (hV W' (Tp b + 16#64) ph pn) → Z.cpu.rip = 6981872#64 → Z.cpu.gpr.rsp = sp - 8#64 →
      Z.cpu.gpr.rdi = 0#64 → Z.cpu.gpr.r15 = X.cpu.gpr.r15 →
      GoG prof L o (gev ++ [gEv { X.cpu.gpr with rsp := sp - 8#64 } (.procExe x)] ++ evs) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have h72 := cx.h72
  have hfs := mc.hfs
  have hbl := mc.hbl
  have hbt := mc.hB.brk_lt
  have hb47 : b.toNat < 2 ^ 47 := by omega
  refine ndi_a c cx.hin hgo (by rw [gor_length]; decide) hsn (w8 cx.hstk) hpw hK hA hrip hsp ?_
  intro Z₁ t₁ hK₁ hA₁ hr₁ hg
  have hz : Z₁.cpu.gpr.rsp = sp - 8#64 := by rw [hg] <;> rfl
  have hzn : Z₁.cpu.gpr.rsp.toNat = sp.toNat - 8 := by rw [hz, m8 sp (by omega)]
  have h32 : 8192 ≤ Z₁.cpu.gpr.rsp.toNat := by rw [hzn]; omega
  refine gor_ok (V := nV W sp X.cpu.gpr) (e' := ndi_at) (code := ndi) (j := 21) c hgo mc hK₁ hA₁ (hr₁.trans rfl)
    h32 (by rw [hzn]; omega) (by rw [hzn]; omega) (by rw [hz]; exact hst) (by rw [hz]; exact hsm)
    (by rw [hzn]; omega) (by rw [hzn]; omega) (by rw [hz]; exact hbuf) (by rw [hz]; exact hfr) hpf hpn hpz hpp
    hof hoz hps hpre hinc hc0 hcpy
    (fun W₀ h => cx.hPm W₀ fun a a1 a2 => (h a a2).trans (nV_fV (by omega) hsn (.inl (by omega))))
    cx.hin (lt_len (by decide))
    (by
      rw [hz]
      unfold nV
      rw [Sga.vs (toBytesLE_length _ 8) (by rw [m8 sp (by omega)]; omega)]
      exact ofBytesLE_toBytesLE (w := 64) (n := 8) rfl _)
    (fun r Z t' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 => by
      rw [hg] at a2 a5 a6 a7 a8 a9 a10 a11 ⊢
      exact ke r Z t' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) ?_
  intro x n s s₁ Vc M W' evs Z t' g hx c₁ hB₁ hK₂ hA₂ h2n hn4 h1s hs1 hg' hVc hAf MV ML hnul hout hr₂ hax hsp₂
    _ _ _ _ _ h15 hev
  rw [hz] at hg' hAf
  rw [hg]
  obtain ⟨hn1, hnb⟩ := nbOf_bnd (n := n) (by omega)
  obtain ⟨hbc, hc15, hT0, -, hT2⟩ := lay hb47 mc.hnb mc.hpd hnb
  have LO : ∀ a : Addr, Lo b fsb a → W' a = fV W sp X.cpu.gpr a := fun a hL => by
    have ha := hL.1
    rw [hout a (.inl (by omega)) (.inl (by rw [hzn]; omega)), ML a hL, Vg_lo (a := a) h32 hx (by rw [hzn]; omega),
      nV_fV (a := a) (W := W) (g := X.cpu.gpr) (by omega) hsn (.inl (by omega))]
  have HI : ∀ a : Addr, sp.toNat ≤ a.toNat → W' a = fV W sp X.cpu.gpr a := fun a ha => by
    rw [hout a (.inr (by omega)) (.inr (by rw [hzn]; omega)), MV a (by rw [hzn]; omega),
      Vg_hi (a := a) h32 hx (by rw [hzn]; omega), nV_fV (a := a) (W := W) (g := X.cpu.gpr) (by omega) hsn (.inr ha)]
  have SM : Same sp (fV W sp X.cpu.gpr) W' := fun a h => by
    rcases h with h | h | h | h
    · exact HI a h
    · exact LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
    · exact LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
  have LZ : ∀ a : Addr, 8014912 ≤ a.toNat → a.toNat < 8029888 → W' a = fV W sp X.cpu.gpr a := fun a a1 a2 =>
    LO a ⟨by omega, by omega, by omega, by omega, by omega⟩
  refine ndi_b (V := W') (W := W') (ph := ph) (pn := pn) c₁ (Cx.mv cx mc.hown SM) hip hp0
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029448) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact h1)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029568) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact h2)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029592) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact h3)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 8029424) (n := 8) (by omega) fun a a1 a2 => LZ a (by omega)
      (by omega)]; exact h4)
    (by rw [rd_of (V := fV W sp X.cpu.gpr) (x := 7937248) (n := 4) (by omega) fun a a1 a2 =>
      LO a ⟨by omega, by omega, by omega, by omega, by omega⟩]; exact h5)
    hK₂ hA₂ (fun _ _ => rfl) hr₂ (by rw [hsp₂, hz, p8]) ?_
  intro Z' t'' W'' hK' hA' hM' hr' hsp' hdi' h15'
  rw [hax] at hM'
  exact k x n s s₁ Vc M W' evs g Z' t'' W'' hx c₁ hB₁ h2n hn4 h1s hs1 hg'
    (fun a h => by rw [hVc a (by rw [hzn]; exact h), hg]) hAf hnul
    (fun a a1 a2 => hout a a1 (by rw [hzn]; exact a2)) LO SM hev hK' hA' hM' hr' hsp' hdi'
    (by rw [h15', h15, hg] <;> rfl)

end FV7z.Ndi
