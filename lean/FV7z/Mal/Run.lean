import FV7z.Mal.Holds
import FV7z.Mhi.Run
/-!
# The first `malloc (50)` of the process (PLAN.md G3, `malloc`)

`malloc` finds `__malloc_hook` as the file has it, `malloc_hook_ini`, and jumps there (`Mal.mal_hook`); that runs
`ptmalloc_init`, `tcache_init` and `_int_malloc` (`Mhi.mhi_ok`) and returns to `malloc`'s caller.

- `Vm_out`: the three pushes leave the bytes outside the 24 below the stack pointer.
- `fofs`, `bnd`, `sp376`: offsets.
- `mal_first`: from `malloc`'s entry to its caller, with `mhi_ok`'s hypotheses on the bytes at `malloc`'s entry.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Raf (off_ft)
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (rd_eq)
open FV7z.Smm (corr corr2 size smEv smEv2)
open FV7z.Imm (imm imm_at Out add_n)
open FV7z.Im2 (Vsp)
open FV7z.Mhi (Tp C2 Sz Vh mhi mhi_at)
namespace FV7z.Mal
variable {F : Footprint} {Wl : List Rgn}

/-- A byte outside the 24 below the stack pointer: the pushes left it. -/
theorem Vm_out (g : Gprs) (V : Addr → Byte) (h : 24 ≤ g.rsp.toNat) {a : Addr}
    (ha : a.toNat < g.rsp.toNat - 24 ∨ g.rsp.toNat ≤ a.toNat) : Vm g V a = V a := by
  have e1 : (g.rsp - 8).toNat = g.rsp.toNat - 8 := by bv_omega
  have e2 : (g.rsp - 8 - 8).toNat = g.rsp.toNat - 16 := by bv_omega
  have e3 : (g.rsp - 8 - 8 - 8).toNat = g.rsp.toNat - 24 := by bv_omega
  have l : ∀ v : Addr, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  have hR := g.rsp.isLt
  unfold Vm
  rw [Vst_out _ _ _ _ (by rw [l, e3]; omega) (by rw [l, e3]; omega),
    Vst_out _ _ _ _ (by rw [l, e2]; omega) (by rw [l, e2]; omega),
    Vst_out _ _ _ _ (by rw [l, e1]; omega) (by rw [l, e1]; omega)]

/-- The thread pointer's offsets that `malloc_hook_ini` reads. -/
theorem fofs (fsb : Addr) (h1 : 40 ≤ fsb.toNat) (h2 : fsb.toNat + 48 < 2 ^ 64) :
    (fsb + 24#64).toNat = fsb.toNat + 24 ∧ (fsb + 18446744073709551584#64).toNat = fsb.toNat - 32 ∧
      (fsb + 18446744073709551576#64).toNat = fsb.toNat - 40 :=
  ⟨by bv_omega, by bv_omega, by bv_omega⟩

/-- The break's page below the stack. -/
theorem bnd {b pad S : Addr} (hb : b.toNat < 2 ^ 47) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47)
    (h : (b + size pad 656#64).toNat + 4096 + 168 ≤ S.toNat) :
    pageUp b.toNat / 4096 * 4096 + 168 ≤ S.toNat ∧ b.toNat + 4096 + 168 ≤ S.toNat := by
  have hR : (size pad 656#64).toNat = (4127 + pad.toNat + 656) / 4096 * 4096 :=
    Smm.size_toNat (pad := pad) (nb := 656#64) (by show 656 + pad.toNat + 4127 < 2 ^ 47; omega)
  generalize size pad 656#64 = R at hR h
  have e : (b + R).toNat = b.toNat + R.toNat := by bv_omega
  unfold pageUp
  omega

theorem sp376 (S : Addr) : S + 232#64 - 24 = S - 168 + BitVec.ofNat 64 376 := by bv_omega

theorem t232 (S : Addr) (h : S.toNat + 512 < 2 ^ 64) : (S + 232#64).toNat = S.toNat + 232 := by bv_omega

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {V : Addr → Byte}

set_option maxHeartbeats 2000000 in
/-- The first `malloc (50)` of the process, one thread: from `malloc`'s entry (`S + 232` the stack pointer, the hook
`malloc_hook_ini`) to its return address, as `Mhi.mhi_ok` with its hypotheses on the bytes at `malloc`'s entry;
`malloc_hook_ini` starts from them with the three pushes of `malloc` (`Vm`). -/
theorem mal_first {lim : Nat} {b fsb S : Addr} {ks : Kst} {pad sm mx : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hin : CodeIn L mal_at mal) (hinH : CodeIn L mhi_at mhi)
    (hinP : CodeIn L Pmi.pmi_at Pmi.pmi)
    (hinG : CodeIn L Tgv.tgv_at Tgv.tgv) (hinT : CodeIn L Tci.tci_at Tci.tci) (hinI : CodeIn L imm_at imm)
    (hinS : CodeIn L Smm.smm_at Smm.smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinK : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = mal_at)
    (hhook : rdq(V, 7940656#64) = mhi_at)
    (hrsp : X.cpu.gpr.rsp = S + 232#64) (hdi : X.cpu.gpr.rdi = 50#64)
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
    (hf2 : rdq(V, 7940704#64) = 0#64) (htb : rdq(V, 7940592#64) = 64#64)
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
    (hh : ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 80 → Foot (N ++ Wl) a)
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
        M a = Vsp (Tp b) (Sz b pad) (Vst V₁ (fsb + 18446744073709551576#64) (toBytesLE (b + corr b + 16#64) 8)) a) →
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
  refine Mhi.mhi_ok (V := Vm X.cpu.gpr V) c hB hinH hinP hinG hinT hinI hinS hinD hinK hinb hKZ hAZ hrZ
    (by rw [hgZ]; exact hrsp) (by rw [hgZ]; exact hdi) hsp hS hst hW hhk hcur hml hpb hgmf hft hfa hfm hfl hfs1
    hfs hfb (by rw [Rc (7940484#64) 4 (by decide) (by decide)]; exact hmi)
    (fun d hd => (h32 d hd).out (by have := g32 d hd; omega) (by omega) ho)
    (fun d hd => (h64 d hd).out (by have := g64 d hd; omega) (by omega) ho)
    (by rw [R (fsb + 18446744073709551584#64) 1 (by rw [f32]; omega)]; exact hsd)
    (by rw [R (fsb + 24#64) 4 (by rw [f24]; omega)]; exact hmt)
    (by rw [Rc (7940672#64) 4 (by decide) (by decide)]; exact hlk)
    (by rw [R (fsb + 18446744073709551576#64) 8 (by rw [f40]; omega)]; exact htc)
    (by rw [Rc (7940704#64) 8 (by decide) (by decide)]; exact hf2)
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

/-- The new pages of the first `malloc`'s `sbrk` as one region, `[pageUp b, pageUp (b + size))`: a choice of the
regions `N` for `mal_first`. -/
def Nr (b pad : Addr) : List Rgn :=
  [⟨BitVec.ofNat 64 (pageUp b.toNat / 4096 * 4096),
    pageUp (b + size pad 656#64).toNat / 4096 * 4096 - pageUp b.toNat / 4096 * 4096⟩]

theorem pg_toNat {b : Addr} (hb : b.toNat < 2 ^ 47) :
    (BitVec.ofNat 64 (pageUp b.toNat / 4096 * 4096)).toNat = pageUp b.toNat / 4096 * 4096 :=
  Nat.mod_eq_of_lt (by unfold pageUp; omega)

theorem brk_up {b pad : Addr} (hb : b.toNat < 2 ^ 47) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47) :
    (b + size pad 656#64).toNat = b.toNat + (size pad 656#64).toNat ∧ 4096 ≤ (size pad 656#64).toNat := by
  have hR : (size pad 656#64).toNat = (4127 + pad.toNat + 656) / 4096 * 4096 :=
    Smm.size_toNat (pad := pad) (nb := 656#64) (by show 656 + pad.toNat + 4127 < 2 ^ 47; omega)
  generalize size pad 656#64 = R at hR ⊢
  exact ⟨by bv_omega, by omega⟩

/-- `Nr` lies in the new pages (`hN` of `mal_first`). -/
theorem Nr_in {b pad : Addr} (hb : b.toNat < 2 ^ 47) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47) :
    ∀ r ∈ Nr b pad, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad 656#64).toNat / 4096 * 4096) := by
  intro r hr
  simp only [Nr, List.mem_singleton] at hr
  subst hr
  obtain ⟨e, hR⟩ := brk_up (pad := pad) hb hnb
  show _ ≤ (BitVec.ofNat 64 (pageUp b.toNat / 4096 * 4096)).toNat ∧
    (BitVec.ofNat 64 (pageUp b.toNat / 4096 * 4096)).toNat +
      (pageUp (b + size pad 656#64).toNat / 4096 * 4096 - pageUp b.toNat / 4096 * 4096) ≤ _
  rw [pg_toNat hb, e]
  unfold pageUp
  omega

/-- The heap bytes `mal_first` writes (`hh`) are in `Nr` or in the rest of the break's page, if `Wl` has that rest. -/
theorem Nr_hh {b pad : Addr} {Wl : List Rgn} (hb : b.toNat < 2 ^ 47) (hnb : 656 + pad.toNat + 4127 < 2 ^ 47)
    (hw : ∀ a : Addr, b.toNat ≤ a.toNat → a.toNat < pageUp b.toNat / 4096 * 4096 → Foot Wl a) :
    ∀ a : Addr, (b + corr b).toNat ≤ a.toNat → a.toNat < (b + corr b).toNat + 656 + 80 →
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
