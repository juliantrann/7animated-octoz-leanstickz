import FV7z.Smm.Vc
import FV7z.Dmc.Holds
import FV7z.Lemmas.CallR
/-!
# `sysmalloc`: to the return of the first `MORECORE` (PLAN.md G3, `malloc`)

`sysmalloc (nb, av)` on the way of the first call (`Smm/Vc.lean`), from the entry through
`call *__morecore` (`0x7932d8`, the address of `__default_morecore`) and back.

- `call_894`: the `call qword [rip + 1453044]`.
- `rd_Va`: a read below the end of the program's data, in the bytes at the call.
- `size_toNat`, `page_lt`: the size asked for is a number of pages, at least one: the break moves to a higher page.
- `sm_a`: the run from the entry to offset 900, from a new start with the new pages' regions and `Base` with the
  break `b + size`: `rax` is the old break `b`, the frame is `sysmalloc`'s (104 bytes), the new pages' bytes are 0,
  and the bytes outside them, the 56 below the frame and `__curbrk` are those of `Va`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self Vst_out)
open FV7z.Brk (curbrk)
open FV7z.Sbrk (sbrkEv)
namespace FV7z.Smm

/-! ## The instruction outside the blocks -/

def pc894 : List Byte := [0xff, 0x15, 0xf4, 0x2b, 0x16, 0x00]
theorem pc894_0 : ∀ feat, Dec feat pc894 0 (FV7z.mk .call 64 [.mem (mrip 1453044 64)] 6) := by dec_rfl
theorem w_894 : pc894 <+: smm.drop 894 := by decide +kernel
/-- `call *__morecore`, the first. -/
theorem call_894 (feat : Features) : Dec feat smm 894 (FV7z.mk .call 64 [.mem (mrip 1453044 64)] 6) :=
  Dec.shift (j := 894) (k := 0) (pc894_0 feat) w_894 (Nat.zero_le _)

/-- Where `__morecore` is. -/
theorem mc_at : smm_at.add (894 + 6) + BitVec.ofNat 64 1453044 = 7942872#64 := by decide

/-! ## The bytes and the size -/

theorem b104 (S : Addr) : S - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 = S - 104#64 := by bv_omega

/-- A read below the end of the program's data, in the bytes at the first call. -/
theorem rd_Va {g : Gprs} {V : Addr → Byte} {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 8029888)
    (hsp : 8029888 + 104 ≤ g.rsp.toNat) : List.map (Va g V) (byteAddrs x n) = List.map V (byteAddrs x n) := by
  have a1 : Hi (g.rsp - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a2 : Hi (g.rsp - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a3 : Hi (g.rsp - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a4 : Hi (g.rsp - 8 - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a5 : Hi (g.rsp - 8 - 8 - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a6 : Hi (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) 8 := ⟨by bv_omega, by bv_omega⟩
  have a7 : Hi (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64) 1 := ⟨by bv_omega, by bv_omega⟩
  have a8 : Hi (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64) 8 := ⟨by bv_omega, by bv_omega⟩
  have a9 : Hi (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 + 16#64) 8 := ⟨by bv_omega, by bv_omega⟩
  have a10 : Hi (g.rsp - 8 - 8 - 8 - 8 - 8 - 8 - 56#64 + 8#64) 8 := ⟨by bv_omega, by bv_omega⟩
  have q := @rd_hi x n hx
  simp only [Va, q, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, toBytesLE_length]

/-- The size asked for, as a number: whole pages. -/
theorem size_toNat {pad nb : BitVec 64} (h : nb.toNat + pad.toNat + 4127 < 2 ^ 47) :
    (size pad nb).toNat = (4127 + pad.toNat + nb.toNat) / 4096 * 4096 := by
  have hx : (4096#64 + pad + 31#64 + nb).toNat = 4127 + pad.toNat + nb.toNat := by bv_omega
  rw [← hx]
  exact and_m4096 _

/-- The break after is in a higher page. -/
theorem page_lt {pad nb b : BitVec 64} (h : nb.toNat + pad.toNat + 4127 < 2 ^ 47) (hb : b.toNat ≤ 2 ^ 47 - 4096) :
    pageUp b.toNat / 4096 < pageUp (b + size pad nb).toNat / 4096 := by
  have h1 := size_toNat h
  have h2 : (b + size pad nb).toNat = b.toNat + (size pad nb).toNat := by
    rw [BitVec.toNat_add]
    omega
  rw [h2, h1]
  unfold pageUp
  omega

variable {F : Footprint} {Wl : List Rgn}

/-- A byte of the 160 below the stack pointer at the entry: the frame, the return address of the call, and the 48
bytes of `__default_morecore`. -/
theorem stk {sp a : Addr} (hst : ∀ i < 160, Foot Wl (Addr.add (sp - 160) i)) (hs : 160 ≤ sp.toNat)
    (h1 : sp.toNat - 160 ≤ a.toNat) (h2 : a.toNat < sp.toNat) : Foot Wl a := by
  have e : Addr.add (sp - 160) (a.toNat - (sp.toNat - 160)) = a := by
    simp only [Addr.add]
    bv_omega
  exact e ▸ hst (a.toNat - (sp.toNat - 160)) (by omega)

/-- The event of the `brk` of the first `MORECORE`: the break asked for and answered is `b + size`. -/
abbrev smEv (g : Gprs) (pad b : BitVec 64) : Event :=
  ⟨12, [b + size pad g.rdi, size pad g.rdi, 0 - 4096#64, 0 - 4096#64, g.r8, g.r9], b + size pad g.rdi, [], []⟩

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

/-- `sysmalloc (nb, &main_arena)` with the top the initial one, `nb` below the `mmap` threshold, the break `b` known
and the kernel not refusing memory: the run reaches offset 900, after the first `MORECORE (size)`, from a new start
with the regions `N` of the new pages and `Base` with the break `b + size`. There `rax` is `b`, the frame is in
place, `rbx` is `av`, `rbp` is `nb`, `r12` the old size (0), `r13` the old top, `r14` the size, `r15` is
`nb + MINSIZE`; the new pages' bytes are 0, `__curbrk` is `b + size`, and the other bytes are those of `Va` but for
the 56 below the frame. -/
theorem sm_a {lim : Nat} {b fsb : Addr} {ks : Kst} {pad : BitVec 64} (c : Seg prof F Wl L s₀ o)
    (hB : Base s₀ lim b fsb ks) (hin : CodeIn L smm_at smm) (hinD : CodeIn L Dmc.dmc_at Dmc.dmc)
    (hinS : CodeIn L Sbrk.sbk_at Sbrk.sbk) (hinb : CodeIn L Brk.brk_at Brk.brk)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = smm_at)
    (hav : X.cpu.gpr.rsi = 7940672#64) (hsp : 8029888 + 160 ≤ X.cpu.gpr.rsp.toNat)
    (hst : ∀ i < 160, Foot Wl (Addr.add (X.cpu.gpr.rsp - 160) i))
    (hD : ∀ a : Addr, 7940480 ≤ a.toNat → a.toNat < 7943136 → Foot F.data a)
    (hcur : ∀ i < 8, Foot Wl (curbrk.add i)) (hml : ∀ i < 4, Foot F.data (Addr.add (7944640#64) i))
    (hps : rdq(V, 7943128#64) = 4096#64)
    (hthr : X.cpu.gpr.rdi.toNat < (rdq(V, 7940528#64)).toNat)
    (htop : rdq(V, 7940768#64) = 7940768#64) (hsz : rdq(V, 7940776#64) = 0#64)
    (hpad : rdq(V, 7940520#64) = pad) (hsm : X.cpu.gpr.rdi.toNat + pad.toNat + 4127 < 2 ^ 47)
    (hfl : ofBytesLE 8 ((byteAddrs (7940676#64) 1).map V) &&& 2#8 = 0#8)
    (hmc : rdq(V, 7942872#64) = Dmc.dmc_at)
    (hcb : rdq(V, curbrk) = b) (hm0 : rdd(V, 7944640#64) = 0)
    (hmg : ∀ t p, o t (.memFail p) = none)
    (hlim : pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 ≤ lim)
    {N : List Rgn}
    (hN : ∀ r ∈ N, r.In (pageUp b.toNat / 4096 * 4096) (pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 * 4096))
    (k : ∀ V₂ s₁ Z t', Seg prof (withNew F N) (N ++ Wl) L s₁ o → Base s₁ lim (b + size pad X.cpu.gpr.rdi) fsb ks →
      KeptW (N ++ Wl) s₁ Z → Agree (withNew F N) Z.proc.mm.mem V₂ → Z.cpu.rip = smm_at.add 900 →
      Z.cpu.gpr.rax = b → Z.cpu.gpr.rdx = 0 →
      (Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 104#64 ∧ Z.cpu.gpr.rbx = 7940672#64 ∧ Z.cpu.gpr.rbp = X.cpu.gpr.rdi ∧
        Z.cpu.gpr.r12 = 0#64 ∧ Z.cpu.gpr.r13 = 7940768#64 ∧ Z.cpu.gpr.r14 = size pad X.cpu.gpr.rdi ∧
        Z.cpu.gpr.r15 = X.cpu.gpr.rdi + 32#64) →
      (∀ a : Addr, pageUp b.toNat / 4096 * 4096 ≤ a.toNat →
        a.toNat < pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 * 4096 → V₂ a = 0) →
      (∀ a : Addr, ¬ (pageUp b.toNat / 4096 * 4096 ≤ a.toNat ∧
          a.toNat < pageUp (b + size pad X.cpu.gpr.rdi).toNat / 4096 * 4096) →
        ¬ (X.cpu.gpr.rsp.toNat - 160 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat - 104) →
        ¬ (0x7a4c38 ≤ a.toNat ∧ a.toNat < 0x7a4c40) → V₂ a = Va X.cpu.gpr V a) →
      rdq(V₂, curbrk) = b + size pad X.cpu.gpr.rdi →
      GoG prof L o (gev ++ [smEv X.cpu.gpr pad b]) gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hbt := hB.brk_lt
  have hsn := size_toNat hsm
  -- to the call
  refine (c_0 prof).run c hin _ hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 (pad := pad) hav (by omega)
      (fun i hi => stk hst (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega))
      hD hps hthr htop hsz hpad (by omega) (by omega) hfl) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, rfl⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  have hsp₁ : Y₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 104#64 := by
    rw [hg₁]
    exact b104 _
  -- `call *__morecore`
  refine c.s_callR hK₁ hA₁ hin (lt_len (by decide)) hr₁ (call_894 _) (fun i hi => ?_) hinD
    (Dmc.lt_len (j := 0) (by decide)) ?_ (fun i hi => ?_) ?_
  · rw [mc_at]
    exact hD _ (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [mc_at, rd_Va (by decide) (by omega)]
    exact hmc
  · rw [hsp₁]
    exact stk hst (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsp₁] at hA₂ hg₂
  have hsp₂ : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 104#64 - 8 := by rw [hg₂]; rfl
  have hdi₂ : Y₂.cpu.gpr.rdi = size pad X.cpu.gpr.rdi := by rw [hg₂, hg₁]; rfl
  have hkp : Y₂.cpu.gpr.rbx = 7940672#64 ∧ Y₂.cpu.gpr.rbp = X.cpu.gpr.rdi ∧ Y₂.cpu.gpr.r12 = 0#64 ∧
      Y₂.cpu.gpr.r13 = 7940768#64 ∧ Y₂.cpu.gpr.r14 = size pad X.cpu.gpr.rdi ∧
      Y₂.cpu.gpr.r15 = X.cpu.gpr.rdi + 32#64 := by
    rw [hg₂, hg₁]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have ev : sbrkEv Y₂ (b + size pad X.cpu.gpr.rdi) (b + size pad X.cpu.gpr.rdi) = smEv X.cpu.gpr pad b := by
    simp only [sbrkEv, smEv, hg₂, hg₁]
    rfl
  -- `__default_morecore (size)`
  refine Dmc.dmc_next c hB hinD hinS hinb hK₂ hA₂ hr₂ hcur hml (fun i hi => ?_) (fun i hi => ?_)
    (by rw [hsp₂]; bv_omega) (by rw [hsp₂]; bv_omega) ?_ ?_ (by rw [hdi₂]; omega) (by rw [hdi₂]; omega) hmg
    (by rw [hdi₂]; exact page_lt hsm hbt) (by rw [hdi₂]; exact hlim) (by rw [hdi₂]; exact hN) hin (j₂ := 900)
    (lt_len (by decide)) ?_ ?_
  · rw [hsp₂]
    exact stk hst (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [hsp₂]
    exact stk hst (by omega) (by simp only [Addr.add]; bv_omega) (by simp only [Addr.add]; bv_omega)
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
      rd_Va (by decide) (by omega)]
    exact hcb
  · rw [rd_Vst _ _ _ _ _ (by sd) (by sd) (by sd),
      rd_Va (by decide) (by omega)]
    exact hm0
  · rw [hsp₂, rd_Vst_self _ _ _ (by sd) (by sd), ofBytesLE_toBytesLE (n := 8) rfl]
  rw [hdi₂, ev]
  intro V₂ s₁ Z t' c' hB' hKz hAz hrz hax hdx ⟨s1, s2, s3, s4, s5, s6, s7⟩ hz hfr hq
  refine k V₂ s₁ Z t' c' hB' hKz hAz hrz hax hdx ⟨s1.trans (by rw [hsp₂]; bv_omega), s2.trans hkp.1,
    s3.trans hkp.2.1, s4.trans hkp.2.2.1, s5.trans hkp.2.2.2.1, s6.trans hkp.2.2.2.2.1, s7.trans hkp.2.2.2.2.2⟩
    hz ?_ hq
  intro a h1 h2 h3
  rw [hfr a h1 (by rw [hsp₂]; bv_omega) h3, Vst_out _ _ _ _ (by sd) (by simp only [toBytesLE_length]; bv_omega)]

end FV7z.Smm
