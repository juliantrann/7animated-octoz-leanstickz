import FV7z.Start.MainCall
/-!
# From the return of `__cxa_atexit` to `main` (PLAN.md G3, startup)

`lsb_csu`, `lsb_dbg`, `lsb_sjp` and `lsb_main` joined: from `0x61344a` (`lsm` 1034), `rsp = q`, through
`__libc_csu_init`, `_dl_debug_initialize` and `_setjmp` to the first byte of `main (argc, argv, __environ)`.
What the 104 functions of `__libc_csu_init` do is `Csu.Runs` for an invariant `I`; `I 104` must keep the bytes
`main`'s call reads (`argc`, `argv`, `main` in `__libc_start_main`'s frame, `__environ`).

- `tq_add`, `tq_sub8`, `q_m16`, `q_120`, `q_m8`: offsets of `q`, each its own lemma (`bv_omega` in a big context hangs).
- `lsb_tail`: the run; at `main` the bytes are `I 104`'s but for `_r_debug`, the slots of the return addresses,
  the cancellation buffer and `fs:0x300`, and the return address `0x6134d0` is on the stack.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst_self Vst_out)
open FV7z.DebugInit (rDebug rLoaded)
namespace FV7z.StartB

theorem tq_add {q : Addr} {k : Nat} (h : q.toNat + k < 2 ^ 64) : (q + BitVec.ofNat 64 k).toNat = q.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega)]
  exact Nat.mod_eq_of_lt h

theorem tq_sub8 {q : Addr} (h : 8 ≤ q.toNat) : (q - 8#64).toNat = q.toNat - 8 := by
  bv_omega

theorem q_m16 (q : Addr) : q - 8#64 - 8#64 = q - 16#64 := by
  bv_omega

theorem q_120 (q : Addr) : q - 8#64 + 120#64 = q + 112#64 := by
  bv_omega

theorem q_m8 (q : Addr) : q - 8 = q - 8#64 := rfl

/-- A byte away from a stored word. -/
theorem vo8 {V : Addr → Byte} {v : BitVec 64} (a x : Addr) (ha : a.toNat + 8 ≤ 2 ^ 64)
    (h : x.toNat < a.toNat ∨ a.toNat + 8 ≤ x.toNat) : Vst V a (toBytesLE v 8) x = V x :=
  Vst_out _ _ _ _ (by rw [toBytesLE_length]; exact ha) (by rw [toBytesLE_length]; exact h)

variable {F : Footprint} {Wl : List Rgn} {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

set_option maxHeartbeats 1600000 in
/-- From `0x61344a` (`rsp = q`) to the first byte of `main` (`e₂`, the word at `q + 24`), `__libc_enable_secure`
0 and `init` `__libc_csu_init`: with `lsb_csu`'s conditions, the bounds and footprints of `lsb_dbg`, `lsb_sjp` and
`lsb_main`, and `I 104` keeping `argc`, `argv`, `main` and `__environ`. At `main`, `rdi`, `rsi`, `rdx` are
`argc`, `argv`, `__environ`, `rsp = q - 8`, and the bytes are those of a `V₁` with `I 104 V₁` but for `_r_debug`,
`[q - 16, q)`, `[q + 112, q + 208)` and `[fb + 768, fb + 776)`, with the return address `0x6134d0` at `q - 8`. -/
theorem lsb_tail {fb q e₂ : Addr} {code₂ : List Byte} {tg : Nat → Addr} {I : Nat → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hl : CodeIn L lsm_at lsm)
    (hinD : CodeIn L Dbg.dbg_at Dbg.dbg) (hinP : CodeIn L Sjp.sjp_at Sjp.sjp) (hinS : CodeIn L Ssj.ssj_at Ssj.ssj)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : 0 < code₂.length)
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1034)
    (hq : X.cpu.gpr.rsp = q) (hbp : X.cpu.gpr.rbp = Csu.csu_at)
    -- bounds
    (hq0 : 0x7a8508 ≤ q.toNat) (hqn : q.toNat + 216 ≤ 2 ^ 64) (hq16 : q.toNat % 16 = 0)
    (hfn : fb.toNat + 776 ≤ 2 ^ 64)
    (hfsd : fb.toNat + 56 ≤ q.toNat - 8 ∨ q.toNat ≤ fb.toNat)
    (hfd : fb.toNat + 56 ≤ q.toNat + 112 ∨ q.toNat + 208 ≤ fb.toNat)
    (hfq : fb.toNat + 776 ≤ q.toNat + 12 ∨ q.toNat + 32 ≤ fb.toNat + 768)
    (hfe : fb.toNat + 776 ≤ 8013720 ∨ 8013728 ≤ fb.toNat + 768)
    -- footprints
    (h0 : ∀ i < 4, Foot F.data (Addr.add 7937248#64 i)) (hfe8 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i))
    (hfc : ∀ i < 4, Foot F.data ((q + 12#64).add i)) (hfa : ∀ i < 8, Foot F.data ((q + 16#64).add i))
    (hfm : ∀ i < 8, Foot F.data ((q + 24#64).add i))
    (hra : ∀ i < 8, Foot Wl (Addr.add (q - 8#64) i)) (hst : ∀ i < 16, Foot Wl (Addr.add (q - 16#64) i))
    (hsw : ∀ y : Addr, q.toNat - 8 ≤ y.toNat → y.toNat < q.toNat → Foot F.writes y)
    (hbw : ∀ i < 96, Foot Wl (Addr.add (q + 112#64) i))
    (hs0 : ∀ i < 8, Foot Wl ((q + 184#64).add i)) (hs1 : ∀ i < 8, Foot Wl ((q + 192#64).add i))
    (hdw : ∀ y, rDebug.Mem y → Foot F.writes y) (hdW : ∀ y, rDebug.Mem y → Foot Wl y)
    (hlr : ∀ y, rLoaded.Mem y → Foot F.writes y ∨ Foot F.reads y)
    (hft : ∀ i < 56, Foot F.data (Addr.add fb i))
    (hg0 : ∀ i < 8, Foot F.data ((fb + 768#64).add i)) (hg1 : ∀ i < 8, Foot F.data ((fb + 760#64).add i))
    (hgw : ∀ i < 8, Foot Wl ((fb + 768#64).add i))
    -- the bytes at `0x61344a`
    (hsec : rdd(V, 7937248#64) = 0) (hmn : rdq(V, q + 24#64) = e₂)
    -- `__libc_csu_init`
    (hE : Csu.Env F Wl L (q - 8#64) tg) (hpre : rdq(V, 7829400#64) = tg 0)
    (harr : ∀ k < 102, rdq(V, BitVec.ofNat 64 (7829408 + 8 * k)) = tg (k + 2))
    (hI : ∀ m V V', I m V → FV7z.Raf.Out ((q - 8#64).toNat - 64) (q - 8#64).toNat V V' → I m V')
    (hI0 : I 0 (Vst V (q - 8#64) (toBytesLE (lsm_at.add 1070) 8)))
    (hfn' : ∀ m < 104, Csu.Runs prof F Wl L s₀ o gev gP gE I (q - 8#64)
      ((((rdd(V, q + 12#64)).setWidth 64).setWidth 32).setWidth 64) rdq(V, q + 16#64) rdq(V, 8013720#64) m (tg m))
    (hI104 : ∀ V', I 104 V' → ∀ a : Addr,
      (q.toNat + 12 ≤ a.toNat ∧ a.toNat < q.toNat + 32 ∨ 8013720 ≤ a.toNat ∧ a.toNat < 8013728) → V' a = V a)
    (k : ∀ (Vm V₁ : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem Vm → I 104 V₁ →
      (∀ a : Addr, ¬ (q.toNat - 16 ≤ a.toNat ∧ a.toNat < q.toNat) →
        ¬ (q.toNat + 112 ≤ a.toNat ∧ a.toNat < q.toNat + 208) → ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) →
        ¬ (fb.toNat + 768 ≤ a.toNat ∧ a.toNat < fb.toNat + 776) → Vm a = V₁ a) →
      rdq(Vm, q - 8#64) = lsm_at.add 1168 →
      Z.cpu.rip = e₂ → Z.cpu.gpr.rsp = q - 8#64 → Z.cpu.gpr.rdi = (rdd(V, q + 12#64)).setWidth 64 →
      Z.cpu.gpr.rsi = rdq(V, q + 16#64) → Z.cpu.gpr.rdx = rdq(V, 8013720#64) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  subst hq
  have tq8 := tq_sub8 (q := X.cpu.gpr.rsp) (by omega)
  have t12 := tq_add (q := X.cpu.gpr.rsp) (k := 12) (by omega)
  have t16 := tq_add (q := X.cpu.gpr.rsp) (k := 16) (by omega)
  have t112 := tq_add (q := X.cpu.gpr.rsp) (k := 112) (by omega)
  have hb8 : ∀ v : BitVec 64, (toBytesLE v 8).length = 8 := fun v => toBytesLE_length _ _
  -- `__libc_csu_init`
  refine lsb_csu c hfs hl hK hA hrip hbp h0 hsec hfe8 hfa hfc hra hE hpre harr hI hI0 hfn' ?_
  intro V₁ Z₁ t₁ hK₁ hA₁ hI₁ hr₁ hB₁
  -- `_dl_debug_initialize`
  refine lsb_dbg (sp := X.cpu.gpr.rsp - 8#64) c hfs hl hinD hK₁ hA₁ hr₁ hB₁.1 hdf hx87
    (by rw [BitVec.sub_add_cancel]; exact hq16) (by rw [tq8]; omega) (by rw [tq8]; omega) hra
    (fun y h1 h2 => hsw y (by rw [tq8] at h1; omega) (by rw [tq8] at h2; omega)) hdw hdW hlr ?_
  intro V₂ Z₂ t₂ hK₂ hA₂ hout₂ hr₂ hB₂ _
  -- `_setjmp`
  refine lsb_sjp (sp := X.cpu.gpr.rsp - 8#64) c hfs hl hinP hinS hK₂ hA₂ hr₂ hB₂.1 (by rw [tq8]; omega)
    (by rw [tq8]; omega) (fun i hi => by rw [q_m16]; exact hst i hi)
    (fun i hi => by rw [q_120]; exact hbw i hi) hft (by omega) (by rw [tq8]; omega) (by rw [tq8]; omega) ?_
  intro V₃ g₃ Z₃ t₃ hK₃ hA₃ hJ hr₃ hg₃ hax₃ hB₃
  have hz3 : Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp := by
    rw [hg₃, hB₃.1]
    show X.cpu.gpr.rsp - 8#64 + 8#64 = X.cpu.gpr.rsp
    exact BitVec.sub_add_cancel _ _
  rw [q_120] at hJ
  -- the bytes after `_setjmp` are `V₁`'s away from what the three calls store
  have hkeep : ∀ a : Addr, ¬ (X.cpu.gpr.rsp.toNat - 16 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat) →
      ¬ (X.cpu.gpr.rsp.toNat + 112 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat + 208) →
      ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) → V₃ a = V₁ a := by
    intro a n1 n2 n3
    have e3 := hJ.out a (by rw [tq8]; omega) (by rw [t112]; omega)
    rw [e3, vo8 _ a (by rw [tq8]; omega) (by rw [tq8]; omega), hout₂ a (fun h => n3 (rDebug_mem h)),
      vo8 _ a (by rw [tq8]; omega) (by rw [tq8]; omega)]
  have hk1 : ∀ a : Addr, X.cpu.gpr.rsp.toNat + 12 ≤ a.toNat ∧ a.toNat < X.cpu.gpr.rsp.toNat + 32 → V₃ a = V a :=
    fun a ha => (hkeep a (by omega) (by omega) (by omega)).trans (hI104 V₁ hI₁ a (.inl ha))
  have hk2 : ∀ a : Addr, 8013720 ≤ a.toNat ∧ a.toNat < 8013728 → V₃ a = V a :=
    fun a ha => (hkeep a (by omega) (by omega) (by omega)).trans (hI104 V₁ hI₁ a (.inr ha))
  have e12 : List.map V₃ (byteAddrs (X.cpu.gpr.rsp + 12#64) 4) = List.map V (byteAddrs (X.cpu.gpr.rsp + 12#64) 4) :=
    Csu.rd_in hk1 (by rw [t12]; omega) (by rw [t12]; omega) (by rw [t12]; omega)
  have e16 : List.map V₃ (byteAddrs (X.cpu.gpr.rsp + 16#64) 8) = List.map V (byteAddrs (X.cpu.gpr.rsp + 16#64) 8) :=
    Csu.rd_in hk1 (by rw [t16]; omega) (by rw [t16]; omega) (by rw [t16]; omega)
  have e24 : List.map V₃ (byteAddrs (X.cpu.gpr.rsp + 24#64) 8) = List.map V (byteAddrs (X.cpu.gpr.rsp + 24#64) 8) :=
    Csu.rd_in hk1 (by rw [tq_add (by omega)]; omega) (by rw [tq_add (by omega)]; omega)
      (by rw [tq_add (by omega)]; omega)
  have eev : List.map V₃ (byteAddrs 8013720#64 8) = List.map V (byteAddrs 8013720#64 8) :=
    Csu.rd_in hk2 (by decide) (by decide) (by decide)
  -- the call of `main`
  refine lsb_main c hfs hl hin₂ h₂ hK₃ hA₃ hr₃ (by rw [hg₃]; exact hax₃) (by rw [hz3]; omega)
    (by rw [hz3]; omega) hfn hg0 hg1 hgw (fun i hi => by rw [hz3]; exact hs0 i hi)
    (fun i hi => by rw [hz3]; exact hs1 i hi) (fun i hi => by rw [hz3]; exact hra i hi) hfe8
    (fun i hi => by rw [hz3]; exact hfc i hi) (fun i hi => by rw [hz3]; exact hfa i hi)
    (fun i hi => by rw [hz3]; exact hfm i hi) (by rw [hz3]; exact hfq) hfe (by rw [hz3]; omega)
    (by rw [hz3, e24]; exact hmn) ?_
  intro Z t' hKZ hAZ hrZ hgZ
  rw [hz3, q_m8] at hAZ hgZ
  refine k _ V₁ Z t' hKZ hAZ hI₁ ?_ ?_ hrZ ?_ ?_ ?_ ?_
  · intro a n1 n2 n3 n4
    have t184 := tq_add (q := X.cpu.gpr.rsp) (k := 184) (by omega)
    have t192 := tq_add (q := X.cpu.gpr.rsp) (k := 192) (by omega)
    have t768 := tq_add (q := fb) (k := 768) (by omega)
    rw [vo8 _ a (by rw [tq8]; omega) (by rw [tq8]; omega)]
    unfold MainMem
    rw [vo8 _ a (by rw [t768]; omega) (by rw [t768]; omega), vo8 _ a (by rw [t192]; omega) (by rw [t192]; omega),
      vo8 _ a (by rw [t184]; omega) (by rw [t184]; omega)]
    exact hkeep a n1 n2 n3
  · rw [rd_Vst_self _ _ _ (hb8 _) (by rw [tq8]; omega), ofBytesLE_toBytesLE (n := 8) rfl]
  · rw [hgZ]
    rfl
  · rw [hgZ]
    show (ofBytesLE 32 (List.map V₃ (byteAddrs (X.cpu.gpr.rsp + 12#64) 4))).setWidth 64 = _
    rw [e12]
  · rw [hgZ]
    show ofBytesLE 64 (List.map V₃ (byteAddrs (X.cpu.gpr.rsp + 16#64) 8)) = _
    rw [e16]
  · rw [hgZ]
    show ofBytesLE 64 (List.map V₃ (byteAddrs 8013720#64 8)) = _
    rw [eev]

end FV7z.StartB
