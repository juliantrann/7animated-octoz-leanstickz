import FV7z.Start.CxaCall
import FV7z.Csu.Holds
import FV7z.Lemmas.CallReg
/-!
# `__libc_start_main` calls `init` (PLAN.md G3, startup)

After `__cxa_atexit` returns to `0x61344a` (`lsm` 1034), glibc 2.31's `__libc_start_main` checks
`__libc_enable_secure` (`0x791ce0`; 0 for a launch that is not a secure one, so `__libc_check_standard_fds` is not
called), then `init` (`__libc_csu_init`, kept in `rbp`) is not null, so it is called at `0x61346c` (`lsm` 1068) as
`init (argc, argv, __environ)` and returns to `0x61346e` (`lsm` 1070).

- `vc_1034`: the verification condition of the stretch to the call.
- `call_1068`: the `call *%rbp`.
- `lsb_csu`: the run from `0x61344a` to the return of `__libc_csu_init`, with `Csu.csu_ok`'s conditions (what each
  of the 104 functions of `.preinit_array`, `_init` and `.init_array` does is `Csu.Runs`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Tun (rd_Vst rd_Vst_self)
open FV7z.Raf (Out off_ft)
namespace FV7z.StartB

variable {F : Footprint} {Wl : List Rgn}

/-- From `0x61344a` to the call of `init`, `__libc_enable_secure` 0 and `init` (`rbp`) not null: its arguments
`argc`, `argv`, `__environ`. -/
theorem vc_1034 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {ev av : BitVec 64} {ac : BitVec 32}
    (h0 : ∀ i < 4, Foot F.data (Addr.add 7937248#64 i)) (hsec : rdd(V, 7937248#64) = 0) (hbp : g.rbp ≠ 0#64)
    (h1 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i)) (h2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h3 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i)) (he : rdq(V, 8013720#64) = ev)
    (ha : rdq(V, g.rsp + 16#64) = av) (hc : rdd(V, g.rsp + 12#64) = ac) :
    W_1034 fb F Wl (fun j' g' _ V' => j' = 1068 ∧ g' = ((g.set 2 ev).set 6 av).set 7 (ac.setWidth 64) ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h2 h3 ha hc hbp
  subst he ha hc
  have hb : (rbp &&& rbp == 0) = false := by rw [BitVec.and_self]; exact beq_false_of_ne hbp
  wpx [W_1034, W_1047, W_1052, o7, o8, o9, Op.cmpmia, Op.test, Op.lda, Op.ld]
  simp only [hb]
  refine ⟨h0, fun h => ?_, fun _ => ⟨fun h => ?_, fun _ => ?_⟩⟩
  · first | exact absurd h (by decide) | (rw [hsec] at h; exact absurd h (by decide)) | simp_all
  · first | exact absurd h (by decide) | (rw [hb] at h; exact absurd h (by decide)) | simp_all
  · first | exact ⟨h1, h2, h3, rfl⟩ | exact ⟨h1, h2, h3, rfl, rfl, rfl⟩ | exact ⟨h1, h2, h3, trivial⟩

/-- The `call *%rbp` of `init` in `__libc_start_main`. -/
def pc1068 : List Byte := [0xff, 0xd5]
theorem pc1068_0 : ∀ feat, Dec feat pc1068 0 (FV7z.mk .call 64 [gr 64 5] 2) := by dec_rfl
theorem wc1068 : pc1068 <+: lsm.drop 1068 := by decide +kernel
theorem call_1068 (feat : Features) : Dec feat lsm 1068 (FV7z.mk .call 64 [gr 64 5] 2) :=
  Dec.shift (j := 1068) (k := 0) (pc1068_0 feat) wc1068 (Nat.zero_le _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {V : Addr → Byte}

set_option maxHeartbeats 800000 in
/-- From `0x61344a` to the return of `init (argc, argv, __environ)` at `0x61346e`, `__libc_enable_secure` 0 and
`init` (`rbp`) `__libc_csu_init`: with `Csu.csu_ok`'s conditions on the bytes `V` before the call (the stack below
`sp = rsp - 8`, the two arrays, the code of the 104 functions `tg` and what each does, `Csu.Runs` for the invariant
`I`), at the return `I 104` and the registers a call keeps as at the entry of `__libc_csu_init`. -/
theorem lsb_csu {fb : Addr} {tg : Nat → Addr} {I : Nat → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hl : CodeIn L lsm_at lsm) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1034) (hbp : X.cpu.gpr.rbp = Csu.csu_at)
    (h0 : ∀ i < 4, Foot F.data (Addr.add 7937248#64 i)) (hsec : rdd(V, 7937248#64) = 0)
    (h1 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i))
    (h2 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 16#64) i))
    (h3 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rsp + 12#64) i))
    (hra : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8#64) i)) (hE : Csu.Env F Wl L (X.cpu.gpr.rsp - 8#64) tg)
    (hpre : rdq(V, 7829400#64) = tg 0)
    (harr : ∀ k < 102, rdq(V, BitVec.ofNat 64 (7829408 + 8 * k)) = tg (k + 2))
    (hI : ∀ m V V', I m V → Out ((X.cpu.gpr.rsp - 8#64).toNat - 64) (X.cpu.gpr.rsp - 8#64).toNat V V' → I m V')
    (hI0 : I 0 (Vst V (X.cpu.gpr.rsp - 8#64) (toBytesLE (lsm_at.add 1070) 8)))
    (hfn : ∀ m < 104, Csu.Runs prof F Wl L s₀ o gev gP gE I (X.cpu.gpr.rsp - 8#64)
      ((((rdd(V, X.cpu.gpr.rsp + 12#64)).setWidth 64).setWidth 32).setWidth 64) rdq(V, X.cpu.gpr.rsp + 16#64)
      rdq(V, 8013720#64) m (tg m))
    (k : ∀ (V' : Addr → Byte) (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → I 104 V' →
      Z.cpu.rip = lsm_at.add 1070 →
      Osv.Back ((((X.cpu.gpr.set 2 rdq(V, 8013720#64)).set 6 rdq(V, X.cpu.gpr.rsp + 16#64)).set 7
        ((rdd(V, X.cpu.gpr.rsp + 12#64)).setWidth 64)).set 4 (X.cpu.gpr.rsp - 8#64)) Z.cpu.gpr →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hs8 := hE.s8
  have had := hE.ad
  have t0 : (7829400#64 : Addr).toNat = 7829400 := rfl
  have hb8 : (toBytesLE (lsm_at.add 1070) 8).length = 8 := toBytesLE_length _ _
  refine (c_1034 prof fb).run c hfs hl _ hK hA hrip
    (vc_1034 h0 hsec (by rw [hbp]; decide) h1 h2 h3 rfl rfl rfl) ?_
  rintro j' g fl V' ⟨rfl, rfl, rfl⟩ Y t₁ hKY hAY hrY hgY -
  have hYs : Y.cpu.gpr.rsp - 8 = X.cpu.gpr.rsp - 8#64 := by
    rw [hgY]
    rfl
  refine c.s_callr hKY hAY hl (by rw [lsm_length]; decide) hrY (call_1068 _) hE.code
    (by rw [Csu.csu_length]; decide) (by rw [hgY]; exact hbp) (fun i hi => by rw [hYs]; exact hra i hi) ?_
  rintro Z₁ u₁ hKZ hAZ ⟨hrZ, hgZ⟩
  rw [hYs] at hAZ hgZ
  have hzs : Z₁.cpu.gpr.rsp = X.cpu.gpr.rsp - 8#64 := by
    rw [hgZ]
    rfl
  have hrd : ∀ (x : Addr) (n : Nat), x.toNat + n ≤ 2 ^ 64 →
      ((X.cpu.gpr.rsp - 8#64).toNat + 8 ≤ x.toNat ∨ x.toNat + n ≤ (X.cpu.gpr.rsp - 8#64).toNat) →
      List.map (Vst V' (X.cpu.gpr.rsp - 8#64) (toBytesLE (lsm_at.add 1070) 8)) (byteAddrs x n) =
        List.map V' (byteAddrs x n) := fun x n hx h => rd_ra x n hb8 (by omega) hx h
  refine Csu.csu_ok (e₂ := lsm_at) (j₂ := 1070) c (by rw [hzs]; exact hE) hKZ hAZ hrZ hl
    (by rw [lsm_length]; decide)
    (by rw [hzs, rd_Vst_self _ _ _ hb8 (by omega), ofBytesLE_toBytesLE (n := 8) rfl])
    (by rw [hrd 7829400#64 8 (by decide) (by rw [t0]; omega)]; exact hpre)
    (fun k hk => by
      have tk : (BitVec.ofNat 64 (7829408 + 8 * k) : Addr).toNat = 7829408 + 8 * k := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hrd _ 8 (by rw [tk]; omega) (by rw [tk]; omega)]
      exact harr k hk)
    (by rw [hzs]; exact hI) hI0 ?_ ?_
  · rw [hzs]
    intro m hm
    rw [hgZ, hgY]
    exact hfn m hm
  · intro V₂ Z t' hK₂ hA₂ hI₂ hr₂ hB₂
    rw [hgZ, hgY] at hB₂
    exact k V₂ Z t' hK₂ hA₂ hI₂ hr₂ hB₂

end FV7z.StartB
