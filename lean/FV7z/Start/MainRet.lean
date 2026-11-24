import FV7z.Start.StkRet
import FV7z.Start.TailCall
/-!
# From the return of `__cxa_atexit` to `main` (PLAN.md G3, startup)

`StartB.lsb_tail` runs from `0x61344a` (`lsm` 1034) through `init`, `_dl_debug_initialize` and `_setjmp` to the first
byte of `main`, given what it reads. Here the reads are taken back, through `__cxa_atexit`'s stores (`Cxa.Reg`) and
the layers since `0x613434` (`RetAt`), to the launch's bytes: `__libc_enable_secure` is 0 (`RetAt.sec`), the two
arrays are the file's (`RetAt.arr`, so the 104 functions are `csuTg`), and `main`, `argc`, `argv` are the slots of
`__libc_start_main`'s frame (`RetAt.cxa_rd`, `Fr`).

- `cxa_main`: from `0x61344a` to `main`, with `rdi`, `rsi` the launch's `argc` and `argv`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.DebugInit (rDebug rLoaded)
open FV7z.Tls (rd_ext)

variable {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}
  {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}

theorem bp_12 (b : Addr) : b + 112#64 + 12#64 = b + 124#64 := by rw [BitVec.add_assoc]; rfl
theorem bp_16 (b : Addr) : b + 112#64 + 16#64 = b + 128#64 := by rw [BitVec.add_assoc]; rfl
theorem bp_24 (b : Addr) : b + 112#64 + 24#64 = b + 136#64 := by rw [BitVec.add_assoc]; rfl

set_option maxHeartbeats 1600000 in
/-- From the return of `__cxa_atexit` to `0x61344a` (the bytes `V`, `Cxa.Reg` of those at `0x613439`) to the first
byte of `main`, `q = K.bp + 112` the stack pointer: with `csuTg` the 104 functions `__libc_csu_init` calls and
`Csu.Runs` for the invariant `I`, at `main` `rdi` and `rsi` are the launch's `argc` and `argv`, `rdx` is
`__environ`, and the bytes are those of a `V₁` with `I 104 V₁` but for `_r_debug`, `[q - 16, q)`, `[q + 112, q + 208)`
and the TCB's `[fb + 768, fb + 776)`, with the return address `0x6134d0` at `q - 8`. -/
theorem cxa_main {K : Ctx} {V₀ V : Addr → Byte} {ver : BitVec 32} {f0 : BitVec 64} {q : Addr} {code₂ : List Byte}
    {I : Nat → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = B + 2176#64) (hl : CodeIn L lsm_at lsm)
    (hinD : CodeIn L Dbg.dbg_at Dbg.dbg) (hinP : CodeIn L Sjp.sjp_at Sjp.sjp) (hinS : CodeIn L Ssj.ssj_at Ssj.ssj)
    (hin₂ : CodeIn L K.main code₂) (h₂ : 0 < code₂.length)
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1034)
    (hqb : q = K.bp + 112#64) (hq : X.cpu.gpr.rsp = q) (hbp : X.cpu.gpr.rbp = Csu.csu_at)
    -- the bytes at `0x61344a`, from those at `0x613439` and at `0x613434`
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
      (toBytesLE (lsm_at.add 1034) 8)) V (lifSp Z + 152#64) 8010400#64 8010416#64 0 f0 0 0)
    (h : RetAt W W₂ Z B g) (hKo : K.Ok) (hIm : Img K.V0) (hM : MB K V₀) (hW : PtrW K W V₀ B ver (fun _ => True))
    -- bounds
    (hez : K.bp.toNat + 112 = (entG Z).rsp.toNat + 8) (hg : g.rsp.toNat ≤ (entG Z).rsp.toNat + 8)
    (hbB : B.toNat + 2072 + 448 < K.bp.toNat) (hbn : K.bp.toNat + 328 ≤ 2 ^ 64) (hq16 : q.toNat % 16 = 0)
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
    (hft : ∀ i < 56, Foot F.data (Addr.add (B + 2176#64) i))
    (hg0 : ∀ i < 8, Foot F.data ((B + 2176#64 + 768#64).add i))
    (hg1 : ∀ i < 8, Foot F.data ((B + 2176#64 + 760#64).add i))
    (hgw : ∀ i < 8, Foot Wl ((B + 2176#64 + 768#64).add i))
    -- `__libc_csu_init`
    (hE : Csu.Env F Wl L (q - 8#64) csuTg)
    (hI : ∀ m V V', I m V → FV7z.Raf.Out ((q - 8#64).toNat - 64) (q - 8#64).toNat V V' → I m V')
    (hI0 : I 0 (Vst V (q - 8#64) (toBytesLE (lsm_at.add 1070) 8)))
    (hfn : ∀ m < 104, Csu.Runs prof F Wl L s₀ o gev gP gE I (q - 8#64)
      (((K.argc.setWidth 64).setWidth 32).setWidth 64) K.argv rdq(V, 8013720#64) m (csuTg m))
    (hI104 : ∀ V', I 104 V' → ∀ a : Addr,
      (q.toNat + 12 ≤ a.toNat ∧ a.toNat < q.toNat + 32 ∨ 8013720 ≤ a.toNat ∧ a.toNat < 8013728) → V' a = V a)
    (k : ∀ (Vm V₁ : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem Vm → I 104 V₁ →
      (∀ a : Addr, ¬ (q.toNat - 16 ≤ a.toNat ∧ a.toNat < q.toNat) →
        ¬ (q.toNat + 112 ≤ a.toNat ∧ a.toNat < q.toNat + 208) → ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) →
        ¬ ((B + 2176#64).toNat + 768 ≤ a.toNat ∧ a.toNat < (B + 2176#64).toNat + 776) → Vm a = V₁ a) →
      rdq(Vm, q - 8#64) = lsm_at.add 1168 →
      Z'.cpu.rip = K.main → Z'.cpu.gpr.rsp = q - 8#64 → Z'.cpu.gpr.rdi = K.argc.setWidth 64 →
      Z'.cpu.gpr.rsi = K.argv → Z'.cpu.gpr.rdx = rdq(V, 8013720#64) →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  subst hqb
  have := h.hb; have := h.hb'; have := h.he; have := h.he'
  have hf : (B + 2176#64).toNat = B.toNat + 2176 := by bv_omega
  have tq : (K.bp + 112#64).toNat = K.bp.toNat + 112 := StartB.tq_add (by omega)
  have t0 : (7937248#64 : Addr).toNat = 7937248 := rfl
  -- the frame's slots
  have ec : rdd(V, K.bp + 112#64 + 12#64) = K.argc := by
    rw [bp_12, h.cxa_rd hW hR hez hg hbn (c := 124) (n := 4) (by omega) (by omega)]
    exact hM.fr.argc
  have ea : rdq(V, K.bp + 112#64 + 16#64) = K.argv := by
    rw [bp_16, h.cxa_rd hW hR hez hg hbn (c := 128) (n := 8) (by omega) (by omega)]
    exact hM.fr.argv
  have hmn : rdq(V, K.bp + 112#64 + 24#64) = K.main := by
    rw [bp_24, h.cxa_rd hW hR hez hg hbn (c := 136) (n := 8) (by omega) (by omega)]
    exact hM.fr.main
  -- `__libc_enable_secure` and the arrays
  have hsec : rdd(V, 7937248#64) = 0 := by
    rw [rd_ext (W' := V) (W := Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) 7937248#64 4 fun i hi =>
      h.cxa_lo hR (by rw [toNat_add_of_fits hi (by rw [t0]; omega), t0]; omega)]
    exact h.sec hKo hM hbB hW fun _ _ => trivial
  obtain ⟨hpre, harr⟩ := arr_tg (V := V) hIm fun a ha =>
    (h.cxa_lo hR (by omega)).trans (h.arr hKo hM hW ha trivial)
  refine StartB.lsb_tail c hfs hl hinD hinP hinS hin₂ h₂ hdf hx87 hK hA hrip hq hbp (by rw [tq]; omega)
    (by rw [tq]; omega) hq16 (by rw [hf]; omega) (.inl (by rw [hf, tq]; omega)) (.inl (by rw [hf, tq]; omega))
    (.inl (by rw [hf, tq]; omega)) (.inr (by rw [hf]; omega)) h0 hfe8 hfc hfa hfm hra hst hsw hbw hs0 hs1 hdw hdW
    hlr hft hg0 hg1 hgw hsec hmn hE hpre harr hI hI0 (by rw [ec, ea]; exact hfn) hI104 ?_
  intro Vm V₁ Z' t' hKZ hAZ hI1 hout hra' hrZ hsZ hdi hsi hdx
  exact k Vm V₁ Z' t' hKZ hAZ hI1 hout hra' hrZ hsZ (by rw [hdi, ec]) (by rw [hsi, ea]) hdx

end FV7z.Start
