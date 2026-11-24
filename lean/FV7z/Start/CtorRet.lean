import FV7z.Start.CsuPre
/-!
# From the return of `__cxa_atexit` to `main`, with the first three `__libc_csu_init` calls done (PLAN.md G3)

`AtMain` asks for an invariant of all 104 calls of `__libc_csu_init`. `AtCtor` asks for one of the 101
constructors of 7-Zip only (from the call 3 on): the first three (`elision_init`, `_init`, `frame_dummy`) are run
by `pre_runs`, on the bytes of `PreB`, which are the launch image's at `0x61344a` (`RetAt.pre`).

- `AtCtor`: an invariant `J` from the call 3 on, `J 3` after `frame_dummy`'s stores (`Rfi.Dat`) on bytes whose
  `PreB` are the image's and the others away from the stack as `V`, the 101 constructors' `Csu.Runs` for `J`, and
  the run from `main` on.
- `at_main_of_ctor`: `AtCtor` gives `AtMain` with `preI`.
- `cxa_ctor_at`: `cxa_main_at` with `AtCtor`.
- `gd_ro`: `.rodata` (with `__EH_FRAME_BEGIN__`) is data of `lifG`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Tun (Vst_out)
open FV7z.DebugInit (rDebug rLoaded)

variable {F : Footprint} {Wl : List Rgn}
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State} {t : Nat}
  {W W₂ : Addr → Byte} {Z : State} {B a0 s : Addr} {g : Gprs} {a1 a2 a3 : BitVec 64}

/-- What the run from `0x61344a` to `main` asks beyond the bytes, for the bytes `V` there and the TCB at `fb`, once
the first three calls of `__libc_csu_init` are proved: an invariant `J` of the 101 constructors (`Csu.Runs` for
`csuTg 3` to `csuTg 103`), which `frame_dummy`'s stores start on bytes with `PreB` as the image's and the bytes
outside the stack's `[sp - 136, sp + 8)` and `elision_init`'s word as `V` (`Near`), and the run from `main` on. -/
def AtCtor (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (K : Ctx)
    (fb : Addr) (V : Addr → Byte) : Prop :=
  ∃ J : Nat → (Addr → Byte) → Prop,
    (∀ m, 3 ≤ m → ∀ V V', J m V →
      FV7z.Raf.Out ((K.bp + 112#64 - 8#64).toNat - 64) (K.bp + 112#64 - 8#64).toNat V V' → J m V') ∧
    (∀ W W', Agr K.V0 W → Near ((K.bp + 112#64 - 8#64).toNat - 136) ((K.bp + 112#64 - 8#64).toNat + 8) V W →
      Rfi.Dat ((K.bp + 112#64 - 8#64).toNat - 64 - 72) ((K.bp + 112#64 - 8#64).toNat - 64) 7947808#64 7388000#64 W W' →
      J 3 W') ∧
    (∀ m, 3 ≤ m → m < 104 → Csu.Runs prof F Wl L s₀ o gev gP gE J (K.bp + 112#64 - 8#64)
      (((K.argc.setWidth 64).setWidth 32).setWidth 64) K.argv rdq(V, 8013720#64) m (csuTg m)) ∧
    (∀ V', J 104 V' → ∀ a : Addr, ((K.bp + 112#64).toNat + 12 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat + 32 ∨
      8013720 ≤ a.toNat ∧ a.toNat < 8013728) → V' a = V a) ∧
    ∀ (Vm V₁ : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem Vm → J 104 V₁ →
      (∀ a : Addr, ¬ ((K.bp + 112#64).toNat - 16 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat) →
        ¬ ((K.bp + 112#64).toNat + 112 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat + 208) →
        ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) → ¬ (fb.toNat + 768 ≤ a.toNat ∧ a.toNat < fb.toNat + 776) →
        Vm a = V₁ a) →
      rdq(Vm, K.bp + 112#64 - 8#64) = lsm_at.add 1168 →
      Z'.cpu.rip = K.main → Z'.cpu.gpr.rsp = K.bp + 112#64 - 8#64 → Z'.cpu.gpr.rdi = K.argc.setWidth 64 →
      Z'.cpu.gpr.rsi = K.argv → Z'.cpu.gpr.rdx = rdq(V, 8013720#64) → GoG prof L o gev gP gE Z' t'

/-- `AtCtor` gives `AtMain`, the invariant `preI K.V0 J`, when the bytes of `PreB` are the image's. -/
theorem at_main_of_ctor {K : Ctx} {fb : Addr} {V : Addr → Byte} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hC : Csu.Env F Wl L (K.bp + 112#64 - 8#64) csuTg)
    (hE0 : Eli.Env F Wl L fb (K.bp + 112#64 - 8#64 - 64#64)) (hEi : CodeIn L Ini.ini_at Ini.ini)
    (hE2 : Fdm.Env F Wl L fb (K.bp + 112#64 - 8#64 - 64#64)) (hIm : Img K.V0) (hB : Bss K.V0)
    (hF : ∀ y : Addr, 0x777000 ≤ y.toNat → y.toNat < 0x792000 → Foot F.data y) (hV : Agr K.V0 V)
    (hG : AtCtor prof F Wl L s₀ o gev gP gE K fb V) : AtMain prof F Wl L s₀ o gev gP gE K fb V := by
  obtain ⟨J, hJo, hJ3, hJr, hJ104, k⟩ := hG
  have n := Csu.sp_n hC.s0
  have hs2 := hE2.s0
  have hs8 := hC.s8
  rw [n] at hs2
  refine ⟨preI K.V0 V ((K.bp + 112#64 - 8#64).toNat - 136) ((K.bp + 112#64 - 8#64).toNat + 8) J,
    fun m V V' hm ho => ?_, (preI_lt (by decide)).2 ⟨fun a ha => ?_, fun a h1 _ => ?_⟩, fun m hm => ?_,
    fun V' h => hJ104 V' ((preI_ge (by decide)).1 h),
    fun Vm V₁ Z' t' h1 h2 h104 => k Vm V₁ Z' t' h1 h2 ((preI_ge (by decide)).1 h104)⟩
  · by_cases h : m < 3
    · obtain ⟨hA, hN⟩ := (preI_lt h).1 hm
      refine (preI_lt h).2 ⟨fun a ha => ?_, fun a h1 h2 => (ho a (by omega)).trans (hN a h1 h2)⟩
      have ha' := ha
      unfold PreB PreN at ha'
      exact (ho a (by omega)).trans (hA a ha)
    · exact (preI_ge h).2 (hJo m (by omega) V V' ((preI_ge h).1 hm) ho)
  · have ha' := ha
    unfold PreB PreN at ha'
    rw [Vst_out _ _ _ _ (by simp only [toBytesLE_length]; omega) (.inl (by omega))]
    exact hV a ha
  · exact Vst_out _ _ _ _ (by simp only [toBytesLE_length]; omega) (by simp only [toBytesLE_length]; omega)
  · by_cases h : m < 3
    · exact pre_runs c hfs hC hE0 hEi hE2 hIm hB hF hJ3 m h
    · exact runs_congr (funext fun V => propext (preI_ge h)) (funext fun V => propext (preI_ge (by omega)))
        (hJr m (by omega) hm)

/-- `cxa_main_at` with `AtCtor`: the first three calls of `__libc_csu_init` from the bytes of the launch. -/
theorem cxa_ctor_at {K : Ctx} {V₀ V : Addr → Byte} {ver : BitVec 32} {f0 : BitVec 64} {code₂ : List Byte}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = B + 2176#64) (hl : CodeIn L lsm_at lsm)
    (hinD : CodeIn L Dbg.dbg_at Dbg.dbg) (hinP : CodeIn L Sjp.sjp_at Sjp.sjp) (hinS : CodeIn L Ssj.ssj_at Ssj.ssj)
    (hin₂ : CodeIn L K.main code₂) (h₂ : 0 < code₂.length)
    (hdf : s₀.cpu.rflags.df = false) (hx87 : s₀.cpu.x87.full = 0)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lsm_at.add 1034)
    (hq : X.cpu.gpr.rsp = K.bp + 112#64) (hbp : X.cpu.gpr.rbp = Csu.csu_at)
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s) (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
      (toBytesLE (lsm_at.add 1034) 8)) V (lifSp Z + 152#64) 8010400#64 8010416#64 0 f0 0 0)
    (h : RetAt W W₂ Z B g) (hKo : K.Ok) (hIm : Img K.V0) (hB : Bss K.V0) (hM : MB K V₀)
    (hW : PtrW K W V₀ B ver (fun _ => True))
    (hez : K.bp.toNat + 112 = (entG Z).rsp.toNat + 8) (hg : g.rsp.toNat ≤ (entG Z).rsp.toNat + 8)
    (hbB : B.toNat + 2072 + 448 < K.bp.toNat) (hbn : K.bp.toNat + 328 ≤ 2 ^ 64)
    (hq16 : (K.bp + 112#64).toNat % 16 = 0)
    (h0 : ∀ i < 4, Foot F.data (Addr.add 7937248#64 i)) (hfe8 : ∀ i < 8, Foot F.data (Addr.add 8013720#64 i))
    (hfc : ∀ i < 4, Foot F.data ((K.bp + 112#64 + 12#64).add i))
    (hfa : ∀ i < 8, Foot F.data ((K.bp + 112#64 + 16#64).add i))
    (hfm : ∀ i < 8, Foot F.data ((K.bp + 112#64 + 24#64).add i))
    (hra : ∀ i < 8, Foot Wl (Addr.add (K.bp + 112#64 - 8#64) i))
    (hst : ∀ i < 16, Foot Wl (Addr.add (K.bp + 112#64 - 16#64) i))
    (hsw : ∀ y : Addr, (K.bp + 112#64).toNat - 8 ≤ y.toNat → y.toNat < (K.bp + 112#64).toNat → Foot F.writes y)
    (hbw : ∀ i < 96, Foot Wl (Addr.add (K.bp + 112#64 + 112#64) i))
    (hs0 : ∀ i < 8, Foot Wl ((K.bp + 112#64 + 184#64).add i))
    (hs1 : ∀ i < 8, Foot Wl ((K.bp + 112#64 + 192#64).add i))
    (hdw : ∀ y, rDebug.Mem y → Foot F.writes y) (hdW : ∀ y, rDebug.Mem y → Foot Wl y)
    (hlr : ∀ y, rLoaded.Mem y → Foot F.writes y ∨ Foot F.reads y)
    (hft : ∀ i < 56, Foot F.data (Addr.add (B + 2176#64) i))
    (hg0 : ∀ i < 8, Foot F.data ((B + 2176#64 + 768#64).add i))
    (hg1 : ∀ i < 8, Foot F.data ((B + 2176#64 + 760#64).add i))
    (hgw : ∀ i < 8, Foot Wl ((B + 2176#64 + 768#64).add i))
    (hE : Csu.Env F Wl L (K.bp + 112#64 - 8#64) csuTg)
    (hE0 : Eli.Env F Wl L (B + 2176#64) (K.bp + 112#64 - 8#64 - 64#64)) (hEi : CodeIn L Ini.ini_at Ini.ini)
    (hE2 : Fdm.Env F Wl L (B + 2176#64) (K.bp + 112#64 - 8#64 - 64#64))
    (hF : ∀ y : Addr, 0x777000 ≤ y.toNat → y.toNat < 0x792000 → Foot F.data y)
    (hG : AtCtor prof F Wl L s₀ o gev gP gE K (B + 2176#64) V) :
    GoG prof L o gev gP gE X t :=
  cxa_main_at c hfs hl hinD hinP hinS hin₂ h₂ hdf hx87 hK hA hrip hq hbp hR h hKo hIm hM hW hez hg hbB hbn hq16 h0
    hfe8 hfc hfa hfm hra hst hsw hbw hs0 hs1 hdw hdW hlr hft hg0 hg1 hgw hE
    (at_main_of_ctor c hfs hE hE0 hEi hE2 hIm hB hF (fun _ ha => h.pre hKo hM hW hR ha) hG)

theorem gd_ro {lo top : Nat} {B : Addr} {L : List (Addr × List Byte)} {y : Addr} (h1 : 0x6d8000 ≤ y.toNat)
    (h2 : y.toNat < 0x776000) : Foot (lifG lo top B L).data y :=
  foot_reads ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩

end FV7z.Start
