import FV7z.Start.RegZ
import FV7z.Start.ToCxa
import FV7z.Ctor.HO
/-!
# `CEnv` at the call of `__libc_csu_init` (PLAN.md §M, `launch_to_main`)

`Ctor.at_ctor_gs` asks for `CEnv`: the code of the constructors, the registrars' contracts, the frame's
preconditions (`PEnv`), the footprint around the call and the tables of constructors 82 and 87. Here it is for the
footprint `lifG` of the start after `__libc_init_first`, from the layout: the TCB at `B + 2176` in the break's first
pages, the heap's top `hi` above it, the stack from `lo` to `top` with `sp` in it.

- `Ctor.CtorCode`: the code `CEnv` asks for.
- `rng_at`: bytes from an address in a range; `gr_ro`: `.rodata` is read by `lifG`; `reg_var`: the registrars'
  tables and counts are in `.data`/`.bss`.
- `ctor_env`: `CEnv` for `lifG`.
- `FromMain`: what the run from `main` on asks; `ctor_at_lif`: `AtCtor` for `lifG` from it (`Ctor.at_ctor_gs`).
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start FV7z.Mal FV7z.Prepare

/-- The code `CEnv` asks for: the stretch of the constructors that store and jump (`sti`), the bare `ret`, the
registrars and the functions the constructors call or jump to. -/
structure CtorCode (L : List (Addr × List Byte)) : Prop where
  hin : CodeIn L sti_at sti
  hinN : CodeIn L nret_at nret
  hinR : ∀ r, CodeIn L (regAt r) (regCode r)
  i3 : CodeIn L C3.c3_at C3.c3
  i15 : CodeIn L C15.c15_at C15.c15
  i78 : CodeIn L C78.c78_at C78.c78
  iF17 : CodeIn L cf17_at cf17
  iU17 : CodeIn L umk_at umk
  iLz : CodeIn L 0x427de0 lz
  iSse41 : CodeIn L 0x424390 sse41
  iAvx2 : CodeIn L 0x4244b0 avx2
  iAvx : CodeIn L 0x424440 avx
  iMaxf : CodeIn L 0x4242b0 maxf
  iCpuid : CodeIn L 0x424290 cpuid
  iSha1p : CodeIn L 0x43a740 sha1p
  iSha : CodeIn L 0x4243e0 sha
  iSsse3 : CodeIn L 0x424340 ssse3
  iSha256p : CodeIn L 0x43b3e0 sha256p
  iAesg : CodeIn L 0x41e540 aesg
  iAes : CodeIn L 0x4242f0 aes
  iVaes : CodeIn L 0x4245a0 vaes
  iB2s : CodeIn L 0x422a20 b2s
  iSwap : CodeIn L 0x43d3d0 swap
  iMxs : CodeIn L Mxs.mxs_at Mxs.mxs
  iMxi : CodeIn L Mxi.mxi_at Mxi.mxi
  iCxa : CodeIn L Cxa.cxa_at Cxa.cxa
  iNef : CodeIn L Nef.nef_at Nef.nef
  iOin : CodeIn L Oin.oin_at Oin.oin
  iNst : CodeIn L Nst.nst_at Nst.nst
  iOnw : CodeIn L Onw.onw_at Onw.onw
  iMnx : CodeIn L Mnx.mnx_at Mnx.mnx
  iImm : CodeIn L Imm.imm_at Imm.imm
  iHca : CodeIn L Hca.hca_at Hca.hca

/-- The registrars' tables and counts are in `[0x792000, 0x7a9000)`. -/
theorem reg_var : ∀ r, 0x792000 ≤ (regTab r).toNat ∧ (regTab r).toNat + 8 * regMax r ≤ 0x7a9000 ∧
    0x792000 ≤ (regCnt r).toNat ∧ (regCnt r).toNat + 4 ≤ 0x7a9000
  | 0 => by decide
  | 1 => by decide
  | _ + 2 => (by decide : 0x792000 ≤ (7981024#64 : Addr).toNat ∧ (7981024#64 : Addr).toNat + 8 * 32 ≤ 0x7a9000 ∧
      0x792000 ≤ (7981280#64 : Addr).toNat ∧ (7981280#64 : Addr).toNat + 4 ≤ 0x7a9000)

end FV7z.Ctor

namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn

variable {lo top : Nat} {B : Addr} {L : List (Addr × List Byte)} {y : Addr}

/-- `n` bytes from `x` (at `c`) in a range where `P` holds. -/
theorem rng_at {x : Addr} {c n lo hi : Nat} {P : Addr → Prop} (hxt : x.toNat = c) (hc : lo ≤ c) (hn : c + n ≤ hi)
    (hhi : hi ≤ 2 ^ 64) (hP : ∀ y : Addr, lo ≤ y.toNat → y.toNat < hi → P y) : ∀ i < n, P (x.add i) :=
  fun i hi' => by
    have t : (x.add i).toNat = c + i := by rw [toNat_add_of_fits hi' (by omega), hxt]
    exact hP _ (by omega) (by omega)

/-- `.rodata` (`[0x6d8000, 0x776000)`) is read by `lifG`. -/
theorem gr_ro (h1 : 0x6d8000 ≤ y.toNat) (h2 : y.toNat < 0x776000) : Foot (lifG lo top B L).reads y :=
  ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, show _ ∧ _ from ⟨by rgn_red; omega, by rgn_red; omega⟩⟩

/-- The stack offsets `CEnv` names. -/
theorem env_offs {sp : Addr} (h : 1024 ≤ sp.toNat) : (sp - 64#64 - 8).toNat = sp.toNat - 72 ∧
    (sp - 64#64 - 8 - 8).toNat = sp.toNat - 80 ∧ (sp - 256#64).toNat = sp.toNat - 256 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

/-- The stack guard's word in the TCB. -/
theorem fb_40 (h : B.toNat + 8192 ≤ 2 ^ 63) : (B + 2176#64 + 40#64).toNat = B.toNat + 2216 := by
  bv_omega

/-- `CEnv` for the footprint `lifG` at a state with the TCB at `B + 2176`, the heap's top `hi` and `sp` on the
stack. -/
theorem ctor_env {prof : Profile} {s : State} {o : Oracle} {gP : State → Nat → List Event → Prop}
    {gE : Outcome → List Event → Prop} {V : Addr → Byte} {sp : Addr} {hi : Nat}
    (c : Seg prof (lifG lo top B L) (lifG lo top B L).writes L s o)
    (hC : Csu.Env (lifG lo top B L) (lifG lo top B L).writes L sp csuTg) (cc : Ctor.CtorCode L)
    (hU : InsOK 95 gP gE) (hCe : Glibc.CacheEnds prof) (hpc : prof.Consistent)
    (hfs : s.cpu.seg.fsBase = B + 2176#64) (hrs : s.thread.rseq = none) (hdf : s.cpu.rflags.df = false)
    (hx87 : s.cpu.x87.full = 0) (hb : 0x7a9000 ≤ B.toNat) (hbt : B.toNat + 8192 ≤ 2 ^ 63) (htop : top ≤ 2 ^ 47)
    (hlo : lo ≤ hi) (hfh : B.toNat + 2240 ≤ hi) (hhs : hi + 1024 ≤ sp.toNat) (hst : sp.toNat + 8 ≤ top)
    (hal : (sp - 64#64 + 8).toNat % 16 = 0) (hTb : C82.Tb V) (hT3 : C87.T3 V) :
    Ctor.CEnv prof (lifG lo top B L) (lifG lo top B L).writes L s o gP gE V sp (B + 2176#64) hi := by
  have ef := brk_2176 hbt
  have e40 := fb_40 hbt
  obtain ⟨o72, o80, o256⟩ := env_offs (sp := sp) (by omega)
  have ec : (Addr.add s.cpu.seg.fsBase 40).toNat = B.toNat + 2216 := by
    rw [hfs, toNat_add_of_fits (a := B + 2176#64) (i := 40) (n := 41) (by decide) (by omega), ef]
  have hFs : ∀ y : Addr, lo ≤ y.toNat → y.toNat < top → Foot (lifG lo top B L).data y :=
    fun _ h1 h2 => gd_stack htop h1 h2
  have hWs : ∀ y : Addr, lo ≤ y.toNat → y.toNat < top → Foot (lifG lo top B L).writes y :=
    fun _ h1 h2 => gw_stack htop h1 h2
  have hFd : ∀ y : Addr, 0x792000 ≤ y.toNat → y.toNat < 0x7a9000 → Foot (lifG lo top B L).data y :=
    fun _ h1 h2 => gd_var h1 h2
  have hWd : ∀ y : Addr, 0x792000 ≤ y.toNat → y.toNat < 0x7a9000 → Foot (lifG lo top B L).writes y :=
    fun _ h1 h2 => gw_var h1 h2
  have hFb : ∀ y : Addr, B.toNat ≤ y.toNat → y.toNat < B.toNat + 8192 → Foot (lifG lo top B L).data y :=
    fun _ h1 h2 => gd_brk h1 h2
  have hWb : ∀ y : Addr, B.toNat ≤ y.toNat → y.toNat < B.toNat + 8192 → Foot (lifG lo top B L).writes y :=
    fun _ h1 h2 => gw_brk h1 h2
  have hR : ∀ r, Ctor.RegSpec prof (lifG lo top B L) (lifG lo top B L).writes L s o (Ctor.regAt r) (Ctor.regCnt r)
      (Ctor.regTab r) (Ctor.regMax r) := fun r => by
    obtain ⟨t1, t2, c1, c2⟩ := Ctor.reg_var r
    exact Ctor.reg_ok c r (cc.hinR r) (rng_at rfl (by omega) (by omega) (by omega) hFd)
      (rng_at rfl (by omega) (by omega) (by omega) hWd) (rng_at rfl (by omega) (by omega) (by omega) hWd)
  have hP : Ctor.PEnv prof (lifG lo top B L) (lifG lo top B L).writes s sp :=
    { pc := hpc, df := hdf, x87 := hx87, al := hal, hi := by omega,
      stk := fun y h1 h2 => hWs y (by omega) (by omega), can := by omega,
      canF := fun y hy => by
        have hy' : (Addr.add s.cpu.seg.fsBase 40).toNat ≤ y.toNat ∧
            y.toNat < (Addr.add s.cpu.seg.fsBase 40).toNat + 8 := hy
        exact .inl (hWb y (by omega) (by omega)) }
  have hSb : ∀ y, Foot [Ctor.canary s, ⟨0x6d8040, 256⟩] y →
      Foot (lifG lo top B L).writes y ∨ Foot (lifG lo top B L).reads y := fun y ⟨r, hr, hm⟩ => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have hy' : (Addr.add s.cpu.seg.fsBase 40).toNat ≤ y.toNat ∧
          y.toNat < (Addr.add s.cpu.seg.fsBase 40).toNat + 8 := hm
      exact .inl (hWb y (by omega) (by omega))
    · have hy' : (0x6d8040#64 : Addr).toNat ≤ y.toNat ∧ y.toNat < (0x6d8040#64 : Addr).toNat + 256 := hm
      have t : (0x6d8040#64 : Addr).toNat = 0x6d8040 := rfl
      exact .inr (gr_ro (by omega) (by omega))
  exact
    { c := c, hC := hC, hin := cc.hin, hR := hR, hinR := cc.hinR, hP := hP, hfs := hfs, hU := hU, hrs := hrs,
      hCe := hCe, hfb := by omega, hfh := by omega, hhs := hhs,
      hW := fun a h1 h2 => hWd a (by omega) (by omega),
      hsw := fun a h1 h2 => hWs a (by omega) (by omega),
      hst72 := rng_at o72 (by omega) (by omega) (by omega) hWs,
      hst80 := rng_at o80 (by omega) (by omega) (by omega) hWs,
      hRo := fun a h1 h2 => foot_reads (gr_ro (by omega) (by omega)),
      hRw := fun a h1 h2 => hFd a (by omega) (by omega),
      hft := rng_at ef (by omega) (by omega) (by omega) hFb,
      hcn := rng_at e40 (by omega) (by omega) (by omega) hFb,
      hld := rng_at o256 (by omega) (by omega) (by omega) hFs,
      hSb := hSb, hTb := hTb, hT3 := hT3,
      i3 := cc.i3,
      i15 := cc.i15,
      i78 := cc.i78,
      iF17 := cc.iF17,
      iU17 := cc.iU17,
      iLz := cc.iLz,
      iSse41 := cc.iSse41,
      iAvx2 := cc.iAvx2,
      iAvx := cc.iAvx,
      iMaxf := cc.iMaxf,
      iCpuid := cc.iCpuid,
      iSha1p := cc.iSha1p,
      iSha := cc.iSha,
      iSsse3 := cc.iSsse3,
      iSha256p := cc.iSha256p,
      iAesg := cc.iAesg,
      iAes := cc.iAes,
      iVaes := cc.iVaes,
      iB2s := cc.iB2s,
      iSwap := cc.iSwap,
      iMxs := cc.iMxs,
      iMxi := cc.iMxi,
      iCxa := cc.iCxa,
      iNef := cc.iNef,
      iOin := cc.iOin,
      iNst := cc.iNst,
      iOnw := cc.iOnw,
      iMnx := cc.iMnx,
      iImm := cc.iImm,
      iHca := cc.iHca }

/-- The stack offsets at `0x61344a`: `main`'s return address below `q = K.bp + 112`, the frame's alignment. -/
theorem q_offs8 {q : Addr} (h : 128 ≤ q.toNat) (h16 : q.toNat % 16 = 0) :
    (q - 8#64).toNat = q.toNat - 8 ∧ (q - 8#64 - 64#64 + 8).toNat % 16 = 0 := by
  constructor <;> bv_omega

/-- What the run from `main` on asks once the constructors are done (`Ctor.at_ctor_gs`'s last hypothesis): from a
state at `main` with the bytes `Vm`, those of the invariant `Ctor.JG` at the end but on the stack's frame, `atexit`'s
word and the TCB's `768`. -/
def FromMain (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (K : Ctx) (V : Addr → Byte) (fb : Addr) (hi k : Nat) : Prop :=
  ∀ (Vm V₁ : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem Vm →
    Ctor.JG V (K.bp + 112#64 - 8#64) F Wl fb hi k 104 V₁ →
    (∀ a : Addr, ¬ ((K.bp + 112#64).toNat - 16 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat) →
      ¬ ((K.bp + 112#64).toNat + 112 ≤ a.toNat ∧ a.toNat < (K.bp + 112#64).toNat + 208) →
      ¬ (0x7a84c0 ≤ a.toNat ∧ a.toNat < 0x7a84e8) → ¬ (fb.toNat + 768 ≤ a.toNat ∧ a.toNat < fb.toNat + 776) →
      Vm a = V₁ a) →
    rdq(Vm, K.bp + 112#64 - 8#64) = lsm_at.add 1168 →
    Z'.cpu.rip = K.main → Z'.cpu.gpr.rsp = K.bp + 112#64 - 8#64 → Z'.cpu.gpr.rdi = K.argc.setWidth 64 →
    Z'.cpu.gpr.rsi = K.argv → Z'.cpu.gpr.rdx = rdq(V, 8013720#64) → GoG prof L o gev gP gE Z' t'

/-- `AtCtor` after `__cxa_atexit (fini, NULL, NULL)` returns, for the footprint `lifG`: `Ctor.at_ctor_gs` with
`ctor_env`, `csu_rz` and `csu_gs`, from the run from `main` on. -/
theorem ctor_at_lif {prof : Profile} {s : State} {o : Oracle} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {K : Ctx} {V V'' W W₂ : Addr → Byte}
    {Z : State} {g : Gprs} {a0 s' : Addr} {a1 a2 a3 : BitVec 64} {ver : BitVec 32} {fn : BitVec 64}
    (c : Seg prof (lifG lo top B L) (lifG lo top B L).writes L s o)
    (hC : Csu.Env (lifG lo top B L) (lifG lo top B L).writes L (K.bp + 112#64 - 8#64) csuTg)
    (cc : Ctor.CtorCode L) (hU : InsOK 95 gP gE) (hCe : Glibc.CacheEnds prof) (hpc : prof.Consistent)
    (hfs : s.cpu.seg.fsBase = B + 2176#64) (hrs : s.thread.rseq = none) (hdf : s.cpu.rflags.df = false)
    (hx87 : s.cpu.x87.full = 0) (h : RetAt W W₂ Z B g) (hKo : K.Ok) (hI : Img K.V0) (hB : Bss K.V0)
    (hM : MB K V) (hW : PtrW K W V B ver (fun _ => True))
    (hHp : Mal.Hp (withNew (withNew (zzsFoot lo top L) [⟨B, 8192⟩]) (brkN B))
      (brkN B ++ ([⟨B, 8192⟩] ++ (zzsFoot lo top L).writes)) (B + 2176#64) ((lifSp Z).toNat - 4144)
      (1072 * 0 + 73840) (Cti.CtMem (Lif.bcV W₂ g a0 s') (B + 2176#64) a1 a2 a3))
    (hR : Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ g a0 s') (B + 2176#64) a1 a2 a3) (lifSp Z + 152#64)
      (toBytesLE (lsm_at.add 1034) 8)) V'' (lifSp Z + 152#64) 8010400#64 8010416#64 0 fn 0 0)
    (htop : top ≤ 2 ^ 47) (hlo : lo + 4144 ≤ (lifSp Z).toNat) (hbt : B.toNat + 0x23000 ≤ 2 ^ 47)
    (hq : (K.bp + 112#64).toNat = (lifSp Z).toNat + 160) (hq16 : (K.bp + 112#64).toNat % 16 = 0)
    (hqt : (K.bp + 112#64).toNat ≤ top) (hbp : K.bp.toNat + 392 ≤ 2 ^ 64)
    (hbB : B.toNat + 8192 + 448 < K.bp.toNat)
    (hmain : FromMain prof (lifG lo top B L) (lifG lo top B L).writes L s o gev gP gE K V'' (B + 2176#64)
      ((lifSp Z).toNat - 4144) 16) :
    AtCtor prof (lifG lo top B L) (lifG lo top B L).writes L s o gev gP gE K (B + 2176#64) V'' := by
  have := h.hb; have := h.hb'; have := h.hsp
  obtain ⟨e8, eal⟩ := q_offs8 (q := K.bp + 112#64) (by omega) hq16
  obtain ⟨-, hT82, hT87⟩ := csu_tabs h hKo hI hM hW hR
  have E := ctor_env (V := V'') (hi := (lifSp Z).toNat - 4144) c hC cc hU hCe hpc hfs hrs hdf hx87 h.hb h.hb' htop
    (by omega) (by omega) (by omega) (by omega) eal hT82 hT87
  exact Ctor.at_ctor_gs rfl E (Nat.le_refl 16) cc.hinN E.hst80 hbp (csu_rz h hKo hB hM hW hR)
    (csu_gs h hKo hI hB hM hW hbB htop (by omega) hbt hHp hR) hmain

end FV7z.Start
