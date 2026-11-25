import FV7z.Start.ToCxa
import FV7z.Start.CtorRet
import FV7z.Start.CtorEnv
/-!
# From the launch of `7zzs` to `main` (PLAN.md G3, startup)

`launch_to_cxa` ends at the return of `__cxa_atexit (fini, NULL, NULL)` to `0x61344a`; `cxa_ctor_at` runs from there
through `__libc_csu_init` (its first three calls proved, the 101 constructors by `Csu.Runs` for an invariant),
`_dl_debug_initialize` and `_setjmp` to the first byte of `main` (`0x41cd90`), with `argc`, `argv` of the launch in
`rdi`, `rsi`. Here the two are joined: the footprint facts come from `lifG` and the layout, the stack pointer and
`rbp` (`init`) from `Osv.Back` and `Rg`.

- `MainCode L`: the code of the functions called on the way and of `main`, and of the 104 functions `csuTg`.
- `q_offs`, `s_offs`, `brk_offs`, `back_q`: the offsets, apart from the large context (`rng_at`: `Start/CtorEnv`).
- `launch_to_main`: as `launch_to_cxa`, with `__cxa_atexit`'s return continued through the constructors
  (`ctor_at_lif`) to `main` (`FromMain`).
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Smm (size smEv smEv2)
open FV7z.Mhi (C2)
open FV7z.Gor (gEv gor_at)
open FV7z.StartB (PimCode)
open FV7z.Tls (TlsMem)

/-- The code of `_dl_debug_initialize`, `_setjmp` (and `__sigsetjmp`), `__libc_csu_init`, of `main` and of the 104
functions `__libc_csu_init` calls, with that of the first three and of the functions they call (`__tunable_get_val`,
`register_tm_clones`, `__register_frame_info_bases`, `pthread_mutex_lock`, `pthread_mutex_unlock`). -/
structure MainCode (L : List (Addr × List Byte)) : Prop where
  dbg : CodeIn L Dbg.dbg_at Dbg.dbg
  sjp : CodeIn L Sjp.sjp_at Sjp.sjp
  ssj : CodeIn L Ssj.ssj_at Ssj.ssj
  csu : CodeIn L Csu.csu_at Csu.csu
  main : ∃ code, CodeIn L 0x41cd90#64 code ∧ 0 < code.length
  tcode : ∀ i < 104, ∃ code, CodeIn L (csuTg i) code ∧ 0 < code.length
  eli : CodeIn L Eli.eli_at Eli.eli
  tgv : CodeIn L Tgv.tgv_at Tgv.tgv
  ini : CodeIn L Ini.ini_at Ini.ini
  fdm : CodeIn L Fdm.fdm_at Fdm.fdm
  rtc : CodeIn L Rtc.rtc_at Rtc.rtc
  rfi : CodeIn L Rfi.rfi_at Rfi.rfi
  pml : CodeIn L Pml.pml_at Pml.pml
  pmu : CodeIn L Pmu.pmu_at Pmu.pmu

/-- The stack offsets of `cxa_main_at` from `q = rsp` at `0x613434`. -/
theorem q_offs {q : Addr} {S : Nat} (h : q.toNat = S - 288) (h1 : 4096 ≤ S) (h2 : S ≤ 2 ^ 47) :
    (q + 12#64).toNat = S - 276 ∧ (q + 16#64).toNat = S - 272 ∧ (q + 24#64).toNat = S - 264 ∧
      (q - 8#64).toNat = S - 296 ∧ (q - 16#64).toNat = S - 304 ∧ (q + 112#64).toNat = S - 176 ∧
      (q + 184#64).toNat = S - 104 ∧ (q + 192#64).toNat = S - 96 ∧ (q - 8#64 - 64#64).toNat = S - 360 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- The frames of the first functions `__libc_csu_init` calls. -/
theorem s_offs {q : Addr} {S : Nat} (h : q.toNat = S - 288) (h1 : 4096 ≤ S) (h2 : S ≤ 2 ^ 47) :
    (q - 8#64 - 64#64 - 32#64).toNat = S - 392 ∧ (q - 8#64 - 64#64 - 72#64).toNat = S - 432 := by
  constructor <;> bv_omega

/-- The TCB's offsets from the break. -/
theorem brk_offs {B : Addr} (h : B.toNat + 8192 ≤ 2 ^ 63) :
    (B + 2176#64 + 768#64).toNat = B.toNat + 2944 ∧ (B + 2176#64 + 760#64).toNat = B.toNat + 2936 ∧
      (B + 2176#64 + 40#64).toNat = B.toNat + 2216 ∧ (B + 2176#64 + 720#64).toNat = B.toNat + 2896 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- `__cxa_atexit`'s stack pointer at its return (`R - 320`) against `main`'s entry one (`R - 296`): stated alone so
that `omega` does not run in `launch_to_main`'s context (maximum recursion depth, kt101, kt102). -/
theorem rsp_320_296 (R : Nat) : R - 320 ≤ R - 296 + 8 := by omega

/-- The stack pointer after `__cxa_atexit` returns: that at `0x613434`. -/
theorem back_q (Z : State) : lifSp Z + 152#64 + 8#64 = Z.cpu.gpr.rsp := by
  rw [lifSp_152]
  show Z.cpu.gpr.rsp - 8#64 + 8#64 = Z.cpu.gpr.rsp
  exact BitVec.sub_add_cancel _ _

set_option maxHeartbeats 4000000 in
/-- From the launch of `7zzs` to the first byte of `main` (and to the branch where `readlink` of `/proc/self/exe`
fails). -/
theorem launch_to_main {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {t : Nat}
    -- the launch, as in `launch_to_ptr`
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (hroom : StackRoom l.args n) (hn : 5000 ≤ n)
    (hs : l.args.secure = false) (hq : l.args.threadPending = [] ∧ l.args.signal.pending = [])
    (hlu : LimitsUnlimited l.s₀)
    (noG : ∀ i < l.args.envp.length, (∀ k < 14, (l.args.envp.getD i [] ++ [0]).getD k 0 = Tun.gz k) →
      (l.args.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < l.args.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (l.args.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (l.args.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61)
    (noLD : ∀ i < l.args.envp.length, ¬ ((l.args.envp.getD i [] ++ [0]).getD 0 0 = 0x4c ∧
      (l.args.envp.getD i [] ++ [0]).getD 1 0 = 0x44 ∧ (l.args.envp.getD i [] ++ [0]).getD 2 0 = 0x5f))
    (hpc : l.prof.Consistent) (hch : Chain l.prof) (ho : Undisturbed o) (hvd : l.prof.linux.vdso = false)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (hC : StartCode L) (hT : TlsCode L) (hO : OsvCode L)
    (hP : PimCode L) (hM : l.prof.linux.Modest) (hmg : ∀ t p, o t (.memFail p) = none) (hpse : ProcSelfExe o)
    (hcpy : Tls.CpyAt l.prof L o 4198512#64 (GotOkB l.prof)) (hun : ∀ t, KernelNew (o t .uname).val)
    -- `__libc_init_first`'s code and the contracts of the functions it calls through the PLT
    (hLC : LifCode L) (hMC : MalCode L)
    (hlen : Str.LenAt l.prof L o 4198664#64 (GotOkB l.prof))
    (hcmp : Str.NcmpAt l.prof L o 4198472#64 (GotOkB l.prof))
    (hpcy : Gor.PcpyAt l.prof L o 4198592#64 (GotOkB l.prof))
    (hset : Ipa.SetAt l.prof L o 4198528#64 (GotOkB l.prof))
    (hrchr : Str.RchrAt l.prof L o 4198480#64 (GotOkB l.prof))
    -- `__cxa_atexit`'s code, and that of the tail of `__libc_start_main` up to `main`
    (hX : CxaCode L) (hMn : MainCode L)
    -- the constructors' code; `umask` (95) adds no event the goal minds; the CPUs' cache leaves end
    (hCC : Ctor.CtorCode L) (hU : InsOK 95 gP gE) (hCe : Glibc.CacheEnds l.prof) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
      ((∀ (s₂ Z : State) (W V' : Addr → Byte) (g : Gprs) (x1 x2 x3 d r10 r8 r9 : BitVec 64) (u : List Byte)
          (y1 y2 y3 y4 y5 q1 q2 q3 : BitVec 64),
        g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 →
        Seg l.prof (withNew (zzsFoot (loOf l n c) c.stackTop L) [⟨brkOf l, 8192⟩])
          ([⟨brkOf l, 8192⟩] ++ (zzsFoot (loOf l n c) c.stackTop L).writes) L s₂ o →
        Base s₂ (limOf l) (brkOf l + 4544#64) (brkOf l + 2176#64) ⟨l.s₀.thread.tid⟩ →
        KeptW ([⟨brkOf l, 8192⟩] ++ (zzsFoot (loOf l n c) c.stackTop L).writes) s₂ Z →
        Agree (withNew (zzsFoot (loOf l n c) c.stackTop L) [⟨brkOf l, 8192⟩]) Z.proc.mm.mem W →
        Z.cpu.rip = 0x613434 → Rg (ctxOf l.prof l.s₀ l.args c) Z.cpu.gpr →
        Z.cpu.gpr.rdx = (ctxOf l.prof l.s₀ l.args c).envp → Z.cpu.gpr.rsi = (ctxOf l.prof l.s₀ l.args c).argv →
        Z.cpu.gpr.rdi = BitVec.setWidth 64 (ctxOf l.prof l.s₀ l.args c).argc →
        CpuOk l.prof Z.proc.mm.mem → V2606.GotOk l.prof Z.proc.mm.mem → CpuFeat.HwW Z.proc.mm.mem.readByte →
        CpuFeat.PlW V' Z.proc.mm.mem.readByte → MB (ctxOf l.prof l.s₀ l.args c) V' →
        UtsnameOk u → KernelNew u → PtrW (ctxOf l.prof l.s₀ l.args c) W V' (brkOf l) (osVersion u) (fun _ => True) →
        rdd(TlsMem V' (brkOf l), 8029624#64) = 0 →
        -- `readlink` of `/proc/self/exe` fails
        (∀ r Z' t', KeptW ([⟨brkOf l, 8192⟩] ++ (zzsFoot (loOf l n c) c.stackTop L).writes) s₂ Z' →
          Agree (withNew (zzsFoot (loOf l n c) c.stackTop L) [⟨brkOf l, 8192⟩]) Z'.proc.mm.mem
            (Gor.frV (Ndi.nV (lifW W Z) (lifSp Z) (lifY W Z)) { lifY W Z with rsp := lifSp Z - 8#64 }) →
          Z'.cpu.rip = gor_at.add 271 → Z'.cpu.gpr.rax = 18446744073709551615#64 →
          Z'.cpu.gpr.rsp = lifSp Z - 8#64 → Z'.cpu.gpr.rbx = (lifY W Z).rbx → Z'.cpu.gpr.rbp = (lifY W Z).rbp →
          Z'.cpu.gpr.r12 = (lifY W Z).r12 → Z'.cpu.gpr.r13 = (lifY W Z).r13 → Z'.cpu.gpr.r14 = (lifY W Z).r14 →
          Z'.cpu.gpr.r15 = (lifY W Z).r15 →
          GoG l.prof L o (gev ++ ptrEvs l c s₂ g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 ++
            [gEv { lifY W Z with rsp := lifSp Z - 8#64 } r]) gP gE Z' t') ∧
        -- `__libc_init_first` returns
        (∀ (x : ExePath) (evs : List Event) (s₃ Z₁ Z' : State) (s : Addr) (W₂ : Addr → Byte),
          (∃ g₁ g₂ : Gprs, g₁.rdi = 656#64 ∧ g₂.rax = brkOf l + 4544#64 ∧ g₂.r14 = size 0x20000#64 656#64 ∧
            (evs = [smEv g₁ 0x20000#64 (brkOf l + 4544#64)] ∨
              evs = [smEv g₁ 0x20000#64 (brkOf l + 4544#64), smEv2 g₂])) →
          Seg l.prof (lifG (loOf l n c) c.stackTop (brkOf l) L) (lifG (loOf l n c) c.stackTop (brkOf l) L).writes L
            s₃ o →
          Base s₃ (limOf l) (brkOf l + 4544#64 + size 0x20000#64 656#64 + C2 (brkOf l + 4544#64) 0x20000#64)
            (brkOf l + 2176#64) ⟨l.s₀.thread.tid⟩ →
          Ndi.NdiRet (lifW W Z) (lifSp Z) (lifY W Z) (brkOf l + 4544#64) (brkOf l + 2176#64) W₂ →
          Z₁.cpu.gpr.rsp = lifSp Z + 128#64 → Z₁.cpu.gpr.rbp = (lifY W Z).rbp →
          Z₁.cpu.gpr.r12 = (lifY W Z).r12 → Z₁.cpu.gpr.r13 = (lifY W Z).r13 →
          KeptW (lifG (loOf l n c) c.stackTop (brkOf l) L).writes s₃ Z' →
          Agree (lifG (loOf l n c) c.stackTop (brkOf l) L) Z'.proc.mm.mem
            (Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings) s)
              (brkOf l + 2176#64) 7299392#64 7296832#64 7295296#64) →
          Mal.Hp (withNew (withNew (zzsFoot (loOf l n c) c.stackTop L) [⟨brkOf l, 8192⟩]) (brkN (brkOf l)))
            (brkN (brkOf l) ++ ([⟨brkOf l, 8192⟩] ++ (zzsFoot (loOf l n c) c.stackTop L).writes)) (brkOf l + 2176#64)
            ((lifSp Z).toNat - 4144) (1072 * 0 + 73840)
            (Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings) s)
              (brkOf l + 2176#64) 7299392#64 7296832#64 7295296#64) →
          Ims.Short (lifW W Z) (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings) (arg0 l.args).length s →
          Z'.cpu.rip = lsm_at.add 1017 → Z'.cpu.gpr.rsp = lifSp Z + 160#64 →
          Z'.cpu.gpr.rbx = (lifY W Z).rbx → Z'.cpu.gpr.rbp = rdq(lifW W Z, lifSp Z + 128#64) →
          Z'.cpu.gpr.r12 = rdq(lifW W Z, lifSp Z + 136#64) → Z'.cpu.gpr.r13 = rdq(lifW W Z, lifSp Z + 144#64) →
          Z'.cpu.gpr.r14 = (lifY W Z).r14 → Z'.cpu.gpr.r15 = (lifY W Z).r15 →
          -- `__cxa_atexit (fini, NULL, NULL)` returns, the constructors run: the run from `main` on
          ∀ (V'' : Addr → Byte) (g' : Gprs) (Z'' : State),
          KeptW (lifG (loOf l n c) c.stackTop (brkOf l) L).writes s₃ Z'' →
          Agree (lifG (loOf l n c) c.stackTop (brkOf l) L) Z''.proc.mm.mem V'' →
          Cxa.Reg (Vst (Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr
              (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings) s) (brkOf l + 2176#64) 7299392#64
              7296832#64 7295296#64) (lifSp Z + 152#64) (toBytesLE (lsm_at.add 1034) 8))
            V'' (lifSp Z + 152#64) 8010400#64 8010416#64 0
            ((Z'.cpu.gpr.r12 ^^^ rdq(Cti.CtMem (Lif.bcV W₂ Z₁.cpu.gpr
              (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings) s) (brkOf l + 2176#64) 7299392#64 7296832#64
              7295296#64, brkOf l + 2176#64 + 48#64)).rotateLeft 17) 0 0 →
          Z''.cpu.rip = lsm_at.add 1034 → Z''.cpu.gpr = g' → g'.rax = 0 →
          Osv.Back (Z'.cpu.gpr.set 4 (lifSp Z + 152#64)) g' →
          FromMain l.prof (lifG (loOf l n c) c.stackTop (brkOf l) L) (lifG (loOf l n c) c.stackTop (brkOf l) L).writes
            L s₃ o (gev ++ ptrEvs l c s₂ g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 ++
              [gEv { lifY W Z with rsp := lifSp Z - 8#64 } (.procExe x)] ++ evs ++ [Ndi.ndiEv]) gP gE
            (ctxOf l.prof l.s₀ l.args c) V'' (brkOf l + 2176#64) ((lifSp Z).toNat - 4144) 16)) →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hK, hI0, hB0, hto⟩ := launch_to_cxa (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom hn hs
    hq hlu noG noA noLD hpc hch ho hvd hL hC hT hO hP hM hmg hpse hcpy hun hLC hMC hlen hcmp hpcy hset hrchr hX
  refine ⟨c, hv, hst, hK, hI0, hB0, fun hfin => hto ?_⟩
  intro s₂ Z W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hK₂ hA₂ hr₂ hRg hdx hsi hdi'
    hcpu hgot hhw hpl hMB hu hnew hW hT3
  obtain ⟨hke, hk⟩ := hfin s₂ Z W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hK₂ hA₂ hr₂
    hRg hdx hsi hdi' hcpu hgot hhw hpl hMB hu hnew hW hT3
  refine ⟨hke, ?_⟩
  intro x evs s₃ Z₁ Z' s W₂ hevs c₃ hB₃ hN hz1 hzp h12' h13' hK₃ hA₃ hHp hsh hrip hrsp hrbx hrbp hr12 hr13 hr14 hr15
    V'' g' Z'' t'' hK'' hA'' hReg hr'' hg'' hax' hBk
  have hG := hk x evs s₃ Z₁ Z' s W₂ hevs c₃ hB₃ hN hz1 hzp h12' h13' hK₃ hA₃ hHp hsh hrip hrsp hrbx hrbp hr12 hr13 hr14
    hr15 V'' g' Z'' hK'' hA'' hReg hr'' hg'' hax' hBk
  -- where the layout puts things
  obtain ⟨h16, hn', -, -, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  have hrsp0 : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [hst.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf l.prof l.s₀ l.args c).bp.toNat = (stackLayout l.args l.prof.linux c).sp - 400 := by
    show (l.s₀.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  have hz : Z.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp - 288 := by
    rw [hRg.1]
    bv_omega
  obtain ⟨-, hb1, hb2⟩ := launch_brk h
  have hb1' : 0x7a9000 ≤ (brkOf l).toNat := hb1
  have hb2' : (brkOf l).toNat < 0x7a9000 + 4096 + 2 ^ 30 := hb2
  have hb' : (brkOf l).toNat + 8192 ≤ 2 ^ 63 := by omega
  have hlo' : loOf l n c = (stackLayout l.args l.prof.linux c).sp - n := rfl
  obtain ⟨n1, n2, -⟩ := lif_nums (Z := Z) hz (by omega) (by omega) h16
  obtain ⟨n3, n4⟩ := cxa_nums n2 (by omega) (by omega)
  have hf : (brkOf l + 2176#64).toNat = (brkOf l).toNat + 2176 := brk_2176 hb'
  obtain ⟨f768, f760, f40, f720⟩ := brk_offs hb'
  have hR : RetAt W W₂ Z (brkOf l) Z₁.cpu.gpr :=
    ⟨hN, hb1', hb', by omega, by omega, by omega, by omega, by rw [hz1, n4]; omega⟩
  have hgr : Z₁.cpu.gpr.rsp.toNat ≤ (entG Z).rsp.toNat + 8 := by rw [hz1, n4, n1]; exact rsp_320_296 _
  -- `q = rsp` at `0x613434`, `__libc_start_main`'s frame at `K.bp`
  have tq : ((ctxOf l.prof l.s₀ l.args c).bp + 112#64).toNat = (stackLayout l.args l.prof.linux c).sp - 288 := by
    rw [← hRg.1]
    exact hz
  obtain ⟨o12, o16, o24, om8, om16, o112, o184, o192, om72⟩ := q_offs tq (by omega) (by omega)
  have hFs : ∀ y : Addr, loOf l n c ≤ y.toNat → y.toNat < c.stackTop →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).data y := fun _ h1 h2 => gd_stack htop h1 h2
  have hWs : ∀ y : Addr, loOf l n c ≤ y.toNat → y.toNat < c.stackTop →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).writes y := fun _ h1 h2 => gw_stack htop h1 h2
  have hFr : ∀ y : Addr, 0x777000 ≤ y.toNat → y.toNat < 0x792000 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).data y := fun _ h1 h2 => gd_relro h1 h2
  have hFd : ∀ y : Addr, 0x792000 ≤ y.toNat → y.toNat < 0x7a9000 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).data y := fun _ h1 h2 => gd_var h1 h2
  have hFw : ∀ y : Addr, 0x792000 ≤ y.toNat → y.toNat < 0x7a9000 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).writes y := fun _ h1 h2 => gw_var h1 h2
  have hFb : ∀ y : Addr, (brkOf l).toNat ≤ y.toNat → y.toNat < (brkOf l).toNat + 8192 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).data y := fun _ h1 h2 => gd_brk h1 h2
  have hWb : ∀ y : Addr, (brkOf l).toNat ≤ y.toNat → y.toNat < (brkOf l).toNat + 8192 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).writes y := fun _ h1 h2 => gw_brk h1 h2
  have t0 : (7937248#64 : Addr).toNat = 7937248 := rfl
  have te : (8013720#64 : Addr).toNat = 8013720 := rfl
  have ta : (7829400#64 : Addr).toNat = 7829400 := rfl
  obtain ⟨os32, os72⟩ := s_offs tq (by omega) (by omega)
  have tfe : (7991628#64 : Addr).toNat = 7991628 := rfl
  have trt : (7938696#64 : Addr).toNat = 7938696 := rfl
  have tob : (7947808#64 : Addr).toNat = 7947808 := rfl
  have tbg : (7388000#64 : Addr).toNat = 7388000 := rfl
  have tmu : (8008608#64 : Addr).toNat = 8008608 := rfl
  have tan : (8008648#64 : Addr).toNat = 8008648 := rfl
  have tun : (8008664#64 : Addr).toNat = 8008664 := rfl
  have hFo : ∀ y : Addr, 0x6d8000 ≤ y.toNat → y.toNat < 0x776000 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).data y := fun _ h1 h2 => gd_ro h1 h2
  have hE0 : Eli.Env (lifG (loOf l n c) c.stackTop (brkOf l) L) (lifG (loOf l n c) c.stackTop (brkOf l) L).writes L
      (brkOf l + 2176#64) ((ctxOf l.prof l.s₀ l.args c).bp + 112#64 - 8#64 - 64#64) :=
    { code := hMn.eli, tcode := hMn.tgv, s0 := by omega, s8 := by omega, hi := by omega,
      st := rng_at os32 (by omega) (by omega) (by omega) hWs, lr := rng_at om72 (by omega) (by omega) (by omega) hFs,
      fl := rng_at f40 (by omega) (by omega) (by omega) hFb, fb8 := by omega, fd := .inl (by omega),
      fg := .inr (by omega),
      fe := rng_at tfe (by omega) (by omega) (by omega) hFd,
      rt := rng_at trt (by omega) (by omega) (by omega) hFw }
  have hE2 : Fdm.Env (lifG (loOf l n c) c.stackTop (brkOf l) L) (lifG (loOf l n c) c.stackTop (brkOf l) L).writes L
      (brkOf l + 2176#64) ((ctxOf l.prof l.s₀ l.args c).bp + 112#64 - 8#64 - 64#64) :=
    { code := hMn.fdm, tcode := hMn.rtc, rcode := hMn.rfi, lcode := hMn.pml, ucode := hMn.pmu,
      s0 := by omega, s8 := by omega, f0 := by omega, f1 := by omega,
      st := rng_at os72 (by omega) (by omega) (by omega) hWs, lr := rng_at om72 (by omega) (by omega) (by omega) hFs,
      ob := rng_at tob (by omega) (by omega) (by omega) hFw,
      bg := rng_at tbg (by omega) (by omega) (by omega) hFo,
      mu := rng_at tmu (by omega) (by omega) (by omega) hFw,
      any := rng_at tan (by omega) (by omega) (by omega) hFw,
      uns := rng_at tun (by omega) (by omega) (by omega) hFw,
      tid := rng_at f720 (by omega) (by omega) (by omega) hFb,
      fe := rng_at tfe (by omega) (by omega) (by omega) hFd }
  obtain ⟨code₂, hin₂, h₂⟩ := hMn.main
  have hE1 : Csu.Env (lifG (loOf l n c) c.stackTop (brkOf l) L) (lifG (loOf l n c) c.stackTop (brkOf l) L).writes L
      ((ctxOf l.prof l.s₀ l.args c).bp + 112#64 - 8#64) csuTg :=
    ⟨hMn.csu, rng_at om72 (by omega) (by omega) (by omega) hWs, by omega,
      rng_at om8 (by omega) (by omega) (by omega) hFs, by omega, rng_at ta (by omega) (by omega) (by omega) hFr,
      .inr (by omega), hMn.tcode, rfl⟩
  have hAt := ctor_at_lif c₃ hE1 hCC hU hCe hpc hB₃.fsb hB₃.rseq hB₃.df hB₃.x87 hR hK hI0 hB0 hMB hW hHp hReg
    htop (by omega) (by omega) (by omega) (by rw [tq]; omega) (by omega) (by omega) (by omega) hG
  refine cxa_ctor_at (t := t'') c₃ hB₃.fsb hC.lsm hMn.dbg hMn.sjp hMn.ssj hin₂ h₂ hB₃.df hB₃.x87 hK'' hA'' hr''
    ?_ ?_ hReg hR hK hI0 hB0 hMB hW (by omega) hgr (by omega) (by omega) (by rw [tq]; omega)
    (rng_at t0 (by omega) (by omega) (by omega) hFr) (rng_at te (by omega) (by omega) (by omega) hFd)
    (rng_at o12 (by omega) (by omega) (by omega) hFs) (rng_at o16 (by omega) (by omega) (by omega) hFs)
    (rng_at o24 (by omega) (by omega) (by omega) hFs) (rng_at om8 (by omega) (by omega) (by omega) hWs)
    (rng_at om16 (by omega) (by omega) (by omega) hWs) (fun y h1 h2 => hWs y (by omega) (by omega))
    (rng_at o112 (by omega) (by omega) (by omega) hWs) (rng_at o184 (by omega) (by omega) (by omega) hWs)
    (rng_at o192 (by omega) (by omega) (by omega) hWs)
    (fun y hy => by have := StartB.rDebug_mem hy; exact hFw y (by omega) (by omega))
    (fun y hy => by have := StartB.rDebug_mem hy; exact hFw y (by omega) (by omega))
    (fun y hy => by have := StartB.rLoaded_mem hy; exact .inl (hFw y (by omega) (by omega)))
    (rng_at hf (by omega) (by omega) (by omega) hFb) (rng_at f768 (by omega) (by omega) (by omega) hFb)
    (rng_at f760 (by omega) (by omega) (by omega) hFb) (rng_at f768 (by omega) (by omega) (by omega) hWb)
    hE1 hE0 hMn.ini hE2 hFr hAt
  · rw [hg'', hBk.1, ← hRg.1]
    exact back_q Z
  · rw [hg'', hBk.2.2.1]
    show Z'.cpu.gpr.rbp = _
    rw [hrbp, lif_rbp (by omega), hRg.2.1]
    rfl

end FV7z.Start
