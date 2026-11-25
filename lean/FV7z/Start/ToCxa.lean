import FV7z.Start.ToLifL
import FV7z.Start.CxaRet
/-!
# From the launch of `7zzs` to the return of `__cxa_atexit (fini, …)` (PLAN.md G3, startup)

`launch_to_lif` ends at the return of `__libc_init_first` to `0x613439`; `ret_cxa` runs from there to the return of
`__cxa_atexit (fini, NULL, NULL)` at `0x61344a`. Here the two are joined: `ret_cxa`'s conditions come from where the
layout puts the stack (above the break's two pages), `lifG`'s footprint, `PtrW`'s bytes and `ctxOf`'s `fini`
(`0x613d40`, not null).

- `CxaCode L`: `__cxa_atexit`'s code and that of `__new_exitfn` are in `L`.
- `cxa_nums`, `brk_2176`, `var_at`: the offsets and footprint facts, apart from the large context.
- `launch_to_cxa`: as `launch_to_lif`, with `__libc_init_first`'s return continued to `__cxa_atexit`'s.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Smm (size smEv smEv2)
open FV7z.Mhi (C2)
open FV7z.Gor (gEv gor_at)
open FV7z.StartB (PimCode)
open FV7z.Tls (TlsMem)

/-- `__cxa_atexit`'s code and that of `__new_exitfn`, which it calls. -/
structure CxaCode (L : List (Addr × List Byte)) : Prop where
  cxa : CodeIn L Cxa.cxa_at Cxa.cxa
  nef : CodeIn L Nef.nef_at Nef.nef

/-- The stack offsets of `ret_cxa` from `lif_ok`'s stack pointer. -/
theorem cxa_nums {Z : State} {R : Nat} (h : (lifSp Z).toNat = R - 448) (hR : 4096 ≤ R) (hR' : R ≤ 2 ^ 47) :
    (lifSp Z + 152#64 - 56#64).toNat = R - 352 ∧ (lifSp Z + 128#64).toNat = R - 320 := by
  constructor <;> bv_omega

/-- The TCB's address from the break. -/
theorem brk_2176 {B : Addr} (h : B.toNat + 8192 ≤ 2 ^ 63) : (B + 2176#64).toNat = B.toNat + 2176 := by
  bv_omega

/-- `n` bytes from `x.toNat = c` in `[0x792000, 0x7a9000)`. -/
theorem var_at {x : Addr} {c n : Nat} {P : Addr → Prop} (hxt : x.toNat = c) (hc : 0x792000 ≤ c)
    (hn : c + n ≤ 0x7a9000) (hP : ∀ y : Addr, 0x792000 ≤ y.toNat → y.toNat < 0x7a9000 → P y) :
    ∀ i < n, P (x.add i) := fun i hi => by
  have t : (x.add i).toNat = c + i := by rw [toNat_add_of_fits hi (by omega), hxt]
  exact hP _ (by omega) (by omega)

set_option maxHeartbeats 4000000 in
/-- From the launch of `7zzs` to the return of `__cxa_atexit (fini, NULL, NULL)` to `0x61344a` (and to the branch
where `readlink` of `/proc/self/exe` fails). -/
theorem launch_to_cxa {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
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
    -- `__cxa_atexit`'s code
    (hX : CxaCode L) :
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
          -- `__cxa_atexit (fini, NULL, NULL)` returns
          ∀ (V'' : Addr → Byte) (g' : Gprs) (Z'' : State) (t' : Nat),
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
          GoG l.prof L o (gev ++ ptrEvs l c s₂ g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 ++
            [gEv { lifY W Z with rsp := lifSp Z - 8#64 } (.procExe x)] ++ evs ++ [Ndi.ndiEv]) gP gE Z'' t')) →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hK, hI0, hB0, hto⟩ := launch_to_lif (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom hn hs
    hq hlu noG noA noLD hpc hch ho hvd hL hC hT hO hP hM hmg hpse hcpy hun hLC hMC hlen hcmp hpcy hset hrchr
  refine ⟨c, hv, hst, hK, hI0, hB0, fun hfin => hto ?_⟩
  intro s₂ Z W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hK₂ hA₂ hr₂ hRg hdx hsi hdi'
    hcpu hgot hhw hpl hMB hu hnew hW hT3
  obtain ⟨hke, hk⟩ := hfin s₂ Z W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hK₂ hA₂ hr₂
    hRg hdx hsi hdi' hcpu hgot hhw hpl hMB hu hnew hW hT3
  refine ⟨hke, ?_⟩
  intro x evs s₃ Z₁ Z' t' s W₂ hevs c₃ hB₃ hN hz1 hzp h12' h13' hK₃ hA₃ hHp hsh hrip hrsp hrbx hrbp hr12 hr13 hr14 hr15
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
  have hFd : ∀ y : Addr, 0x792000 ≤ y.toNat → y.toNat < 0x7a9000 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).data y := fun _ h1 h2 => gd_var h1 h2
  have hFw : ∀ y : Addr, 0x792000 ≤ y.toNat → y.toNat < 0x7a9000 →
      Foot (lifG (loOf l n c) c.stackTop (brkOf l) L).writes y := fun _ h1 h2 => gw_var h1 h2
  have hfi : (ctxOf l.prof l.s₀ l.args c).fini = 0x613d40#64 := rfl
  have tl : (8010388#64 : Addr).toNat = 8010388 := rfl
  have tp : (7938992#64 : Addr).toNat = 7938992 := rfl
  have ti : (8010400#64 : Addr).toNat = 8010400 := rfl
  have tk : (8029184#64 : Addr).toNat = 8029184 := rfl
  have hR : RetAt W W₂ Z (brkOf l) Z₁.cpu.gpr :=
    ⟨hN, hb1', hb', by omega, by omega, by omega, by omega, by rw [hz1, n4]; omega⟩
  exact ret_cxa (t := t') c₃ hB₃.fsb hC.lsm hX.cxa hX.nef hK₃ hA₃ hrip hrsp hr12
    (by rw [hRg.2.2.1, hfi]; decide) hR hK hI0 hB0 hMB hW (by omega)
    (fun i hi => gw_stack htop (by rw [toNat_add_of_fits hi (by omega), n3]; omega)
      (by rw [toNat_add_of_fits hi (by omega), n3]; omega))
    (fun i hi => gd_brk (by rw [toNat_add_of_fits hi (by omega), hf]; omega)
      (by rw [toNat_add_of_fits hi (by omega), hf]; omega))
    (var_at tl (by omega) (by omega) hFd)
    (var_at tp (by omega) (by omega) hFd)
    (var_at ti (by omega) (by omega) hFw)
    (var_at tk (by omega) (by omega) hFw)
    (fun V'' g' Z'' t'' a1 a2 a3 a4 a5 a6 a7 => hk x evs s₃ Z₁ Z' s W₂ hevs c₃ hB₃ hN hz1 hzp h12' h13' hK₃ hA₃ hHp hsh
      hrip hrsp hrbx hrbp hr12 hr13 hr14 hr15 V'' g' Z'' t'' a1 a2 a3 a4 a5 a6 a7)

end FV7z.Start
