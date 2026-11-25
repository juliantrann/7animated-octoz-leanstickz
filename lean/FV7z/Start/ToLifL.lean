import FV7z.Start.LifL
/-!
# From the launch of `7zzs` to the return of `__libc_init_first` (PLAN.md G3, startup)

`launch_to_ptr` takes the run from the first instruction to `0x613434`, the call of `__libc_init_first`, and
`ptr_lif` from there to `lif_ok`'s continuations. Here the two are joined: what `ptr_lif` asks of the launch comes
from `StackAt` (where the layout puts the stack words, the strings and the platform string), `ctxOf`'s values of
`_dl_aux_init`'s variables, the break of `Launch.Of` and the bytes `ptrW_all` gives.

The library functions `__libc_init_first` calls through the PLT (`strlen`, `strncmp`, `mempcpy`, `memset`,
`strrchr`) are taken by their contracts for bytes with the GOT `irel` resolved (`GotOkB`), as `memcpy`'s in
`launch_to_ptr`: the GOT is as at `0x613434` until `strrchr`'s call.

Two conditions on the launch are new: no environment string begins with `LD_` (`_dl_non_dynamic_init` then reads
none of them), and the profile has no vDSO (`AT_SYSINFO_EHDR` is not passed, so `_dl_sysinfo_dso` stays 0).

- `launch_to_lif`: the run from the first instruction goes on as `lif_ok`'s continuations do, for every run of
  `launch_to_ptr` to `0x613434`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Smm (size smEv smEv2)
open FV7z.Mhi (C2)
open FV7z.Gor (gEv gor_at)
open FV7z.StartB (PimCode)
open FV7z.Tls (TlsMem)

set_option maxHeartbeats 4000000 in
/-- From the launch of `7zzs` to the return of `__libc_init_first` to `0x613439` (and to the branch where `readlink`
of `/proc/self/exe` fails). -/
theorem launch_to_lif {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
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
    (hrchr : Str.RchrAt l.prof L o 4198480#64 (GotOkB l.prof)) :
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
        (∀ r, (∃ t₀, o t₀ (.readlink none Gor.pse) = r ∧ ∀ x, r = .procExe x → pathMax ≤ x.bytes.length) →
          ∀ Z' t', KeptW ([⟨brkOf l, 8192⟩] ++ (zzsFoot (loOf l n c) c.stackTop L).writes) s₂ Z' →
          Agree (withNew (zzsFoot (loOf l n c) c.stackTop L) [⟨brkOf l, 8192⟩]) Z'.proc.mm.mem
            (Gor.frV (Ndi.nV (lifW W Z) (lifSp Z) (lifY W Z)) { lifY W Z with rsp := lifSp Z - 8#64 }) →
          Z'.cpu.rip = gor_at.add 271 → Z'.cpu.gpr.rax = 18446744073709551615#64 →
          Z'.cpu.gpr.rsp = lifSp Z - 8#64 → Z'.cpu.gpr.rbx = (lifY W Z).rbx → Z'.cpu.gpr.rbp = (lifY W Z).rbp →
          Z'.cpu.gpr.r12 = (lifY W Z).r12 → Z'.cpu.gpr.r13 = (lifY W Z).r13 → Z'.cpu.gpr.r14 = (lifY W Z).r14 →
          Z'.cpu.gpr.r15 = (lifY W Z).r15 →
          GoG l.prof L o (gev ++ ptrEvs l c s₂ g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 ++
            [gEv { lifY W Z with rsp := lifSp Z - 8#64 } r]) gP gE Z' t') ∧
        -- `__libc_init_first` returns
        (∀ (x : ExePath) (evs : List Event) (s₃ Z₁ Z' : State) (t' : Nat) (s : Addr) (W₂ : Addr → Byte),
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
          GoG l.prof L o (gev ++ ptrEvs l c s₂ g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 ++
            [gEv { lifY W Z with rsp := lifSp Z - 8#64 } (.procExe x)] ++ evs ++ [Ndi.ndiEv]) gP gE Z' t')) →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hK, hI0, hB0, hto⟩ := launch_to_ptr (gev := gev) (gP := gP) (gE := gE) (t := t) h hroom
    (by omega) hs hq hlu noG noA hpc hch ho hL hC hT hO hP hM hmg hcpy hun
  refine ⟨c, hv, hst, hK, hI0, hB0, fun hfin => hto ?_⟩
  intro s₂ Z t₂ W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hK₂ hA₂ hr₂ hRg hdx hsi hdi'
    hcpu hgot hhw hpl hMB hu hnew hW hT3
  -- the bytes: `PtrMem …`'s at every address apart from the start code's stores
  obtain ⟨W', hA', hW'⟩ := ptrW_all (K := ctxOf l.prof l.s₀ l.args c) (V := V')
    (b := l.s₀.proc.mm.brk) (ver := osVersion u) (D := fun a => Foot (zzsFoot (loOf l n c) c.stackTop L).data a) hA₂ hW
    (fun _ ha => wn_data ha)
  obtain ⟨hke, hk⟩ := hfin s₂ Z W' V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3 hax hdi c₂ hB₂ hK₂ hA' hr₂
    hRg hdx hsi hdi' hcpu hgot hhw hpl hMB hu hnew hW' hT3
  -- where the layout puts things
  obtain ⟨h16, hn', -, -, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  have hTM : c.stackTop ≤ 2 ^ 47 - 4096 := hv.stackTop.2.2
  have ht4 : c.stackTop % 4096 = 0 := hv.stackTop.1
  have hrsp : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [hst.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf l.prof l.s₀ l.args c).bp.toNat = (stackLayout l.args l.prof.linux c).sp - 400 := by
    show (l.s₀.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  have hz : Z.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp - 288 := by
    rw [hRg.1]
    bv_omega
  have hav : (ctxOf l.prof l.s₀ l.args c).argv.toNat = (stackLayout l.args l.prof.linux c).sp + 8 := by
    show (l.s₀.cpu.gpr.rsp + 8#64).toNat = _
    bv_omega
  obtain ⟨hb0, hb1, hb2⟩ := launch_brk h
  obtain ⟨h12, h23, h3⟩ := runs_apart (prof := l.prof) (hdr := ElfHeader.read V2606.zzs.blob.bytes)
    (phs := zzsPhdrs) hst.top.1 hst.align hst.limits
  have hl23 : (toBytesLE c.random 16 ++ platformString).length = 23 := by
    simp [toBytesLE_length, platformString]
  rw [hl23] at h23
  obtain ⟨-, -, a1, a2⟩ := StackAt.argv0 hst (by omega) l.s₀.cpu.gpr.rax
  have hev : (ctxOf l.prof l.s₀ l.args c).envp.toNat =
      (stackLayout l.args l.prof.linux c).sp + 8 * (1 + l.args.argv'.length + 1) := by
    show (BitVec.ofNat 64 _).toNat = _
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have eN : (ctxOf l.prof l.s₀ l.args c).N = l.args.envp.length := rfl
  have het : (ctxOf l.prof l.s₀ l.args c).envp.toNat + 8 * ((ctxOf l.prof l.s₀ l.args c).N + 1) ≤ c.stackTop := by
    rw [hev, eN]
    omega
  have hptr : ∀ i < (ctxOf l.prof l.s₀ l.args c).N,
      (stackLayout l.args l.prof.linux c).sp ≤ ((ctxOf l.prof l.s₀ l.args c).ptr i).toNat ∧
        ((ctxOf l.prof l.s₀ l.args c).ptr i).toNat + (ctxOf l.prof l.s₀ l.args c).len i + 2 ≤ c.stackTop :=
    fun i hi => by
      rw [eN] at hi
      obtain ⟨e1, e2⟩ := env_in l.args (stackLayout l.args l.prof.linux c).strings hi
      have ep : ((ctxOf l.prof l.s₀ l.args c).ptr i).toNat =
          (stringAddrs (stackLayout l.args l.prof.linux c).strings (l.args.argv' ++ l.args.envp)).getD
            (l.args.argv'.length + i) 0 := by
        show (BitVec.ofNat 64 _).toNat = _
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt (by omega)
      have el : (ctxOf l.prof l.s₀ l.args c).len i = (l.args.envp.getD i []).length := rfl
      rw [ep, el]
      omega
  have es : (BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings).toNat =
      (stackLayout l.args l.prof.linux c).strings := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hlim : l.s₀.proc.mm.brk.toNat + 0x23000 ≤ 4096 * (pageUp (l.s₀.proc.mm.brk.toNat + 2 ^ 41) / 4096) := by
    unfold pageUp
    omega
  -- the stack words of `lif_ok`
  obtain ⟨n1, n2, -⟩ := lif_nums (Z := Z) hz (by omega) (by omega) h16
  have hb' : l.s₀.proc.mm.brk.toNat + 8192 ≤ 2 ^ 63 := by omega
  -- `argv[0]`
  obtain ⟨ha0, hnz, nfit, nnz, nz⟩ := ent_argv (g := entG Z) (ra := Lif.lif_at.add 70) (ra₀ := lsm_at.add 1017)
    hst h.2.2 hMB hb1 hb' hW' (by omega) (by omega) (by omega) (by omega) (fun _ _ _ => trivial)
  -- the GOT: as in the memory at `0x613434`
  have hG0 := GotOkB.of_mem hgot
  have hgw : ∀ a : Addr, 7937720 ≤ a.toNat → a.toNat < 7940480 → lifW W' Z a = Z.proc.mm.mem.readByte a :=
    fun a e1 e2 => (lifW_lo (W := W') (g := entG Z) (ra := Lif.lif_at.add 70) (ra₀ := lsm_at.add 1017) (by omega)
      (by omega) (by omega)).trans (hA' a (lf_var (by omega) (by omega))).symm
  have hgm : ∀ a : Addr, 7937720 ≤ a.toNat → a.toNat < 7940480 → lifM W' Z a = Z.proc.mm.mem.readByte a :=
    fun a e1 e2 => (lifM_lo (by omega) (by omega)).trans (hgw a e1 e2)
  have hPm : ∀ W₁ : Addr → Byte, (∀ x : Addr, 7938048 ≤ x.toNat → x.toNat < 7940480 → W₁ x = lifM W' Z x) →
      GotOkB l.prof W₁ := fun W₁ h₁ =>
    GotOkB.congr hG0 fun a e1 e2 => (h₁ a (by omega) (by omega)).trans (hgm a (by omega) (by omega))
  have hPq : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → (a.toNat < 7937664 ∨ 7937720 ≤ a.toNat) →
      ¬ Ndi.Hv a → W₁ a = lifM W' Z a) → GotOkB l.prof W₁ := fun W₁ h₁ =>
    GotOkB.congr hG0 fun a e1 e2 => (h₁ a (by omega) (.inr (by omega)) (by unfold Ndi.Hv; omega)).trans
      (hgm a (by omega) (by omega))
  have hPk : ∀ W₁ : Addr → Byte, (∀ a : Addr, a.toNat < 7940480 → ¬ Ndi.Hv a → W₁ a = lifM W' Z a) →
      GotOkB l.prof W₁ := fun W₁ h₁ =>
    GotOkB.congr hG0 fun a e1 e2 => (h₁ a (by omega) (by unfold Ndi.Hv; omega)).trans
      (hgm a (by omega) (by omega))
  have hPr : ∀ W₁ : Addr → Byte, (∀ a : Addr, (a.toNat < 7937208 ∨ 7937720 ≤ a.toNat ∧ a.toNat < 7940480) →
      W₁ a = lifW W' Z a) → GotOkB l.prof W₁ := fun W₁ h₁ =>
    GotOkB.congr hG0 fun a e1 e2 => (h₁ a (.inr ⟨by omega, by omega⟩)).trans (hgw a (by omega) (by omega))
  exact ptr_lif (prof := l.prof) (L := L) (o := o)
    (gev := gev ++ ptrEvs l c s₂ g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3) (s₂ := s₂) (Z := Z) (t := t₂)
    (lim := pageUp (l.s₀.proc.mm.brk.toNat + 2 ^ 41) / 4096) (ks := ⟨l.s₀.thread.tid⟩)
    (K := ctxOf l.prof l.s₀ l.args c) (W := W') (V := V') (B := l.s₀.proc.mm.brk) (ver := osVersion u)
    (lo := (stackLayout l.args l.prof.linux c).sp - n) (top := c.stackTop)
    (R := (stackLayout l.args l.prof.linux c).sp)
    (P := (stackLayout l.args l.prof.linux c).platform - platformString.length)
    (a0 := BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).strings) (n := (arg0 l.args).length)
    (Pm := GotOkB l.prof) (Pq := GotOkB l.prof) (Pk := GotOkB l.prof) (Ps := GotOkB l.prof) (Pr := GotOkB l.prof)
    (hLC := hLC) (hMC := hMC) (hlsm := hC.lsm) (hlen := hlen) (hcmp := hcmp) (hcpy := hpcy) (hcpq := hpcy)
    (hlenA := hlen) (hset := hset) (hrchr := hrchr) (hPm := hPm) (hPq := hPq) (hPk := hPk) (hPs := hPq)
    (hPr := hPr) (hmg := hmg) (hpse := hpse) (hc := c₂) (hBs := hB₂) (hKZ := hK₂) (hAZ := hA') (hrip := hr₂)
    (hRg := hRg) (hdx := hdx) (hsi := hsi) (hHw := hhw) (hPl := hpl) (hW := hW') (hK := hK) (hI := hI0)
    (hB := hB0) (hM := hMB) (hps := ctxOf_ps _ _ _ _) (hph := (ctxOf_ph _ _ _ _).1) (hpn := (ctxOf_ph _ _ _ _).2)
    (hsd := ctxOf_sdso _ _ _ _ hvd) (hfp := ctxOf_fpu _ _ _ _) (hKp := ctxOf_platform _ _ _ _)
    (hV0 := fun k hk => StackAt.v1_pstr hst (by omega) l.s₀.cpu.gpr.rax hk) (noLD := noLD)
    (hz := hz) (h16 := h16) (hlo := by omega) (hlR := by omega) (hRt := hlt) (htop := hTM) (ht4 := ht4)
    (hbl := hb1) (hal := hb0) (hBl := by omega) (hlim := hlim)
    (hL := fun p hp => by
      obtain ⟨a, e, -, e2, -⟩ := hL p hp
      rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact e2)
    (hPR := by omega) (hPt := by omega) (hle := by rw [hev]; omega) (het := het)
    (hls := fun i hi => (hptr i hi).1) (hlt := fun i hi => (hptr i hi).2) (hav := hav)
    (ha0 := ha0) (hnz := hnz) (nfit := nfit) (nnz := nnz) (nz := nz) (ha1 := by rw [es]; omega)
    (ha2 := by rw [es]; omega) (ke := hke) (k := hk)

end FV7z.Start
