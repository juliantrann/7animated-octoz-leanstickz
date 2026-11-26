import FV7z.Start.ToMain
/-!
# The launch reaches `main` (PLAN.md §M, the theorem against vacuity)

`launch_to_main` with the goal "at `main`" (`0x41cd90`), or at the branch where `readlink` of `/proc/self/exe`
fails (`gor_at + 271`, not proved on yet), and no outcome: every run from the launch stays in the code `L` and gets
to one of the two, with no fault, exit or signal on the way. The obligations of `launch_to_main` hold at once
(`runsFrom_done`); `umask` (95) adds an event no goal here looks at.

- `launch_reaches`: that run.
- `launch_main`: where the oracle's `readlink` of `/proc/self/exe` gives a path of fewer than `PATH_MAX` bytes (procfs
  mounted, as `ProcSelfExe` allows), the failing branch does not happen (`ke` knows the answer is the oracle's): the
  run gets to `main`.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.Smm (size smEv smEv2)
open FV7z.Mhi (C2)
open FV7z.Gor (gEv gor_at)
open FV7z.StartB (PimCode)
open FV7z.Tls (TlsMem)

/-- From the launch of `7zzs`, the run gets to `main` or to the failed `readlink` of `/proc/self/exe`, staying in `L`
with no outcome on the way. -/
theorem launch_reaches {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
    {t : Nat}
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
    (hcmp : Str.NcmpAt l.prof L o 4198472#64 (GotTab l.prof))
    (hpcy : Gor.PcpyAt l.prof L o 4198592#64 (GotOkB l.prof))
    (hset : Ipa.SetAt l.prof L o 4198528#64 (GotOkB l.prof))
    (hrchr : Str.RchrAt l.prof L o 4198480#64 (GotOkB l.prof))
    -- `__cxa_atexit`'s code, and that of the tail of `__libc_start_main` up to `main`
    (hX : CxaCode L) (hMn : MainCode L)
    -- the constructors' code; `umask` (95) adds no event the goal minds; the CPUs' cache leaves end
    (hCC : Ctor.CtorCode L) (hCe : Glibc.CacheEnds l.prof) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
      GoG l.prof L o gev (fun X _ _ => X.cpu.rip = 0x41cd90#64 ∨ X.cpu.rip = gor_at.add 271) (fun _ _ => False)
        l.s₀ t := by
  obtain ⟨c, hv, hst, hK, hI, hB, hto⟩ :=
    launch_to_main (gP := fun X _ _ => X.cpu.rip = 0x41cd90#64 ∨ X.cpu.rip = gor_at.add 271)
      (gE := fun _ _ => False) (gev := gev) (t := t) h hroom hn hs hq hlu noG noA noLD hpc hch ho hvd hL hC hT hO
      hP hM hmg hpse hcpy hun hLC hMC hlen hcmp hpcy hset hrchr hX hMn hCC
      (fun _ _ => ⟨fun _ _ _ _ h => h, fun _ _ _ h => h⟩) hCe
  refine ⟨c, hv, hst, hK, hI, hB, hto ?_⟩
  intro s₂ Z W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3
  intros
  refine ⟨?_, ?_⟩
  · intro r _ Z' t' _ _ hrip
    intros
    exact runsFrom_done (.inr hrip)
  · intros
    intro Vm V₁ Z₃ t₃ _ _ _ _ _ hrip
    intros
    exact runsFrom_done (.inl hrip)


/-- From the launch of `7zzs`, where `readlink` of `/proc/self/exe` gives the executable's path, of fewer than
`PATH_MAX` bytes: the run gets to `main`, staying in `L` with no outcome on the way. -/
theorem launch_main {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
    {t : Nat}
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
    (hok : ∀ t, ∃ x : ExePath, x.bytes.length < pathMax ∧ o t (.readlink none Gor.pse) = .procExe x)
    (hpc : l.prof.Consistent) (hch : Chain l.prof) (ho : Undisturbed o) (hvd : l.prof.linux.vdso = false)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (hC : StartCode L) (hT : TlsCode L) (hO : OsvCode L)
    (hP : PimCode L) (hM : l.prof.linux.Modest) (hmg : ∀ t p, o t (.memFail p) = none) (hpse : ProcSelfExe o)
    (hcpy : Tls.CpyAt l.prof L o 4198512#64 (GotOkB l.prof)) (hun : ∀ t, KernelNew (o t .uname).val)
    -- `__libc_init_first`'s code and the contracts of the functions it calls through the PLT
    (hLC : LifCode L) (hMC : MalCode L)
    (hlen : Str.LenAt l.prof L o 4198664#64 (GotOkB l.prof))
    (hcmp : Str.NcmpAt l.prof L o 4198472#64 (GotTab l.prof))
    (hpcy : Gor.PcpyAt l.prof L o 4198592#64 (GotOkB l.prof))
    (hset : Ipa.SetAt l.prof L o 4198528#64 (GotOkB l.prof))
    (hrchr : Str.RchrAt l.prof L o 4198480#64 (GotOkB l.prof))
    -- `__cxa_atexit`'s code, and that of the tail of `__libc_start_main` up to `main`
    (hX : CxaCode L) (hMn : MainCode L)
    -- the constructors' code; `umask` (95) adds no event the goal minds; the CPUs' cache leaves end
    (hCC : Ctor.CtorCode L) (hCe : Glibc.CacheEnds l.prof) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
      GoG l.prof L o gev (fun X _ _ => X.cpu.rip = 0x41cd90#64) (fun _ _ => False)
        l.s₀ t := by
  obtain ⟨c, hv, hst, hK, hI, hB, hto⟩ :=
    launch_to_main (gP := fun X _ _ => X.cpu.rip = 0x41cd90#64)
      (gE := fun _ _ => False) (gev := gev) (t := t) h hroom hn hs hq hlu noG noA noLD hpc hch ho hvd hL hC hT hO
      hP hM hmg hpse hcpy hun hLC hMC hlen hcmp hpcy hset hrchr hX hMn hCC
      (fun _ _ => ⟨fun _ _ _ _ h => h, fun _ _ _ h => h⟩) hCe
  refine ⟨c, hv, hst, hK, hI, hB, hto ?_⟩
  intro s₂ Z W V' g x1 x2 x3 d r10 r8 r9 u y1 y2 y3 y4 y5 q1 q2 q3
  intros
  refine ⟨?_, ?_⟩
  · intro r ⟨t₀, hr, hf⟩
    obtain ⟨x, hx, hox⟩ := hok t₀
    rw [hox] at hr
    exact absurd (hf x hr.symm) (Nat.not_le.2 hx)
  · intros
    intro Vm V₁ Z₃ t₃ _ _ _ _ _ hrip
    intros
    exact runsFrom_done hrip

end FV7z.Start
