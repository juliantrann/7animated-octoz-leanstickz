import FV7z.Start.Reach
import FV7z.Strncmp.Plt
import FV7z.Strrchr.Plt
import FV7z.Memcpy.PltC
import FV7z.Memset.Plt
/-!
# The launch reaches `main`, with the PLT's functions proved (PLAN.md §M, G3)

`launch_main` takes the contracts of the six functions the startup calls through the PLT (`memcpy`, `strlen`,
`strncmp`, `mempcpy`, `memset`, `strrchr`). On a processor without SSSE3 and SSE3 together and without AVX and AVX2
together, `apply_irel` puts their SSE2 versions in the GOT, and each stub's jump to it meets its contract
(`cpyAt_plt`, `lenAt_plt`, `ncmpAt_plt`, `pcpyAt_plt`, `setAt_plt`, `rchrAt_plt`): only their code is left to ask.

- `PltCode L`: the six stubs (the bytes `pltLen`) and the SSE2 functions they jump to.
- `launch_main_plt`: `launch_main` without the six contracts.
-/
namespace FV7z.Start
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Glibc FV7z.AuxInit
open FV7z.StartB (PimCode)

/-- The PLT's stubs of `memcpy`, `strlen`, `strncmp`, `mempcpy`, `memset`, `strrchr`, and the code of
`__memmove_sse2_unaligned`, `__strlen_sse2`, `__strncmp_sse2`, `__memset_sse2_unaligned`, `__strrchr_sse2`. -/
structure PltCode (L : List (Addr × List Byte)) : Prop where
  cpyP : CodeIn L 4198512#64 Strlen.pltLen
  lenP : CodeIn L 4198664#64 Strlen.pltLen
  cmpP : CodeIn L 4198472#64 Strlen.pltLen
  pcpyP : CodeIn L 4198592#64 Strlen.pltLen
  setP : CodeIn L 4198528#64 Strlen.pltLen
  rchrP : CodeIn L 4198480#64 Strlen.pltLen
  cpy : CodeIn L 0x65b8d0#64 Memcpy.mc2
  len : CodeIn L 0x6546d0#64 Strlen.sl2
  cmp : CodeIn L (0x63a420 : Addr) Strncmp.scm
  set : CodeIn L 0x65c650#64 Memset.ms2
  rchr : CodeIn L 0x654200#64 Strrchr.sr2

/-- From the launch of `7zzs` on such a processor, the run gets to `main`, staying in `L` with no outcome on the
way. -/
theorem launch_main_plt {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
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
    (hun : ∀ t, KernelNew (o t .uname).val)
    -- `__libc_init_first`'s code, and the PLT's stubs and the functions they jump to on such a processor
    (hLC : LifCode L) (hMC : MalCode L) (hPl : PltCode L)
    (hs3 : ¬ (l.prof.feat.ssse3 = true ∧ l.prof.feat.sse3 = true))
    (hav : ¬ (l.prof.feat.avx = true ∧ l.prof.feat.avx2 = true))
    -- `__cxa_atexit`'s code, and that of the tail of `__libc_start_main` up to `main`
    (hX : CxaCode L) (hMn : MainCode L)
    -- the constructors' code; `umask` (95) adds no event the goal minds; the CPUs' cache leaves end
    (hCC : Ctor.CtorCode L) (hCe : Glibc.CacheEnds l.prof) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      (ctxOf l.prof l.s₀ l.args c).Ok ∧ Img (ctxOf l.prof l.s₀ l.args c).V0 ∧ Bss (ctxOf l.prof l.s₀ l.args c).V0 ∧
      GoG l.prof L o gev (fun X _ _ => X.cpu.rip = 0x41cd90#64) (fun _ _ => False)
        l.s₀ t := launch_main h hroom hn hs hq hlu noG noA noLD hok hpc hch ho hvd hL hC hT hO hP hM hmg hpse
    (Memcpy.cpyAt_plt hs3 hav hPl.cpyP hPl.cpy) hun hLC hMC (Strlen.lenAt_plt hav hPl.lenP hPl.len)
    (Strncmp.ncmpAt_plt hs3 hch hav hPl.cmpP hPl.cmp) (Memcpy.pcpyAt_plt hs3 hav hPl.pcpyP hPl.cpy)
    (Memset.setAt_plt hav hPl.setP hPl.set) (Strrchr.rchrAt_plt hav hPl.rchrP hPl.rchr) hX hMn hCC hCe

end FV7z.Start
