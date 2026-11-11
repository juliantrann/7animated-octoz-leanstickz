import FV7z.Start.SegOf
import FV7z.Entry.Holds
/-!
# From the launch of `7zzs` to `0x6133bb` in `__libc_start_main` (PLAN.md G3, startup)

`Entry.entry_cpu` is about a run with a footprint, a context and a state that are as it asks. Here they are the
launch's: the state `execve` starts `7zzs` in (Zellic's `Launch.Of`), `zzsFoot` from `n` bytes below the first `rsp`
(`Start/SegOf.lean`) and `ctxOf` (`Start/LchOf.lean`).

- `StartCode L`: the code the startup runs up to `0x6133bb` is in the code segments `L`.
- `tun_bd`, `tun_z`: where the tunables `init_cpu_features` reads lie, and that the file has them not set.
- `launch_to_cpu`: for a launch with room for `n ≥ 656` bytes of stack that is not a secure one, an environment with
  no string beginning with `GLIBC_TUNABLES=` or a tunable's alias and `=`, a consistent processor with the
  extensions in order (`Chain`), an undisturbed run and code segments `L` that are the file's bytes in the text
  segment's pages and have the startup's code: the run from the first instruction goes on as the run from `0x6133bb`
  does, there with the processor's features recorded as it reports them (`CpuOk`), every slot of the GOT holding a
  variant the processor has (`GotOk`), and one system call made (`arch_prctl (ARCH_CET_STATUS, …)`).
-/
namespace FV7z.Start
open ZellicX86 FV7z.Fn FV7z.Glibc
open FV7z.CpuFeat (cpuW icfW irelW IE JT RE TKi rela tgvInit tgvEnt TunOk)
open FV7z.Tun (gz)

/-- The code the startup runs up to `0x6133bb` is in the code segments `L`. -/
structure StartCode (L : List (Addr × List Byte)) : Prop where
  ent : CodeIn L Entry.ent_at Entry.ent
  lsm : CodeIn L lsm_at lsm
  pie : CodeIn L Pie.pie_at Pie.pie
  aux : CodeIn L Auxv.aux_at Auxv.aux
  sec : CodeIn L Sec.sec_at Sec.sec
  tin : CodeIn L Tun.tin_at Tun.tin
  icf : CodeIn L 0x613113 CpuFeat.icf
  icfk : CodeIn L 0x613592 CpuFeat.icfk
  tgv : CodeIn L 0x66f3a0 CpuFeat.tgv
  gci : CodeIn L 0x612cc0 CpuFeat.gci
  icfa : CodeIn L 0x6132ad CpuFeat.icfa
  icfh : CodeIn L 0x613803 CpuFeat.icfh
  icfi : CodeIn L 0x613676 CpuFeat.icfi
  irl : CodeIn L 0x613278 CpuFeat.irl
  next : ∃ cx, CodeIn L 0x6133bb cx ∧ 0 < cx.length
  res : ∀ r ∈ V2606.resolvers, ∀ rc, Exe.bytesAt V2606.zzs.blob r.1 r.2.1 = some rc →
    CodeIn L (BitVec.ofNat 64 r.1) rc

/-- Where the type and the value of the tunables `init_cpu_features` reads lie. -/
theorem tun_bd : ∀ n ∈ [16, 9, 20, 3, 15, 10],
    (∀ i < 4, 0x791660 ≤ (Addr.add (tgvEnt (BitVec.ofNat 64 n) + BitVec.ofNat 64 8) i).toNat ∧
      (Addr.add (tgvEnt (BitVec.ofNat 64 n) + BitVec.ofNat 64 8) i).toNat < 0x791c10) ∧
    ∀ i < 8, 0x791660 ≤ (Addr.add (tgvEnt (BitVec.ofNat 64 n) + BitVec.ofNat 64 32) i).toNat ∧
      (Addr.add (tgvEnt (BitVec.ofNat 64 n) + BitVec.ofNat 64 32) i).toNat < 0x791c10 := by decide

/-- The file has the tunables `init_cpu_features` reads not set. -/
theorem tun_z : ∀ n ∈ [16, 9, 20, 3, 15, 10],
    tgvInit (BitVec.ofNat 64 n) = BitVec.ofNat 64 (0x791660 + (56 * n + 40)) ∧ 56 * n + 40 < 1456 ∧
      tl.getD (56 * n + 40) 0 = 0 := by decide +kernel

/-- From the launch of `7zzs` to `0x6133bb` in `__libc_start_main`. -/
theorem launch_to_cpu {l : Launch} {n : Nat} {o : Oracle} {L : List (Addr × List Byte)} {gev : List Event}
    {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {t : Nat}
    (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (hroom : StackRoom l.args n) (hn : 656 ≤ n)
    (hs : l.args.secure = false)
    (noG : ∀ i < l.args.envp.length, (∀ k < 14, (l.args.envp.getD i [] ++ [0]).getD k 0 = gz k) →
      (l.args.envp.getD i [] ++ [0]).getD 14 0 ≠ 61)
    (noA : ∀ i < l.args.envp.length, ∀ t < 26, aqI t ≠ 0 →
      (∀ k < alenI t, (l.args.envp.getD i [] ++ [0]).getD k 0 = azI t k) →
      (l.args.envp.getD i [] ++ [0]).getD (alenI t) 0 ≠ 61)
    (hpc : l.prof.Consistent) (hch : Chain l.prof) (ho : Undisturbed o)
    (hL : ∀ p ∈ L, ∃ a, p.1 = BitVec.ofNat 64 a ∧ 0x401000 ≤ a ∧ a + p.2.length ≤ 0x6d8000 ∧
      Exe.bytesAt V2606.zzs.blob a p.2.length = some p.2) (hC : StartCode L) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      StackAt l.prof l.s₀ l.args (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs c ∧
      ((∀ (g g' : Gprs) (V' : Addr → Byte), FinP (ctxOf l.prof l.s₀ l.args c) g' V' →
        ∀ (Y : State) (t' : Nat),
        g.rax = BitVec.ofNat 64 158 → g.rdi = BitVec.ofNat 64 0x3001 →
        KeptW (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).writes l.s₀ Y →
        CpuOk l.prof Y.proc.mm.mem → V2606.GotOk l.prof Y.proc.mm.mem →
        (∀ y, Foot (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).data y →
          ¬ Foot (cpuW ((ctxOf l.prof l.s₀ l.args c).bp + 104#64)) y → Y.proc.mm.mem.readByte y = V' y) →
        Y.cpu.rip = 0x6133bb → TKi g' Y.cpu.gpr → GoG l.prof L o (gev ++ [Seg.cetEv g]) gP gE Y t') →
      GoG l.prof L o gev gP gE l.s₀ t) := by
  obtain ⟨c, hv, hst, hLch⟩ := launch_lch h hroom hs noG noA
  obtain ⟨h16, hn', hst', hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  have hT0 := hv.stackTop.1
  refine ⟨c, hv, hst, fun hfin => ?_⟩
  obtain ⟨c', -, hrip, -, -, -, -, -, hdf⟩ := launch_regs h
  obtain ⟨c'', -, hcpu⟩ := launch_cpu h
  have hx87 : l.s₀.cpu.x87.full = 0 := by rw [hcpu]; rfl
  have hrsp : l.s₀.cpu.gpr.rsp.toNat = (stackLayout l.args l.prof.linux c).sp := by
    rw [hst.rsp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hbp : (ctxOf l.prof l.s₀ l.args c).bp.toNat = (stackLayout l.args l.prof.linux c).sp - 400 := by
    show (l.s₀.cpu.gpr.rsp - 400#64).toNat = _
    bv_omega
  have hq : ((ctxOf l.prof l.s₀ l.args c).bp + 104#64).toNat = (stackLayout l.args l.prof.linux c).sp - 296 := by
    show (l.s₀.cpu.gpr.rsp - 400#64 + 104#64).toNat = _
    bv_omega
  obtain ⟨kbp, kmain, kargc, kargv, kinit, kfini, krtld, kV0, kq, kz, kln⟩ := ctxOf_entry l.prof l.s₀ l.args c
  have hI := launch_img h
  have hB := launch_bss h
  have himg : l.s₀.cpu.gpr.rsp.toNat ≤ 0x400000 ∨ 0x7a9000 + 24 ≤ l.s₀.cpu.gpr.rsp.toNat := .inr (by omega)
  have hI0 : Img (ctxOf l.prof l.s₀ l.args c).V0 := kV0 ▸ Entry.V1_img hI (by omega) himg
  have hK : (ctxOf l.prof l.s₀ l.args c).Ok := Ctx.ok hLch hI0 kq kz kln
  have hsg := launch_segOf (lo := (stackLayout l.args l.prof.linux c).sp - n) (L := L) (o := o) h hroom hst
    (by omega) (by omega) (by omega) hL ho
  have hE : Env (ctxOf l.prof l.s₀ l.args c)
      (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L)
      (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).writes := hst.envOf (by omega)
  have hcb := fun y (hy : Foot (cpuW ((ctxOf l.prof l.s₀ l.args c).bp + 104#64)) y) => cpuW_bd hK (by omega) hy
  have hcw : ∀ y, Foot (cpuW ((ctxOf l.prof l.s₀ l.args c).bp + 104#64)) y →
      Foot (zzsFoot ((stackLayout l.args l.prof.linux c).sp - n) c.stackTop L).writes y := by
    intro y hy
    rcases hcb y hy with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact zzsFoot_stack htop (by omega) (by omega)
    · exact zzsFoot_stack htop (by omega) (by omega)
    · exact zzsFoot_var (by omega) (by omega)
  have hcn : ∀ y : Addr, y.toNat < 0x792018 → ¬ Foot (cpuW ((ctxOf l.prof l.s₀ l.args c).bp + 104#64)) y := by
    intro y hy hf
    rcases hcb y hf with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega
  refine Entry.entry_cpu hsg hC.ent hC.lsm hC.pie hC.aux hC.sec hC.tin (KeptW.refl _ _) (fun _ _ => rfl) hrip
    (by omega) (by omega) ?_ ?_ hI hB himg _ kbp kmain kargc kargv kinit kfini krtld kV0 hLch kq kz kln hE hcw ?_
    ?_ ?_ ?_ ?_ hpc hch hdf hx87 hfin
  · intro i hi
    have e : (Addr.add l.s₀.cpu.gpr.rsp i).toNat = (stackLayout l.args l.prof.linux c).sp + i := by
      simp only [Addr.add]
      bv_omega
    exact foot_writes (zzsFoot_stack htop (by omega) (by omega))
  · intro a h1 h2
    exact zzsFoot_stack htop (by omega) (by omega)
  · refine ⟨hC.icf, hC.icfk, hC.tgv, hC.gci, hC.icfa, hC.icfh, hC.icfi, fun y hy => foot_append_iff.2 (.inl hy),
      by omega, .inl (by omega), by omega, by omega, ?_⟩
    intro m hm
    obtain ⟨t1, t2⟩ := tun_bd m hm
    obtain ⟨b1, b2⟩ := tgvInit_bd m hm
    obtain ⟨z1, z2, z3⟩ := tun_z m hm
    refine ⟨fun i hi => ?_, fun i hi => ?_, foot_writes (zzsFoot_var (by omega) (by omega)), hcn _ (by omega), ?_⟩
    · have := t1 i hi
      exact foot_writes (zzsFoot_var (by omega) (by omega))
    · have := t2 i hi
      exact foot_writes (zzsFoot_var (by omega) (by omega))
    · rw [z1, hI0 0x791660 1456 tl tl_pin (by decide) (by decide) _ z2, z3]
  · intro i hi
    have e : ((0x6ee6d0 : Addr).add i).toNat = 0x6ee6d0 + i := tg (b := 0x6ee6d0) hi (by decide)
    exact foot_reads (zzsFoot_ro (by rw [e]; omega) (by rw [e]; omega))
  · intro i hi
    have e : ((0x6ee6d0 : Addr).add i).toNat = 0x6ee6d0 + i := tg (b := 0x6ee6d0) hi (by decide)
    exact hcn _ (by rw [e]; omega)
  · refine ⟨hC.irl, hC.next, hC.res, fun y hy => foot_append_iff.2 (.inr hy), ?_, ?_, by omega, .inl (by omega),
      by omega⟩
    · intro j hj
      have e : ((0x400248 : Addr).add j).toNat = 0x400248 + j := tg (b := 0x400248) hj (by decide)
      exact foot_reads (zzsFoot_hdr (by rw [e]; omega) (by rw [e]; omega))
    · intro y hy
      have h1 : 0x7a4ae0 ≤ y.toNat := hy.1
      have h2 : y.toNat < 0x7a4ae0 + 0x68 := hy.2
      exact foot_writes (zzsFoot_var (by omega) (by omega))
  · intro j hj
    have e : ((0x400248 : Addr).add j).toNat = 0x400248 + j := tg (b := 0x400248) hj (by decide)
    exact hcn _ (by rw [e]; omega)

end FV7z.Start
