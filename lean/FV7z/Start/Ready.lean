import FV7z.Start.Regions
import FV7z.Start.Access
/-!
# The state `execve` starts `7zzs` in is one a call can start from (PLAN.md G3, startup)

- `zzsRegions`: the regions of the address space: the vsyscall page's, the stack's, the five of the segments, the
  vDSO's. `launch_full`: the state `execve` starts `7zzs` in (`ExecStart.full` with the file's program headers).
- `zzs_brk`: the end of the file's data (`0x7945d0`) and the first break (`0x7a9000`).
- `launch_noAlias`: no two pages alias (`NoAliasOver`, of every list of regions).
- `launch_ready`: Zellic's `Ready`: the thread is plain, has no `rseq` area, and the layout is one a process can
  have (`LayoutOk`).
- `launch_misc`: `PKRU` allows key 0, there is no `rseq` area, the break is page-aligned, above 0 and below
  `2 ^ 47`, and the thread's id is in `(0, 2 ^ 32)`: what a C library's startup assumes of them
  (`C.CStart.startup`).
-/
namespace FV7z.Start
open ZellicX86

/-- The regions of the address space `execve` builds for `7zzs`. -/
noncomputable def zzsRegions (prof : Profile) (files : Files) (exe : FileId) (hdr : ElfHeader) (a : ExecArgs)
    (c : ExecChoice) : List Region :=
  vsyscallRegions prof.linux.vsyscall ++ (stackRegion prof hdr zzsPhdrs a c ::
    [segFile files exe ph0, segFile files exe ph1, segFile files exe ph2, segFile files exe ph3, segAnon ph3] ++
    vdsoRegions prof c)

/-- The state `execve` starts `7zzs` in. -/
theorem launch_full {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    ∃ hdr c, readElf l.files l.exe = some (hdr, zzsPhdrs) ∧ c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      l.s₀.cpu = entryCpu hdr.entry (stackLayout l.args l.prof.linux c).sp l.kcfg.initPkru ∧
      l.s₀.proc.mm.mem = regionsMemory (zzsRegions l.prof l.files l.exe hdr l.args c)
        { l.files with denyWrite := fun f => decide (f = l.exe) || l.files.denyWrite f }
        [BitVec.ofNat 52 ((stackLayout l.args l.prof.linux c).start / 4096)] ∧
      l.s₀.proc.mm.brkMin = BitVec.ofNat 64 (brkMin l.prof.linux zzsPhdrs l.args c) ∧
      l.s₀.proc.mm.brk = BitVec.ofNat 64 c.brk ∧
      l.s₀.thread.tid = l.args.tid ∧ l.s₀.thread.rseq = none ∧ l.s₀.thread.shstk = none ∧
      l.s₀.thread.cpuidFaults = false := by
  obtain ⟨hf, hx, -⟩ := h
  obtain ⟨hdr, phs, c, segs, hr, hv, hl, hc, hm, hb⟩ := ExecStart.full hx
  obtain ⟨-, rfl⟩ := readElf_zzs hf hr
  obtain rfl := zzs_segs hl
  exact ⟨hdr, c, hr, hv, hc, hm, hb⟩

theorem zzs_brk : endData zzsPhdrs = 0x7945d0 ∧ brkBase zzsPhdrs = 0x7a9000 := by
  rw [zzs_phdrs]
  exact ⟨by decide, by decide⟩

/-- No region of the address space has a shared file page. -/
theorem zzsRegions_backing {prof : Profile} {files : Files} {exe : FileId} {hdr : ElfHeader} {a : ExecArgs}
    {c : ExecChoice} {r : Region} (hr : r ∈ zzsRegions prof files exe hdr a c) {k : Nat} (hk : k < r.count)
    (fp : FilePage) : r.backing k ≠ .file fp := by
  simp only [zzsRegions, List.mem_append, List.mem_cons] at hr
  rcases hr with hr | (rfl | hr) | hr
  · unfold vsyscallRegions at hr
    split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      intro e
      cases e
    · cases hr
  · intro e
    cases e
  · rcases seg_backing files exe (by simpa using hr) hk with ⟨f, hf⟩ | ⟨i, hi, -⟩
    · rw [hf]
      intro e
      cases e
    · rw [hi]
      intro e
      cases e
  · unfold vdsoRegions at hr
    split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · intro e
        cases e
      · intro e
        cases e
    · cases hr

theorem launch_noAlias {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (qs : List Rgn) :
    NoAliasOver l.s₀ qs := by
  obtain ⟨hdr, c, -, -, -, hm, -⟩ := launch_full h
  exact rm_noAlias hm (fun r hr k hk fp => zzsRegions_backing hr hk fp) qs

theorem taskSize_ge (feat : Features) : 2 ^ 47 - 4096 ≤ taskSize feat := by
  unfold taskSize userPtrMax
  split <;> decide

/-- Every region's maximum protection allows reading, and every region ends at or below the end of the user
address space or is the vsyscall page's. -/
theorem zzsRegions_layout {prof : Profile} {files : Files} {exe : FileId} {hdr : ElfHeader} {a : ExecArgs}
    {k : KernelConfig} {c : ExecChoice} (hv : c.Valid prof.linux zzsPhdrs a k)
    (hs : (stackLayout a prof.linux c).start ≤ c.stackTop) {r : Region}
    (hr : r ∈ zzsRegions prof files exe hdr a c) :
    r.maxProt.read = true ∧ ((r.first + r.count) * 4096 ≤ taskSize prof.feat ∨
      (r.first = vsyscallPage.toNat ∧ r.count = 1 ∧ r.special = true)) := by
  have hts := taskSize_ge prof.feat
  have hT := hv.stackTop.2.2
  simp only [stackTopMax] at hT
  simp only [zzsRegions, List.mem_append, List.mem_cons] at hr
  rcases hr with hr | (rfl | hr) | hr
  · unfold vsyscallRegions at hr
    split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨rfl, .inr ⟨rfl, rfl, rfl⟩⟩
    · cases hr
  · refine ⟨rfl, .inl (Nat.le_trans ?_ hts)⟩
    show ((stackLayout a prof.linux c).start / 4096 + (c.stackTop - (stackLayout a prof.linux c).start) / 4096) *
      4096 ≤ 2 ^ 47 - 4096
    omega
  · obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages files exe
    simp only [List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨rfl, .inl (Nat.le_trans (by rw [a0, b0]; decide) hts)⟩
    · exact ⟨rfl, .inl (Nat.le_trans (by rw [a1, b1]; decide) hts)⟩
    · exact ⟨rfl, .inl (Nat.le_trans (by rw [a2, b2]; decide) hts)⟩
    · exact ⟨rfl, .inl (Nat.le_trans (by rw [a3, b3]; decide) hts)⟩
    · exact ⟨rfl, .inl (Nat.le_trans (by rw [a4, b4]; decide) hts)⟩
  · unfold vdsoRegions at hr
    split at hr
    · rename_i hvd
      have hh := (hv.vdso hvd).high
      simp only [stackTopMax, ExecChoice.vdsoEnd, ExecChoice.vdsoText] at hh
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · refine ⟨rfl, .inl (Nat.le_trans ?_ hts)⟩
        show (c.vdsoBase / 4096 + 6) * 4096 ≤ 2 ^ 47 - 4096
        omega
      · refine ⟨rfl, .inl (Nat.le_trans ?_ hts)⟩
        show (c.vdsoText / 4096 + prof.linux.vdsoText.length) * 4096 ≤ 2 ^ 47 - 4096
        simp only [ExecChoice.vdsoText]
        omega
    · cases hr

/-- The state `execve` starts `7zzs` in, with room on its stack, is one a call can start from. -/
theorem launch_ready {l : Launch} {n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args n) : Ready l.prof.feat l.s₀ := by
  obtain ⟨hdr, c, hr, hv, hc, hm, hbm, hbk, htid, hrs, hsh, hcf⟩ := launch_full h
  obtain ⟨h16, hn, hst, hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  obtain ⟨eD, eB⟩ := zzs_brk
  obtain ⟨k0, k1, k2⟩ := hv.brk
  have hT0 := hv.stackTop.1
  refine ⟨⟨by rw [hc]; rfl, by rw [hc]; rfl, hsh, hcf⟩, by simp only [RseqQuiet, hrs], ?_⟩
  refine rm_layout hm ⟨stackRegion l.prof hdr zzsPhdrs l.args c, ?_, ?_⟩
    (fun r hr => (zzsRegions_layout hv (by omega) hr).1) (fun r hr => (zzsRegions_layout hv (by omega) hr).2) ?_ ?_
  · simp only [zzsRegions, List.mem_append, List.mem_cons, true_or, or_true]
  · rw [has_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    show (stackLayout l.args l.prof.linux c).start / 4096 ≤ (stackLayout l.args l.prof.linux c).start / 4096 ∧
      (stackLayout l.args l.prof.linux c).start / 4096 <
        (stackLayout l.args l.prof.linux c).start / 4096 +
          (c.stackTop - (stackLayout l.args l.prof.linux c).start) / 4096
    omega
  · rw [hbm, BitVec.toNat_ofNat]
    unfold brkMin
    split
    · rw [eD]
      decide
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [hbm, hbk, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c.brk) (by omega)]
    unfold brkMin
    split
    · rw [eD]
      have : (0x7945d0 : Nat) % 2 ^ 64 = 0x7945d0 := by decide
      rw [this]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      exact Nat.le_refl _

/-- What a C library's startup assumes of `PKRU`, the `rseq` area, the break and the thread's id. -/
theorem launch_misc {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    l.s₀.cpu.pkru &&& 3 = 0 ∧ l.s₀.thread.rseq = none ∧ l.s₀.proc.mm.brk.toNat % 4096 = 0 ∧
      0 < l.s₀.proc.mm.brk.toNat ∧ l.s₀.proc.mm.brk.toNat < 2 ^ 47 ∧ 0 < l.s₀.thread.tid ∧
      l.s₀.thread.tid < 2 ^ 32 := by
  obtain ⟨hdr, c, hr, hv, hc, hm, hbm, hbk, htid, hrs, hsh, hcf⟩ := launch_full h
  obtain ⟨eD, eB⟩ := zzs_brk
  obtain ⟨k0, k1, k2⟩ := hv.brk
  have hk : l.kcfg.initPkru &&& 3 = 0 := h.2.1.1
  obtain ⟨-, -, -, -, -, -, t0, t1, -⟩ := h.2.2
  simp only [pidMaxLimit] at t1
  have eb : (BitVec.ofNat 64 c.brk).toNat = c.brk := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨by rw [hc]; exact hk, hrs, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbk, eb]
    exact k0
  · rw [hbk, eb]
    omega
  · rw [hbk, eb]
    omega
  · rw [htid]
    exact t0
  · rw [htid]
    omega

end FV7z.Start
