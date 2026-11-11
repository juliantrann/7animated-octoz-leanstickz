import FV7z.Start.Ready
/-!
# Room above the program break of `7zzs` at its first instruction (PLAN.md G3, startup)

glibc's startup grows the break (`__libc_setup_tls` calls `__sbrk` for the thread's static TLS block and its control
block), and so does `malloc`. Zellic's `brk` maps the pages up to the new break when they and the page after them
are free (`sysBrk`); `BreakRoom s n` (`Spec/Process.lean`) says they are, for a growth of `n` bytes.

- `rm_free`: pages no region has are free in `regionsMemory`.
- `zzs_load_lo`: every loadable segment of the file begins at or below `0x777000`.
- `launch_breakRoom`: on a kernel `LinuxBoot.Modest`, with room on the stack (`StackRoom`), the break of `7zzs` at its
  first instruction has room for `2 ^ 41` bytes: its segments end at `0x7a9000`, the break is less than a page and
  `2 ^ 30` bytes above, the stack is in the top `2 ^ 35` bytes below `2 ^ 47`, and the vDSO is below a segment or
  above `2 ^ 42` (`ExecChoice.VdsoPlace.floor`).
-/
namespace FV7z.Start
open ZellicX86

theorem rm_free {rs : List Region} {fs : Files} {gd : List PageNum} {first n : Nat}
    (h : ∀ r ∈ rs, ∀ P, first ≤ P → P < first + n → r.has P = false) :
    (regionsMemory rs fs gd).free first n = true := by
  simp only [Memory.free, List.all_eq_true, List.mem_range]
  intro j hj
  unfold Memory.mapAt
  split
  · rename_i hlt
    have hnone : rs.reverse.find? (·.has (BitVec.ofNat 52 (first + j)).toNat) = none := by
      rw [List.find?_eq_none]
      intro r hr
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      simpa using h r (List.mem_reverse.1 hr) (first + j) (by omega) (by omega)
    simp only [regionsMemory, hnone, Option.map_none, Option.isNone_none]
  · rfl

theorem zzs_load_lo {p : Phdr} (hp : p ∈ zzsPhdrs) (hty : p.type = PT_LOAD) : pageDown p.vaddr ≤ 0x777000 := by
  rw [zzs_phdrs] at hp
  simp only [zzsPh, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | decide | exact absurd hty (by decide)

/-- At the first instruction of `7zzs`, on a kernel `LinuxBoot.Modest`, the break has room for `2 ^ 41` bytes. -/
theorem launch_breakRoom {l : Launch} {m n : Nat} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l)
    (hroom : StackRoom l.args m) (hM : l.prof.linux.Modest) (hn : n ≤ 2 ^ 41) : BreakRoom l.s₀ n := by
  obtain ⟨hdr, c, hr, hv, hc, hm, hbm, hbk, -⟩ := launch_full h
  obtain ⟨h16, hn', hst, hpg, hlt, hlo, htop⟩ :=
    stack_room (lb := l.prof.linux) hv.stackTop hv.stackAlign (ExecStart.limits h.2.1) hroom
  obtain ⟨eD, eB⟩ := zzs_brk
  obtain ⟨k0, k1, k2⟩ := hv.brk
  obtain ⟨g1, g2⟩ := hM
  rw [eB] at k1 k2
  have eb : l.s₀.proc.mm.brk.toNat = c.brk := by
    rw [hbk, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hvs : vsyscallPage.toNat = 0xffffffffff600 := by decide
  unfold BreakRoom
  rw [eb, hm]
  simp only [pageUp, stackTopMax]
  refine ⟨by omega, rm_free ?_⟩
  intro r hr P h1 h2
  rw [← Bool.not_eq_true, has_iff]
  simp only [zzsRegions, List.mem_append, List.mem_cons] at hr
  rcases hr with hr | (rfl | hr) | hr
  · unfold vsyscallRegions at hr
    split at hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      show ¬ (vsyscallPage.toNat ≤ P ∧ P < vsyscallPage.toNat + 1)
      omega
    · cases hr
  · show ¬ ((stackLayout l.args l.prof.linux c).start / 4096 ≤ P ∧ P < (stackLayout l.args l.prof.linux c).start /
      4096 + (c.stackTop - (stackLayout l.args l.prof.linux c).start) / 4096)
    omega
  · obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages l.files l.exe
    simp only [List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [a0, b0]
      omega
    · rw [a1, b1]
      omega
    · rw [a2, b2]
      omega
    · rw [a3, b3]
      omega
    · rw [a4, b4]
      omega
  · unfold vdsoRegions at hr
    split at hr
    · rename_i hvd
      have vp := hv.vdso hvd
      have hal := vp.aligned
      have hmb : 2 ^ 42 + 2 ^ 36 ≤ mmapBaseMin := by decide
      have hfl : min mmapBaseMin ((stackLayout l.args l.prof.linux c).reserved - 4096 * l.prof.linux.stackGuardGap) -
          (c.vdsoBase + 6 * 4096 + 4096 * l.prof.linux.vdsoText.length - c.vdsoBase) - 2 ^ 21 ≤ c.vdsoBase ∨
          ∃ ph ∈ zzsPhdrs, ph.type = PT_LOAD ∧
            c.vdsoBase + 6 * 4096 + 4096 * l.prof.linux.vdsoText.length ≤ pageDown ph.vaddr := vp.floor
      generalize mmapBaseMin = M at hmb hfl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hP : P < 2 ^ 30 := by omega
      have hB : 2 ^ 42 ≤ c.vdsoBase ∨ c.vdsoBase + 24576 + 4096 * l.prof.linux.vdsoText.length ≤ 0x777000 := by
        rcases hfl with hfl | ⟨ph, hph, hty, hfl⟩
        · left
          rw [Nat.min_def] at hfl
          split at hfl <;> omega
        · right
          have hlo' := zzs_load_lo hph hty
          omega
      rcases hr with rfl | rfl
      · show ¬ (c.vdsoBase / 4096 ≤ P ∧ P < c.vdsoBase / 4096 + 6)
        omega
      · show ¬ (c.vdsoText / 4096 ≤ P ∧ P < c.vdsoText / 4096 + l.prof.linux.vdsoText.length)
        simp only [ExecChoice.vdsoText]
        omega
    · cases hr

end FV7z.Start
