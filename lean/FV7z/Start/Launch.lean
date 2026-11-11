import FV7z.Start.Loaded
import FV7z.Start.Exec
/-!
# The first instruction of `7zzs` (PLAN.md G3, startup)

A start of `7zzs` in the words of Zellic's model (`Launch.Of`, `Spec/Process.lean`: the file holds the bytes of
`zzs.blob`, and `execve` starts it): what the kernel's ELF reader reads from the file is what the kernel's evaluation
of Zellic's reader on `zzs.blob` gives.

- `leNat_congr`, `hdr_congr`, `phdrs_congr`: the ELF header and the program headers are read from the file's first
  bytes alone, so two files that agree on them have the same.
- `readElf_zzs`: of a file that holds the bytes of `7zzs`, the entry is `0x41d350` and the program headers are
  `zzsPhdrs`.
- `launch_cpu`: so at the first instruction `rip` is `0x41d350` (`_start`), `rsp` is where `stackLayout` puts the
  argument count, and every other general register is 0 (`entryCpu`); `launch_regs`: the ones `_start` reads
  (`Entry/Holds.lean`: `rip`, `rsp`, `rdx`), and the flags `TF`, `AC`, `DF` clear.
-/
namespace FV7z.Start
open ZellicX86

theorem leNat_congr {rd rd' : Nat → Byte} {n : Nat} (h : ∀ i, i < n → rd i = rd' i) :
    ∀ (k off : Nat), off + k ≤ n → leNat rd off k = leNat rd' off k
  | 0, _, _ => rfl
  | k + 1, off, hk => by
    simp only [leNat]
    rw [h off (by omega), leNat_congr h k (off + 1) (by omega)]

theorem hdr_congr {rd rd' : Nat → Byte} {n : Nat} (h : ∀ i, i < n → rd i = rd' i) (hn : 64 ≤ n) :
    ElfHeader.read rd = ElfHeader.read rd' := by
  simp only [ElfHeader.read]
  rw [leNat_congr h 2 16 (by omega), leNat_congr h 2 18 (by omega), leNat_congr h 8 24 (by omega),
    leNat_congr h 8 32 (by omega), leNat_congr h 2 54 (by omega), leNat_congr h 2 56 (by omega)]

theorem phdrs_congr {rd rd' : Nat → Byte} {n : Nat} (h : ∀ i, i < n → rd i = rd' i) {off k : Nat}
    (hk : off + phdrSize * k ≤ n) : readPhdrs rd off k = readPhdrs rd' off k := by
  simp only [readPhdrs]
  apply List.map_congr_left
  intro i hi
  have hi' : i < k := List.mem_range.1 hi
  have hb : off + phdrSize * i + 56 ≤ n := by
    have : phdrSize * (i + 1) ≤ phdrSize * k := Nat.mul_le_mul_left _ hi'
    simp only [phdrSize] at this hk ⊢
    omega
  simp only [Phdr.read]
  rw [leNat_congr h 4 _ (by omega), leNat_congr h 4 _ (by omega), leNat_congr h 8 _ (by omega),
    leNat_congr h 8 _ (by omega), leNat_congr h 8 _ (by omega), leNat_congr h 8 _ (by omega)]

theorem zzs_size : 64 ≤ V2606.zzs.blob.size := by decide +kernel
theorem zzs_entry : (ElfHeader.read V2606.zzs.blob.bytes).entry = 0x41d350 := by decide +kernel

theorem readElf_zzs {files : Files} {exe : FileId}
    (hf : FileHolds files exe V2606.zzs.blob.bytes V2606.zzs.blob.size) {hdr : ElfHeader} {phs : List Phdr}
    (hr : readElf files exe = some (hdr, phs)) : hdr.entry = 0x41d350 ∧ phs = zzsPhdrs := by
  obtain ⟨hsz, hby⟩ := hf
  unfold readElf at hr
  simp only at hr
  split at hr
  · rename_i hc
    have he : ElfHeader.read (files.byte exe) = ElfHeader.read V2606.zzs.blob.bytes := hdr_congr hby zzs_size
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hr)
    refine ⟨by rw [he]; exact zzs_entry, ?_⟩
    rw [phdrs_congr hby (by rw [← hsz]; exact hc.2.2.2.2.2.2), he]
    rfl
  · cases hr

theorem zzs_phoff : (ElfHeader.read V2606.zzs.blob.bytes).phoff = 64 := by decide +kernel

/-- Of a file that holds the bytes of `7zzs`, the ELF header is the one read from `zzs.blob`. -/
theorem readElf_zzs_hdr {files : Files} {exe : FileId}
    (hf : FileHolds files exe V2606.zzs.blob.bytes V2606.zzs.blob.size) {hdr : ElfHeader} {phs : List Phdr}
    (hr : readElf files exe = some (hdr, phs)) : hdr = ElfHeader.read V2606.zzs.blob.bytes := by
  obtain ⟨hsz, hby⟩ := hf
  unfold readElf at hr
  simp only at hr
  split at hr
  · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hr)
    exact hdr_congr hby zzs_size
  · cases hr

theorem launch_cpu {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧
      l.s₀.cpu = entryCpu 0x41d350 (stackLayout l.args l.prof.linux c).sp l.kcfg.initPkru := by
  obtain ⟨hf, hx, -⟩ := h
  obtain ⟨hdr, phs, c, hr, hv, hc⟩ := ExecStart.cpu hx
  obtain ⟨he, rfl⟩ := readElf_zzs hf hr
  exact ⟨c, hv, by rw [hc, he]⟩

/-- The registers `_start` and the code after it read, at the first instruction. -/
theorem launch_regs {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    ∃ c, c.Valid l.prof.linux zzsPhdrs l.args l.kcfg ∧ l.s₀.cpu.rip = 0x41d350#64 ∧
      l.s₀.cpu.gpr.rsp = BitVec.ofNat 64 (stackLayout l.args l.prof.linux c).sp ∧ l.s₀.cpu.gpr.rdx = 0 ∧
      l.s₀.cpu.gpr.rax = 0 ∧ l.s₀.cpu.rflags.tf = false ∧ l.s₀.cpu.rflags.ac = false ∧
      l.s₀.cpu.rflags.df = false := by
  obtain ⟨c, hv, hc⟩ := launch_cpu h
  exact ⟨c, hv, by rw [hc]; rfl, by rw [hc]; rfl, by rw [hc]; rfl, by rw [hc]; rfl, by rw [hc]; rfl, by rw [hc]; rfl,
    by rw [hc]; rfl⟩

end FV7z.Start
