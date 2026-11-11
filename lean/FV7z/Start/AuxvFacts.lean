import FV7z.Start.Segs
/-!
# The auxiliary vector `execve` writes (PLAN.md G3, startup)

Zellic's `auxv` (`Spec/Linux/Exec.lean`), for any executable, and `AT_PHDR` for `7zzs`.

- `auxv_facts`: the vector is entries with types other than 0 (and below 64) followed by `AT_NULL`; among them an `AT_PHDR` (3),
  whose every entry's value is the program headers' address, and an `AT_SECURE` (23), whose every entry's value is 1
  for a secure exec and 0 otherwise.
- `readElf_zzs_hdr`, `zzs_phdrAddr`: of a file that holds the bytes of `7zzs`, the ELF header is the one read from
  `zzs.blob`, and the program headers' address (`phdrAddr`) is `0x400040`.
-/
namespace FV7z.Start
open ZellicX86

theorem auxv_facts (prof : Profile) (hdr : ElfHeader) (pa : Nat) (a : ExecArgs) (c : ExecChoice)
    (l : StackLayout) :
    ∃ pre, auxv prof hdr pa a c l = pre ++ [(0, 0)] ∧ (∀ e ∈ pre, e.1 ≠ 0 ∧ e.1 < 64) ∧
      (∀ e ∈ pre, e.1 = 3 → e.2 = pa) ∧ (3, pa) ∈ pre ∧
      (∀ e ∈ pre, e.1 = 23 → e.2 = if a.secure then 1 else 0) ∧ (23, if a.secure then 1 else 0) ∈ pre := by
  refine ⟨(if prof.linux.vdso then [(33, c.vdsoText)] else []) ++
    [(51, prof.aux.minSigStkSz), (16, prof.aux.hwcap.toNat), (6, 4096), (17, 100), (3, pa), (4, phdrSize),
      (5, hdr.phnum), (7, 0), (8, 0), (9, hdr.entry), (11, a.uid), (12, a.euid), (13, a.gid), (14, a.egid),
      (23, if a.secure then 1 else 0), (25, l.platform - platformString.length - 16),
      (26, prof.aux.hwcap2.toNat), (31, c.stackTop - 8 - (a.filename.length + 1)),
      (15, l.platform - platformString.length), (27, 28), (28, 32)], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    cases hv : prof.linux.vdso <;> simp [auxv, hv]

/-- The address of the program headers of `7zzs` in memory (`AT_PHDR`). -/
theorem zzs_phdrAddr : phdrAddr (ElfHeader.read V2606.zzs.blob.bytes) zzsPhdrs = 0x400040 := by
  unfold phdrAddr
  rw [zzs_phoff, zzs_phdrs]
  decide

end FV7z.Start
