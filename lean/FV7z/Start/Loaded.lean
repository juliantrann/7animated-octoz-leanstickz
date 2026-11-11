import FV7z.Start.Image
import ZellicX86.Spec.Process
/-!
# The image's bytes from the segments `execve` loads (PLAN.md G3, startup)

`Img` and `Bss` (`Start/Image.lean`) of the memory of a state in which the loadable segments of `7zzs` are as
`execve` leaves them, in the words of Zellic's model (`SegmentsLoaded`, `Spec/Process.lean`: each `PT_LOAD` segment's
`p_filesz` bytes from the file at `p_vaddr`, and zeros from there to `p_memsz` in a writable one).

- `bytesAt_some`: what `Exe.bytesAt` reads at an address is in one loadable segment's file part, read from the file
  at that segment's offset.
- `Img.of_loaded`: so the bytes `Exe.bytesAt` reads are in memory where `SegmentsLoaded` puts them.
- `zzs_data`: the writable segment's file part ends at `0x7945d0`, and its memory `0x140f0` bytes further, at
  `0x7a86c0` (by the kernel's evaluation of the ELF reader on the file).
- `Bss.of_loaded`: so `.bss` is zero.
-/
namespace FV7z.Start
open ZellicX86

/-- The program headers of `7zzs`, as Zellic's ELF reader reads them. -/
noncomputable def zzsPhdrs : List Phdr :=
  readPhdrs V2606.zzs.blob.bytes (ElfHeader.read V2606.zzs.blob.bytes).phoff
    (ElfHeader.read V2606.zzs.blob.bytes).phnum

theorem bytesAt_some {e : Blob} {a n : Nat} {bs : List Byte} (h : Exe.bytesAt e a n = some bs) :
    ∃ p ∈ readPhdrs e.bytes (ElfHeader.read e.bytes).phoff (ElfHeader.read e.bytes).phnum,
      p.type = PT_LOAD ∧ p.vaddr ≤ a ∧ a + n ≤ p.vaddr + p.filesz ∧
      bs = (List.range n).map fun i => e.bytes (p.offset + (a - p.vaddr) + i) := by
  unfold Exe.bytesAt at h
  simp only at h
  split at h
  · rename_i p hp
    split at h
    · rename_i hc
      have hm := List.mem_of_getLast? hp
      rw [List.mem_filter] at hm
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm hc
      exact ⟨p, hm.1, hm.2.1.1.1, hc.1.1, hc.1.2, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem Img.of_loaded {feat : Features} {s : State}
    (h : SegmentsLoaded feat s V2606.zzs.blob.bytes zzsPhdrs) : Img s.proc.mm.mem.readByte := by
  intro a n bs hb _ _ i hi
  obtain ⟨p, hp, hty, hlo, hhi, rfl⟩ := bytesAt_some hb
  obtain ⟨hB, -, -⟩ := h p hp hty
  have hk : a - p.vaddr + i < p.filesz := by omega
  have h1 := congrArg (fun l => l.getD (a - p.vaddr + i) 0) hB
  simp only [readBytes, byteAddrs, List.length_map, List.length_range, List.map_map,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, Function.comp_apply] at h1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]
  have e : BitVec.ofNat 64 (a + i) = Addr.add (BitVec.ofNat 64 p.vaddr) (a - p.vaddr + i) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    have : a + i = p.vaddr + (a - p.vaddr + i) := by omega
    omega
  rw [e, h1, Nat.add_assoc]

theorem zzs_data' : zzsPhdrs.any (fun p => p.type == PT_LOAD && p.hasFlag 2 && p.vaddr + p.filesz == 0x7945d0 &&
    p.memsz - p.filesz == 0x140f0) = true := by decide +kernel

theorem zzs_data : ∃ p ∈ zzsPhdrs, p.type = PT_LOAD ∧ p.hasFlag 2 = true ∧ p.vaddr + p.filesz = 0x7945d0 ∧
    p.memsz - p.filesz = 0x140f0 := by
  obtain ⟨p, hp, h⟩ := List.any_eq_true.1 zzs_data'
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨p, hp, h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem Bss.of_loaded {feat : Features} {s : State}
    (h : SegmentsLoaded feat s V2606.zzs.blob.bytes zzsPhdrs) : Bss s.proc.mm.mem.readByte := by
  obtain ⟨p, hp, hty, hw, hv, hm⟩ := zzs_data
  obtain ⟨-, -, hZ⟩ := h p hp hty
  obtain ⟨hB, -⟩ := hZ hw
  intro a hlo hhi
  generalize hl : p.memsz - p.filesz = l at hB hm
  generalize hb : p.vaddr + p.filesz = b at hB hv
  have hk : a.toNat - b < l := by omega
  have h1 := congrArg (fun l => l.getD (a.toNat - b) 0) hB
  simp only [readBytes, byteAddrs, List.length_replicate, List.map_map,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, Function.comp_apply, List.getElem?_replicate, hk, ↓reduceIte] at h1
  have e : a = Addr.add (BitVec.ofNat 64 b) (a.toNat - b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Addr.add, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact h1

end FV7z.Start
