import FV7z.Start.Pages
/-!
# The bytes of `7zzs`'s segments at its first instruction (PLAN.md G3, startup)

- `pageOf_ofNat`, `pageOffset_ofNat`: an address's page number and its offset in the page.
- `file_page`: a byte of a file, in the file's page.
- `segFile_byte`: a byte of a segment's file part lies in the region of the segment's file pages (`segFile`), where
  it is the file's byte at the segment's offset: the page maps the file's page, or, the last one of a writable
  segment with zeros after its file part, holds a copy of its bytes up to where the zeros start.
- `launch_bytes`, `launch_zero`: so at the first instruction of a launch of `7zzs` (`Launch.Of`), each segment's bytes
  in the file are in memory at its address, and `.bss` is zero (the rest of the data's last file page, which `execve`
  zeroes, and the zero pages after it).
- `launch_img`, `launch_bss`: `Img` and `Bss` (`Start/Image.lean`) of that state's memory, what `entry_cpu`
  (`Entry/Holds.lean`) assumes of the image.
-/
namespace FV7z.Start
open ZellicX86

theorem pageOf_ofNat {n : Nat} (h : n < 2 ^ 64) : (pageOf (BitVec.ofNat 64 n)).toNat = n / 4096 := by
  simp only [pageOf, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem pageOffset_ofNat (n : Nat) : pageOffset (BitVec.ofNat 64 n) = BitVec.ofNat 12 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [pageOffset, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

theorem file_page {fs : Files} {file : FileId} {img : Nat → Byte} {n : Nat} (hf : FileHolds fs file img n) {i : Nat}
    (hi : i < n) : fs.page ⟨file, i / 4096⟩ (BitVec.ofNat 12 i) = img i := by
  obtain ⟨hs, hb⟩ := hf
  have h := hb i hi
  simp only [Files.byte, hs, hi, ↓reduceIte] at h
  exact h

theorem segFile_byte {files files' : Files} (hp : files'.page = files.page) {exe : FileId} {ph : Phdr}
    (hoff : ph.offset % 4096 = ph.vaddr % 4096) {j : Nat} (hj : j < ph.filesz) (hx : ph.vaddr + j < 2 ^ 64) :
    (segFile files exe ph).has (pageOf (BitVec.ofNat 64 (ph.vaddr + j))).toNat = true ∧
    ((segFile files exe ph).backing ((pageOf (BitVec.ofNat 64 (ph.vaddr + j))).toNat -
        (segFile files exe ph).first)).frame files' (pageOffset (BitVec.ofNat 64 (ph.vaddr + j))) =
      files.page ⟨exe, (ph.offset + j) / 4096⟩ (BitVec.ofNat 12 (ph.offset + j)) := by
  have h0 : ph.filesz ≠ 0 := by omega
  have eo : BitVec.ofNat 12 (ph.vaddr + j) = BitVec.ofNat 12 (ph.offset + j) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  rw [pageOf_ofNat hx, pageOffset_ofNat, has_iff]
  simp only [segFile, h0, ↓reduceIte, pageDown, pageUp]
  refine ⟨by omega, ?_⟩
  have ei : (ph.offset - ph.vaddr % 4096) / 4096 + ((ph.vaddr + j) / 4096 - ph.vaddr / 4096 * 4096 / 4096) =
      (ph.offset + j) / 4096 := by omega
  split
  · rename_i hc
    have hlt : (BitVec.ofNat 12 (ph.offset + j)).toNat < (ph.vaddr + ph.filesz) % 4096 := by
      simp only [BitVec.toNat_ofNat]
      omega
    simp only [Backing.frame, ei, eo, hlt, ↓reduceIte]
  · simp only [Backing.frame, hp, ei, eo]

theorem zzs_size_eq : V2606.zzs.blob.size = 3759224 := by decide +kernel

/-- At the first instruction of `7zzs`, each loadable segment's bytes in the file are in memory at its address. -/
theorem launch_bytes {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) {ph : Phdr}
    (hph : ph ∈ [ph0, ph1, ph2, ph3]) {j : Nat} (hj : j < ph.filesz) :
    l.s₀.proc.mm.mem.readByte (BitVec.ofNat 64 (ph.vaddr + j)) = V2606.zzs.blob.bytes (ph.offset + j) := by
  obtain ⟨files', hp, hrd⟩ := launch_page h
  have hs := zzs_size_eq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hph
  have hfacts : ph.offset + ph.filesz ≤ 3759224 ∧ ph.offset % 4096 = ph.vaddr % 4096 ∧
      ph.vaddr + ph.filesz < 2 ^ 64 ∧
      segFile l.files l.exe ph ∈ [segFile l.files l.exe ph0, segFile l.files l.exe ph1,
        segFile l.files l.exe ph2, segFile l.files l.exe ph3, segAnon ph3] := by
    rcases hph with rfl | rfl | rfl | rfl <;> exact ⟨by decide, rfl, by decide, by simp⟩
  obtain ⟨h1, h2, h3, h4⟩ := hfacts
  obtain ⟨hhas, hfr⟩ := segFile_byte (files := l.files) (exe := l.exe) hp h2 hj (by omega)
  rw [hrd _ _ h4 hhas, hfr, file_page h.1 (by omega)]

/-- At the first instruction of `7zzs`, `.bss` (`0x7945d0` to `0x7a86c0`) is zero. -/
theorem launch_zero {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) {x : Nat}
    (hlo : 0x7945d0 ≤ x) (hhi : x < 0x7a86c0) : l.s₀.proc.mm.mem.readByte (BitVec.ofNat 64 x) = 0 := by
  obtain ⟨files', hp, hrd⟩ := launch_page h
  obtain ⟨-, -, -, ⟨a3, b3⟩, a4, b4⟩ := seg_pages l.files l.exe
  have hP := pageOf_ofNat (n := x) (by omega)
  by_cases hx : x < 0x795000
  · rw [hrd (segFile l.files l.exe ph3) _ (by simp) (by rw [has_iff, hP, a3, b3]; omega), hP, pageOffset_ofNat, a3]
    have hk : x / 4096 - 0x777 = 0x1d := by omega
    rw [hk]
    simp [segFile, ph3, pageDown, pageUp, Phdr.prot, Phdr.hasFlag, Backing.frame]
    intro hlt
    omega
  · rw [hrd (segAnon ph3) _ (by simp) (by rw [has_iff, hP, a4, b4]; omega)]
    rfl

/-- The file's bytes are in memory at the first instruction of `7zzs` (`Img`, `Start/Image.lean`). -/
theorem launch_img {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    Img l.s₀.proc.mm.mem.readByte := by
  intro a n bs hb _ _ i hi
  obtain ⟨p, hp, hty, hlo, hhi, rfl⟩ := bytesAt_some hb
  have hp' : p ∈ [ph0, ph1, ph2, ph3] := by
    change p ∈ zzsPhdrs at hp
    rw [zzs_phdrs] at hp
    simp only [zzsPh, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (simp [ph0, ph1, ph2, ph3]; done) | (exact absurd hty (by decide))
  have h1 := launch_bytes h hp' (j := a - p.vaddr + i) (by omega)
  have e : a + i = p.vaddr + (a - p.vaddr + i) := by omega
  rw [e, h1]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, Nat.add_assoc]

/-- `.bss` is zero at the first instruction of `7zzs` (`Bss`, `Start/Image.lean`). -/
theorem launch_bss {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    Bss l.s₀.proc.mm.mem.readByte := by
  intro a hlo hhi
  have h1 := launch_zero h hlo hhi
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h1

end FV7z.Start
