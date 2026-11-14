import FV7z.Start.Pages
/-!
# The protection of the pages of `7zzs`'s segments at its first instruction (PLAN.md G3, startup)

- `launch_seg`: at the first instruction of `7zzs`, a page one of the segments' five regions has is mapped, with
  the region's protection (as `launch_page` gives the page's bytes).
- `seg_prots`: the five regions' protections, from the segments' flags.
- `launch_prot`: so the headers' page and `.rodata`'s pages are read-only, the code's pages readable and executable
  and not writable, and the pages of `.data` and `.bss` readable and writable and not executable.
-/
namespace FV7z.Start
open ZellicX86

theorem pageOf_toNat (x : Addr) : (pageOf x).toNat = x.toNat / 4096 := by
  have := x.isLt
  simp only [pageOf, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

/-- At the first instruction of `7zzs`, a page one of the segments' five regions has is mapped as the region says:
its protection, key 0, the region's backing for it; and the files' sizes are the launch's. -/
theorem launch_seg' {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) {r : Region} {x : Addr}
    (hmem : r ∈ [segFile l.files l.exe ph0, segFile l.files l.exe ph1, segFile l.files l.exe ph2,
      segFile l.files l.exe ph3, segAnon ph3]) (hhas : r.has (pageOf x).toNat = true) :
    ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot = r.prot ∧ mp.pkey = 0 ∧
      l.s₀.proc.mm.mem.backings mp.backing = r.backing ((pageOf x).toNat - r.first) ∧
      l.s₀.proc.mm.mem.files.size = l.files.size ∧ mp.special = r.special := by
  obtain ⟨hf, hx, -⟩ := h
  obtain ⟨hdr, phs, c, segs, stack, post, gd, hr, hv, -, hl, hm, hpost, -⟩ := ExecStart.start hx
  obtain ⟨-, rfl⟩ := readElf_zzs hf hr
  obtain rfl := zzs_segs hl
  obtain ⟨ph, hph, hty, hlo, hhi⟩ := seg_ph _ _ hmem hhas
  have hfind := find_segs (vs := vsyscallRegions l.prof.linux.vsyscall) (stack := stack)
    (post_apart hv hpost hph hty hlo hhi) (zzs_find _ _ hmem hhas)
  refine ⟨⟨r.prot, (pageOf x).toNat, 0, r.special, r.origin ((pageOf x).toNat - r.first), (pageOf x).toNat,
    r.maxProt, r.growsDown⟩, ?_, rfl, rfl, ?_, ?_, rfl⟩
  · rw [hm]
    simp only [regionsMemory, hfind, Option.map_some]
  · rw [hm]
    simp only [regionsMemory, hfind]
  · rw [hm]
    rfl

theorem launch_seg {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) {r : Region} {x : Addr}
    (hmem : r ∈ [segFile l.files l.exe ph0, segFile l.files l.exe ph1, segFile l.files l.exe ph2,
      segFile l.files l.exe ph3, segAnon ph3]) (hhas : r.has (pageOf x).toNat = true) :
    ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot = r.prot := by
  obtain ⟨mp, h1, h2, -⟩ := launch_seg' h hmem hhas
  exact ⟨mp, h1, h2⟩

theorem seg_prots (files : Files) (exe : FileId) :
    (segFile files exe ph0).prot = ⟨true, false, false⟩ ∧ (segFile files exe ph1).prot = ⟨true, false, true⟩ ∧
    (segFile files exe ph2).prot = ⟨true, false, false⟩ ∧ (segFile files exe ph3).prot = ⟨true, true, false⟩ ∧
    (segAnon ph3).prot = ⟨true, true, false⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The protection of the pages of `7zzs` at its first instruction: read, write, execute. -/
theorem launch_prot {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (x : Addr) :
    (0x400000 ≤ x.toNat → x.toNat < 0x401000 →
      ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot = ⟨true, false, false⟩) ∧
    (0x401000 ≤ x.toNat → x.toNat < 0x6d8000 →
      ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot = ⟨true, false, true⟩) ∧
    (0x6d8000 ≤ x.toNat → x.toNat < 0x776000 →
      ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot = ⟨true, false, false⟩) ∧
    (0x777000 ≤ x.toNat → x.toNat < 0x7a9000 →
      ∃ mp, l.s₀.proc.mm.mem.map (pageOf x) = some mp ∧ mp.prot = ⟨true, true, false⟩) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages l.files l.exe
  obtain ⟨p0, p1, p2, p3, p4⟩ := seg_prots l.files l.exe
  have hP := pageOf_toNat x
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · rw [← p0]
    exact launch_seg h (by simp) (by rw [has_iff]; omega)
  · rw [← p1]
    exact launch_seg h (by simp) (by rw [has_iff]; omega)
  · rw [← p2]
    exact launch_seg h (by simp) (by rw [has_iff]; omega)
  · by_cases hb : x.toNat < 0x795000
    · rw [← p3]
      exact launch_seg h (by simp) (by rw [has_iff]; omega)
    · rw [← p4]
      exact launch_seg h (by simp) (by rw [has_iff]; omega)

/-- The 27 pages of the RELRO segment (`0x777000`–`0x792000`) are mapped, to no special mapping: what
`_dl_protect_relro`'s `mprotect` needs. A field of `Base`, as `brk` and `mprotect` keep it. -/
def Relro (m : Memory) : Prop :=
  ∀ i < 27, ∃ mp, m.mapAt (0x777 + i) = some mp ∧ mp.special = false

/-- At the first instruction of `7zzs`, the RELRO pages are pages of the file part of the data segment. -/
theorem launch_relro {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    Relro l.s₀.proc.mm.mem := by
  intro i hi
  obtain ⟨-, -, -, ⟨a3, b3⟩, -⟩ := seg_pages l.files l.exe
  have hx : (pageOf (BitVec.ofNat 64 ((0x777 + i) * 4096))).toNat = 0x777 + i := by
    rw [pageOf_toNat, BitVec.toNat_ofNat]
    omega
  obtain ⟨mp, hm, -, -, -, -, hsp⟩ := launch_seg' h (r := segFile l.files l.exe ph3) (by simp)
    (by rw [has_iff, hx]; omega)
  have e : pageOf (BitVec.ofNat 64 ((0x777 + i) * 4096)) = BitVec.ofNat 52 (0x777 + i) :=
    BitVec.eq_of_toNat_eq (by rw [hx, BitVec.toNat_ofNat]; omega)
  refine ⟨mp, ?_, hsp.trans rfl⟩
  rw [e] at hm
  simp only [Memory.mapAt, show 0x777 + i < 2 ^ 52 by omega, ↓reduceIte, hm]

end FV7z.Start
