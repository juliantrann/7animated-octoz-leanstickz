import FV7z.Start.SegMap
import FV7z.Start.StackMap
import FV7z.Start.Bytes
/-!
# What `7zzs` can access of its segments at its first instruction (PLAN.md G3, startup)

Zellic's `Memory.check` (`Accessible`, byte by byte) for the pages of the segments, as `launch_stack_rw` for the
stack's.

- `check_ok`: a mapped page with key 0 whose backing is private memory, or a file page not beyond the file's end,
  allows what its protection allows, when `PKRU`'s two low bits are clear.
- `segFile_backing`, `seg_backing`: a page of the five regions is private memory or a page of the executable
  within its 3759224 bytes.
- `launch_access`: the code can be fetched and read, the headers and `.rodata` read, `.data` and `.bss` read and
  written.
-/
namespace FV7z.Start
open ZellicX86

theorem check_ok {feat : Features} {pkru : BitVec 32} {mem : Memory} {x : Addr} {mp : Mapping}
    (hm : mem.map (pageOf x) = some mp) (hk : mp.pkey = 0)
    (hb : (∃ f, mem.backings mp.backing = .priv f) ∨
      ∃ fp, mem.backings mp.backing = .cow fp ∧ mem.files.beyondEof fp = false)
    (hp : pkru &&& 3 = 0) (acc : Access) (ha : mp.allows feat acc = true) : mem.check feat pkru acc x = none := by
  obtain ⟨p0, p1⟩ := pkru_low hp
  have hd : pkeyDenies pkru 0 acc = false := by
    cases acc
    · simpa [pkeyDenies] using p0
    · simpa [pkeyDenies] using And.intro p0 p1
    · rfl
  rcases hb with ⟨f, hf⟩ | ⟨fp, hf, he⟩
  · simp [Memory.check, Memory.check.rest, hm, hf, Backing.filePage, Backing.noSource, hk, ha]
    exact fun _ => hd
  · simp [Memory.check, Memory.check.rest, hm, hf, Backing.filePage, he, hk, ha]
    exact fun _ => hd

theorem ite_priv {c : Prop} [Decidable c] {g : Frame} {b : Backing} :
    (∃ f, (if c then Backing.priv g else b) = .priv f) ∨ (if c then Backing.priv g else b) = b := by
  by_cases h : c
  · exact .inl ⟨g, by simp only [h, ↓reduceIte]⟩
  · exact .inr (by simp only [h, ↓reduceIte])

theorem segFile_backing (files : Files) (exe : FileId) (ph : Phdr) (k : Nat) :
    (∃ f, (segFile files exe ph).backing k = .priv f) ∨
      (segFile files exe ph).backing k = .cow ⟨exe, (ph.offset - ph.vaddr % 4096) / 4096 + k⟩ := by
  simp only [segFile]
  exact ite_priv

theorem seg_backing (files : Files) (exe : FileId) {r : Region}
    (hm : r ∈ [segFile files exe ph0, segFile files exe ph1, segFile files exe ph2, segFile files exe ph3,
      segAnon ph3]) {k : Nat} (hk : k < r.count) :
    (∃ f, r.backing k = .priv f) ∨ ∃ i, r.backing k = .cow ⟨exe, i⟩ ∧ 4096 * i < 3759224 := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages files exe
  have e0 : (ph0.offset - ph0.vaddr % 4096) / 4096 = 0 := rfl
  have e1 : (ph1.offset - ph1.vaddr % 4096) / 4096 = 1 := rfl
  have e2 : (ph2.offset - ph2.vaddr % 4096) / 4096 = 0x2d8 := rfl
  have e3 : (ph3.offset - ph3.vaddr % 4096) / 4096 = 0x376 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · rcases segFile_backing files exe ph0 k with hf | hc
    · exact .inl hf
    · exact .inr ⟨_, hc, by omega⟩
  · rcases segFile_backing files exe ph1 k with hf | hc
    · exact .inl hf
    · exact .inr ⟨_, hc, by omega⟩
  · rcases segFile_backing files exe ph2 k with hf | hc
    · exact .inl hf
    · exact .inr ⟨_, hc, by omega⟩
  · rcases segFile_backing files exe ph3 k with hf | hc
    · exact .inl hf
    · exact .inr ⟨_, hc, by omega⟩
  · exact .inl ⟨_, rfl⟩

/-- At the first instruction of `7zzs`, a page of one of the five regions allows what the region's protection
allows. -/
theorem launch_seg_check {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) {r : Region}
    {x : Addr}
    (hmem : r ∈ [segFile l.files l.exe ph0, segFile l.files l.exe ph1, segFile l.files l.exe ph2,
      segFile l.files l.exe ph3, segAnon ph3]) (hhas : r.has (pageOf x).toNat = true) (acc : Access)
    (ha : ∀ mp : Mapping, mp.prot = r.prot → mp.allows l.prof.feat acc = true) :
    l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru acc x = none := by
  obtain ⟨mp, hm, hpr, hkey, hb, hsz⟩ := launch_seg' h hmem hhas
  obtain ⟨hfh, hx, -⟩ := h
  have hk : l.kcfg.initPkru &&& 3 = 0 := hx.1
  obtain ⟨hdr, phs, c, -, -, hc⟩ := ExecStart.cpu hx
  have ep : l.s₀.cpu.pkru = l.kcfg.initPkru := by rw [hc]; rfl
  have hcnt : (pageOf x).toNat - r.first < r.count := by
    rw [has_iff] at hhas
    omega
  refine check_ok hm hkey ?_ (ep ▸ hk) acc (ha mp hpr)
  rw [hb]
  rcases seg_backing l.files l.exe hmem hcnt with hf | ⟨i, hi, hlt⟩
  · exact .inl hf
  · refine .inr ⟨_, hi, ?_⟩
    have hs := hfh.1
    rw [zzs_size_eq] at hs
    simp only [Files.beyondEof, hsz, hs, decide_eq_false_iff_not]
    omega

/-- What `7zzs` can access of its segments at its first instruction. -/
theorem launch_access {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) (x : Addr) :
    (0x400000 ≤ x.toNat → x.toNat < 0x401000 →
      l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .read x = none) ∧
    (0x401000 ≤ x.toNat → x.toNat < 0x6d8000 →
      l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .fetch x = none ∧
      l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .read x = none) ∧
    (0x6d8000 ≤ x.toNat → x.toNat < 0x776000 →
      l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .read x = none) ∧
    (0x777000 ≤ x.toNat → x.toNat < 0x7a9000 →
      l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .read x = none ∧
      l.s₀.proc.mm.mem.check l.prof.feat l.s₀.cpu.pkru .write x = none) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages l.files l.exe
  obtain ⟨p0, p1, p2, p3, p4⟩ := seg_prots l.files l.exe
  have hP := pageOf_toNat x
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ⟨?_, ?_⟩, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · exact launch_seg_check h (r := segFile l.files l.exe ph0) (by simp) (by rw [has_iff]; omega) _
      fun mp e => by simp [Mapping.allows, e, p0]
  · exact launch_seg_check h (r := segFile l.files l.exe ph1) (by simp) (by rw [has_iff]; omega) _
      fun mp e => by simp [Mapping.allows, e, p1]
  · exact launch_seg_check h (r := segFile l.files l.exe ph1) (by simp) (by rw [has_iff]; omega) _
      fun mp e => by simp [Mapping.allows, e, p1]
  · exact launch_seg_check h (r := segFile l.files l.exe ph2) (by simp) (by rw [has_iff]; omega) _
      fun mp e => by simp [Mapping.allows, e, p2]
  · by_cases hb : x.toNat < 0x795000
    · exact ⟨launch_seg_check h (r := segFile l.files l.exe ph3) (by simp) (by rw [has_iff]; omega) _
          fun mp e => by simp [Mapping.allows, e, p3],
        launch_seg_check h (r := segFile l.files l.exe ph3) (by simp) (by rw [has_iff]; omega) _
          fun mp e => by simp [Mapping.allows, e, p3]⟩
    · exact ⟨launch_seg_check h (r := segAnon ph3) (by simp) (by rw [has_iff]; omega) _
          fun mp e => by simp [Mapping.allows, e, p4],
        launch_seg_check h (r := segAnon ph3) (by simp) (by rw [has_iff]; omega) _
          fun mp e => by simp [Mapping.allows, e, p4]⟩

end FV7z.Start
