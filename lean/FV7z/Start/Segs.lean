import FV7z.Start.Launch
/-!
# The loadable segments of `7zzs` in the address space `execve` makes (PLAN.md G3, startup)

Towards `SegmentsLoaded` (Zellic's `Spec/Process.lean`) of the state a launch of `7zzs` starts in
(`ExecStart.start`, `Start/Exec.lean`: the address space is `regionsMemory` of the regions `loadRegions` gives, among
others).

- `regionsMemory_readByte`, `regionsMemory_unmapped`: the byte at an address of such an address space is its page's
  in the last region that has the page, 0 where none has.
- `zzsPh`, `zzs_phdrs`: the eight program headers of `7zzs` (`readelf -lW`: four `PT_LOAD`, then `PT_NOTE`, `PT_TLS`,
  `PT_GNU_STACK`, `PT_GNU_RELRO`), by the kernel's evaluation of Zellic's ELF reader on the file.
-/
namespace FV7z.Start
open ZellicX86

theorem regionsMemory_readByte {rs : List Region} {files : Files} {gd : List PageNum} {a : Addr} {r : Region}
    (h : rs.reverse.find? (·.has (pageOf a).toNat) = some r) :
    (regionsMemory rs files gd).readByte a =
      (r.backing ((pageOf a).toNat - r.first)).frame files (pageOffset a) := by
  simp only [Memory.readByte, regionsMemory, h, Option.map_some]

theorem regionsMemory_unmapped {rs : List Region} {files : Files} {gd : List PageNum} {a : Addr}
    (h : rs.reverse.find? (·.has (pageOf a).toNat) = none) : (regionsMemory rs files gd).readByte a = 0 := by
  simp only [Memory.readByte, regionsMemory, h, Option.map_none]

/-- The program headers of `7zzs`: type, flags, offset, address, size in the file, size in memory. -/
def zzsPh : List Phdr :=
  [⟨1, 4, 0, 0x400000, 0x530, 0x530⟩, ⟨1, 5, 0x1000, 0x401000, 0x2d667d, 0x2d667d⟩,
    ⟨1, 4, 0x2d8000, 0x6d8000, 0x9dbe9, 0x9dbe9⟩, ⟨1, 6, 0x376770, 0x777770, 0x1ce60, 0x30f50⟩,
    ⟨4, 4, 0x200, 0x400200, 0x44, 0x44⟩, ⟨7, 4, 0x376770, 0x777770, 0x28, 0x80⟩, ⟨0x6474e551, 6, 0, 0, 0, 0⟩,
    ⟨0x6474e552, 4, 0x376770, 0x777770, 0x1a890, 0x1a890⟩]

/-- A program header's fields. -/
def phKey (p : Phdr) : List Nat := [p.type, p.flags, p.offset, p.vaddr, p.filesz, p.memsz]

theorem phKey_inj (p q : Phdr) (h : phKey p = phKey q) : p = q := by
  obtain ⟨_, _, _, _, _, _⟩ := p
  obtain ⟨_, _, _, _, _, _⟩ := q
  simp only [phKey, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

theorem zzs_keys : zzsPhdrs.map phKey = zzsPh.map phKey := by decide +kernel

theorem zzs_phdrs : zzsPhdrs = zzsPh := (List.map_inj_right phKey_inj).1 zzs_keys

/-! ## The regions of a segment -/

/-- The region of a segment's file pages (`segmentRegions`' `fileR`). -/
def segFile (files : Files) (exe : FileId) (ph : Phdr) : Region :=
  let pgoff := ph.vaddr % 4096
  let fileStart := pageDown ph.vaddr
  let fileEnd := if ph.filesz = 0 then fileStart else pageUp (ph.vaddr + ph.filesz)
  let zeroStart := if ph.filesz = 0 then fileStart else ph.vaddr + ph.filesz
  let firstPage := (ph.offset - pgoff) / 4096
  let filePage (k : Nat) : FilePage := ⟨exe, firstPage + k⟩
  let lastFile := (zeroStart - fileStart) / 4096
  let padded := ph.filesz > 0 ∧ ph.memsz > ph.filesz ∧ zeroStart % 4096 ≠ 0
  let backing (k : Nat) : Backing :=
    if padded ∧ ph.prot.write ∧ k = lastFile then
      .priv fun o => if o.toNat < zeroStart % 4096 then files.page (filePage k) o else 0
    else .cow (filePage k)
  ⟨fileStart / 4096, (fileEnd - fileStart) / 4096, ph.prot, backing, false,
    fun k => some (filePage k), ⟨true, true, true⟩, false⟩

/-- The region of a segment's zero pages after its file pages (`segmentRegions`' `anonR`). -/
def segAnon (ph : Phdr) : Region :=
  let fileStart := pageDown ph.vaddr
  let fileEnd := if ph.filesz = 0 then fileStart else pageUp (ph.vaddr + ph.filesz)
  let anonStart := if ph.filesz = 0 then fileStart else fileEnd
  let anonEnd := if ph.memsz > ph.filesz then max anonStart (pageUp (ph.vaddr + ph.memsz))
    else anonStart
  ⟨anonStart / 4096, (anonEnd - anonStart) / 4096,
    ⟨true, true, ph.hasFlag 1⟩, fun _ => .priv zeroFrame, false, fun _ => none, ⟨true, true, true⟩, false⟩

/-- A conditional that gives `.ok rs` and whose first branch does not, gives it by its second. -/
theorem ite_seg {c : Prop} [Decidable c] {A B : SegResult} {rs : List Region}
    (h : (if c then A else B) = .ok rs) (hA : A ≠ .ok rs) : B = .ok rs := by
  split at h
  · exact absurd h hA
  · exact h

/-- The regions `execve` maps for a segment, when it maps them. -/
theorem segmentRegions_ok {feat : Features} {files : Files} {exe : FileId} {k : KernelConfig} {lo hi : Nat}
    {ph : Phdr} {rs : List Region} (h : segmentRegions feat files exe k lo hi ph = .ok rs) :
    rs = [segFile files exe ph, segAnon ph].filter (·.count > 0) := by
  unfold segmentRegions at h
  dsimp only at h
  repeat (replace h := ite_seg h (by intro h; cases h))
  exact (SegResult.ok.inj h).symm

/-- The regions `execve` maps for the loadable segments, when it maps them: each one's, in the headers' order. -/
theorem loadRegions_ok {feat : Features} {files : Files} {exe : FileId} {k : KernelConfig} {lo hi : Nat} :
    ∀ (phs : List Phdr) {segs : List Region}, loadRegions feat files exe k lo hi phs = .ok segs →
      segs = (phs.filter (·.type = PT_LOAD)).flatMap fun ph =>
        [segFile files exe ph, segAnon ph].filter (·.count > 0)
  | [], segs, h => by
    simp only [loadRegions] at h
    obtain rfl := SegResult.ok.inj h
    rfl
  | ph :: phs, segs, h => by
    unfold loadRegions at h
    split at h
    · rename_i hne
      rw [loadRegions_ok phs h, List.filter_cons_of_neg (by simpa using hne)]
    · rename_i heq
      have heq' : ph.type = PT_LOAD := Decidable.not_not.1 heq
      split at h
      · rename_i rs hs
        split at h
        · rename_i rs' hs'
          obtain rfl := SegResult.ok.inj h
          rw [List.filter_cons_of_pos (by simpa using heq'), List.flatMap_cons, ← segmentRegions_ok hs,
            ← loadRegions_ok phs hs']
        · rename_i hr
          exact absurd h (hr _)
      · rename_i hr
        exact absurd h (hr _)

/-! ## The regions of `7zzs` -/

/-- The four loadable segments of `7zzs`: the ELF header's page, the code, the read-only data, the data. -/
def ph0 : Phdr := ⟨1, 4, 0, 0x400000, 0x530, 0x530⟩
def ph1 : Phdr := ⟨1, 5, 0x1000, 0x401000, 0x2d667d, 0x2d667d⟩
def ph2 : Phdr := ⟨1, 4, 0x2d8000, 0x6d8000, 0x9dbe9, 0x9dbe9⟩
def ph3 : Phdr := ⟨1, 6, 0x376770, 0x777770, 0x1ce60, 0x30f50⟩

/-- The regions `execve` maps for `7zzs`: each segment's file pages (1, `0x2d7`, `0x9e` and `0x1e` pages from
`0x400000`, `0x401000`, `0x6d8000` and `0x777000`), and the `0x14` zero pages of `.bss` from `0x795000`. -/
theorem zzs_segs {feat : Features} {files : Files} {exe : FileId} {k : KernelConfig} {lo hi : Nat}
    {segs : List Region} (h : loadRegions feat files exe k lo hi zzsPhdrs = .ok segs) :
    segs = [segFile files exe ph0, segFile files exe ph1, segFile files exe ph2, segFile files exe ph3,
      segAnon ph3] := by
  rw [zzs_phdrs] at h
  rw [loadRegions_ok _ h]
  rfl

theorem seg_pages (files : Files) (exe : FileId) :
    ((segFile files exe ph0).first = 0x400 ∧ (segFile files exe ph0).count = 1) ∧
    ((segFile files exe ph1).first = 0x401 ∧ (segFile files exe ph1).count = 0x2d7) ∧
    ((segFile files exe ph2).first = 0x6d8 ∧ (segFile files exe ph2).count = 0x9e) ∧
    ((segFile files exe ph3).first = 0x777 ∧ (segFile files exe ph3).count = 0x1e) ∧
    ((segAnon ph3).first = 0x795 ∧ (segAnon ph3).count = 0x14) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl⟩

end FV7z.Start
