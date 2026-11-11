import FV7z.Start.Segs
/-!
# The pages of `7zzs`'s segments at its first instruction (PLAN.md G3, startup)

Which region of the address space `execve` makes (`ExecStart.start`) has a page of a segment of `7zzs`
(`zzs_segs`): the segment's own, since the segments' pages are apart from each other, the stack's region comes
before them, and the vDSO's regions, which come after, lie apart from every segment (`ExecChoice.VdsoPlace.segs`).

- `find?_unique`: the one element of a list with a property is what `find?` finds.
- `find_segs`: in `vsyscall ++ (stack :: segs ++ post)`, a page no region of `post` has is found in `segs`.
- `zzs_find`: of the five regions of `7zzs`, the one that has a page, by the page's number.
-/
namespace FV7z.Start
open ZellicX86

theorem has_iff {r : Region} {P : Nat} : r.has P = true ↔ r.first ≤ P ∧ P < r.first + r.count := by
  simp [Region.has]

theorem find?_unique {α : Type} {p : α → Bool} {r : α} : ∀ {l : List α}, r ∈ l → p r = true →
    (∀ q ∈ l, p q = true → q = r) → l.find? p = some r
  | [], h, _, _ => by cases h
  | x :: l, h, hp, hu => by
    rw [List.find?_cons]
    by_cases hx : p x = true
    · rw [hx, hu x (List.mem_cons_self ..) hx]
    · rcases List.mem_cons.1 h with rfl | h'
      · exact absurd hp hx
      · rw [Bool.not_eq_true] at hx
        rw [hx]
        exact find?_unique h' hp fun q hq => hu q (List.mem_cons_of_mem _ hq)

theorem find_segs {vs post segs : List Region} {stack : Region} {P : Nat} {r : Region}
    (hpost : ∀ q ∈ post, q.has P = false) (hr : segs.reverse.find? (·.has P) = some r) :
    (vs ++ (stack :: segs ++ post)).reverse.find? (·.has P) = some r := by
  have hp : post.reverse.find? (·.has P) = none := by
    rw [List.find?_eq_none]
    intro q hq
    simpa using hpost q (List.mem_reverse.1 hq)
  simp only [List.reverse_append, List.reverse_cons, List.find?_append, List.append_assoc, hp, hr, Option.none_or,
    Option.some_or]

/-- The region of `7zzs` that has page `P`: `i` among the file pages' regions of the four segments and `.bss`'s. -/
theorem zzs_find (files : Files) (exe : FileId) {P : Nat} {r : Region}
    (hm : r ∈ [segFile files exe ph0, segFile files exe ph1, segFile files exe ph2, segFile files exe ph3,
      segAnon ph3])
    (hP : r.has P = true) :
    [segFile files exe ph0, segFile files exe ph1, segFile files exe ph2, segFile files exe ph3,
      segAnon ph3].reverse.find? (·.has P) = some r := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages files exe
  apply find?_unique (List.mem_reverse.2 hm) hP
  intro q hq hq'
  rw [List.mem_reverse] at hq
  rw [has_iff] at hP hq'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm hq
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl | rfl <;>
    first | rfl | (exfalso; omega)

/-- A page of one of the five regions is a page of its segment's memory. -/
theorem seg_ph (files : Files) (exe : FileId) {P : Nat} {r : Region}
    (hm : r ∈ [segFile files exe ph0, segFile files exe ph1, segFile files exe ph2, segFile files exe ph3,
      segAnon ph3])
    (hP : r.has P = true) :
    ∃ ph ∈ zzsPhdrs, ph.type = PT_LOAD ∧ pageDown ph.vaddr ≤ 4096 * P ∧ 4096 * P < pageUp (ph.vaddr + ph.memsz) := by
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩, a4, b4⟩ := seg_pages files exe
  rw [has_iff] at hP
  rw [zzs_phdrs]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have e0 : pageDown ph0.vaddr = 0x400000 ∧ pageUp (ph0.vaddr + ph0.memsz) = 0x401000 := ⟨rfl, rfl⟩
  have e1 : pageDown ph1.vaddr = 0x401000 ∧ pageUp (ph1.vaddr + ph1.memsz) = 0x6d8000 := ⟨rfl, rfl⟩
  have e2 : pageDown ph2.vaddr = 0x6d8000 ∧ pageUp (ph2.vaddr + ph2.memsz) = 0x776000 := ⟨rfl, rfl⟩
  have e3 : pageDown ph3.vaddr = 0x777000 ∧ pageUp (ph3.vaddr + ph3.memsz) = 0x7a9000 := ⟨rfl, rfl⟩
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact ⟨ph0, by simp [zzsPh, ph0], rfl, by rw [e0.1]; omega, by rw [e0.2]; omega⟩
  · exact ⟨ph1, by simp [zzsPh, ph1], rfl, by rw [e1.1]; omega, by rw [e1.2]; omega⟩
  · exact ⟨ph2, by simp [zzsPh, ph2], rfl, by rw [e2.1]; omega, by rw [e2.2]; omega⟩
  · exact ⟨ph3, by simp [zzsPh, ph3], rfl, by rw [e3.1]; omega, by rw [e3.2]; omega⟩
  · exact ⟨ph3, by simp [zzsPh, ph3], rfl, by rw [e3.1]; omega, by rw [e3.2]; omega⟩

/-- No region of the vDSO has a page of a loadable segment's memory. -/
theorem post_apart {lb : LinuxBoot} {phs : List Phdr} {a : ExecArgs} {k : KernelConfig} {c : ExecChoice}
    {post : List Region} (hv : c.Valid lb phs a k)
    (hpost : ∀ r ∈ post, lb.vdso = true ∧ ((r.first = c.vdsoBase / 4096 ∧ r.count = 6) ∨
      (r.first = c.vdsoText / 4096 ∧ r.count = lb.vdsoText.length)))
    {ph : Phdr} (hph : ph ∈ phs) (hty : ph.type = PT_LOAD) {P : Nat} (hlo : pageDown ph.vaddr ≤ 4096 * P)
    (hhi : 4096 * P < pageUp (ph.vaddr + ph.memsz)) : ∀ q ∈ post, q.has P = false := by
  intro q hq
  obtain ⟨hvd, hq'⟩ := hpost q hq
  have vp := hv.vdso hvd
  have hs := vp.segs ph hph hty
  have hal := vp.aligned
  rw [← Bool.not_eq_true, has_iff]
  simp only [ExecChoice.vdsoEnd, ExecChoice.vdsoText] at hs hq'
  rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- At the first instruction of `7zzs`, the byte at an address whose page one of the segments' five regions has is
that page's in the region, over files whose pages are the launch's. -/
theorem launch_page {l : Launch} (h : Launch.Of V2606.zzs.blob.bytes V2606.zzs.blob.size l) :
    ∃ files' : Files, files'.page = l.files.page ∧ ∀ (r : Region) (x : Addr),
      r ∈ [segFile l.files l.exe ph0, segFile l.files l.exe ph1, segFile l.files l.exe ph2,
        segFile l.files l.exe ph3, segAnon ph3] → r.has (pageOf x).toNat = true →
      l.s₀.proc.mm.mem.readByte x = (r.backing ((pageOf x).toNat - r.first)).frame files' (pageOffset x) := by
  obtain ⟨hf, hx, -⟩ := h
  obtain ⟨hdr, phs, c, segs, stack, post, gd, hr, hv, -, hl, hm, hpost, -⟩ := ExecStart.start hx
  obtain ⟨-, rfl⟩ := readElf_zzs hf hr
  obtain rfl := zzs_segs hl
  refine ⟨_, rfl, ?_⟩
  intro r x hmem hhas
  obtain ⟨ph, hph, hty, hlo, hhi⟩ := seg_ph _ _ hmem hhas
  rw [hm]
  exact regionsMemory_readByte (find_segs (post_apart hv hpost hph hty hlo hhi) (zzs_find _ _ hmem hhas))

end FV7z.Start
