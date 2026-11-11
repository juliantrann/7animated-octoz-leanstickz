import FV7z.Start.State
import FV7z.Start.Pages
/-!
# An address space made of regions (PLAN.md G3, startup)

Facts about Zellic's `regionsMemory` (`Spec/Linux/Exec.lean`), the address space `execve` builds, for any regions.

- `rm_map`: a mapped page's mapping is that of the last region that has the page; its backing's index is the page's
  number, its key 0.
- `rm_noAlias`: where no region has a shared file page, no two pages alias (`NoAliasOver`, of every list of regions).
- `rm_layout`: the layout is one a process can have (`LayoutOk`), where the page that grows down is in a region,
  every region's maximum protection allows reading and every region ends at or below the end of the user address
  space, or is the vsyscall page's.
-/
namespace FV7z.Start
open ZellicX86

theorem rm_map {rs : List Region} {fs : Files} {gd : List PageNum} {p : PageNum} {m : Mapping}
    (h : (regionsMemory rs fs gd).map p = some m) :
    ∃ r ∈ rs, r.has p.toNat = true ∧ rs.reverse.find? (·.has p.toNat) = some r ∧ m.prot = r.prot ∧
      m.backing = p.toNat ∧ m.pkey = 0 ∧ m.special = r.special ∧ m.maxProt = r.maxProt ∧
      m.growsDown = r.growsDown ∧ (regionsMemory rs fs gd).backings m.backing = r.backing (p.toNat - r.first) := by
  simp only [regionsMemory] at h
  cases hf : rs.reverse.find? (·.has p.toNat) with
  | none => simp [hf] at h
  | some r =>
    rw [hf, Option.map_some] at h
    cases h
    refine ⟨r, List.mem_reverse.1 (List.mem_of_find?_eq_some hf), ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · simpa using List.find?_some hf
    · simp only [regionsMemory, hf]

/-- A page some region has is mapped. -/
theorem rm_mapped {rs : List Region} {fs : Files} {gd : List PageNum} {p : PageNum} {r : Region} (hr : r ∈ rs)
    (hh : r.has p.toNat = true) : (regionsMemory rs fs gd).map p ≠ none := by
  simp only [regionsMemory]
  cases hf : rs.reverse.find? (·.has p.toNat) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd hh (hf r (List.mem_reverse.2 hr))
  | some q => simp

theorem rm_noAlias {s : State} {rs : List Region} {fs : Files} {gd : List PageNum}
    (hm : s.proc.mm.mem = regionsMemory rs fs gd)
    (hB : ∀ r ∈ rs, ∀ k, k < r.count → ∀ fp, r.backing k ≠ .file fp) (qs : List Rgn) :
    NoAliasOver s qs := by
  intro a b _ _ hne m n hma hmb
  rw [hm] at hma hmb ⊢
  obtain ⟨r, hr, hh, -, -, eb, -, -, -, -, ebk⟩ := rm_map hma
  obtain ⟨r', -, -, -, -, eb', -⟩ := rm_map hmb
  refine ⟨?_, ?_⟩
  · rw [eb, eb']
    intro e
    exact hne (BitVec.eq_of_toNat_eq e)
  · intro fp hfp
    rw [ebk] at hfp
    rw [has_iff] at hh
    exact absurd hfp (hB r hr _ (by omega) fp)

theorem rm_layout {feat : Features} {s : State} {rs : List Region} {fs : Files} {g : PageNum}
    (hm : s.proc.mm.mem = regionsMemory rs fs [g]) (hg : ∃ r ∈ rs, r.has g.toNat = true)
    (hmax : ∀ r ∈ rs, r.maxProt.read = true)
    (htop : ∀ r ∈ rs, (r.first + r.count) * 4096 ≤ taskSize feat ∨
      (r.first = vsyscallPage.toNat ∧ r.count = 1 ∧ r.special = true))
    (hb0 : 0 < s.proc.mm.brkMin.toNat) (hb1 : s.proc.mm.brkMin.toNat ≤ s.proc.mm.brk.toNat) : LayoutOk feat s := by
  refine ⟨?_, ?_, hb0, hb1, ?_, ?_⟩
  · intro g' hg'
    rw [hm] at hg' ⊢
    obtain rfl : g' = g := by simpa [regionsMemory] using hg'
    obtain ⟨r, hr, hh⟩ := hg
    exact rm_mapped hr hh
  · intro p m hp
    rw [hm] at hp ⊢
    obtain ⟨r, -, -, -, -, eb, -⟩ := rm_map hp
    rw [eb]
    exact p.isLt
  · intro p m hp
    rw [hm] at hp
    obtain ⟨r, hr, -, -, -, -, -, -, em, -⟩ := rm_map hp
    rw [em]
    exact hmax r hr
  · intro p m hp
    rw [hm] at hp
    obtain ⟨r, hr, hh, -, -, -, -, es, -⟩ := rm_map hp
    rw [has_iff] at hh
    rcases htop r hr with ht | ⟨h1, h2, h3⟩
    · left
      exact Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) ht
    · right
      exact ⟨BitVec.eq_of_toNat_eq (by omega), es.trans h3⟩

end FV7z.Start
