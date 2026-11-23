import ZellicX86.Spec.Statement.Linux
/-!
Probe (Zellic R2): `may_expand_vm` with `RLIMIT_AS` and `RLIMIT_DATA` unlimited lets every growth by fewer than
`2 ^ 51` pages through, given `LayoutOk`. R2 names this (`mayExpand_unlimited`, Statement/Linux.lean) without
proving it; `sysBrk`'s growth needs it.
-/
namespace FV7z.Acct
open ZellicX86

/-- `nextMapped` finds a page that is mapped. -/
theorem nextMapped_some (mem : Memory) :
    ∀ {p n q : Nat} {m : Mapping}, mem.nextMapped p n = some (q, m) → mem.mapAt q = some m
  | _, 0, _, _, h => by simp [Memory.nextMapped] at h
  | p, n + 1, q, m, h => by
    unfold Memory.nextMapped at h
    split at h
    · next m' hm =>
      cases h
      exact hm
    · exact nextMapped_some mem h

/-- The pages after `p` that `countMapped` counts are mapped and satisfy `P`, so lie below `B` or are page `v`
(`B ≤ v`): at most `B - p - 1`, and `v` if after `p`. -/
theorem countMapped_le (mem : Memory) (P : Nat → Mapping → Bool) (B v : Nat) (hv : B ≤ v)
    (hB : ∀ q m, mem.mapAt q = some m → P q m = true → q < B ∨ q = v) :
    ∀ n p, mem.countMapped P p n ≤ B - p - 1 + (if p < v then 1 else 0) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro p
    rw [Memory.countMapped]
    split
    · exact Nat.zero_le _
    · next q m h =>
      have hr := mem.nextMapped_range h
      have hm := nextMapped_some mem h
      have hi := ih (p + n - q) (by omega) q
      by_cases hp : P q m = true
      · have := hB q m hm hp
        simp only [hp, ↓reduceIte]
        split at hi <;> split <;> omega
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        split at hi <;> split <;> omega

/-- The mapped pages that satisfy `P`, all below `B` but page `v` (`B ≤ v`): at most `B + 1`. -/
theorem pagesWhere_le (mem : Memory) (P : Nat → Mapping → Bool) (B v : Nat) (hv : B ≤ v)
    (hB : ∀ q m, mem.mapAt q = some m → P q m = true → q < B ∨ q = v) : mem.pagesWhere P ≤ B + 1 := by
  have hc := countMapped_le mem P B v hv hB (2 ^ 52 - 1) 0
  unfold Memory.pagesWhere
  split
  · next m hm =>
    by_cases hp : P 0 m = true
    · have := hB 0 m hm hp
      simp only [hp, ↓reduceIte]
      split at hc <;> omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      split at hc <;> omega
  · split at hc <;> omega

/-- A mapped page lies below the end of the user address space, or is the vsyscall page (`LayoutOk.user`). -/
theorem mapAt_user {feat : Features} {s : State} (hl : LayoutOk feat s) {q : Nat} {m : Mapping}
    (h : s.proc.mm.mem.mapAt q = some m) :
    (q + 1) * 4096 ≤ taskSize feat ∨ (q = vsyscallPage.toNat ∧ m.special = true) := by
  unfold Memory.mapAt at h
  split at h
  · next hq =>
    have hn : (BitVec.ofNat 52 q).toNat = q := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hq
    rcases hl.user _ m h with h1 | ⟨h1, h2⟩
    · left
      rw [hn] at h1
      exact h1
    · right
      exact ⟨by rw [← h1, hn], h2⟩
  · cases h

theorem taskSize_le (feat : Features) : taskSize feat ≤ 2 ^ 56 := by
  unfold taskSize userPtrMax
  split <;> decide

theorem vsyscallPage_toNat : vsyscallPage.toNat = 0xffffffffff600 := rfl

/-- The mapped pages that satisfy `P`: at most `2 ^ 44 + 1`, given `LayoutOk`. -/
theorem pagesWhere_user {feat : Features} {s : State} (hl : LayoutOk feat s) (P : Nat → Mapping → Bool) :
    s.proc.mm.mem.pagesWhere P ≤ 2 ^ 44 + 1 := by
  have ht := taskSize_le feat
  have h := pagesWhere_le s.proc.mm.mem P (taskSize feat / 4096) vsyscallPage.toNat
    (by rw [vsyscallPage_toNat]; omega) fun q m hm _ => by
      rcases mapAt_user hl hm with h | ⟨h, -⟩
      · left; omega
      · right; exact h
  omega

theorem pages_inf {r : Rlimit} (h : r.cur = RLIM_INFINITY) : r.pages = 2 ^ 52 - 1 := by
  unfold Rlimit.pages
  rw [h]
  decide

/-- `mayExpand_unlimited`: with `RLIMIT_AS` and `RLIMIT_DATA` at `RLIM_INFINITY` and `LayoutOk`, `may_expand_vm` lets
`n < 2 ^ 51` pages through, data or not, without the kernel ignoring a limit. -/
theorem mayExpand_unlimited {feat : Features} {s : State} (hl : LayoutOk feat s)
    (has : (s.proc.signal.rlimits RLIMIT_AS).cur = RLIM_INFINITY)
    (hds : (s.proc.signal.rlimits RLIMIT_DATA).cur = RLIM_INFINITY) {n : Nat} (hn : n < 2 ^ 51) (data : Bool) :
    mayExpand (s.proc.signal.rlimits RLIMIT_AS) (s.proc.signal.rlimits RLIMIT_DATA) false s.proc.mm.mem.totalVm
      s.proc.mm.mem.dataVm n data = true := by
  have h1 := pagesWhere_user hl fun p m => !(m.special && p == vsyscallPage.toNat)
  have h2 := pagesWhere_user hl fun _ m =>
    m.prot.write && !m.growsDown && !(s.proc.mm.mem.backings m.backing).isFile
  unfold mayExpand
  rw [pages_inf has, pages_inf hds]
  have e1 : s.proc.mm.mem.totalVm + n ≤ 2 ^ 52 - 1 := by unfold Memory.totalVm; omega
  have e2 : s.proc.mm.mem.dataVm + n ≤ 2 ^ 52 - 1 := by unfold Memory.dataVm; omega
  simp [e1, e2]

end FV7z.Acct

#print axioms FV7z.Acct.mayExpand_unlimited
