import ZellicX86.Spec.Statement.Linux
/-!
Probe (Zellic R2): `may_expand_vm` with `RLIMIT_AS` and `RLIMIT_DATA` unlimited lets every growth by fewer than
`2 ^ 51` pages through, given `LayoutOk` and a vsyscall page that is not writable. R2 names this
(`mayExpand_unlimited`, Statement/Linux.lean) without proving it; `sysBrk`'s growth needs it.
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

/-- The pages after `p` that `countMapped` counts are mapped, satisfy `P`, and so lie below `B`: at most
`B - p - 1` of them. -/
theorem countMapped_le (mem : Memory) (P : Nat → Mapping → Bool) (B : Nat)
    (hB : ∀ q m, mem.mapAt q = some m → P q m = true → q < B) :
    ∀ n p, mem.countMapped P p n ≤ B - p - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
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
        omega
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        omega

/-- The mapped pages that satisfy `P`, all below `B`: at most `B`. -/
theorem pagesWhere_le (mem : Memory) (P : Nat → Mapping → Bool) (B : Nat)
    (hB : ∀ q m, mem.mapAt q = some m → P q m = true → q < B) : mem.pagesWhere P ≤ B := by
  have hc := countMapped_le mem P B hB (2 ^ 52 - 1) 0
  unfold Memory.pagesWhere
  split
  · next m hm =>
    by_cases hp : P 0 m = true
    · have := hB 0 m hm hp
      simp only [hp, ↓reduceIte]
      omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      omega
  · omega

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

/-- The pages of the process's mappings (`Memory.totalVm`): at most `2 ^ 44`. -/
theorem totalVm_le {feat : Features} {s : State} (hl : LayoutOk feat s) : s.proc.mm.mem.totalVm ≤ 2 ^ 44 := by
  have ht := taskSize_le feat
  unfold Memory.totalVm
  refine pagesWhere_le _ _ _ fun q m hm hp => ?_
  rcases mapAt_user hl hm with h | ⟨h1, h2⟩
  · omega
  · simp [h1, h2] at hp

/-- The pages of the process's private writable mappings (`Memory.dataVm`): at most `2 ^ 44`, the vsyscall page
not being writable. -/
theorem dataVm_le {feat : Features} {s : State} (hl : LayoutOk feat s)
    (hvs : ∀ m, s.proc.mm.mem.map vsyscallPage = some m → m.prot.write = false) :
    s.proc.mm.mem.dataVm ≤ 2 ^ 44 := by
  have ht := taskSize_le feat
  unfold Memory.dataVm
  refine pagesWhere_le _ _ _ fun q m hm hp => ?_
  rcases mapAt_user hl hm with h | ⟨h1, -⟩
  · omega
  · have hq : q < 2 ^ 52 := by
      unfold Memory.mapAt at hm
      split at hm
      · assumption
      · cases hm
    have e : BitVec.ofNat 52 q = vsyscallPage := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, h1]
    have hw := hvs m (by unfold Memory.mapAt at hm; rw [if_pos hq, e] at hm; exact hm)
    simp [hw] at hp

theorem pages_inf {r : Rlimit} (h : r.cur = RLIM_INFINITY) : r.pages = 2 ^ 52 - 1 := by
  unfold Rlimit.pages
  rw [h]
  decide

/-- `mayExpand_unlimited`: with `RLIMIT_AS` and `RLIMIT_DATA` at `RLIM_INFINITY`, `LayoutOk` and the vsyscall page
not writable, `may_expand_vm` lets `n < 2 ^ 51` pages through, data or not, without the kernel ignoring a limit. -/
theorem mayExpand_unlimited {feat : Features} {s : State} (hl : LayoutOk feat s)
    (hvs : ∀ m, s.proc.mm.mem.map vsyscallPage = some m → m.prot.write = false)
    (has : (s.proc.signal.rlimits RLIMIT_AS).cur = RLIM_INFINITY)
    (hds : (s.proc.signal.rlimits RLIMIT_DATA).cur = RLIM_INFINITY) {n : Nat} (hn : n < 2 ^ 51) (data : Bool) :
    mayExpand (s.proc.signal.rlimits RLIMIT_AS) (s.proc.signal.rlimits RLIMIT_DATA) false s.proc.mm.mem.totalVm
      s.proc.mm.mem.dataVm n data = true := by
  have h1 := totalVm_le hl
  have h2 := dataVm_le hl hvs
  unfold mayExpand
  rw [pages_inf has, pages_inf hds]
  have e1 : s.proc.mm.mem.totalVm + n ≤ 2 ^ 52 - 1 := by omega
  have e2 : s.proc.mm.mem.dataVm + n ≤ 2 ^ 52 - 1 := by omega
  simp [e1, e2]

end FV7z.Acct

#print axioms FV7z.Acct.mayExpand_unlimited
