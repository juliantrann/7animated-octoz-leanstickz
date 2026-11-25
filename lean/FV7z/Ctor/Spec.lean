import FV7z.Ctor.GsC
import FV7z.Ctor.Cx95
import FV7z.Ctor.Cx98
import FV7z.Ctor.Cx99
import FV7z.Ctor.CxM
import FV7z.Ctor.PrepC
/-!
# The table of stores for `at_ctor` (PLAN.md §M, constructors)

`spec V hi`: what each constructor not `Done` stores to, for the exit list `initial` at `xl` with its place `0`
taken before `__libc_csu_init` (by `__libc_start_main`, `Start/StkRet`), so the constructors take the places from
`1` on (`nOf 1`). `csuTg 90` also takes the words `malloc` reads (`exH hi`): `csuTg 94` … `csuTg 102` share them
with it (`k₀ = 90`). `61`, `96`, `97` say what they store (`stSpec`).

The intervals but the heap's top `[8029888, hi)` are `cw`, and their facts are by `decide` over `k < 104`: apart
from the registrars' tables (`cwT`), from each other (`cwS`, but `90` and `103`, whose post is `True`), from the
shared words (`cwX`) and from what `96`, `97` read (`cwR`), between `7938368` and `8029888` (`cwB`). The heap's top
is above all of them.
-/
namespace FV7z.Ctor

open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start

/-- The words `malloc` reads below the heap's top. -/
def exC : List (Nat × Nat) := [(7940480, 7943136), (8013220, 8013232)]

/-- The intervals of the constructors not `Done`, but the heap's top. -/
def cw : Nat → List (Nat × Nat)
  | 3 => C3.wr3 | 5 => wrOf w5 | 7 => wrOf w7 | 9 => wrOf w9 | 15 => C15.wr15 | 17 => c17Wr
  | 37 => C37.wr37 | 55 => C55.wr55 | 61 => C61.wr61 | 67 => wrOf w67 | 70 => C70.wr70 | 75 => C75.wr75
  | 77 => wrOf w77 | 78 => C78.wr78 | 82 => C82.wr82 | 87 => C87.wr87
  | 90 => c90Wr xl 1 ++ exC
  | 92 => wrOf w92 | 94 => c94Wr xl 3 | 95 => c95Wr xl 4 | 96 => wr96 | 97 => wr97 | 98 => c98Wr xl 6
  | 99 => c99Wr xl 7 | 100 => mcWr xl 7991456 9 | 101 => mcWr xl 7991520 10 | 102 => c102Wr | 103 => c103Wr
  | _ => []

/-- `cw` below `104`. -/
def wrs (k : Nat) : List (Nat × Nat) := if k < 104 then cw k else []

/-- The words `malloc` reads (`Mal.GlR hi`), in the spec of `csuTg 90`. -/
def exH (hi : Nat) : List (Nat × Nat) := exC ++ [(8029888, hi)]

/-- The table of stores of the constructors. -/
def spec (V : Addr → Byte) (hi k : Nat) : CSpec :=
  if k = 61 then stSpec C61.st61 V C61.wr61 else if k = 96 then stSpec st96 V wr96
  else if k = 97 then stSpec st97 V wr97 else if k = 90 then wrSpec (c90Wr xl 1 ++ exH hi) else wrSpec (wrs k)

theorem cwT : ∀ k < 104, ∀ x ∈ cw k, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide +kernel
theorem cwE : ∀ k < 104, ∀ x ∈ cw k, x.2 ≤ 8013720 ∨ 8013728 ≤ x.1 := by decide +kernel
theorem cwB : ∀ k < 104, ∀ x ∈ cw k, 7938368 ≤ x.1 ∧ x.2 ≤ 8029888 := by decide +kernel
theorem cwS : ∀ j < 104, ∀ k < j, (k = 90 ∧ j = 103) ∨ ∀ x ∈ cw k, ∀ y ∈ cw j, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by
  decide +kernel
theorem cwX : ∀ k < 103, k ≠ 90 → ∀ x ∈ cw k, ∀ y ∈ cxSh xl ++ exC, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide +kernel
theorem cwR : ∀ k < 104, ∀ x ∈ cw k, ∀ y ∈ rd96 ++ rd97, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := by decide +kernel
theorem rdB : ∀ y ∈ rd96 ++ rd97, y.2 ≤ 8029888 := by decide
theorem tabsB : ∀ y ∈ tabs, y.2 ≤ 8029888 := by decide

theorem leasN : ∀ x ∈ leas, x.1 ≠ 61 ∧ x.1 ≠ 96 ∧ x.1 ≠ 97 := by decide +kernel
theorem chainsN : ∀ x ∈ chains, x.1 ≠ 61 ∧ x.1 ≠ 96 ∧ x.1 ≠ 97 := by decide +kernel

/-- `n` in `bs` is in `as ++ bs`. -/
theorem InR_append_right {n : Nat} {bs : List (Nat × Nat)} : ∀ {as : List (Nat × Nat)}, InR bs n → InR (as ++ bs) n
  | [], h => h
  | (_, _) :: _, h => Or.inr (InR_append_right h)

variable {V : Addr → Byte} {hi : Nat}

theorem spec_dep : ∀ k, (spec V hi k).Dep := fun k => by
  unfold spec
  split
  · exact stSpec_dep _ _ _
  split
  · exact stSpec_dep _ _ _
  split
  · exact stSpec_dep _ _ _
  split <;> exact wrSpec_dep _

theorem spec_wr (k : Nat) : (spec V hi k).wr = wrs k ++ if k = 90 then [(8029888, hi)] else [] := by
  unfold spec
  split
  · subst_vars
    rfl
  split
  · subst_vars
    rfl
  split
  · subst_vars
    rfl
  split
  · subst_vars
    first | rfl | simp [wrSpec, exH, wrs, cw]
  · simp [wrSpec, *]

/-- An interval of `spec` is one of `cw`, or the heap's top in `csuTg 90`'s. -/
theorem spec_mem {k : Nat} {x : Nat × Nat} (h : x ∈ (spec V hi k).wr) :
    k < 104 ∧ x ∈ cw k ∨ k = 90 ∧ x = (8029888, hi) := by
  rw [spec_wr, List.mem_append] at h
  rcases h with h | h
  · unfold wrs at h
    split at h
    · exact .inl ⟨‹k < 104›, h⟩
    · simp at h
  · split at h
    · exact .inr ⟨‹k = 90›, by simpa using h⟩
    · simp at h

theorem spec_T : ∀ k, ∀ x ∈ (spec V hi k).wr, ∀ y ∈ tabs, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := fun k x hx y hy => by
  rcases spec_mem hx with ⟨hk, hx⟩ | ⟨-, rfl⟩
  · exact cwT k hk x hx y hy
  · exact .inr (tabsB y hy)

theorem spec_E : ∀ k, ∀ x ∈ (spec V hi k).wr, x.2 ≤ 8013720 ∨ 8013728 ≤ x.1 := fun k x hx => by
  rcases spec_mem hx with ⟨hk, hx⟩ | ⟨-, rfl⟩
  · exact cwE k hk x hx
  · right
    show 8013728 ≤ 8029888
    decide

theorem spec_lo : ∀ k, ∀ x ∈ (spec V hi k).wr, 7938368 ≤ x.1 := fun k x hx => by
  rcases spec_mem hx with ⟨hk, hx⟩ | ⟨-, rfl⟩
  · exact (cwB k hk x hx).1
  · show 7938368 ≤ 8029888
    decide

theorem spec_B {s : Nat} (hhi : 8029888 ≤ hi) (hhs : hi + 1024 ≤ s) :
    ∀ k, ∀ x ∈ (spec V hi k).wr, x.2 ≤ s - 1024 := fun k x hx => by
  rcases spec_mem hx with ⟨hk, hx⟩ | ⟨-, rfl⟩
  · have := (cwB k hk x hx).2
    omega
  · show hi ≤ s - 1024
    omega

theorem spec_R : ∀ k, ∀ x ∈ (spec V hi k).wr, ∀ y ∈ rd96 ++ rd97, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := fun k x hx y hy => by
  rcases spec_mem hx with ⟨hk, hx⟩ | ⟨-, rfl⟩
  · exact cwR k hk x hx y hy
  · exact .inr (rdB y hy)

/-- The constructors `Done` store nothing `spec` says. -/
theorem spec_done : ∀ m W, Done m → (spec V hi m).post W := fun m W h => by
  have hn : m ≠ 61 ∧ m ≠ 96 ∧ m ≠ 97 := by
    rcases h with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl
    · exact leasN x hx
    · exact chainsN x hx
    · decide
  unfold spec
  rw [if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2]
  split <;> trivial

/-- An earlier constructor's intervals are apart from those of `cw j` (but `90`'s from `103`'s). -/
theorem sepC {j k : Nat} (hkj : k < j) (hj : j < 104) (hn : ¬ (k = 90 ∧ j = 103)) :
    ∀ x ∈ (spec V hi k).wr, ∀ y ∈ cw j, x.2 ≤ y.1 ∨ y.2 ≤ x.1 := fun x hx y hy => by
  rcases spec_mem hx with ⟨-, hx⟩ | ⟨rfl, rfl⟩
  · rcases cwS j hj k hkj with h | h
    · exact absurd h hn
    · exact h x hx y hy
  · exact .inr (cwB j hj y hy).2

/-- `hXw` of a constructor `m ≠ 90, 103`. -/
theorem spec_Xw {m : Nat} (hm : m < 103) :
    ∀ k, 3 ≤ k → k < m → ∀ x ∈ (spec V hi k).wr, ∀ y ∈ cw m, x.2 ≤ y.1 ∨ y.2 ≤ x.1 :=
  fun _ _ hkm => sepC hkm (by omega) (by omega)

/-- `hXw` of `csuTg 90`. -/
theorem spec_X90 :
    ∀ k, 3 ≤ k → k < 90 → ∀ x ∈ (spec V hi k).wr, ∀ y ∈ c90Wr xl 1 ++ exH hi, x.2 ≤ y.1 ∨ y.2 ≤ x.1 :=
  fun k _ hk x hx y hy => by
    rw [exH, ← List.append_assoc, List.mem_append] at hy
    rcases hy with hy | hy
    · exact sepC (j := 90) hk (by decide) (by omega) x hx y hy
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      subst hy
      rcases spec_mem hx with ⟨hk', hx⟩ | ⟨h, -⟩
      · exact .inl (cwB k hk' x hx).2
      · omega

/-- `hXw` of `csuTg 103`: `90`'s post is `True`. -/
theorem spec_X103 : ∀ k, 3 ≤ k → k < 103 →
    (∀ U, (spec V hi k).post U) ∨ ∀ x ∈ (spec V hi k).wr, ∀ y ∈ cw 103, x.2 ≤ y.1 ∨ y.2 ≤ x.1 :=
  fun k _ hk => by
    by_cases h : k = 90
    · subst h
      exact .inl fun _ => trivial
    · exact .inr (sepC hk (by decide) (by omega))

/-- `hXr` of `csuTg 96`. -/
theorem spec_R96 : ∀ k, 3 ≤ k → k < 96 → ∀ x ∈ (spec V hi k).wr, ∀ y ∈ rd96, x.2 ≤ y.1 ∨ y.2 ≤ x.1 :=
  fun k _ _ x hx y hy => spec_R k x hx y (List.mem_append_left _ hy)

/-- `hXr` of `csuTg 97`. -/
theorem spec_R97 : ∀ k, 3 ≤ k → k < 97 → ∀ x ∈ (spec V hi k).wr, ∀ y ∈ rd97, x.2 ≤ y.1 ∨ y.2 ≤ x.1 :=
  fun k _ _ x hx y hy => spec_R k x hx y (List.mem_append_right _ hy)

/-- `csuTg 90`'s spec has the shared words. -/
theorem spec_Sh : ∀ x, InR (cxSh xl ++ exH hi) x → InR (spec V hi 90).wr x := fun x h => by
  show InR (c90Wr xl 1 ++ exH hi) x
  simp only [cxSh, exH, exC, c90Wr, List.cons_append, List.nil_append, InR] at h ⊢
  omega

theorem spec_P90 : ∀ U, (spec V hi 90).post U := fun _ => trivial

/-- The constructors but `90` and `103` store none of the shared words. -/
theorem spec_ShD {m : Nat} (hm : m ≤ 103) :
    ∀ k, 3 ≤ k → k < m → k ≠ 90 → ∀ x, InR (spec V hi k).wr x → ¬ InR (cxSh xl ++ exH hi) x :=
  fun k _ hkm hk9 x hx => InR_sep hx fun a ha b hb => by
    rcases spec_mem ha with ⟨hk, ha⟩ | ⟨h, -⟩
    · rw [exH, ← List.append_assoc, List.mem_append] at hb
      rcases hb with hb | hb
      · exact cwX k (by omega) hk9 a ha b hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        exact .inl (cwB k hk a ha).2
    · exact absurd h hk9

end FV7z.Ctor
