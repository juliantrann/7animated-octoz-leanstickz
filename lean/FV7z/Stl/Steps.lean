import FV7z.Stl.Cuts
import FV7z.Sbrk.Holds
/-!
# `____strtoul_l_internal`: the steps outside the generated pieces (PLAN.md §M, M1)

- `ret_429`, `ret_462`: the two `ret`s (after the `cmov` and the pops; after `errno` or the `endptr` store and the
  pops).
-/
namespace FV7z.Stl
open ZellicX86 Decode FV7z.Leaf

theorem pr_429 : Sbrk.pret <+: stl.drop 429 := by decide +kernel
theorem ret_429 (feat : Features) : Dec feat stl 429 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 429) (k := 0) (Sbrk.pret_0 feat) pr_429 (Nat.zero_le _)

theorem pr_462 : Sbrk.pret <+: stl.drop 462 := by decide +kernel
theorem ret_462 (feat : Features) : Dec feat stl 462 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 462) (k := 0) (Sbrk.pret_0 feat) pr_462 (Nat.zero_le _)

end FV7z.Stl
