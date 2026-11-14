import FV7z.Ipa.Blocks
import FV7z.Lemmas.Wp
/-!
# The cut points of `_dl_init_paths` (PLAN.md G3, startup)

The 9 cut points: the entry and where two ways meet. From each, the blocks up to the next cut points as one piece
(`W_*`, with its `Sp`, `c_*`): a block's straight-line code, then at its jump's exits the next block's condition, or `Q`
at a cut point or at an offset the proof does not go past (53, 70, 148, 276, 451, 454, 546, 617, 664, 718, 743, 769,
774, 790, 795; the `ret`). `Wt` is the table of the cut points' conditions, `spAll` its `Sp`s, for `Seg.cfg`. Generated
by `tools/blk_gen.py`.
-/
namespace FV7z.Ipa
set_option linter.unusedVariables false
open ZellicX86 Decode FV7z.Leaf

def W_0 : Wpt := fun F Wl Q => wp F Wl o0 (Q 53)
theorem c_0 (prof : Profile) : Sp prof ipa ipa_at 0 W_0 := Sp.blkA_then (blk_0 prof) (Sp.skip 53)

def W_58 : Wpt := fun F Wl Q => wp F Wl o1 (Q 70)
theorem c_58 (prof : Profile) : Sp prof ipa ipa_at 58 W_58 := Sp.blkA_then (blk_58 prof) (Sp.skip 70)

def W_91 : Wpt := fun F Wl Q => wp F Wl o3 (Q 148)
theorem c_91 (prof : Profile) : Sp prof ipa ipa_at 91 W_91 := Sp.blkA_then (blk_91 prof) (Sp.skip 148)

def W_75 : Wpt := fun F Wl Q => wp F Wl o2 fun g f V =>
    (f.cond 4 = true → Q 795 g (rfz f) V) ∧
    (f.cond 4 = false → W_91 F Wl Q g (rfz f) V)
theorem c_75 (prof : Profile) : Sp prof ipa ipa_at 75 W_75 :=
  Sp.blkA_then (blk_75 prof) (Sp.jcc_then (spj_85 prof) (Sp.skip 795) (c_91 prof))

def W_168 : Wpt := fun F Wl Q => wp F Wl o5 fun g f V =>
    (f.cond 4 = true → Q 281 g (rfz f) V) ∧
    (f.cond 4 = false → Q 267 g (rfz f) V)
theorem c_168 (prof : Profile) : Sp prof ipa ipa_at 168 W_168 :=
  Sp.blkA_then (blk_168 prof) (Sp.jcc_then (spj_265 prof) (Sp.skip 281) (Sp.skip 267))

def W_153 : Wpt := fun F Wl Q => wp F Wl o4 fun g f V =>
    (f.cond 4 = true → Q 774 g (rfz f) V) ∧
    (f.cond 4 = false → W_168 F Wl Q g (rfz f) V)
theorem c_153 (prof : Profile) : Sp prof ipa ipa_at 153 W_153 :=
  Sp.blk_then (blk_153 prof) (Sp.jcc_then (spj_162 prof) (Sp.skip 774) (c_168 prof))

def W_267 : Wpt := fun F Wl Q => wp F Wl o6 (Q 276)
theorem c_267 (prof : Profile) : Sp prof ipa ipa_at 267 W_267 := Sp.blk_then (blk_267 prof) (Sp.skip 276)

def W_281 : Wpt := fun F Wl Q => wp F Wl o7 fun g f V =>
    (f.cond 4 = true → Q 384 g (rfz f) V) ∧
    (f.cond 4 = false → Q 293 g (rfz f) V)
theorem c_281 (prof : Profile) : Sp prof ipa ipa_at 281 W_281 :=
  Sp.blkA_then (blk_281 prof) (Sp.jcc_then (spj_291 prof) (Sp.skip 384) (Sp.skip 293))

def W_372 : Wpt := fun F Wl Q => wp F Wl o10 fun g f V =>
    (f.cond 5 = true → Q 293 g (rfz f) V) ∧
    (f.cond 5 = false → Q 384 g (rfz f) V)
theorem c_372 (prof : Profile) : Sp prof ipa ipa_at 372 W_372 :=
  Sp.blkA_then (blk_372 prof) (Sp.jcc_then (spj_382 prof) (Sp.skip 293) (Sp.skip 384))

def W_362 : Wpt := fun F Wl Q => wp F Wl o9 fun g f V =>
    (f.cond 5 = true → Q 267 g (rfz f) V) ∧
    (f.cond 5 = false → W_372 F Wl Q g (rfz f) V)
theorem c_362 (prof : Profile) : Sp prof ipa ipa_at 362 W_362 :=
  Sp.blk_then (blk_362 prof) (Sp.jcc_then (spj_370 prof) (Sp.skip 267) (c_372 prof))

def W_293 : Wpt := fun F Wl Q => wp F Wl o8 fun g f V =>
    (f.cond 5 = true → Q 743 g (rfz f) V) ∧
    (f.cond 5 = false → W_362 F Wl Q g (rfz f) V)
theorem c_293 (prof : Profile) : Sp prof ipa ipa_at 293 W_293 :=
  Sp.blkA_then (blk_293 prof) (Sp.jcc_then (spj_356 prof) (Sp.skip 743) (c_362 prof))

def W_416 : Wpt := fun F Wl Q => wp F Wl o12 fun g f V =>
    (f.cond 5 = true → Q 451 g (rfz f) V) ∧
    (f.cond 5 = false → Q 425 g (rfz f) V)
theorem c_416 (prof : Profile) : Sp prof ipa ipa_at 416 W_416 :=
  Sp.blk_then (blk_416 prof) (Sp.jcc_then (spj_423 prof) (Sp.skip 451) (Sp.skip 425))

def W_384 : Wpt := fun F Wl Q => wp F Wl o11 fun g f V =>
    (f.cond 4 = true → Q 425 g (rfz f) V) ∧
    (f.cond 4 = false → W_416 F Wl Q g (rfz f) V)
theorem c_384 (prof : Profile) : Sp prof ipa ipa_at 384 W_384 :=
  Sp.blkA_then (blk_384 prof) (Sp.jcc_then (spj_414 prof) (Sp.skip 425) (c_416 prof))

def W_425 : Wpt := fun F Wl Q => wp F Wl o13 (Q 450)
theorem c_425 (prof : Profile) : Sp prof ipa ipa_at 425 W_425 := Sp.blkA_then (blk_425 prof) (Sp.skip 450)

/-- The cut points. -/
def cuts : List Nat := [0, 58, 75, 153, 267, 281, 293, 384, 425]

/-- What the code from a cut point needs for `Q` at the next ones. -/
def Wt (ℓ : Nat) : Wpt :=
  if ℓ = 0 then W_0 else
  if ℓ = 58 then W_58 else
  if ℓ = 75 then W_75 else
  if ℓ = 153 then W_153 else
  if ℓ = 267 then W_267 else
  if ℓ = 281 then W_281 else
  if ℓ = 293 then W_293 else
  if ℓ = 384 then W_384 else
  if ℓ = 425 then W_425 else
  fun _ _ _ _ _ _ => False

theorem spAll (prof : Profile) (ℓ : Nat) : Sp prof ipa ipa_at ℓ (Wt ℓ) :=
  Sp.table (c_0 prof) <|
  Sp.table (c_58 prof) <|
  Sp.table (c_75 prof) <|
  Sp.table (c_153 prof) <|
  Sp.table (c_267 prof) <|
  Sp.table (c_281 prof) <|
  Sp.table (c_293 prof) <|
  Sp.table (c_384 prof) <|
  Sp.table (c_425 prof) <|
  Sp.never ℓ

end FV7z.Ipa
