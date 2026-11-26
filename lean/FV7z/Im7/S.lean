import FV7z.Im7.Cuts
import FV7z.Im5.S0
/-!
# `_int_malloc` for every largebin request: the closer (PLAN.md G3, `malloc`)

`Im5.lcl` with the simp set of the piece given (`lc7 [...]`): the requests of `Im7` keep `nb` a variable, so each
verification condition has its own flag facts (`decide (nb.toNat < c) = b`, `decide (nb = c#64) = b`) to hand to
`lwp`. `exact hF` closes the frame at 2549 when it starts from one at 512 (`Im7.Pb`); `Im2.Fr.base` when it starts at
the entry (`Im7.Pa*`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Start
open FV7z.Imm (imm imm_at rd_off rd_off_self rd_below stk_f pu)
namespace FV7z.Im7

set_option hygiene false in
/-- The goals a piece leaves (`Im5.lcl`), `lwp` with the given facts. -/
macro "lc7" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| repeat' first
    | apply And.intro
    | refine Im2.Fr.vst _ hS ?_ (by decide) (by decide)
    | exact Im2.Fr.base _ _ hS
    | exact hF
    | rfl
    | with_reducible exact stk_f hsw (by decide)
    | with_reducible exact stk_f hsd (by decide)
    | with_reducible exact hgf
    | with_reducible exact htf
    | with_reducible exact D _ _ (by decide) (by decide)
    | (lwp [eaG]; with_reducible exact D _ _ (by decide) (by decide))
    | lwp [$ls,*]
    | intro (_ : Rflags)
    | intro (_ : Rflags.zf _ = false)
    | intro (_ : Rflags.zf _ = true)
    | decide)

end FV7z.Im7
