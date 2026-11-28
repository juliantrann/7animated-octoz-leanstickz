import FV7z.Um2.Defs
/-!
# `UnicodeStringToMultiByte2`: the pieces (PLAN.md §M, M1)

`vc_0`: the prologue (the guard's value named `cn`) to the `call`; `vc_39`: the guard checked (`hc`), the frame
dropped, to the `ret`. Both keep the callee-saved registers (`KS`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Um2
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, `sub rsp, 0x18`, `ecx` = `'_'`, the stack guard stored at `rsp + 8`, `eax` = 0, `r8` = `rsp + 7`, to
the `call` of `UnicodeStringToMultiByte` at 34. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(V, fb + 40#64) = cn) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → KS g g' → ∀ fl, Q 34 g' fl (Vst V (aR g.rsp + 8#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR] at hcn hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible exact hcl
    | with_reducible exact hw
    | ostep)

/-- The stack guard checked (`hc`), `add rsp, 0x18`, to the `ret` at 59. -/
theorem vc_39 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (h : ∀ g', g'.rsp = g.rsp + 24#64 → KS g g' → ∀ fl, Q 59 g' fl V) :
    W_39 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_39, W_55, o1, o2, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fcl
    | apply And.intro
    | intro _)

end FV7z.Um2
