import FV7z.Fsv.Defs
/-!
# `fs2us (const char *)`, the twin: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`)
to the `call` of the conversion; `vc_36` checks the guard (`hc`), sets `rax` = the slot and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Fsv
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the push, `edx` = 0, `r12` = the slot, `sub rsp, 0x10`, the stack guard stored, `eax` = 0, to the
`call` of the conversion at 31. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P1 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.rbp = g.rbp → g'.r12 = g.rdi → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 31 g' fl (Vst (P1 V g) (aR g.rsp + 8#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P1] at hcn hs1 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hcl
    | with_reducible exact hw
    | fsvstep)

/-- Back from the conversion: the stack guard checked (`hc`), `add rsp, 0x10`, `rax` = the slot, the pop, to the
`ret` at 61. -/
theorem vc_36 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h : ∀ g', g'.rsp = g.rsp + 16#64 + 8 → g'.rax = g.r12 → g'.r12 = rdq(V, g.rsp + 16#64) → g'.rbx = g.rbx →
      g'.rbp = g.rbp → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 61 g' fl V) :
    W_36 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 f1 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_36, W_52, o1, o2, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fcl
    | with_reducible exact f1
    | apply And.intro
    | intro _)

end FV7z.Fsv
