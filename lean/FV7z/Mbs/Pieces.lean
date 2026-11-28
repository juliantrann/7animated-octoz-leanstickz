import FV7z.Mbs.Defs
/-!
# `MultiByteToUnicodeString (const AString &, UINT)`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `P3`), then the arguments of
`MultiByteToUnicodeString2` (`vc_23`, keeping `rsp`, `rbx`, `r12`, `r14`, `r15`: `Fr`); `vc_37` sets `rax` = the
slot and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Mbs
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the three pushes, `r13d` = `codePage`, `r12` = the slot, `rbp` = `src`, to the `call` of
`UString::UString ()` at 18 (`rdi` = the slot). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.r12 = g.rdi → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 18 g' fl (P3 V g)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P3] at hs1 hs2 hs3 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | mbsstep)

/-- Back from `UString::UString ()`: `edx` = `codePage`, `rsi` = `src`, `rdi` = the slot, to the `call` of
`MultiByteToUnicodeString2` at 32. -/
theorem vc_23 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 32 g' fl V) :
    W_23 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_23, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | mbsstep)

/-- Back from `MultiByteToUnicodeString2`: `rax` = the slot, the three pops, to the `ret` at 45. -/
theorem vc_37 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 → g'.rax = g.r12 → g'.rbp = rdq(V, g.rsp) →
      g'.r12 = rdq(V, g.rsp + 8) → g'.r13 = rdq(V, g.rsp + 8 + 8) → g'.rbx = g.rbx → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 45 g' fl V) :
    W_37 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 f3 h ⊢
  wpx [W_37, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | apply And.intro
    | intro _)

end FV7z.Mbs
