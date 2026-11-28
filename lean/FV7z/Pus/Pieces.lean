import FV7z.Pus.Defs
/-!
# `CStdOutStream::PrintUString`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0`), the arguments of `fputs` (`vc_21`,
keeping `rsp`, `rbx`, `rbp`, `r12`..`r15`: `Fr`), the epilogue (`vc_33`: the pops).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pus
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, `push rbp`, `rbp` = `this`, `push rbx`, `rbx` = `temp`, `sub rsp, 8`, to the `call` of
`Convert_UString_to_AString` at 16. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdx → g'.rbp = g.rdi → g'.r12 = g.r12 → g'.r13 = g.r13 →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 16 g' fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V0] at hs1 hs2 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | ostep)

/-- Back from `Convert_UString_to_AString`: `rsi` = `this->_stream` (8 bytes at `rbp`), `rdi` = `temp._chars`
(8 bytes at `rbx`), to the `call` of `fputs` at 28. -/
theorem vc_21 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f5 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (f3 : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 28 g' fl V) :
    W_21 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f5 f3 h ⊢
  wpx [W_21, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact f5
    | with_reducible exact f3
    | ostep)

/-- `add rsp, 8`, the two pops, to the `ret` at 39. -/
theorem vc_33 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8#64 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 8#64) → g'.rbp = rdq(V, g.rsp + 8#64 + 8) →
      g'.r12 = g.r12 → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 39 g' fl V) :
    W_33 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 h ⊢
  wpx [W_33, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f1
    | with_reducible exact f2
    | apply And.intro
    | intro _)

end FV7z.Pus
