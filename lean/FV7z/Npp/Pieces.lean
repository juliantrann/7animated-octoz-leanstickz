import FV7z.Npp.Defs
/-!
# `CStdOutStream::NormalizePrint_UString_Path (const UString &)`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`),
then the code to the next cut points or `call`s, keeping `rsp`, `rbx`, `r15` (`Fr`); `vc_107` checks the guard
(`hc`) and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Npp
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the four pushes, `r12` = `s`, `rbp` = `this`, `sub rsp, 0x38`, the stack guard stored, `r13` = `rsp`,
`r14` = `rsp + 16`, `rdi` = the local `UString`, to the `call` of its constructor at 48. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P4 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 40#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 →
      ∀ fl, Q 48 g' fl (Vst (P4 V g) (aR g.rsp + 40#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P4] at hcn hs1 hs2 hs3 hs4 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hcl
    | with_reducible exact hw
    | nstep)

/-- Back from `UString::UString ()`: `rdi` = the local `AString`, to the `call` of its constructor at 56. -/
theorem vc_53 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 56 g' fl V) :
    W_53 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_53, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | nstep)

/-- Back from `AString::AString ()`: `rcx` = the `AString`, `rdx` = the `UString`, `rsi` = `s`, `rdi` = `this`, to
the `call` of `NormalizePrint_UString_Path` at 73. -/
theorem vc_61 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 73 g' fl V) :
    W_61 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_61, o2]
  all_goals repeat' (first
    | refine h _ ?_ _
    | nstep)

/-- Back from `NormalizePrint_UString_Path`: the `AString`'s characters (null to 93), else to the `call` of
`delete []` at 88. -/
theorem vc_78 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) (h93 : ∀ g', Fr g g' → ∀ fl, Q 93 g' fl V)
    (h88 : ∀ g', Fr g g' → ∀ fl, Q 88 g' fl V) :
    W_78 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 h93 h88 ⊢
  wpx [W_78, o3]
  all_goals repeat' (first
    | refine h93 _ ?_ _
    | refine h88 _ ?_ _
    | with_reducible exact f16
    | nstep)

/-- The `UString`'s characters (null to 107), else to the `call` of `delete []` at 102. -/
theorem vc_93 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h107 : ∀ g', Fr g g' → ∀ fl, Q 107 g' fl V)
    (h102 : ∀ g', Fr g g' → ∀ fl, Q 102 g' fl V) :
    W_93 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h107 h102 ⊢
  wpx [W_93, o4]
  all_goals repeat' (first
    | refine h107 _ ?_ _
    | refine h102 _ ?_ _
    | with_reducible exact f0
    | nstep)

/-- The stack guard checked (`hc`), `add rsp, 0x38`, the four pops, to the `ret` at 134. -/
theorem vc_107 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64)) (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 56#64 + 8 + 8 + 8 + 8 → g'.rbp = rdq(V, g.rsp + 56#64) →
      g'.r12 = rdq(V, g.rsp + 56#64 + 8) → g'.r13 = rdq(V, g.rsp + 56#64 + 8 + 8) →
      g'.r14 = rdq(V, g.rsp + 56#64 + 8 + 8 + 8) → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 134 g' fl V) :
    W_107 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 f1 f2 f3 f4 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_107, W_123, o5, o6, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | apply And.intro
    | intro _)

end FV7z.Npp
