import FV7z.Usm.Defs
/-!
# `UnicodeStringToMultiByte (const UString &, UINT)`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`),
then the code with `r12` = the slot, to the next cut points or `call`s, keeping `rsp`, `rbx`, `r12`, `r14`, `r15`
(`Fr`); `vc_67` checks the guard (`hc`), sets `rax` = the slot and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Usm
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the three pushes, `r13d` = `codePage`, `r12` = the slot, `rbp` = `src`, `sub rsp, 0x10`, the stack
guard stored, to the `call` of `AString::AString ()` at 38 (`rdi` = the slot). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P3 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.r12 = g.rdi → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 38 g' fl (Vst (P3 V g) (aR g.rsp + 8#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P3] at hcn hs1 hs2 hs3 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hcl
    | with_reducible exact hw
    | usmstep)

/-- Back from `AString::AString ()`: `r8` = the `bool`'s address, `edx` = `codePage`, `rsi` = `src`, `ecx` = `'_'`,
`rdi` = the slot, to the `call` of the conversion at 62. -/
theorem vc_43 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 62 g' fl V) :
    W_43 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_43, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | usmstep)

/-- The stack guard checked (`hc`), `add rsp, 0x10`, `rax` = the slot, the three pops, to the `ret` at 95. -/
theorem vc_67 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 16#64 + 8 + 8 + 8 → g'.rax = g.r12 → g'.rbp = rdq(V, g.rsp + 16#64) →
      g'.r12 = rdq(V, g.rsp + 16#64 + 8) → g'.r13 = rdq(V, g.rsp + 16#64 + 8 + 8) → g'.rbx = g.rbx →
      g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 95 g' fl V) :
    W_67 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 f1 f2 f3 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_67, W_83, o2, o3, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f8
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | apply And.intro
    | intro _)

end FV7z.Usm
