import FV7z.Nps.Defs
/-!
# `CStdOutStream::NormalizePrint_UString (const UString &)`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`),
then the code to the next cut points or `call`s, keeping `rsp`, `rbx`, `r14`, `r15` (`Fr`); `vc_110` checks the
guard (`hc`) and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Nps
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the three pushes, `rbp` = `this`, `sub rsp, 0x30`, the stack guard stored, `r12` = `rsp`, `rdi` = the
local `UString`, to the `call` of its copy constructor at 38. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P3 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 40#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 38 g' fl (Vst (P3 V g) (aR g.rsp + 40#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P3] at hcn hs1 hs2 hs3 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hcl
    | with_reducible exact hw
    | sstep)

/-- Back from the copy constructor: `rsi` = the local `UString`, `rdi` = `this`, to the `call` of
`Normalize_UString` at 49. -/
theorem vc_43 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 49 g' fl V) :
    W_43 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_43, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | sstep)

/-- Back from `Normalize_UString`: `r13` = `rdi` = the local `AString`, to the `call` of its constructor at 62. -/
theorem vc_54 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 62 g' fl V) :
    W_54 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_54, o2]
  all_goals repeat' (first
    | refine h _ ?_ _
    | sstep)

/-- Back from `AString::AString ()`: `rdx` = the `AString`, `rsi` = the `UString`, `rdi` = `this`, to the `call` of
`PrintUString` at 76. -/
theorem vc_67 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 76 g' fl V) :
    W_67 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_67, o3]
  all_goals repeat' (first
    | refine h _ ?_ _
    | sstep)

/-- Back from `PrintUString`: the `AString`'s characters (null to 96), else to the `call` of `delete []` at 91. -/
theorem vc_81 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) (h96 : ∀ g', Fr g g' → ∀ fl, Q 96 g' fl V)
    (h91 : ∀ g', Fr g g' → ∀ fl, Q 91 g' fl V) :
    W_81 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 h96 h91 ⊢
  wpx [W_81, o4]
  all_goals repeat' (first
    | refine h96 _ ?_ _
    | refine h91 _ ?_ _
    | with_reducible exact f16
    | sstep)

/-- The `UString`'s characters (null to 110), else to the `call` of `delete []` at 105. -/
theorem vc_96 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h110 : ∀ g', Fr g g' → ∀ fl, Q 110 g' fl V)
    (h105 : ∀ g', Fr g g' → ∀ fl, Q 105 g' fl V) :
    W_96 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h110 h105 ⊢
  wpx [W_96, o5]
  all_goals repeat' (first
    | refine h110 _ ?_ _
    | refine h105 _ ?_ _
    | with_reducible exact f0
    | sstep)

/-- The stack guard checked (`hc`), `add rsp, 0x30`, the three pops, to the `ret` at 135. -/
theorem vc_110 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64)) (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 48#64 + 8 + 8 + 8 → g'.rbp = rdq(V, g.rsp + 48#64) →
      g'.r12 = rdq(V, g.rsp + 48#64 + 8) → g'.r13 = rdq(V, g.rsp + 48#64 + 8 + 8) →
      g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 135 g' fl V) :
    W_110 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 f1 f2 f3 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_110, W_126, o6, o7, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | apply And.intro
    | intro _)

end FV7z.Nps
