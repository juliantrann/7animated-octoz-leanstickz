import FV7z.Ufs.Defs
/-!
# `us2fs (const wchar_t *)`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`),
then the code with `r12` = the slot, to the next cut points or `call`s, keeping `rsp`, `rbx`, `r12`..`r15` (`Fr`);
`vc_68` checks the guard (`hc`), sets `rax` = the slot and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ufs
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the two pushes, `r12` = the slot, `sub rsp, 0x28`, the stack guard stored, `rbp` = `rdi` = the local
`UString`, to the `call` of its constructor at 36. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P2 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.r12 = g.rdi → g'.r13 = g.r13 → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 36 g' fl (Vst (P2 V g) (aR g.rsp + 24#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P2] at hcn hs1 hs2 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hcl
    | with_reducible exact hw
    | ufsstep)

/-- Back from `UString::UString (s)`: `edx` = 0, `rsi` = the `UString`, `rdi` = the slot, to the `call` of
`UnicodeStringToMultiByte` at 49. -/
theorem vc_41 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 49 g' fl V) :
    W_41 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_41, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | ufsstep)

/-- The `UString`'s characters (null to 68), else to the `call` of `delete []` at 63. -/
theorem vc_54 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h68 : ∀ g', Fr g g' → ∀ fl, Q 68 g' fl V)
    (h63 : ∀ g', Fr g g' → ∀ fl, Q 63 g' fl V) :
    W_54 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h68 h63 ⊢
  wpx [W_54, o2]
  all_goals repeat' (first
    | refine h68 _ ?_ _
    | refine h63 _ ?_ _
    | with_reducible exact f0
    | ufsstep)

/-- The stack guard checked (`hc`), `add rsp, 0x28`, `rax` = the slot, the two pops, to the `ret` at 94. -/
theorem vc_68 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 40#64 + 8 + 8 → g'.rax = g.r12 → g'.rbp = rdq(V, g.rsp + 40#64) →
      g'.r12 = rdq(V, g.rsp + 40#64 + 8) → g'.rbx = g.rbx → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 94 g' fl V) :
    W_68 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 f1 f2 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_68, W_84, o3, o4, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f24
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | apply And.intro
    | intro _)

end FV7z.Ufs
