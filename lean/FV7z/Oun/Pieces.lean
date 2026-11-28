import FV7z.Oun.Defs
/-!
# `CStdOutStream::operator<< (unsigned)`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`),
then the code with `r12` = `this`, to the next `call`, keeping `rsp`, `rbx`, `r12`..`r15` (`Fr`); `vc_55` checks the
guard (`hc`), sets `rax` = `this` and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Olg (P2 Fr)
namespace FV7z.Oun
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, `push r12`, `r12` = `this`, `edi` = `number`, `push rbp`, `sub rsp, 0x28`, the stack guard stored,
`eax` = 0, `rbp` = `rsi` = `rsp` (the local `s`), to the `call` of `ConvertUInt32ToString` at 38. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P2 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rbx → g'.r12 = g.rdi → g'.r13 = g.r13 → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 38 g' fl (Vst (P2 V g) (aR g.rsp + 24#64) (toBytesLE cn 8))) :
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
    | ostep)

/-- Back from `ConvertUInt32ToString`: `rsi` = `this->_stream` (8 bytes at `r12`), `rdi` = `s` (`rbp`), to the
`call` of `fputs` at 50. -/
theorem vc_43 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 8, Foot F.data (Addr.add g.r12 i)) (h : ∀ g', Fr g g' → ∀ fl, Q 50 g' fl V) :
    W_43 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 h ⊢
  wpx [W_43, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact f12
    | ostep)

/-- The stack guard checked (`hc`), `add rsp, 0x28`, `rax` = `this`, the two pops, to the `ret` at 81. -/
theorem vc_55 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 40#64 + 8 + 8 → g'.rax = g.r12 → g'.rbp = rdq(V, g.rsp + 40#64) →
      g'.r12 = rdq(V, g.rsp + 40#64 + 8) → g'.rbx = g.rbx → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 81 g' fl V) :
    W_55 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 f1 f2 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_55, W_71, o2, o3, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | apply And.intro
    | intro _)

end FV7z.Oun
