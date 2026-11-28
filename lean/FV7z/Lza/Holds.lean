import FV7z.Lza.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `LzmaDec_Allocate` (PLAN.md §M, M1): the straight-line pieces

7-Zip 26.06's `LzmaDec_Allocate (CLzmaDec *p, const Byte *props, unsigned propsSize, ISzAllocPtr alloc)` at
`0x42bf80` in `7zzs` (`C/LzmaDec.c`; `objdump -d`), `S` the stack pointer at the entry: `push r13; mov r13, rcx; push
r12; push rbp; mov rbp, rdi; push rbx; sub rsp, 0x18`, the stack guard (`fs:0x28`) at `aR S + 8`, `rdi` = `aR S`
(`propNew`, a `CLzmaProps`: `lc`, `lp`, `pb` bytes at `aR S`, `aR S + 1`, `aR S + 2`, `dicSize` at `aR S + 4`); the
`call` (39) of `LzmaProps_Decode` (`Lpd`); `mov r12d, eax`, a nonzero result to the guard's check (51) and the
epilogue (71..84, `ret`); else `rdx`, `rsi` = `propNew.lp`, `propNew.lc`, `rcx` = `alloc`, `rdi` = `p`, the `call`
(103) of `LzmaDec_AllocateProbs2` (`Lap`); a nonzero result to 51; else `dicBufSize` from `dicSize` (108..196: above
1 GiB by 256, else rounded up to 4 KiB below 4 MiB and to 1 MiB from there, at least `dicSize`); unless `p->dic`
(`p + 24`) is set with that size (`p + 32`, 198), `alloc->Free (alloc, p->dic)` (204, `call [r13 + 8]`), `p->dic` = 0,
`alloc->Alloc (alloc, dicBufSize)` (211, `call [r13]`); a null result `LzmaDec_FreeProbs (p, alloc)` (272..284,
`Lfp`) and `SZ_ERROR_MEM` (2) in `r12`; else (238) `p->dicBufSize`, `p->prop` = `propNew`, to 51. Not covered:
`__stack_chk_fail` (294).

This module has the pieces that need no callee: `vc_0` (the frame, to the first `call`), `vc_204`, `vc_211`,
`vc_238`, `vc_272`. The pieces with branches and the run through the callees: `FV7z/Lza/Run.lean`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lza
set_option linter.unusedVariables false

/-- The stack pointer after the four pushes and `sub rsp, 0x18`; `propNew` there. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 24#64

/-- The bytes after the four pushes (`r13`, `r12`, `rbp`, `rbx`). -/
abbrev P4 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, `r13` = `alloc`, `rbp` = `p`, the frame, the stack guard stored, `rdi` = `rsp`, to the first `call`.
The guard's value is named (`cn`). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P4 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 8#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rdi = aR g.rsp → g'.rbp = g.rdi → g'.r13 = g.rcx → g'.rbx = g.rbx →
      g'.r12 = g.r12 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 39 g' fl (Vst (P4 V g) (aR g.rsp + 8#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P4] at hcn hs1 hs2 hs3 hs4 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hcl
    | with_reducible exact hw
    | apply And.intro
    | intro _)

/-- `mov rdi, r13`, to `alloc->Free`. -/
theorem vc_204 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 207 { g with rdi := g.r13 } fl V) :
    W_204 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_204, o9]
  all_goals repeat' (first
    | exact h _
    | apply And.intro
    | intro _)

/-- `p->dic = 0; rsi = dicBufSize; rdi = alloc`, to `alloc->Alloc`. -/
theorem vc_211 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 24#64) i))
    (h : ∀ fl, Q 225 { g with rsi := g.rbx, rdi := g.r13 } fl (Vst V (g.rbp + 24#64) (toBytesLE 0#64 8))) :
    W_211 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w24 h ⊢
  wpx [W_211, o10]
  all_goals repeat' (first
    | exact h _
    | with_reducible assumption
    | apply And.intro
    | intro _)

/-- `rax` = the 8 bytes of `propNew`; `p->dicBufSize = rbx; p->prop = propNew`, to the guard's check. -/
theorem vc_238 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (w32 : ∀ i < 8, Foot Wl (Addr.add (g.rbp + 32#64) i)) (w0 : ∀ i < 8, Foot Wl (Addr.add g.rbp i))
    (h : ∀ fl, Q 51 { g with rax := rdq(V, g.rsp) } fl
      (Vst (Vst V (g.rbp + 32#64) (toBytesLE g.rbx 8)) g.rbp (toBytesLE rdq(V, g.rsp) 8))) :
    W_238 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 w32 w0 h ⊢
  wpx [W_238, o12]
  all_goals repeat' (first
    | exact h _
    | with_reducible assumption
    | apply And.intro
    | intro _)

/-- `rsi = alloc; rdi = p; r12d = SZ_ERROR_MEM`, to `LzmaDec_FreeProbs`. -/
theorem vc_272 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsi = g.r13 → g'.rdi = g.rbp → g'.r12 = 2#64 → g'.rsp = g.rsp → g'.rbx = g.rbx →
      g'.rbp = g.rbp → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 284 g' fl V) :
    W_272 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_272, o14]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | exact rfl
    | decide
    | apply And.intro
    | intro _)

end FV7z.Lza
