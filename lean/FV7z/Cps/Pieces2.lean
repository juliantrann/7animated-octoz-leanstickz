import FV7z.Cps.Defs
/-!
# `NCommandLineParser::CParser::ParseString`: the pieces from the switch found to the return (PLAN.md §M, M1)

The verification conditions of the pieces from 206 (`FV7z/Cps/Defs.lean` for the layout): the form and the result
`sw` (`r12`) of the switch found (206, 221), `ThereIs`, `rem` against `MinLen` (241), `WithMinus`, `PostCharIndex`
and the switch's type (265..302, 439, 472), the end of the string (307), the result (317, 328), the stack guard and
the epilogue (331, 359), the error messages (485, 706, 735) and the `jmp`s.

The stores into `sw` are those `Ok` allows: they keep the invariant `I` of the bytes (`hcl`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

section Pieces
variable {F : Footprint} {Wl : List Rgn} {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-- `r15d` + 1 (`pos`), `rax` = 24 times the index, `r12` = `_switches._items`: to 221. -/
theorem vc_206 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.rbx = g.rbx → g'.rdi = g.rdi →
      g'.r15 = BitVec.setWidth 64 (BitVec.setWidth 32 g.r15 + 1#32) → g'.rax = sz24 g.r8 → g'.r12 = rdq(V, g.rdi) →
      ∀ fl, Q 221 g' fl V) :
    W_206 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h ⊢
  cpx [W_206, o17, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | cstep)

/-- `rbx` = the form, `r12` = `sw`: `Multi` set, or `sw.ThereIs` 0, to 241; else `rdi` = `this + 32` (the
`ErrorMessage`), to the `call` at 407. -/
theorem vc_221 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f9 : ∀ i < 1, Foot F.data (Addr.add (g.rbx + g.rax + 9#64) i))
    (fr : ∀ i < 1, Foot F.data (Addr.add (g.r12 + g.rax) i))
    (h241 : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rbx = g.rbx + g.rax →
      g'.r12 = g.r12 + g.rax → ∀ fl, Q 241 g' fl V)
    (h407 : ∀ g', g'.rsp = g.rsp → g'.rdi = g.rdi + 32#64 → ∀ fl, Q 407 g' fl V) :
    W_221 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f9 fr h241 h407 ⊢
  cpx [W_221, W_385, W_396, o18, o30, o31, Op.cmpmi]
  all_goals repeat' (first
    | refine h241 _ ?_ ?_ ?_ ?_ ?_ _
    | refine h407 _ ?_ ?_ _
    | cstep)

/-- `sw.ThereIs` = 1, `eax` = `s._len - pos` (`rem`): below `MinLen` to 706; else to 265. -/
theorem vc_241 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r14 + 8#64) i))
    (f10 : ∀ i < 1, Foot F.data (Addr.add (g.rbx + 10#64) i))
    (w0 : ∀ i < 1, Foot Wl (Addr.add g.r12 i)) (o0 : Ok g.r12 1) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h706 : ∀ g' V', I V' → g'.rsp = g.rsp → ∀ fl, Q 706 g' fl V')
    (h265 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rbx = g.rbx → g'.r12 = g.r12 →
      g'.rax = BitVec.setWidth 64 (rdd(V, g.r14 + 8#64) - BitVec.setWidth 32 g.r15) → ∀ fl, Q 265 g' fl V') :
    W_241 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f10 w0 o0 h706 h265 ⊢
  cpx [W_241, o19]
  all_goals repeat' (first
    | refine h706 _ _ ?_ ?_ _
    | refine h265 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | cstep)

/-- `sw.WithMinus` = 0, `sw.PostCharIndex` = -1, `dl` = the form's `Type`: 2 (`kString`) to 514; else to 293. -/
theorem vc_265 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 1, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (w1 : ∀ i < 1, Foot Wl (Addr.add (g.r12 + 1#64) i)) (w4 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 4#64) i))
    (o1 : Ok (g.r12 + 1#64) 1) (o4 : Ok (g.r12 + 4#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h514 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rbx = g.rbx → g'.r12 = g.r12 →
      g'.rax = g.rax → ∀ fl, Q 514 g' fl V')
    (h293 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rbx = g.rbx → g'.r12 = g.r12 →
      g'.rax = g.rax → ∀ fl, Q 293 g' fl V') :
    W_265 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 w1 w4 o1 o4 h514 h293 ⊢
  cpx [W_265, o20]
  all_goals repeat' (first
    | refine h514 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine h293 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | cstep)

/-- `Type` 3 (`kChar`) to 439; else to 302. -/
theorem vc_293 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h439 : ∀ fl, Q 439 g fl V) (h302 : ∀ fl, Q 302 g fl V) :
    W_293 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  cpx [W_293, o21]
  all_goals repeat' (first
    | refine h439 _
    | refine h302 _
    | cstep)

/-- `Type` 1 (`kMinus`) and `rem` 1: `eax` = `s[pos]`, to the `sete` at 429; else to 307. -/
theorem vc_302 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.r14 i))
    (fc : BitVec.setWidth 32 g.rax = 1#32 → ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.r14) + g.r15 * 4#64) i))
    (h307 : ∀ fl, Q 307 g fl V)
    (h429 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → ∀ fl, Q 429 g' fl V) :
    W_302 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 fc h307 h429 ⊢
  cpx [W_302, W_414, W_419, o22, o32, o33]
  all_goals repeat' (first
    | refine h307 _
    | refine h429 _ ?_ ?_ _
    | with_reducible exact fc ‹_›
    | cstep)

/-- `pos` not `s._len`: `rdi` = `this + 32`, to the `call` at 783 ("Too long switch"); else to 317. -/
theorem vc_307 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r14 + 8#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h783 : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 24#64) + 32#64 → ∀ fl, Q 783 g' fl V)
    (h317 : ∀ fl, Q 317 g fl V) :
    W_307 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f24 h783 h317 ⊢
  cpx [W_307, W_764, o23, o54]
  all_goals repeat' (first
    | refine h783 _ ?_ ?_ _
    | refine h317 _
    | cstep)

/-- `r13d` = 1 (true), to 331. -/
theorem vc_317 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 331 g' fl V) :
    W_317 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cpx [W_317, o24]
  all_goals repeat' (first
    | refine h _ ?_ _
    | cstep)

/-- `r13d` = 0 (false), to 331. -/
theorem vc_328 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 331 g' fl V) :
    W_328 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cpx [W_328, o25]
  all_goals repeat' (first
    | refine h _ ?_ _
    | cstep)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x48`, `eax` = `r13d`, `pop rbx`: to
359. -/
theorem vc_331 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 56#64) = rdq(V, fb + 40#64)) (f56 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 56#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f72 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 72#64) i))
    (h : ∀ g', g'.rsp = g.rsp + 72#64 + 8 → g'.rbx = rdq(V, g.rsp + 72#64) →
      g'.rax = BitVec.setWidth 64 (BitVec.setWidth 32 g.r13) → ∀ fl, Q 359 g' fl V) :
    W_331 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f56 f72 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_331, W_351, o26, o27, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | cstep)

/-- The five pops, to the `ret`. -/
theorem vc_359 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 + 8 + 8 → g'.rbp = rdq(V, g.rsp) → g'.r12 = rdq(V, g.rsp + 8) →
      g'.r13 = rdq(V, g.rsp + 8 + 8) → g'.r14 = rdq(V, g.rsp + 8 + 8 + 8) →
      g'.r15 = rdq(V, g.rsp + 8 + 8 + 8 + 8) → g'.rbx = g.rbx → g'.rax = g.rax → ∀ fl, Q 368 g' fl V) :
    W_359 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f1 f2 f3 f4 h ⊢
  wpx [W_359, o28]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | cstep)

/-- `jmp` to 331. -/
theorem vc_412 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 331 g fl V) :
    W_412 fb F Wl Q g f V := h _

/-- After the `sete`: to 317 or to 485, by the flags of `cmp eax, '-'`. -/
theorem vc_435 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h317 : ∀ fl, Q 317 g fl V)
    (h485 : ∀ fl, Q 485 g fl V) :
    W_435 fb F Wl Q g f V := ⟨fun _ => h317 _, fun _ => h485 _⟩

/-- `Type` 3 (`kChar`) and `rem` 1: `eax` = `s[pos]`; above 0x7f to 485; else `rdi` = `PostCharSet`, `esi` = the
character, to `FindCharPosInString` (467); `rem` not 1 to 307. -/
theorem vc_439 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.r14 i))
    (fc : BitVec.setWidth 32 g.rax = 1#32 → ∀ i < 4, Foot F.data (Addr.add (rdq(V, g.r14) + g.r15 * 4#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 16#64) i))
    (h307 : ∀ fl, Q 307 g fl V)
    (h485 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → ∀ fl, Q 485 g' fl V)
    (h467 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → ∀ fl, Q 467 g' fl V) :
    W_439 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 fc f16 h307 h485 h467 ⊢
  cpx [W_439, W_448, W_460, o32, o34, o35, Op.sxb32]
  all_goals repeat' (first
    | refine h307 _
    | refine h485 _ ?_ ?_ _
    | refine h467 _ ?_ ?_ _
    | with_reducible exact fc ‹_›
    | cstep)

/-- `sw.PostCharIndex` = `eax`: not negative to 317; else to 485. -/
theorem vc_472 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w4 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 4#64) i)) (o4 : Ok (g.r12 + 4#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h317 : ∀ g' V', I V' → g'.rsp = g.rsp → ∀ fl, Q 317 g' fl V')
    (h485 : ∀ g' V', I V' → g'.rsp = g.rsp → ∀ fl, Q 485 g' fl V') :
    W_472 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w4 o4 h317 h485 ⊢
  cpx [W_472, o36]
  all_goals repeat' (first
    | refine h317 _ _ ?_ ?_ _
    | refine h485 _ _ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | cstep)

/-- `rdi` = `this + 32`, `r13d` = 0, to the `call` at 504 ("Incorrect switch postfix"). -/
theorem vc_485 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 24#64) + 32#64 → ∀ fl, Q 504 g' fl V) :
    W_485 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f24 h ⊢
  cpx [W_485, o37]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | cstep)

/-- `jmp` to 331. -/
theorem vc_509 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 331 g fl V) :
    W_509 fb F Wl Q g f V := h _

/-- `jmp` to 317. -/
theorem vc_701 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 317 g fl V) :
    W_701 fb F Wl Q g f V := h _

/-- `rdi` = `this + 32`, `r13d` = 0, to the `call` at 725 ("Too short switch"). -/
theorem vc_706 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 24#64) + 32#64 → ∀ fl, Q 725 g' fl V) :
    W_706 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f24 h ⊢
  cpx [W_706, o52]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | cstep)

/-- `jmp` to 331. -/
theorem vc_730 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 331 g fl V) :
    W_730 fb F Wl Q g f V := h _

/-- `rdi` = `this + 32`, `r13d` = 0, to the `call` at 754 ("Unknown switch"). -/
theorem vc_735 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rdi = rdq(V, g.rsp + 24#64) + 32#64 → ∀ fl, Q 754 g' fl V) :
    W_735 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f24 h ⊢
  cpx [W_735, o53]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | cstep)

/-- `jmp` to 331. -/
theorem vc_759 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 331 g fl V) :
    W_759 fb F Wl Q g f V := h _

/-- `jmp` to 331. -/
theorem vc_788 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 331 g fl V) :
    W_788 fb F Wl Q g f V := h _

end Pieces

end FV7z.Cps
