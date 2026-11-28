import FV7z.Cps.Defs
/-!
# `NCommandLineParser::CParser::ParseString`: the pieces up to the end of the switch loop (PLAN.md §M, M1)

The verification conditions of the pieces from the entry to 183 (`FV7z/Cps/Defs.lean` for the layout): the
prologue (0, 12), the stack guard and the checks of `s` (28, 55), the switch loop (78..183) with the strlen of each
key (96, 112), the longest prefix so far (126..170).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- The first four pushes, to 12. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (h : ∀ g', g'.rsp = g.rsp - 8 - 8 - 8 - 8 → g'.rbp = g.rbp → g'.rbx = g.rbx → g'.rdi = g.rdi →
      g'.rsi = g.rsi → g'.rdx = g.rdx → g'.rcx = g.rcx → ∀ fl, Q 12 g' fl (P4 V g)) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [P4] at hs1 hs2 hs3 hs4 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | cstep)

/-- `rbp`, `rbx` pushed, `sub rsp, 0x48`, `this` and `switchForms` stored in the frame, to 28. -/
theorem vc_12 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 72#64 + 24#64) i))
    (w16 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 72#64 + 16#64) i))
    (h : ∀ g', g'.rsp = g.rsp - 8 - 8 - 72#64 → g'.rsi = g.rsi → g'.rcx = g.rcx → ∀ fl, Q 28 g' fl (B12 V g)) :
    W_12 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [B12] at hs1 hs2 w24 w16 h ⊢
  wpx [W_12, o1]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | cstep)

/-- The stack guard (`cn`, named) stored at `rsp + 56`, `eax` = `s._len`: 0 to 328; else to 55. -/
theorem vc_28 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(V, fb + 40#64) = cn) (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w56 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 56#64) i))
    (fl8 : ∀ i < 4, Foot F.data (Addr.add (g.rsi + 8#64) i))
    (h328 : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 328 g' fl (Vst V (g.rsp + 56#64) (toBytesLE cn 8)))
    (h55 : ∀ g', g'.rsp = g.rsp → g'.rsi = g.rsi → g'.rcx = g.rcx →
      rdd(Vst V (g.rsp + 56#64) (toBytesLE cn 8), g.rsi + 8#64) ≠ 0 →
      ∀ fl, Q 55 g' fl (Vst V (g.rsp + 56#64) (toBytesLE cn 8))) :
    W_28 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w56 fl8 h328 h55 ⊢
  cpx [W_28, o2, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h328 _ ?_ _
    | refine h55 _ ?_ ?_ ?_ ?_ _
    | cstep)

/-- `rax` = `s._chars`, `r14` = `s`: the first character not '-' to 328; else `numSwitches` 0 to 735, or to 78. -/
theorem vc_55 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsi i)) (fc : ∀ i < 4, Foot F.data (Addr.add rdq(V, g.rsi) i))
    (h328 : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 328 g' fl V)
    (h735 : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 735 g' fl V)
    (h78 : ∀ g', g'.rsp = g.rsp → g'.r14 = g.rsi → g'.rcx = g.rcx → BitVec.setWidth 32 g.rcx ≠ 0 →
      ∀ fl, Q 78 g' fl V) :
    W_55 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 fc h328 h735 h78 ⊢
  cpx [W_55, W_70, o3, o4, Op.cmpmi]
  all_goals repeat' (first
    | refine h328 _ ?_ _
    | refine h735 _ ?_ _
    | refine h78 _ ?_ ?_ ?_ ?_ _
    | cstep)

/-- `r13` = `switchForms`, `r12` = 0, `r15d` = -1, `rbp` = 0: to the loop at 96. -/
theorem vc_78 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.rcx = g.rcx → g'.r13 = rdq(V, g.rsp + 16#64) →
      g'.r12 = 0#64 → BitVec.setWidth 32 g'.r15 = 4294967295#32 → g'.rbp = 0#64 → ∀ fl, Q 96 g' fl V) :
    W_78 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 h ⊢
  cpx [W_78, o5]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | (simp only [sw_64_32]; done)
    | cstep)

/-- `rsi` = the key: empty, `ebx` = `eax` = 0 to 126; else `eax` = 0 to the strlen loop at 112. -/
theorem vc_96 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f13 : ∀ i < 8, Foot F.data (Addr.add g.r13 i)) (fk : ∀ i < 1, Foot F.data (Addr.add rdq(V, g.r13) i))
    (h126 : ∀ g', Lk g g' → g'.rbx = 0#64 → g'.rax = 0#64 → ∀ fl, Q 126 g' fl V)
    (h112 : ∀ g', Lk g g' → g'.rsi = rdq(V, g.r13) → g'.rax = 0#64 → V rdq(V, g.r13) ≠ 0#8 →
      ∀ fl, Q 112 g' fl V) :
    W_96 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f13 fk h126 h112 ⊢
  cpx [W_96, W_376, W_109, o6, o29, o7, Op.cmpmi]
  all_goals repeat' (first
    | refine h126 _ ?_ ?_ ?_ _
    | refine h112 _ ?_ ?_ ?_ ?_ _
    | cstep)

/-- One round of the strlen loop: the byte at `rsi + nx rax` not 0, round again; else `ebx` = its index, to 126. -/
theorem vc_112 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fk : ∀ i < 1, Foot F.data (Addr.add (g.rsi + nx g.rax) i))
    (h112 : ∀ g', Lk g g' → g'.rsi = g.rsi → g'.rax = nx g.rax → V (g.rsi + nx g.rax) ≠ 0#8 →
      ∀ fl, Q 112 g' fl V)
    (h126 : ∀ g', Lk g g' → g'.rbx = nx g.rax → ∀ fl, Q 126 g' fl V) :
    W_112 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [nx] at fk h112 h126 ⊢
  cpx [W_112, W_124, o8, o9, Op.cmpmi]
  all_goals repeat' (first
    | refine h112 _ ?_ ?_ ?_ ?_ _
    | refine h126 _ ?_ ?_ _
    | cstep)

/-- The key's length against the longest so far, `eax` + 1 against `s._len`: to 170; else `ecx` stored at
`rsp + 12`, `rdi` = `s._chars + 4`, to the `call` at 151. -/
theorem vc_126 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.r14 + 8#64) i)) (f0 : ∀ i < 8, Foot F.data (Addr.add g.r14 i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 12#64) i))
    (h170 : ∀ g', Lk g g' → g'.rbx = g.rbx → ∀ fl, Q 170 g' fl V)
    (h151 : ∀ g', Lk g g' → g'.rbx = g.rbx → g'.rdi = rdq(V, g.r14) + 4#64 →
      ∀ fl, Q 151 g' fl (Vst V (g.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 g.rcx) 4))) :
    W_126 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 f0 w12 h170 h151 ⊢
  cpx [W_126, W_131, W_140, o10, o11, o12]
  all_goals repeat' (first
    | refine h170 _ ?_ ?_ _
    | refine h151 _ ?_ ?_ ?_ _
    | cstep)

/-- `ecx` back from `rsp + 12`; `al` not 0: `r15d` = `ebx`, `ebp` = `r12d`; to 170. -/
theorem vc_156 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r13 = g.r13 → g'.r12 = g.r12 →
      g'.rcx = BitVec.setWidth 64 rdd(V, g.rsp + 12#64) →
      (g'.r15 = BitVec.setWidth 64 (BitVec.setWidth 32 g.r15) ∧ g'.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp) ∨
        g'.r15 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) ∧
          g'.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 g.r12)) →
      ∀ fl, Q 170 g' fl V) :
    W_156 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 h ⊢
  by_cases hc : (BitVec.setWidth 8 rax &&& BitVec.setWidth 8 rax == 0) = true
  · wpx [W_156, o13, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ (Or.inl ⟨?_, ?_⟩) _
      | cstep)
  · have hc' := Bool.of_not_eq_true hc
    wpx [W_156, o13, hc', Bool.not_false, eq_self_iff_true, ↓reduceIte]
    all_goals repeat' (first
      | refine h _ ?_ ?_ ?_ ?_ ?_ (Or.inr ⟨?_, ?_⟩) _
      | cstep)

/-- `r12d` + 1, `r13` + 24: not `numSwitches`, round again at 96; else to 183. -/
theorem vc_170 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h96 : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.rcx = g.rcx → g'.r15 = g.r15 → g'.rbp = g.rbp →
      g'.r13 = g.r13 + 24#64 → g'.r12 = BitVec.setWidth 64 (BitVec.setWidth 32 g.r12 + 1#32) →
      ¬BitVec.setWidth 32 g.rcx = BitVec.setWidth 32 g.r12 + 1#32 → ∀ fl, Q 96 g' fl V)
    (h183 : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.rbp = g.rbp →
      BitVec.setWidth 32 g.rcx = BitVec.setWidth 32 g.r12 + 1#32 → ∀ fl, Q 183 g' fl V) :
    W_170 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h96 h183 ⊢
  cpx [W_170, o14]
  all_goals repeat' (first
    | refine h96 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine h183 _ ?_ ?_ ?_ ?_ ?_ _
    | cstep)

/-- No key found (`r15d` = -1) to 735; else `r8d` = its index, `rbx` = `switchForms`, `rdi` = `this`, to 206. -/
theorem vc_183 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (h735 : ∀ g', g'.rsp = g.rsp → ∀ fl, Q 735 g' fl V)
    (h206 : ∀ g', g'.rsp = g.rsp → g'.r14 = g.r14 → g'.r15 = g.r15 →
      g'.r8 = BitVec.setWidth 64 (BitVec.setWidth 32 g.rbp) → g'.rbx = rdq(V, g.rsp + 16#64) →
      g'.rdi = rdq(V, g.rsp + 24#64) → ¬BitVec.setWidth 32 g.r15 = 4294967295#32 → ∀ fl, Q 206 g' fl V) :
    W_183 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 f24 h735 h206 ⊢
  cpx [W_183, W_193, o15, o16]
  all_goals repeat' (first
    | refine h735 _ ?_ _
    | refine h206 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | cstep)

end Pieces

end FV7z.Cps
