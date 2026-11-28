import FV7z.Pew.Defs
/-!
# `Print_ErrorFormatIndex_Warning`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`),
then the code with `rbx` = `arc`, `r13` = `codecs`, to the next cut points or `call`s, keeping `rsp`, `rbx`,
`r13`..`r15` (`Fr`). `vc_87` and `vc_141` read a format index and, by its sign (the cases first), the format's name;
`vc_228` checks the guard (`hc`) and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Pew
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the four pushes, `r13` = `codecs`, `rbp` = `_so`, `rbx` = `arc`, `sub rsp, 0x28`, `rcx` =
`_so->_stream`, the stack guard stored, to the `call` of `fwrite` at 59. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P4 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hso : ∀ i < 8, Foot F.data (Addr.add g.rdi i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdx → g'.r13 = g.rsi → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 59 g' fl (Vst (P4 V g) (aR g.rsp + 24#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P4] at hcn hs1 hs2 hs3 hs4 hso hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hso
    | with_reducible exact hcl
    | with_reducible exact hw
    | pstep)

/-- Back from `fwrite`: `rsi` = `&arc.Path`, `rdi` = `_so`, `r12` = `rsp`, to the `call` of
`NormalizePrint_UString_Path` at 74. -/
theorem vc_64 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 74 g' fl V) :
    W_64 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_64, o1]
  all_goals repeat' (first
    | refine h _ ?_ _
    | pstep)

/-- `rdi` = the local `UString`, to the `call` of its constructor at 82. -/
theorem vc_79 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 82 g' fl V) :
    W_79 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_79, o2]
  all_goals repeat' (first
    | refine h _ ?_ _
    | pstep)

/-- `arc.ErrorInfo.ErrorFormatIndex` (`arc + 164`) against `arc.FormatIndex` (`arc + 88`): equal, `rdi` = the local
`UString` to the `call` of `Add_LF` at 259; else `rdx` = the name of the format (`L"#"` for an index below 0), `rsi`
= the message, `rdi` = the local `UString`, to the `call` of `Add_Messsage_Pre_ArcType` at 136. -/
theorem vc_87 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f88 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 88#64) i))
    (f164 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 164#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.r13 + 16#64) i))
    (fe : (rdd(V, g.rbx + 164#64)).msb = false → ∀ i < 8, Foot F.data
      (Addr.add (rdq(V, g.r13 + 16#64) + (rdd(V, g.rbx + 164#64)).signExtend 64 * 8#64) i))
    (fn : (rdd(V, g.rbx + 164#64)).msb = false → ∀ i < 8, Foot F.data
      (Addr.add (rdq(V, rdq(V, g.r13 + 16#64) + (rdd(V, g.rbx + 164#64)).signExtend 64 * 8#64) + 24#64) i))
    (h259 : ∀ g', Fr g g' → ∀ fl, Q 259 g' fl V) (h126 : ∀ g', Fr g g' → ∀ fl, Q 126 g' fl V) :
    W_87 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f88 f164 f16 fe fn h259 h126 ⊢
  cases hx : (rdd(V, rbx + 164#64)).msb
  · have e1 := fe hx
    have e2 := fn hx
    wpx [W_87, W_103, W_114, W_256, o2, o3, o4, o5, Op.ldsx, Op.cmpmr, sw_sx, BitVec.and_self, hx, Bool.false_eq_true,
      false_implies, implies_true]
    all_goals repeat' (first
      | refine h259 _ ?_ _
      | refine h126 _ ?_ _
      | with_reducible exact f88
      | with_reducible exact f164
      | with_reducible exact f16
      | with_reducible exact e1
      | with_reducible exact e2
      | pstep)
  · wpx [W_87, W_103, W_114, W_256, o2, o3, o4, o5, Op.ldsx, Op.cmpmr, sw_sx, BitVec.and_self, hx, Bool.true_eq_false,
      false_implies, implies_true]
    all_goals repeat' (first
      | refine h259 _ ?_ _
      | refine h126 _ ?_ _
      | with_reducible exact f88
      | with_reducible exact f164
      | pstep)

/-- `rsi` = the message, `rdi` = the local `UString`, to the `call` of `Add_Messsage_Pre_ArcType` at 136. -/
theorem vc_126 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 136 g' fl V) :
    W_126 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_126, o6]
  all_goals repeat' (first
    | refine h _ ?_ _
    | pstep)

/-- Back from `Add_Messsage_Pre_ArcType`: `rdx` = the name of the format `arc.FormatIndex` (`arc + 88`; `L"#"` below
0), to 168. -/
theorem vc_141 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f88 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 88#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.r13 + 16#64) i))
    (fe : (rdd(V, g.rbx + 88#64)).msb = false → ∀ i < 8, Foot F.data
      (Addr.add (rdq(V, g.r13 + 16#64) + (rdd(V, g.rbx + 88#64)).signExtend 64 * 8#64) i))
    (fn : (rdd(V, g.rbx + 88#64)).msb = false → ∀ i < 8, Foot F.data
      (Addr.add (rdq(V, rdq(V, g.r13 + 16#64) + (rdd(V, g.rbx + 88#64)).signExtend 64 * 8#64) + 24#64) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 168 g' fl V) :
    W_141 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f88 f16 fe fn h ⊢
  cases hx : (rdd(V, rbx + 88#64)).msb
  · have e1 := fe hx
    have e2 := fn hx
    wpx [W_141, W_156, o5, o7, Op.ldsx, sw_sx, BitVec.and_self, hx, Bool.false_eq_true, false_implies,
      implies_true]
    all_goals repeat' (first
      | refine h _ ?_ _
      | with_reducible exact f88
      | with_reducible exact f16
      | with_reducible exact e1
      | with_reducible exact e2
      | pstep)
  · wpx [W_141, W_156, o5, o7, Op.ldsx, sw_sx, BitVec.and_self, hx, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first
      | refine h _ ?_ _
      | with_reducible exact f88
      | pstep)

/-- `rsi` = the message, `rdi` = the local `UString`, to the `call` of `Add_Messsage_Pre_ArcType` at 178. -/
theorem vc_168 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 178 g' fl V) :
    W_168 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_168, o8]
  all_goals repeat' (first
    | refine h _ ?_ _
    | pstep)

/-- `rsi` = the local `UString`'s characters, `rdi` = `_so`, to the `call` of `operator<<` at 190. -/
theorem vc_183 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h : ∀ g', Fr g g' → ∀ fl, Q 190 g' fl V) :
    W_183 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h ⊢
  wpx [W_183, o9]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact f0
    | pstep)

/-- Back from `operator<<`: `rbp`, `rdi` = the stream it returns, to the `call` of `endl` at 201. -/
theorem vc_195 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 201 g' fl V) :
    W_195 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_195, o10]
  all_goals repeat' (first
    | refine h _ ?_ _
    | pstep)

/-- Back from `endl`: `rdi` = the stream, to the `call` of `endl` at 209. -/
theorem vc_206 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 209 g' fl V) :
    W_206 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_206, o11]
  all_goals repeat' (first
    | refine h _ ?_ _
    | pstep)

/-- Back from `endl`: the local `UString`'s characters (null to 228), else to the `call` of `delete []` at 223. -/
theorem vc_214 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h228 : ∀ g', Fr g g' → ∀ fl, Q 228 g' fl V)
    (h223 : ∀ g', Fr g g' → ∀ fl, Q 223 g' fl V) :
    W_214 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h228 h223 ⊢
  wpx [W_214, o12]
  all_goals repeat' (first
    | refine h228 _ ?_ _
    | refine h223 _ ?_ _
    | with_reducible exact f0
    | pstep)

/-- The stack guard checked (`hc`), `add rsp, 0x28`, the four pops, to the `ret` at 254. -/
theorem vc_228 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 40#64 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 40#64) →
      g'.rbp = rdq(V, g.rsp + 40#64 + 8) → g'.r12 = rdq(V, g.rsp + 40#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8) → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 254 g' fl V) :
    W_228 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 f1 f2 f3 f4 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_228, W_244, o13, o14, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f24
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | apply And.intro
    | intro _)

/-- Back from `Add_LF`: `rsi` = the message, `rdi` = the local `UString`, to the `call` of `operator+=` at 274. -/
theorem vc_264 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 274 g' fl V) :
    W_264 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_264, o15]
  all_goals repeat' (first
    | refine h _ ?_ _
    | pstep)

/-- Back from `operator+=`: to 183. -/
theorem vc_279 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 183 g fl V) :
    W_279 fb F Wl Q g f V := h _

end FV7z.Pew
