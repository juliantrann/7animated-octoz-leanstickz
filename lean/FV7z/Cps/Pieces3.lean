import FV7z.Cps.Defs
/-!
# `NCommandLineParser::CParser::ParseString`: the pieces of `sw.PostStrings.Add` (PLAN.md §M, M1)

The verification conditions of the pieces from 514 (`FV7z/Cps/Defs.lean` for the layout): `Type` 2 (`kString`), the
local `UString` of `s.Ptr(pos)` (514), `sw.PostStrings` (a `CObjectVector<UString>`, `_items` at `sw + 8`, `_size` at
`+ 16`, `_capacity` at `+ 20`) grown when full (534..626, 809), the new `UString` (636, 646) appended (660, 678), the
local freed.

The stores into `sw` and into `PostStrings._items[_size]` are those `Ok` allows: they keep the invariant `I` of the
bytes (`hcl`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (P6 Stk KS)
namespace FV7z.Cps
set_option linter.unusedVariables false

section Pieces
variable {F : Footprint} {Wl : List Rgn} {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-- `r13` = `rdi` = the local `UString` (`rsp + 32`), `rsi` = `s._chars + 4 pos`: to its constructor (529). -/
theorem vc_514 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.r14 i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.rsp + 32#64 → g'.rdi = g.rsp + 32#64 →
      ∀ fl, Q 529 g' fl V) :
    W_514 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h ⊢
  cpx [W_514, o38]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | cstep)

/-- `PostStrings._size` not `_capacity` to 636; else `_capacity` against 0x7ffffffe, to the `ja` at 551. -/
theorem vc_534 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f20 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 20#64) i))
    (f16 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 16#64) i))
    (h636 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 636 g' fl V)
    (h551 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 551 g' fl V) :
    W_534 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f20 f16 h636 h551 ⊢
  cpx [W_534, W_546, o39, o40, Op.cmpmr]
  all_goals repeat' (first
    | refine h636 _ ?_ ?_ ?_ _
    | refine h551 _ ?_ ?_ ?_ _
    | cstep)

/-- The new capacity, part 1: `edx` = `_capacity / 4`, `ebx` = that + 1, `edx` = 0x7fffffff; to 570. -/
theorem vc_557 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 570 g' fl V) :
    W_557 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cpx [W_557, o41]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | cstep)

/-- The new capacity, part 2 (`cmova`), `edi` = it: to 580. -/
theorem vc_570 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 580 g' fl V) :
    W_570 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cpx [W_570, o42]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | cstep)

/-- `rbx` = the new capacity, `rdi` = 8 times it: to `operator new []` (587). -/
theorem vc_580 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 587 g' fl V) :
    W_580 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cpx [W_580, o43, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | cstep)

/-- `rbp` = the new array, `rsi` = the old `_items`: `_size` not 0, `rdx` = 8 times it, to `memcpy` (804); else to
613. -/
theorem vc_592 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 16#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (h804 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 804 g' fl V)
    (h613 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 613 g' fl V) :
    W_592 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 f8 h804 h613 ⊢
  cpx [W_592, W_793, o44, o55]
  all_goals repeat' (first
    | refine h804 _ ?_ ?_ ?_ _
    | refine h613 _ ?_ ?_ ?_ _
    | cstep)

/-- The old `_items` null to 626; else `rdi` = it, to `operator delete []` (621). -/
theorem vc_613 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h626 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 626 g' fl V)
    (h621 : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 621 g' fl V) :
    W_613 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h626 h621 ⊢
  cpx [W_613, W_618, o45, o46]
  all_goals repeat' (first
    | refine h626 _ ?_ ?_ ?_ _
    | refine h621 _ ?_ ?_ ?_ _
    | cstep)

/-- `_items` = the new array, `_capacity` = the new capacity: to 636. -/
theorem vc_626 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w8 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 8#64) i)) (w20 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 20#64) i))
    (o8 : Ok (g.r12 + 8#64) 8) (o20 : Ok (g.r12 + 20#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 636 g' fl V') :
    W_626 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w8 w20 o8 o20 h ⊢
  cpx [W_626, o47]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | cstep)

/-- `edi` = 16, to `operator new` (641). -/
theorem vc_636 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 641 g' fl V) :
    W_636 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cpx [W_636, o48]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | cstep)

/-- `rsi` = the local, `rdi` = `rbp` = the new object: to the `UString` copy (655). -/
theorem vc_646 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.rdi = g.rax → g'.rsi = g.r13 → ∀ fl, Q 655 g' fl V) :
    W_646 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  cpx [W_646, o49]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | cstep)

/-- `eax` = `_size`, `rdx` = `_items`, `_size` + 1: to 678. -/
theorem vc_660 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 4, Foot F.data (Addr.add (g.r12 + 16#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (w16 : ∀ i < 4, Foot Wl (Addr.add (g.r12 + 16#64) i)) (o16 : Ok (g.r12 + 16#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.r12 = g.r12 → g'.rbp = g.rbp → g'.rdx = rdq(V, g.r12 + 8#64) →
      g'.rax = BitVec.setWidth 64 rdd(V, g.r12 + 16#64) → ∀ fl, Q 678 g' fl V') :
    W_660 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 f8 w16 o16 h ⊢
  cpx [W_660, o50]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | cstep)

/-- `_items[eax]` = the new object, `rdi` = the local's `_chars`: null to 317; else to `operator delete []` (696). -/
theorem vc_678 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (wsl : ∀ i < 8, Foot Wl (Addr.add (g.rdx + g.rax * 8#64) i)) (osl : Ok (g.rdx + g.rax * 8#64) 8)
    (f32 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i)) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h317 : ∀ g' V', I V' → g'.rsp = g.rsp → ∀ fl, Q 317 g' fl V')
    (h696 : ∀ g' V', I V' → g'.rsp = g.rsp → ∀ fl, Q 696 g' fl V') :
    W_678 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at wsl osl f32 h317 h696 ⊢
  cpx [W_678, o51]
  all_goals repeat' (first
    | refine h317 _ _ ?_ ?_ _
    | refine h696 _ _ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | cstep)

/-- After `memcpy`: `rsi` = the old `_items`, to 613. -/
theorem vc_809 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f8 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 8#64) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.r12 = g.r12 → g'.r13 = g.r13 → ∀ fl, Q 613 g' fl V) :
    W_809 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f8 h ⊢
  cpx [W_809, o56]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | cstep)

end Pieces

end FV7z.Cps
