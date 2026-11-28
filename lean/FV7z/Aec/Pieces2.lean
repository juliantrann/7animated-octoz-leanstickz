import FV7z.Aec.Defs
/-!
# `CArchiveExtractCallback::CArchiveExtractCallback`: the pieces, part 2 of 2 (PLAN.md §M, M1)

The pieces from 220 to the `ret`: the stores relative to `rbx` = `this`, the new object in `rbp` (`vc_526`), the pops
(`vc_679`). Each store into the object is one `hcl` allows (an offset below 704), so the invariant `I` of the bytes
holds after it; `ob` gives its footprint.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Aec
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- The fields at `this + 192`, `+ 200`, `rdi` = `r12` = `this + 208`, to the `call` at 252. -/
theorem vc_220 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 252 g' fl V') :
    W_220 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_220, o7]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The fields at `this + 224`, `+ 232`, `rdi` = `this + 240`, to the `call` at 286. -/
theorem vc_257 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 286 g' fl V') :
    W_257 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_257, o8]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- `rdi` = `this + 256`, to the `call` at 298. -/
theorem vc_291 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 298 g' fl V) :
    W_291 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_291, o9]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | astep)

/-- The fields at `this + 273`, `+ 280`, `+ 284`, `rdi` = `this + 288`, to the `call` at 334. -/
theorem vc_303 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 334 g' fl V') :
    W_303 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_303, o10]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The fields at `this + 304` to `+ 336`, `rdi` = `this + 360`, to the `call` at 400. -/
theorem vc_339 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 400 g' fl V') :
    W_339 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_339, o11]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- `rdi` = `this + 384`, to the `call` at 412. -/
theorem vc_405 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 412 g' fl V) :
    W_405 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_405, o12]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | astep)

/-- The fields at `this + 440` to `+ 488`, `edi` = 56, to 477. -/
theorem vc_417 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 477 g' fl V') :
    W_417 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_417, o13]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The fields at `this + 504` to `+ 544`, to the `call` of `operator new` at 521. -/
theorem vc_477 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 521 g' fl V') :
    W_477 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_477, o14]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- `rdi` = `rbp` = the new object, to the `call` at 532. -/
theorem vc_526 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → g'.rbp = g.rax → ∀ fl, Q 532 g' fl V) :
    W_526 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_526, o15]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | astep)

/-- `rdi` = `this + 600`, the new object at `this + 552`, to the `call` at 555. -/
theorem vc_541 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 555 g' fl V') :
    W_541 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_541, o16]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- `eax` = 0, the fields at `this + 616` to `+ 640`, `rdi` = `this + 672`, to 613. -/
theorem vc_560 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 613 g' fl V') :
    W_560 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_560, o17]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The fields at `this + 648` to `+ 668`, to the `call` at 652. -/
theorem vc_613 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 652 g' fl V') :
    W_613 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_613, o18]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The fields at `this + 688`, `+ 696`, to 679. -/
theorem vc_657 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 679 g' fl V') :
    W_657 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl h ⊢
  wpx [W_657, o19]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The five pops, to the `ret` at 687. -/
theorem vc_679 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = rdq(V, g.rsp + 8) →
      g'.r12 = rdq(V, g.rsp + 8 + 8) → g'.r13 = rdq(V, g.rsp + 8 + 8 + 8) →
      g'.r14 = rdq(V, g.rsp + 8 + 8 + 8 + 8) → g'.r15 = g.r15 → ∀ fl, Q 687 g' fl V) :
    W_679 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f1 f2 f3 f4 h ⊢
  wpx [W_679, o20]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | astep)

end FV7z.Aec
