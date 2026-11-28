import FV7z.Aec.Defs
/-!
# `CArchiveExtractCallback::CArchiveExtractCallback`: the pieces, part 1 of 2 (PLAN.md §M, M1)

The pieces from 0 to the `call` at 215: the pushes (`vc_0`, the bytes `P5`), then the stores relative to `rdi` =
`this + 160` (`vc_23` sets `rbx` = `this`), to the `call`s at 203 and 215. Each store into the object is one `hcl`
allows (an offset below 704), so the invariant `I` of the bytes holds after it; `ob` gives its footprint.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Aec
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, `rax` the vtable base, the five pushes, to 23. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)) (h5 : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.r15 = g.r15 → g'.rdi = g.rdi → ∀ fl, Q 23 g' fl (P5 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 h4 h5 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | astep)

/-- `rbx` = `this`, `rdi` = `this + 160`, the vtable pointers at `this`, `this + 8`, to 61. -/
theorem vc_23 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rdi + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rdi + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rdi → g'.r15 = g.r15 → g'.rdi = g.rdi + 160#64 →
      ∀ fl, Q 61 g' fl V') :
    W_23 F Wl Q g f V := by
  have ob0 : ∀ i < 8, Foot Wl (Addr.add g.rdi i) := by
    have := ob 0#64 8 (by decide)
    rwa [BitVec.add_zero] at this
  have hc0 : ∀ (W : Addr → Byte) (bs : List Byte), bs.length = 8 → I W → I (Vst W g.rdi bs) := by
    intro W bs hl hW
    have := hcl W 0#64 8 bs hl (by decide) hW
    rwa [BitVec.add_zero] at this
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl ob0 hc0 h ⊢
  wpx [W_23, o1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible refine hc0 _ _ (toBytesLE_length _ _) ?_
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | with_reducible exact ob0
    | exact ob _ _ (by decide)
    | astep)

/-- The vtable pointers at `this + 16`, `+ 24`, `+ 32`, to 100. -/
theorem vc_61 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (hdi : g.rdi = g.rbx + 160#64)
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → g'.rdi = g.rbx + 160#64 →
      ∀ fl, Q 100 g' fl V') :
    W_61 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi ob hcl h ⊢
  subst hdi
  wpx [W_61, o2, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The vtable pointers at `this + 40`, `+ 48`, the 4 bytes at `this + 56`, to 133. -/
theorem vc_100 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (hdi : g.rdi = g.rbx + 160#64)
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → g'.rdi = g.rbx + 160#64 →
      ∀ fl, Q 133 g' fl V') :
    W_100 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi ob hcl h ⊢
  subst hdi
  wpx [W_100, o3, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The fields at `this + 88`, `+ 96`, `+ 63`, `+ 64`, `+ 72`, `+ 80`, to 171. -/
theorem vc_133 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (hdi : g.rdi = g.rbx + 160#64)
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → g'.rdi = g.rbx + 160#64 →
      ∀ fl, Q 171 g' fl V') :
    W_133 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi ob hcl h ⊢
  subst hdi
  wpx [W_133, o4, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- The fields at `this + 84`, `+ 115`, `+ 128`, `+ 144`, `+ 152`, to the `call` at 203. -/
theorem vc_171 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (hdi : g.rdi = g.rbx + 160#64)
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 203 g' fl V') :
    W_171 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hdi ob hcl h ⊢
  subst hdi
  wpx [W_171, o5, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | astep)

/-- `rdi` = `this + 176`, to the `call` at 215. -/
theorem vc_208 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r15 = g.r15 → ∀ fl, Q 215 g' fl V) :
    W_208 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_208, o6]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | astep)

end FV7z.Aec
