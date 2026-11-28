import FV7z.Bop.Defs
/-!
# `CExtractCallbackConsole::BeforeOpen`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the pushes (`vc_0`, the bytes `P4`), then the code with `rbx` = `this`, its
loads from the object in the footprint's data (`rd`), its stores into it allowed (`ob`) and keeping the invariant `I`
of the bytes (`hcl`, an offset below 456), to the next cut points or `call`s. Where `test r13, r13` decides the way
(`vc_69`, `vc_240`, `vc_267`), the cases of `r13` = 0 first: on the way to 127 (the read of `[r13]`) it is not.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Bop
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the four pushes, `rbx` = `this`, `sub rsp, 8`, to the `call` at 30. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (h2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (h3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 30 g' fl (P4 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h1 h2 h3 h4 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | astep)

/-- Back from `UString::operator=`: `PrintMode = true` (`this + 316`), the break counter: `E_ABORT` to 223, else to
the `add` at 61. -/
theorem vc_35 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 456 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V) (fg : ∀ i < 4, Foot F.data (Addr.add 7991432#64 i))
    (h61 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 61 g' fl V')
    (h223 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 223 g' fl V') :
    W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob hcl fg h61 h223 ⊢
  wpx [W_35, W_288, W_59, o1, o16, o2]
  all_goals repeat' (first
    | refine h61 _ _ ?_ ?_ ?_ ?_ ?_ _
    | refine h223 _ _ ?_ ?_ ?_ ?_ ?_ _
    | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
    | exact ob _ _ (by decide)
    | exact fg
    | astep)

/-- After the `add` (61): `_so` (`this + 264`) into `r13`, the flags, `_percent._so` and `_percent.NeedFlush`: to 240
(no printer, or quiet), the `call` of `ClosePrint` at 262 (the printer's stream is `_so`), 205 (no `_so`) or 127. -/
theorem vc_69 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {I : (Addr → Byte) → Prop}
    (ob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot Wl (Addr.add (g.rbx + k) i))
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 456 →
      I W → I (Vst W (g.rbx + k) bs)) (hI : I V)
    (h240 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      g'.r13 = rdq(V, g.rbx + 264#64) → ∀ fl, Q 240 g' fl V')
    (h262 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 262 g' fl V')
    (h205 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 205 g' fl V')
    (h127 : ∀ g' V', I V' → g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      g'.r13 = rdq(V, g.rbx + 264#64) → g'.r13 ≠ 0 → ∀ fl, Q 127 g' fl V') :
    W_69 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at ob rd hcl h240 h262 h205 h127 ⊢
  by_cases h0 : rdq(V, rbx + 264#64) = 0
  · have hb : (rdq(V, rbx + 264#64) == 0) = true := beq_iff_eq.2 h0
    wpx [W_69, W_107, W_113, W_256, W_122, o3, o4, o5, o14, o6, Op.cmpmi, hb, BitVec.and_self, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h240 _ _ ?_ ?_ ?_ ?_ ?_ ?_ _
      | refine h262 _ _ ?_ ?_ ?_ ?_ ?_ _
      | refine h205 _ _ ?_ ?_ ?_ ?_ ?_ _
      | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
      | exact ob _ _ (by decide)
      | exact rd _ _ (by decide)
      | astep)
  · have hb : (rdq(V, rbx + 264#64) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_69, W_107, W_113, W_256, W_122, o3, o4, o5, o14, o6, Op.cmpmi, hb, BitVec.and_self, Bool.not_true,
      Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h240 _ _ ?_ ?_ ?_ ?_ ?_ ?_ _
      | refine h262 _ _ ?_ ?_ ?_ ?_ ?_ _
      | refine h205 _ _ ?_ ?_ ?_ ?_ ?_ _
      | refine h127 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
      | refine hcl _ _ _ _ (toBytesLE_length _ _) (by decide) ?_
      | exact ob _ _ (by decide)
      | exact rd _ _ (by decide)
      | exact h0
      | astep)

/-- `mov rdi, r13`, to the `call` of `endl` at 130. -/
theorem vc_127 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 130 g' fl V) :
    W_127 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_127, o7]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | astep)

/-- The open or test message (`cmove`), `rsi` = `*_so` (the `FILE *`, read at `r13`), to the `call` of `fputs` at
160. -/
theorem vc_135 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f13 : ∀ i < 8, Foot F.data (Addr.add g.r13 i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 160 g' fl V) :
    W_135 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f13 h ⊢
  wpx [W_135, o8]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | exact f13
    | astep)

/-- `rdi` = `_so`, `rsi` = `name`, to the `call` of `NormalizePrint_UString` at 175. -/
theorem vc_165 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 175 g' fl V) :
    W_165 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h ⊢
  wpx [W_165, o9]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | exact rd _ _ (by decide)
    | astep)

/-- `rdi` = `_so`, to the `call` of `endl` at 187. -/
theorem vc_180 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 187 g' fl V) :
    W_180 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h ⊢
  wpx [W_180, o10]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | exact rd _ _ (by decide)
    | astep)

/-- `_percent._so` and `_percent.NeedFlush`: to 221, or 205 (`_tempA` cleared). -/
theorem vc_192 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h221 : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 221 g' fl V)
    (h205 : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 205 g' fl V) :
    W_192 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h221 h205 ⊢
  wpx [W_192, W_199, o11, o4, Op.cmpmi]
  all_goals repeat' (first
    | refine h221 _ ?_ ?_ ?_ ?_ _
    | refine h205 _ ?_ ?_ ?_ ?_ _
    | exact rd _ _ (by decide)
    | astep)

/-- `rdi` = `&_tempA` (`this + 72`), `rsi` = `""`, to the `call` of `AString::operator=` at 216. -/
theorem vc_205 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 216 g' fl V) :
    W_205 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_205, o12]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | astep)

/-- `eax` = 0 (`S_OK`), to 223. -/
theorem vc_221 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 223 g' fl V) :
    W_221 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_221, o2]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ _
    | astep)

/-- `add rsp, 8; pop rbx; pop rbp; pop r12; pop r13`, to the `ret` at 233. -/
theorem vc_223 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 8#64) →
      g'.rbp = rdq(V, g.rsp + 8#64 + 8) → g'.r12 = rdq(V, g.rsp + 8#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8) → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 233 g' fl V) :
    W_223 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at l1 l2 l3 l4 h ⊢
  wpx [W_223, o13]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | astep)

/-- No printer, or quiet (`r13` = `_so`): to 127 when `_so`, else to 221. -/
theorem vc_240 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h127 : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → g'.r13 = g.r13 →
      g'.r13 ≠ 0 → ∀ fl, Q 127 g' fl V)
    (h221 : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 221 g' fl V) :
    W_240 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h127 h221 ⊢
  by_cases h0 : r13 = 0
  · have hb : (r13 == 0) = true := beq_iff_eq.2 h0
    wpx [W_240, W_245, o6, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h221 _ ?_ ?_ ?_ ?_ _
      | astep)
  · have hb : (r13 == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_240, W_245, o6, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h127 _ ?_ ?_ ?_ ?_ ?_ ?_ _
      | refine h221 _ ?_ ?_ ?_ ?_ _
      | exact h0
      | astep)

/-- Back from `ClosePrint`: `_so` into `r13`, to 127 when not null, else to 192. -/
theorem vc_267 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h127 : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 →
      g'.r13 = rdq(V, g.rbx + 264#64) → g'.r13 ≠ 0 → ∀ fl, Q 127 g' fl V)
    (h192 : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 192 g' fl V) :
    W_267 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h127 h192 ⊢
  by_cases h0 : rdq(V, rbx + 264#64) = 0
  · have hb : (rdq(V, rbx + 264#64) == 0) = true := beq_iff_eq.2 h0
    wpx [W_267, W_283, o15, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h192 _ ?_ ?_ ?_ ?_ _
      | exact rd _ _ (by decide)
      | astep)
  · have hb : (rdq(V, rbx + 264#64) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_267, W_283, o15, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h127 _ ?_ ?_ ?_ ?_ ?_ ?_ _
      | refine h192 _ ?_ ?_ ?_ ?_ _
      | exact rd _ _ (by decide)
      | exact h0
      | astep)

end FV7z.Bop
