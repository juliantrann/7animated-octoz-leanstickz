import FV7z.Exr.Defs
/-!
# `CExtractCallbackConsole::ExtractResult`: the pieces (PLAN.md §M, M1)

One theorem for each cut point (`vc_*`): the prologue (`vc_0`, the bytes `V0` with the guard's value named `cn`),
then the code with `rbx` = `this`, its loads from the object in the footprint's data (`rd`), to the next cut points or
`call`s, keeping `rsp`, `rbx`, `r13`..`r15` (`Fr`). Where `test` decides the way and the way on needs the register
not null (`vc_118`, `vc_273`, `vc_490`), the cases of the register = 0 first. `vc_414` clears the two buffers and
their sizes (the bytes stored any, of their lengths); `vc_202` checks the guard (`hc`) and pops.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Exr
set_option linter.unusedVariables false

variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the three pushes, `r12d` = `result`, `rbx` = `this`, `sub rsp, 0x20`, the stack guard stored, to the
`call` of `Enter` at 41. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P3 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 24#64) i))
    (h : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 41 g' fl (Vst (P3 V g) (aR g.rsp + 24#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P3] at hcn hs1 hs2 hs3 hw h ⊢
  wpx [W_0, o0, Op.ldf, hcn]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hcl
    | with_reducible exact hw
    | estep)

/-- Back from `Enter`: `NeedPercents ()` (`_percent._so` at `this + 104` and `_percent.NeedFlush` at `this + 112`):
`rdi` = `&_percent`, `esi` = 1, to the `call` of `ClosePrint` at 409; else to 63. -/
theorem vc_46 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h63 : ∀ g', Fr g g' → ∀ fl, Q 63 g' fl V) (h409 : ∀ g', Fr g g' → ∀ fl, Q 409 g' fl V) :
    W_46 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h63 h409 ⊢
  wpx [W_46, W_53, W_400, o1, o2, o24, Op.cmpmi]
  all_goals repeat' (first
    | refine h63 _ ?_ _
    | refine h409 _ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- Back from `ClosePrint`: `_percent`'s two buffers (at `this + 72`, `this + 88`) cleared and their lengths
(`this + 80`, `this + 96`) set to 0, to 63. -/
theorem vc_414 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (w80 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 80#64) i)) (w96 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 96#64) i))
    (w72 : ∀ i < 1, Foot Wl (Addr.add rdq(V, g.rbx + 72#64) i))
    (w88 : ∀ (a b : List Byte), a.length = 4 → b.length = 1 → ∀ i < 4,
      Foot Wl (Addr.add rdq(Vst (Vst V (g.rbx + 80#64) a) rdq(V, g.rbx + 72#64) b, g.rbx + 88#64) i))
    (h : ∀ g' (a b c d : List Byte), a.length = 4 → b.length = 1 → c.length = 4 → d.length = 4 → Fr g g' →
      ∀ fl, Q 63 g' fl (Vst (Vst (Vst (Vst V (g.rbx + 80#64) a) rdq(V, g.rbx + 72#64) b) (g.rbx + 96#64) c)
        rdq(Vst (Vst V (g.rbx + 80#64) a) rdq(V, g.rbx + 72#64) b, g.rbx + 88#64) d)) :
    W_414 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd w80 w96 w72 w88 h ⊢
  wpx [W_414, o25]
  all_goals repeat' (first
    | refine h _ _ _ _ _ (toBytesLE_length _ _) (toBytesLE_length _ _) (toBytesLE_length _ _)
        (toBytesLE_length _ _) ?_ _
    | exact rd _ _ (by decide)
    | with_reducible exact w80
    | with_reducible exact w96
    | with_reducible exact w72
    | exact w88 _ _ (toBytesLE_length _ _) (toBytesLE_length _ _)
    | estep)

/-- `_so` (`this + 264`): null to 80, else to the `call` of `Flush` at 75. -/
theorem vc_63 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h80 : ∀ g', Fr g g' → ∀ fl, Q 80 g' fl V) (h75 : ∀ g', Fr g g' → ∀ fl, Q 75 g' fl V) :
    W_63 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h80 h75 ⊢
  wpx [W_63, o3]
  all_goals repeat' (first
    | refine h80 _ ?_ _
    | refine h75 _ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- `result`: not `S_OK` (240) `E_ABORT` or `ERROR_DISK_SPACE` to 190, else `rbp` = `_se` (`this + 272`) to the `add`
at 265; `S_OK` with the count at `this + 448` not 0 to 103; else (456) by the bytes at `this + 317` (not 0: to 103)
and `this + 318` (0: to the `add` at 616, else at 482). -/
theorem vc_80 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h190 : ∀ g', Fr g g' → ∀ fl, Q 190 g' fl V)
    (h265 : ∀ g', g'.rbp = rdq(V, g.rbx + 272#64) → Fr g g' → ∀ fl, Q 265 g' fl V)
    (h103 : ∀ g', Fr g g' → ∀ fl, Q 103 g' fl V) (h616 : ∀ g', Fr g g' → ∀ fl, Q 616 g' fl V)
    (h482 : ∀ g', Fr g g' → ∀ fl, Q 482 g' fl V) :
    W_80 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h190 h265 h103 h616 h482 ⊢
  wpx [W_80, W_240, W_249, W_258, W_89, W_456, W_469, o4, o13, o14, o15, o5, o26, o27, Op.cmpmi]
  all_goals repeat' (first
    | refine h190 _ ?_ _
    | refine h265 _ ?_ ?_ _
    | refine h103 _ ?_ _
    | refine h616 _ ?_ _
    | refine h482 _ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- `rdi` = `_so`, to the `add` at 110. -/
theorem vc_103 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h : ∀ g', g'.rdi = rdq(V, g.rbx + 264#64) → Fr g g' → ∀ fl, Q 110 g' fl V) :
    W_103 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h ⊢
  wpx [W_103, o6]
  all_goals repeat' (first
    | refine h _ ?_ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- `_so` (in `rdi`): null to 167, else to the `call` of `endl` at 123. -/
theorem vc_118 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h167 : ∀ g', Fr g g' → ∀ fl, Q 167 g' fl V)
    (h123 : ∀ g', g.rdi ≠ 0 → Fr g g' → ∀ fl, Q 123 g' fl V) :
    W_118 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h167 h123 ⊢
  by_cases h0 : rdi = 0
  · have hb : (rdi == 0) = true := beq_iff_eq.2 h0
    wpx [W_118, o7, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h167 _ ?_ _
      | estep)
  · have hb : (rdi == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_118, o7, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h167 _ ?_ _
      | refine h123 _ ?_ ?_ _
      | exact h0
      | estep)

/-- Back from `endl`: the count at `this + 448` not 0 (552): `rbp` = `_so`, the message to the `call` of `fwrite` at
580; else to 142. -/
theorem vc_128 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add rdq(V, g.rbx + 264#64) i))
    (h580 : ∀ g', Fr g g' → ∀ fl, Q 580 g' fl V) (h142 : ∀ g', Fr g g' → ∀ fl, Q 142 g' fl V) :
    W_128 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd f5 h580 h142 ⊢
  wpx [W_128, W_552, o5, o30, Op.cmpmi]
  all_goals repeat' (first
    | refine h580 _ ?_ _
    | refine h142 _ ?_ _
    | exact rd _ _ (by decide)
    | with_reducible exact f5
    | estep)

/-- `_so`: null to 167; else `NeedFlush` (`this + 319`) to the `call` of `Flush` at 388, or to 167. -/
theorem vc_142 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h167 : ∀ g', Fr g g' → ∀ fl, Q 167 g' fl V) (h388 : ∀ g', Fr g g' → ∀ fl, Q 388 g' fl V) :
    W_142 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h167 h388 ⊢
  wpx [W_142, W_154, o3, o8, Op.cmpmi]
  all_goals repeat' (first
    | refine h167 _ ?_ _
    | refine h388 _ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- `r12d` = `E_ABORT` or `S_OK` by the break counter, to 190. -/
theorem vc_167 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fg : ∀ i < 4, Foot F.data (Addr.add 7991432#64 i)) (h : ∀ g', Fr g g' → ∀ fl, Q 190 g' fl V) :
    W_167 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_167, o9, Op.cmpmi, Op.not32]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact fg
    | estep)

/-- `rdi` = `&g_CriticalSection`, to the `call` of `Leave` at 197. -/
theorem vc_190 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 197 g' fl V) :
    W_190 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_190, o10]
  all_goals repeat' (first
    | refine h _ ?_ _
    | estep)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x20`, `eax` = `r12d`, the three pops, to
the `ret`. -/
theorem vc_202 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 24#64) = rdq(V, fb + 40#64)) (f24 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 32#64 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 32#64 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 32#64) →
      g'.rbp = rdq(V, g.rsp + 32#64 + 8) → g'.r12 = rdq(V, g.rsp + 32#64 + 8 + 8) →
      g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 233 g' fl V) :
    W_202 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f24 f1 f2 f3 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_202, W_222, o11, o12, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f24
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | apply And.intro
    | intro _)

/-- `_se` (in `rbp`): null to 167, else `rdi` = `_se`, to the `call` of `endl` at 281. -/
theorem vc_273 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h167 : ∀ g', Fr g g' → ∀ fl, Q 167 g' fl V)
    (h281 : ∀ g', g.rbp ≠ 0 → g'.rbp = g.rbp → Fr g g' → ∀ fl, Q 281 g' fl V) :
    W_273 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h167 h281 ⊢
  by_cases h0 : rbp = 0
  · have hb : (rbp == 0) = true := beq_iff_eq.2 h0
    wpx [W_273, W_278, o16, o17, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h167 _ ?_ _
      | estep)
  · have hb : (rbp == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_273, W_278, o16, o17, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h167 _ ?_ _
      | refine h281 _ ?_ ?_ ?_ _
      | exact h0
      | estep)

/-- Back from `endl`: `rcx` = `*_se` (the `FILE *`, read at `rbp`), the message, to the `call` of `fwrite` at 307. -/
theorem vc_286 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f5 : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) (h : ∀ g', Fr g g' → ∀ fl, Q 307 g' fl V) :
    W_286 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f5 h ⊢
  wpx [W_286, o18]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact f5
    | estep)

/-- Back from `fwrite`: `rbp` = `_se`; `E_OUTOFMEMORY` (632) the message to the `call` of `fwrite` at 653; else
`rdi` = the local `AString`, `esi` = `result`, to the `call` of `HResultToMessage` at 338. -/
theorem vc_312 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add rdq(V, g.rbx + 272#64) i))
    (h653 : ∀ g', Fr g g' → ∀ fl, Q 653 g' fl V) (h338 : ∀ g', Fr g g' → ∀ fl, Q 338 g' fl V) :
    W_312 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd f5 h653 h338 ⊢
  wpx [W_312, W_632, W_332, o19, o33, o20]
  all_goals repeat' (first
    | refine h653 _ ?_ _
    | refine h338 _ ?_ _
    | exact rd _ _ (by decide)
    | with_reducible exact f5
    | estep)

/-- Back from `HResultToMessage`: `rsi` = the message's buffer (at `rsp`), `rdi` = `_se`, to the `call` of
`operator<<` at 350. -/
theorem vc_343 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (h : ∀ g', Fr g g' → ∀ fl, Q 350 g' fl V) :
    W_343 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h ⊢
  wpx [W_343, o21]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible exact f0
    | estep)

/-- Back from `operator<<`: the message's buffer: null to 369, else to the `call` of `delete []` at 364. -/
theorem vc_355 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i))
    (h369 : ∀ g', Fr g g' → ∀ fl, Q 369 g' fl V) (h364 : ∀ g', Fr g g' → ∀ fl, Q 364 g' fl V) :
    W_355 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 h369 h364 ⊢
  wpx [W_355, o22]
  all_goals repeat' (first
    | refine h369 _ ?_ _
    | refine h364 _ ?_ _
    | with_reducible exact f0
    | estep)

/-- `rdi` = `_se`, to the `call` of `endl` at 376. -/
theorem vc_369 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 376 g' fl V) :
    W_369 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h ⊢
  wpx [W_369, o23]
  all_goals repeat' (first
    | refine h _ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- `rdi` = `_se`, to the `call` of `Flush` at 388. -/
theorem vc_381 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 388 g' fl V) :
    W_381 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h ⊢
  wpx [W_381, o23]
  all_goals repeat' (first
    | refine h _ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- `jmp` to 167. -/
theorem vc_393 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 167 g fl V) :
    W_393 fb F Wl Q g f V := h _

/-- `rbp` = `_so`: null to 167, else the message to the `call` of `fwrite` at 527. -/
theorem vc_490 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (f5 : rdq(V, g.rbx + 264#64) ≠ 0 → ∀ i < 8, Foot F.data (Addr.add rdq(V, g.rbx + 264#64) i))
    (h167 : ∀ g', Fr g g' → ∀ fl, Q 167 g' fl V) (h527 : ∀ g', Fr g g' → ∀ fl, Q 527 g' fl V) :
    W_490 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd f5 h167 h527 ⊢
  by_cases h0 : rdq(V, rbx + 264#64) = 0
  · have hb : (rdq(V, rbx + 264#64) == 0) = true := beq_iff_eq.2 h0
    wpx [W_490, W_506, o28, o29, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h167 _ ?_ _
      | exact rd _ _ (by decide)
      | estep)
  · have hb : (rdq(V, rbx + 264#64) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_490, W_506, o28, o29, hb, BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h167 _ ?_ _
      | refine h527 _ ?_ _
      | exact rd _ _ (by decide)
      | exact f5 h0
      | estep)

/-- Back from `fwrite`: `rdi` = `_so`, to the `call` of `endl` at 535. -/
theorem vc_532 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 535 g' fl V) :
    W_532 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_532, o17]
  all_goals repeat' (first
    | refine h _ ?_ _
    | estep)

/-- `jmp` to 142. -/
theorem vc_540 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 142 g fl V) :
    W_540 fb F Wl Q g f V := h _

/-- Back from `fwrite`: `rsi` = the count at `this + 448`, `rdi` = `_so`, to the `call` of `operator<<` at
595. -/
theorem vc_585 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (rd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g.rbx + k) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 595 g' fl V) :
    W_585 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at rd h ⊢
  wpx [W_585, o31]
  all_goals repeat' (first
    | refine h _ ?_ _
    | exact rd _ _ (by decide)
    | estep)

/-- Back from `operator<<`: `rdi` = the stream it returns, to the `call` of `endl` at 603. -/
theorem vc_600 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 603 g' fl V) :
    W_600 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_600, o32]
  all_goals repeat' (first
    | refine h _ ?_ _
    | estep)

/-- `jmp` to 142. -/
theorem vc_608 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 142 g fl V) :
    W_608 fb F Wl Q g f V := h _

/-- `jmp` to 490. -/
theorem vc_624 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 490 g fl V) :
    W_624 fb F Wl Q g f V := h _

/-- `jmp` to 369. -/
theorem vc_658 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 369 g fl V) :
    W_658 fb F Wl Q g f V := h _

end FV7z.Exr
