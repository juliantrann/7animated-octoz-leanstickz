import FV7z.Aeq.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Ecq.Holds
/-!
# `CArchiveExtractCallback::QueryInterface`: the pieces at the cut points (PLAN.md §M, M1)

7-Zip 26.06's `CArchiveExtractCallback::QueryInterface (iid, ppv)` (`Z7_COM_QI_*`,
`CPP/7zip/UI/Common/ArchiveExtractCallback.h`; `objdump -d`) at `0x5b16d0` in `7zzs`, `this` = `rdi`, `iid` =
`rsi`, `ppv` = `rdx`: `*ppv = NULL`, then seven loops comparing the 16 bytes of `iid` with the IIDs at `0x6eb970`
(24), `0x6eb890` (64, 88, 98), `0x6eb780` (128), `0x6eb760` (184), `0x6eb7f0` (232), `0x6eb7e0` (280), `0x6eb790`
(328), byte by byte. The first loop loads the byte of `iid` and compares the IID's (`movzx r8d, byte [rsi + rax];
cmp byte [rax + rcx], r8b`), the others the other way round. On a match `*ppv` = `this` + 8, 8, 16, 24, 32, 40, 48
and `AddRef` inline (`add dword [rdi + 0x38], 1`, by hand at 52 and 158), `S_OK`; else `E_NOINTERFACE` (366).

- `bq`, `sw8`: from `FV7z.Ecq`.
- `vc_0`: `*ppv = NULL`, to the first loop at 24 with `rax` = 0, `rcx` = `0x6eb970`.
- `vc_24`: one step of the first loop: on a match on to 24 or (the 16 bytes done) to 45; on a mismatch the second
  loop's first compare, to 88 (match) or 109 (mismatch).
- `vc_35`: the counter of the first loop.
- `vc_45`: `*ppv = this + 8`, to the `AddRef` at 52; `vc_56`: `S_OK`, to the `ret` at 58.
- `vc_88`: the counter of the second loop and its next compare; `vc_109`: to the third loop.
- `vc_128`, `vc_184`, `vc_232`, `vc_280`, `vc_328`: one step of the third to seventh loop with its exits.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn FV7z.Ecq
namespace FV7z.Aeq

variable {F : Footprint} {Wl : List Rgn}

/-- `*ppv = NULL; mov ecx, 0x6eb970; xor eax, eax`, to the first loop at 24. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h : ∀ fl, Q 24 { g with rax := 0#64, rcx := 7256432#64 } fl (Vst V g.rdx (toBytesLE (0#64) 8))) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_0, o0, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `add rax, 1; cmp rax, 16; jne 24`: on to 24, or to 45 after the 16th byte. -/
theorem vc_35 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h24 : ¬ g.rax + 1#64 = 16#64 → ∀ fl, Q 24 { g with rax := g.rax + 1#64 } fl V)
    (h45 : g.rax + 1#64 = 16#64 → ∀ fl, Q 45 { g with rax := g.rax + 1#64 } fl V) :
    W_35 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h24 h45 ⊢
  wpx [W_35, o2, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | (apply h24 <;> assumption)
    | (apply h45 <;> assumption)
    | apply And.intro
    | intro _)

/-- One step of the first loop (`rax` the index, `rcx` = `0x6eb970`): the IID's byte against `iid`'s; on a match
the counter (to 24 or 45); on a mismatch the second loop's first compare (`rcx` = `0x6eb890`, `rax` = 0), to 88 or
109. -/
theorem vc_24 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fc : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (0#64 + 7256208#64) i))
    (fd : ∀ i : Nat, i < 1 → Foot F.data (Addr.add g.rsi i))
    (h24 : bq V (g.rax + g.rcx) = bq V (g.rsi + g.rax) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 24 { g with
        rax := g.rax + 1#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rsi + g.rax))) } fl V)
    (h45 : bq V (g.rax + g.rcx) = bq V (g.rsi + g.rax) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 45 { g with
        rax := g.rax + 1#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rsi + g.rax))) } fl V)
    (h109 : ¬ bq V (g.rax + g.rcx) = bq V (g.rsi + g.rax) → ¬ bq V g.rsi = bq V (0#64 + 7256208#64) →
      ∀ fl, Q 109 { g with
        rax := 0#64
        rcx := 7256208#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rsi + g.rax)))
        r9 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (0#64 + 7256208#64))) } fl V)
    (h88 : ¬ bq V (g.rax + g.rcx) = bq V (g.rsi + g.rax) → bq V g.rsi = bq V (0#64 + 7256208#64) →
      ∀ fl, Q 88 { g with
        rax := 0#64
        rcx := 7256208#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rsi + g.rax)))
        r9 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (0#64 + 7256208#64))) } fl V) :
    W_24 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fc fd h24 h45 h109 h88 ⊢
  wpx [W_24, W_35, W_64, W_84, o1, o2, o5, o6, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h24 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h45 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h109 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h88 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | apply And.intro
    | intro _)

/-- `lea rax, [rdi + 8]; mov [rdx], rax` (`*ppv = this + 8`) on a match of the first or second IID, on to the
`AddRef` at 52. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h : ∀ fl, Q 52 { g with rax := g.rdi + 8#64 } fl (Vst V g.rdx (toBytesLE (g.rdi + 8#64) 8))) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_45, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `xor eax, eax` (`S_OK`), on to the `ret` at 58. -/
theorem vc_56 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 58 { g with rax := 0#64 } fl V) :
    W_56 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_56, o4, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov ecx, 0x6eb780; xor eax, eax`, to the third loop at 128. -/
theorem vc_109 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 128 { g with rax := 0#64, rcx := 7255936#64 } fl V) :
    W_109 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_109, o8, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- The counter of the second loop (`rcx` = `0x6eb890`), then its next compare: to 45 after the 16th byte, else
to 88 (match) or 109 (mismatch). -/
theorem vc_88 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ¬ g.rax + 1#64 = 16#64 → ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + 1#64 + g.rcx) i))
    (fb : ¬ g.rax + 1#64 = 16#64 → ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + (g.rax + 1#64)) i))
    (h45 : g.rax + 1#64 = 16#64 → ∀ fl, Q 45 { g with rax := g.rax + 1#64 } fl V)
    (h88 : ¬ g.rax + 1#64 = 16#64 → bq V (g.rsi + (g.rax + 1#64)) = bq V (g.rax + 1#64 + g.rcx) →
      ∀ fl, Q 88 { g with
        rax := g.rax + 1#64
        r9 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + 1#64 + g.rcx))) } fl V)
    (h109 : ¬ g.rax + 1#64 = 16#64 → ¬ bq V (g.rsi + (g.rax + 1#64)) = bq V (g.rax + 1#64 + g.rcx) →
      ∀ fl, Q 109 { g with
        rax := g.rax + 1#64
        r9 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + 1#64 + g.rcx))) } fl V) :
    W_88 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb h45 h88 h109 ⊢
  wpx [W_88, W_98, o2, o7, Op.cmpmr, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply fa <;> assumption)
    | (apply fb <;> assumption)
    | (apply h45 <;> assumption)
    | (apply h88 <;> assumption)
    | (apply h109 <;> assumption)
    | apply And.intro
    | intro _)

/-- One step of the third loop (`rcx` = `0x6eb780`): on a match on to 128, or (the 16 bytes done) `*ppv = this +
16; xor eax, eax` to the `AddRef` at 158; on a mismatch `mov ecx, 0x6eb760; xor eax, eax` to the fourth loop at
184. -/
theorem vc_128 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h128 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 128 { g with
        rax := g.rax + 1#64
        r10 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h158 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 158 { g with
        rax := 0#64
        r10 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) }
        fl (Vst V g.rdx (toBytesLE (g.rdi + 16#64) 8)))
    (h184 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 184 { g with
        rax := 0#64
        rcx := 7255904#64
        r10 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_128 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h128 h158 h184 ⊢
  wpx [W_128, W_139, W_149, W_168, o2, o9, o10, o11, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h128 <;> assumption)
    | (apply h158 <;> assumption)
    | (apply h184 <;> assumption)
    | apply And.intro
    | intro _)

/-- One step of the loop at 184 (`rcx` its IID): on a match on to 184, or (the 16 bytes done) `*ppv = this + 24`
to the `AddRef` at 52; on a mismatch `mov ecx, 0x6eb7f0; xor eax, eax` to the next loop at 232. -/
theorem vc_184 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h184 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 184 { g with
        rax := g.rax + 1#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h52 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 52 { g with
        rax := g.rdi + 24#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) }
        fl (Vst V g.rdx (toBytesLE (g.rdi + 24#64) 8)))
    (h232 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 232 { g with
        rax := 0#64
        rcx := 7256048#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_184 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h184 h52 h232 ⊢
  wpx [W_184, W_195, W_205, W_217, o2, o12, o13, o14, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h184 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h52 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h232 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | apply And.intro
    | intro _)

/-- One step of the loop at 232 (`rcx` its IID): on a match on to 232, or (the 16 bytes done) `*ppv = this + 32`
to the `AddRef` at 52; on a mismatch `mov ecx, 0x6eb7e0; xor eax, eax` to the next loop at 280. -/
theorem vc_232 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h232 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 232 { g with
        rax := g.rax + 1#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h52 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 52 { g with
        rax := g.rdi + 32#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) }
        fl (Vst V g.rdx (toBytesLE (g.rdi + 32#64) 8)))
    (h280 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 280 { g with
        rax := 0#64
        rcx := 7256032#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_232 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h232 h52 h280 ⊢
  wpx [W_232, W_243, W_253, W_265, o2, o12, o15, o16, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h232 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h52 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h280 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | apply And.intro
    | intro _)

/-- One step of the loop at 280 (`rcx` its IID): on a match on to 280, or (the 16 bytes done) `*ppv = this + 40`
to the `AddRef` at 52; on a mismatch `mov ecx, 0x6eb790; xor eax, eax` to the next loop at 328. -/
theorem vc_280 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h280 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 280 { g with
        rax := g.rax + 1#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h52 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 52 { g with
        rax := g.rdi + 40#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) }
        fl (Vst V g.rdx (toBytesLE (g.rdi + 40#64) 8)))
    (h328 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 328 { g with
        rax := 0#64
        rcx := 7255952#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_280 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h280 h52 h328 ⊢
  wpx [W_280, W_291, W_301, W_313, o2, o12, o17, o18, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h280 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h52 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h328 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | apply And.intro
    | intro _)

/-- One step of the loop at 328 (`rcx` its IID): on a match on to 328, or (the 16 bytes done) `*ppv = this + 48`
to the `AddRef` at 52; on a mismatch `mov eax, E_NOINTERFACE` to the `ret` at 366. -/
theorem vc_328 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h328 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 328 { g with
        rax := g.rax + 1#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h52 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 52 { g with
        rax := g.rdi + 48#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) }
        fl (Vst V g.rdx (toBytesLE (g.rdi + 48#64) 8)))
    (h366 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 366 { g with
        rax := 2147500034#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_328 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h328 h52 h366 ⊢
  wpx [W_328, W_339, W_349, W_361, o2, o12, o19, o20, Op.cmpmr, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h328 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h52 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | (apply h366 <;> first | assumption | exact Eq.symm (by assumption) | exact Ne.symm (by assumption))
    | apply And.intro
    | intro _)

end FV7z.Aeq
