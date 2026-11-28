import FV7z.Ecq.Cuts
import FV7z.Lemmas.LeafRet
/-!
# `CExtractCallbackConsole::QueryInterface`: the pieces at the cut points (PLAN.md §M, M1)

7-Zip 26.06's `CExtractCallbackConsole::QueryInterface (iid, ppv)` (`Z7_COM_QI_*`,
`CPP/7zip/UI/Console/ExtractCallbackConsole.h`; `objdump -d`) at `0x5e9f00` in `7zzs`, `this` = `rdi`, `iid` =
`rsi`, `ppv` = `rdx`: `*ppv = NULL`, then five loops comparing the 16 bytes of `iid` with the IIDs at `0x6eb970`
(24), `0x6eb590` (64, 88, 98), `0x6eb580` (128), `0x6eb780` (192), `0x6eb790` (240), byte by byte (`movzx r8d,
byte [rax + rcx]; cmp byte [rsi + rax], r8b`, `OpI.cmpmr8`). On a match `*ppv` = `this` + 0, 0, 16, 24, 32 and
`AddRef` inline (`add dword [rdi + 0x138], 1`, by hand at 48 and 158), `S_OK`; else `E_NOINTERFACE` (273).

- `bq V a`: the byte at `a`; `sw8`: a byte zero-extended to 32 bits and cut back.
- `vc_0`: `*ppv = NULL`, to the first loop at 24 with `rax` = 0, `rcx` = `0x6eb970`.
- `vc_24`: one step of the first loop: on a match on to 24 or (the 16 bytes done) to 45; on a mismatch the second
  loop's first compare, to 88 (match) or 109 (mismatch).
- `vc_35`: the counter of the first loop.
- `vc_45`: `*ppv = this`, to the `AddRef` at 48; `vc_55`: `S_OK`, to the `ret` at 57.
- `vc_88`: the counter of the second loop and its next compare; `vc_109`: to the third loop.
- `vc_128`, `vc_192`, `vc_240`: one step of the third, fourth and fifth loop with its exits.

The loops by induction are in `Loop1`, `Loop2`, `Loop3`, `Loop45`; the `AddRef`s and `ret`s in `Tail`; `ecq_ok`
in `Ok`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ecq

/-- The byte at `a`. -/
abbrev bq (V : Addr → Byte) (a : Addr) : BitVec 8 := ofBytesLE 8 (List.map V (byteAddrs a 1))

theorem sw8 (x : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

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

/-- One step of the first loop (`rax` the index, `rcx` = `0x6eb970`): the byte of `iid` against the IID's; on a
match the counter (to 24 or 45); on a mismatch the second loop's first compare (`rcx` = `0x6eb590`, `rax` = 0), to
88 or 109. -/
theorem vc_24 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fc : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (0#64 + 7255440#64) i))
    (fd : ∀ i : Nat, i < 1 → Foot F.data (Addr.add g.rsi i))
    (h24 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 24 { g with
        rax := g.rax + 1#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h45 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 45 { g with
        rax := g.rax + 1#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h109 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ bq V g.rsi = bq V (0#64 + 7255440#64) →
      ∀ fl, Q 109 { g with
        rax := 0#64
        rcx := 7255440#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx)))
        r9 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (0#64 + 7255440#64))) } fl V)
    (h88 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → bq V g.rsi = bq V (0#64 + 7255440#64) →
      ∀ fl, Q 88 { g with
        rax := 0#64
        rcx := 7255440#64
        r8 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx)))
        r9 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (0#64 + 7255440#64))) } fl V) :
    W_24 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fc fd h24 h45 h109 h88 ⊢
  wpx [W_24, W_35, W_64, W_84, o1, o2, o5, o6, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h24 <;> assumption)
    | (apply h45 <;> assumption)
    | (apply h109 <;> assumption)
    | (apply h88 <;> assumption)
    | apply And.intro
    | intro _)

/-- `*ppv = this` on a match of the first or second IID, on to the `AddRef` at 48. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h : ∀ fl, Q 48 g fl (Vst V g.rdx (toBytesLE g.rdi 8))) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fw h ⊢
  wpx [W_45, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `xor eax, eax` (`S_OK`), on to the `ret` at 57. -/
theorem vc_55 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 57 { g with rax := 0#64 } fl V) :
    W_55 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_55, o4, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- `mov ecx, 0x6eb580; xor eax, eax`, to the third loop at 128. -/
theorem vc_109 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 128 { g with rax := 0#64, rcx := 7255424#64 } fl V) :
    W_109 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_109, o8, lf_xz, BitVec.xor_self, BitVec.setWidth_zero]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- The counter of the second loop (`rcx` = `0x6eb590`), then its next compare: to 45 after the 16th byte, else
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

/-- One step of the third loop (`rcx` = `0x6eb580`): on a match on to 128, or (the 16 bytes done) `*ppv = this +
16; xor eax, eax` to the `AddRef` at 158; on a mismatch `mov ecx, 0x6eb780; xor eax, eax` to the fourth loop at
192. -/
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
    (h192 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 192 { g with
        rax := 0#64
        rcx := 7255936#64
        r10 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_128 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h128 h158 h192 ⊢
  wpx [W_128, W_139, W_149, W_176, o2, o9, o10, o11, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h128 <;> assumption)
    | (apply h158 <;> assumption)
    | (apply h192 <;> assumption)
    | apply And.intro
    | intro _)

/-- One step of the fourth loop (`rcx` = `0x6eb780`): on a match on to 192, or (the 16 bytes done) `*ppv = this +
24` to the `AddRef` at 48; on a mismatch `mov ecx, 0x6eb790; xor eax, eax` to the fifth loop at 240. -/
theorem vc_192 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h192 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 192 { g with
        rax := g.rax + 1#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h48 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 48 { g with
        rax := g.rdi + 24#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) }
        fl (Vst V g.rdx (toBytesLE (g.rdi + 24#64) 8)))
    (h240 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 240 { g with
        rax := 0#64
        rcx := 7255952#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_192 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h192 h48 h240 ⊢
  wpx [W_192, W_203, W_213, W_225, o2, o12, o13, o14, Op.cmpmr, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h192 <;> assumption)
    | (apply h48 <;> assumption)
    | (apply h240 <;> assumption)
    | apply And.intro
    | intro _)

/-- One step of the fifth loop (`rcx` = `0x6eb790`): on a match on to 240, or (the 16 bytes done) `*ppv = this +
32` to the `AddRef` at 48; on a mismatch `mov eax, E_NOINTERFACE` to the `ret` at 278. -/
theorem vc_240 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fa : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rax + g.rcx) i))
    (fb : ∀ i : Nat, i < 1 → Foot F.data (Addr.add (g.rsi + g.rax) i))
    (fw : ∀ i < 8, Foot Wl (Addr.add g.rdx i))
    (h240 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → ¬ g.rax + 1#64 = 16#64 →
      ∀ fl, Q 240 { g with
        rax := g.rax + 1#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V)
    (h48 : bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) → g.rax + 1#64 = 16#64 →
      ∀ fl, Q 48 { g with
        rax := g.rdi + 32#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) }
        fl (Vst V g.rdx (toBytesLE (g.rdi + 32#64) 8)))
    (h278 : ¬ bq V (g.rsi + g.rax) = bq V (g.rax + g.rcx) →
      ∀ fl, Q 278 { g with
        rax := 2147500034#64
        r11 := BitVec.setWidth 64 (BitVec.setWidth 32 (bq V (g.rax + g.rcx))) } fl V) :
    W_240 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [bq] at fa fb fw h240 h48 h278 ⊢
  wpx [W_240, W_251, W_261, W_273, o2, o12, o15, o16, Op.cmpmr, sw8,
    Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | exact trivial
    | assumption
    | (apply h240 <;> assumption)
    | (apply h48 <;> assumption)
    | (apply h278 <;> assumption)
    | apply And.intro
    | intro _)

end FV7z.Ecq
