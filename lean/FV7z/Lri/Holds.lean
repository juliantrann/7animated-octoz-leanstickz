import FV7z.Lri.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallReg
import FV7z.Lemmas.AddMr64
import FV7z.Lemmas.Fr40
import FV7z.Rst.Holds
/-!
# `NCompress::NLzma::CDecoder::ReadFromInputStream` (PLAN.md §M, M1)

7-Zip 26.06's `HRESULT CDecoder::ReadFromInputStream (void *data, UInt32 size, UInt32 *processedSize)` at
`0x5801f0` in `7zzs` (`CPP/7zip/Compress/LzmaDecoder.cpp`; `objdump -d`), `this` = `rdi` (`T`), `data` = `rsi`,
`size` = `edx`, `processedSize` = `rcx`, `S` the stack pointer at the entry. (The prefix is `Lri`: `Rfi` is taken by
`__register_frame_info`.) The six pushes (`Rst.V1`) and `sub rsp, 0x18` (`Rst.aR S`), `r15d` = `size`, `r14` =
`this`, `r13` = `data`, `rbp` = `processedSize`; at 30 the `call` of `CreateInputBuffer` (`0x57fcc0`), its `eax`
stored at `aR S + 12` (35); not 0 to 97; else `*processedSize = 0` when `rbp` is not 0 (48), and the loop (64):
`r15d` (what is left, `s`) 0 to 97; `_inPos` (`T + 88`) not `_inLim` (`T + 92`) to the copy (183); else (81)
`eax` = the slot at `aR S + 12`, `_inPos = _inLim = 0` (one quadword store), the slot not 0 to 97, else the read
(120): `rdi` = `_inStream` (`[T + 256]`), its vtable's entry at 24 compared with `0x57fb60` (the devirtualized
`Read`): equal, `rdi -= 56` and the `call` of `0x57f9b0` (162); else `call rax` (248, `Seg.s_callr`); either way
`Read (_inStream, _inBuf, _inBufSize, &_inLim)` (`rsi` = `[T + 96]`, `edx` = `[T + 76]`, `rcx` = `T + 92`), its
`eax` stored at `aR S + 12` (167, 250); at 171 `_inLim` 0 to 97, else `esi` = `_inPos` and the copy. The copy
(183): `cur` = `min (s, _inLim - _inPos)` (`cmovbe`, `cu`), `memcpy (data, _inBuf + _inPos, cur)` (211, PLT
`0x401070`); back (216, by hand) `_inPos += cur` (`Seg.s_add_mr32`), `_inProcessed += cur` (220, `[T + 112]`,
`Seg.s_add_mr64`), `*processedSize += cur` when `rbp` is not 0 (233), `data += cur`, `s -= cur`, to 64. At 97
`eax` = the slot, `add rsp, 0x18`, the six pops, the `ret` (115).

The callees are hypotheses (`KC`: at the entry with the return address pushed; from the return with the registers
`Fr40.Fr` keeps): `k1` (`CreateInputBuffer`), `k2` (the direct `Read`), `k3` (the indirect one, at `eR`: the
vtable's entry, `htgt`, when not `0x57fb60`), `k4` (`memcpy`). The memory is the caller's invariant `I` (as in
`FV7z/Rst/Holds.lean`): of the bytes after the pushes, kept by the stores (`hI12`, `hIp`, `hI88`, `hI88q`,
`hI112`), giving the stack (`hIs`); the reads leave `_inPos` 0 (their post), the slot's store does not touch it
(`h88`). The loop by induction on `s`: each copy is not empty (`_inPos` ≠ `_inLim`, `cu_dec`).

- `Stk`, `Lk`, `Ar`, `cu`, `Cn`, `Tg`, `Z8`, `KC`: the stack, the loop's registers, a `Read`'s arguments, the copy's
  size, the read's target and bytes, the callees' contracts.
- `vc_*`: the pieces' conditions; `tail97`: from 97 to the return address; `lri_ok`: the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lri
set_option linter.unusedVariables false

open FV7z.Rst (aR e24 V1)
open FV7z.Wst (sa8)
open FV7z.Fr40 (Fr KS)

/-! ## The instructions outside the blocks -/

/-- The `call`s of `CreateInputBuffer`, the direct `Read`, `memcpy`; `call rax`; the `ret`; the `add`s. -/
def pc1 : List Byte := [0xe8, 0xad, 0xfa, 0xff, 0xff]
theorem pc1_0 : ∀ feat, Dec feat pc1 0 (FV7z.mk .call 64 [.rel 18446744073709550253] 5) := by dec_rfl
theorem wc_30 : pc1 <+: lri.drop 30 := by decide +kernel
theorem call_30 (feat : Features) : Dec feat lri 30 (FV7z.mk .call 64 [.rel 18446744073709550253] 5) :=
  Dec.shift (j := 30) (k := 0) (pc1_0 feat) wc_30 (Nat.zero_le _)

def pc2 : List Byte := [0xe8, 0x19, 0xf7, 0xff, 0xff]
theorem pc2_0 : ∀ feat, Dec feat pc2 0 (FV7z.mk .call 64 [.rel 18446744073709549337] 5) := by dec_rfl
theorem wc_162 : pc2 <+: lri.drop 162 := by decide +kernel
theorem call_162 (feat : Features) : Dec feat lri 162 (FV7z.mk .call 64 [.rel 18446744073709549337] 5) :=
  Dec.shift (j := 162) (k := 0) (pc2_0 feat) wc_162 (Nat.zero_le _)

def pc4 : List Byte := [0xe8, 0xa8, 0x0d, 0xe8, 0xff]
theorem pc4_0 : ∀ feat, Dec feat pc4 0 (FV7z.mk .call 64 [.rel 18446744073707982248] 5) := by dec_rfl
theorem wc_211 : pc4 <+: lri.drop 211 := by decide +kernel
theorem call_211 (feat : Features) : Dec feat lri 211 (FV7z.mk .call 64 [.rel 18446744073707982248] 5) :=
  Dec.shift (j := 211) (k := 0) (pc4_0 feat) wc_211 (Nat.zero_le _)

def pcr : List Byte := [0xff, 0xd0]
theorem pcr_0 : ∀ feat, Dec feat pcr 0 (FV7z.mk .call 64 [gr 64 0] 2) := by dec_rfl
theorem wc_248 : pcr <+: lri.drop 248 := by decide +kernel
theorem callr_248 (feat : Features) : Dec feat lri 248 (FV7z.mk .call 64 [gr 64 0] 2) :=
  Dec.shift (j := 248) (k := 0) (pcr_0 feat) wc_248 (Nat.zero_le _)

def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_115 : pret <+: lri.drop 115 := by decide +kernel
theorem ret_115 (feat : Features) : Dec feat lri 115 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 115) (k := 0) (pret_0 feat) w_115 (Nat.zero_le _)

/-- `add dword [r14 + 0x58], ebx`. -/
def pa1 : List Byte := [0x41, 0x01, 0x5e, 0x58]
theorem pa1_0 : ∀ feat, Dec feat pa1 0 (FV7z.mk .add 32 [.mem (mbd 14 88 32), gr 32 3] 4) := by dec_rfl
theorem wa_216 : pa1 <+: lri.drop 216 := by decide +kernel
theorem add_216 (feat : Features) : Dec feat lri 216 (FV7z.mk .add 32 [.mem (mbd 14 88 32), gr 32 3] 4) :=
  Dec.shift (j := 216) (k := 0) (pa1_0 feat) wa_216 (Nat.zero_le _)

/-- `add qword [r14 + 0x70], r12`. -/
def pa2 : List Byte := [0x4d, 0x01, 0x66, 0x70]
theorem pa2_0 : ∀ feat, Dec feat pa2 0 (FV7z.mk .add 64 [.mem (mbd 14 112 64), gr 64 12] 4) := by dec_rfl
theorem wa_220 : pa2 <+: lri.drop 220 := by decide +kernel
theorem addq_220 (feat : Features) : Dec feat lri 220 (FV7z.mk .add 64 [.mem (mbd 14 112 64), gr 64 12] 4) :=
  Dec.shift (j := 220) (k := 0) (pa2_0 feat) wa_220 (Nat.zero_le _)

/-- `add dword [rbp], ebx`. -/
def pa3 : List Byte := [0x01, 0x5d, 0x00]
theorem pa3_0 : ∀ feat, Dec feat pa3 0 (FV7z.mk .add 32 [.mem (mbd 5 0 32), gr 32 3] 3) := by dec_rfl
theorem wa_233 : pa3 <+: lri.drop 233 := by decide +kernel
theorem add_233 (feat : Features) : Dec feat lri 233 (FV7z.mk .add 32 [.mem (mbd 5 0 32), gr 32 3] 3) :=
  Dec.shift (j := 233) (k := 0) (pa3_0 feat) wa_233 (Nat.zero_le _)

/-! ## Registers, bytes, the copy's size -/

/-- The stack: the saved `r15`, `r14`, `r13`, `r12`, `rbp`, `rbx`, the return address. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8) = g0.r15 ∧ rdq(W, S - 8 - 8) = g0.r14 ∧ rdq(W, S - 8 - 8 - 8) = g0.r13 ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S) = ra

/-- The loop's registers: `rsp` = `A`, `r14` = `this`, `rbp` = `processedSize`, `r13` = the data, `r15` = what is
left (widened). -/
abbrev Lk (A T b p r : Addr) (g : Gprs) : Prop := g.rsp = A ∧ g.r14 = T ∧ g.rbp = b ∧ g.r13 = p ∧ g.r15 = r

theorem Lk.fr {A T b p r : Addr} {g g' : Gprs} (h : Lk A T b p r g) (h' : Fr g g') : Lk A T b p r g' :=
  ⟨h'.1.trans h.1, h'.2.2.2.2.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.2.2.trans h.2.2.2.2⟩

/-- A `Read`'s arguments but `this`: `_inBuf`, `_inBufSize`, `&_inLim`. -/
abbrev Ar (T : Addr) (V : Addr → Byte) (g : Gprs) : Prop :=
  g.rsi = rdq(V, T + 96#64) ∧ g.rdx = BitVec.setWidth 64 rdd(V, T + 76#64) ∧ g.rcx = T + 92#64

/-- `cmp r15d, ebx; cmovbe ebx, r15d`: the smaller. -/
def cu (a d : BitVec 32) : BitVec 32 := if a.toNat ≤ d.toNat then a else d

/-- The copy's size from `s` left and the bytes `W`. -/
abbrev Cn (T : Addr) (s : BitVec 32) (W : Addr → Byte) : BitVec 32 := cu s (rdd(W, T + 92#64) - rdd(W, T + 88#64))

/-- The vtable's entry at 24 of `_inStream`. -/
abbrev Tg (T : Addr) (W : Addr → Byte) : Addr := rdq(W, rdq(W, rdq(W, T + 256#64)) + 24#64)

/-- The bytes after `_inPos = _inLim = 0`. -/
abbrev Z8 (T : Addr) (W : Addr → Byte) : Addr → Byte := Vst W (T + 88#64) (toBytesLE 0#64 8)

theorem cu_dec {s d : BitVec 32} {n : Nat} (hs : s ≠ 0) (hd : d ≠ 0) (hn : s.toNat < n + 1) :
    (s - cu s d).toNat < n := by
  unfold cu
  by_cases h : s.toNat ≤ d.toNat
  · rw [if_pos h]; bv_omega
  · rw [if_neg h]; bv_omega

theorem sub_ne {x y : BitVec 32} (h : ¬y = x) : x - y ≠ 0 := by bv_omega

/-! ## The pieces -/

/-- `wpx` with the flags' lemmas of the pieces here. -/
macro "lrx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [not_true_eq_false, not_false_eq_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, decide_true, decide_false, BitVec.and_self, eq_self_iff_true,
    Bool.true_or, Bool.false_or, ↓reduceIte, $ls,*])

/-- The closers after `refine h …`. -/
macro "lrc" : tactic =>
  `(tactic| first
    | with_reducible rfl
    | with_reducible assumption
    | exact toBytesLE_length _ _
    | exact trivial
    | apply And.intro
    | intro _)

variable {F : Footprint} {Wl : List Rgn}

/-- The pushes, `r15d` = `size`, `r14` = `this`, `r13` = `data`, `rbp` = `processedSize`, `sub rsp, 0x18`, to
the `call` at 30. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (h : ∀ g', g'.rdi = g.rdi →
      Lk (aR g.rsp) g.rdi g.rcx g.rsi (BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx)) g' →
      ∀ fl, Q 30 g' fl (V1 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V1] at hs1 hs2 hs3 hs4 hs5 hs6 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | refine h _ ?_ ?_ _ | lrc)

/-- `mov [rsp + 0xc], eax; test eax, eax`: not 0, to 97. -/
theorem vc_35e {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (w12 : ∀ i < 4, Foot Wl (Addr.add (A + 12#64) i)) (ha : (BitVec.setWidth 32 g.rax == 0) = false)
    (h : ∀ g', g'.rsp = A → ∀ fl, Q 97 g' fl (Vst V (A + 12#64) (toBytesLE (BitVec.setWidth 32 g.rax) 4))) :
    W_35 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ha h ⊢
  subst hs hT hb hp hr
  lrx [W_35, o1, ha]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- `eax` 0, `processedSize` null: to 64. -/
theorem vc_35z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (w12 : ∀ i < 4, Foot Wl (Addr.add (A + 12#64) i)) (ha : (BitVec.setWidth 32 g.rax == 0) = true)
    (hbz : (b == 0) = true)
    (h : ∀ g', Lk A T b p r g' → ∀ fl, Q 64 g' fl (Vst V (A + 12#64) (toBytesLE (BitVec.setWidth 32 g.rax) 4))) :
    W_35 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ha h ⊢
  subst hs hT hb hp hr
  lrx [W_35, W_43, o1, o2, ha, hbz]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- `eax` 0, `processedSize` not null: `*processedSize = 0`, to 64. -/
theorem vc_35p {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (w12 : ∀ i < 4, Foot Wl (Addr.add (A + 12#64) i)) (ha : (BitVec.setWidth 32 g.rax == 0) = true)
    (hbz : (b == 0) = false) (wp : ∀ i < 4, Foot Wl (Addr.add b i))
    (h : ∀ g', Lk A T b p r g' → ∀ fl,
      Q 64 g' fl (Vst (Vst V (A + 12#64) (toBytesLE (BitVec.setWidth 32 g.rax) 4)) b (toBytesLE 0#32 4))) :
    W_35 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ha h ⊢
  subst hs hT hb hp hr
  lrx [W_35, W_43, W_48, o1, o2, o3, ha, hbz]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- `test r15d, r15d`: nothing left, to 97. -/
theorem vc_64z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (hz : (BitVec.setWidth 32 r == 0) = true) (h : ∀ g', g'.rsp = A → ∀ fl, Q 97 g' fl V) :
    W_64 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  lrx [W_64, o4, hz]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- Something left, `_inPos` not `_inLim`: `esi` = `_inPos`, `ebx` = `_inLim`, to the copy (183). -/
theorem vc_64c {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (hz : (BitVec.setWidth 32 r == 0) = false)
    (f88 : ∀ i < 4, Foot F.data (Addr.add (T + 88#64) i)) (f92 : ∀ i < 4, Foot F.data (Addr.add (T + 92#64) i))
    (hne : ¬rdd(V, T + 88#64) = rdd(V, T + 92#64))
    (h : ∀ g', Lk A T b p r g' → g'.rsi = BitVec.setWidth 64 rdd(V, T + 88#64) →
      g'.rbx = BitVec.setWidth 64 rdd(V, T + 92#64) → ∀ fl, Q 183 g' fl V) :
    W_64 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  have hc := eq_false hne
  lrx [W_64, W_69, o4, o5, hz, hc]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | lrc)

/-- `_inPos` = `_inLim`: `eax` = the slot, `_inPos = _inLim = 0`; the slot not 0, to 97. -/
theorem vc_64e {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (hz : (BitVec.setWidth 32 r == 0) = false)
    (f88 : ∀ i < 4, Foot F.data (Addr.add (T + 88#64) i)) (f92 : ∀ i < 4, Foot F.data (Addr.add (T + 92#64) i))
    (heq : rdd(V, T + 88#64) = rdd(V, T + 92#64)) (f12 : ∀ i < 4, Foot F.data (Addr.add (A + 12#64) i))
    (w88 : ∀ i < 8, Foot Wl (Addr.add (T + 88#64) i)) (h12 : (rdd(V, A + 12#64) == 0) = false)
    (h : ∀ g', g'.rsp = A → ∀ fl, Q 97 g' fl (Vst V (T + 88#64) (toBytesLE 0#64 8))) :
    W_64 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  have hc := eq_true heq
  lrx [W_64, W_69, W_81, o4, o5, o6, hz, hc, h12]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- `_inPos` = `_inLim`, the slot 0: `_inPos = _inLim = 0`, to the read (120). -/
theorem vc_64r {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (hz : (BitVec.setWidth 32 r == 0) = false)
    (f88 : ∀ i < 4, Foot F.data (Addr.add (T + 88#64) i)) (f92 : ∀ i < 4, Foot F.data (Addr.add (T + 92#64) i))
    (heq : rdd(V, T + 88#64) = rdd(V, T + 92#64)) (f12 : ∀ i < 4, Foot F.data (Addr.add (A + 12#64) i))
    (w88 : ∀ i < 8, Foot Wl (Addr.add (T + 88#64) i)) (h12 : (rdd(V, A + 12#64) == 0) = true)
    (h : ∀ g', Lk A T b p r g' → ∀ fl, W_120 F Wl Q g' fl (Vst V (T + 88#64) (toBytesLE 0#64 8))) :
    W_64 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  have hc := eq_true heq
  lrx [W_64, W_69, W_81, o4, o5, o6, hz, hc, h12]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- The read, the vtable's entry `0x57fb60`: `rdi` = `_inStream - 56`, to the `call` at 162. -/
theorem vc_120d {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (f256 : ∀ i < 8, Foot F.data (Addr.add (T + 256#64) i)) (f76 : ∀ i < 4, Foot F.data (Addr.add (T + 76#64) i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (T + 96#64) i))
    (fv1 : ∀ i < 8, Foot F.data (Addr.add rdq(V, T + 256#64) i))
    (fv2 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, rdq(V, T + 256#64)) + 24#64) i))
    (ht : rdq(V, rdq(V, rdq(V, T + 256#64)) + 24#64) = 5765984#64)
    (h : ∀ g', Lk A T b p r g' → g'.rdi = rdq(V, T + 256#64) - 56#64 → Ar T V g' → ∀ fl, Q 162 g' fl V) :
    W_120 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  have hc := eq_true ht
  lrx [W_120, W_158, o8, o9, hc]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | lrc)

/-- The read, another entry: `call rax` at 248. -/
theorem vc_120i {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (f256 : ∀ i < 8, Foot F.data (Addr.add (T + 256#64) i)) (f76 : ∀ i < 4, Foot F.data (Addr.add (T + 76#64) i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (T + 96#64) i))
    (fv1 : ∀ i < 8, Foot F.data (Addr.add rdq(V, T + 256#64) i))
    (fv2 : ∀ i < 8, Foot F.data (Addr.add (rdq(V, rdq(V, T + 256#64)) + 24#64) i))
    (ht : ¬rdq(V, rdq(V, rdq(V, T + 256#64)) + 24#64) = 5765984#64)
    (h : ∀ g', Lk A T b p r g' → g'.rax = rdq(V, rdq(V, rdq(V, T + 256#64)) + 24#64) →
      g'.rdi = rdq(V, T + 256#64) → Ar T V g' → ∀ fl, Q 248 g' fl V) :
    W_120 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  have hc := eq_false ht
  lrx [W_120, o8, hc]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ _ | lrc)

/-- Back from the direct `Read`: its `eax` to the slot, to 171. -/
theorem vc_167 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (w12 : ∀ i < 4, Foot Wl (Addr.add (A + 12#64) i))
    (h : ∀ g', Lk A T b p r g' → ∀ fl,
      Q 171 g' fl (Vst V (A + 12#64) (toBytesLE (BitVec.setWidth 32 g.rax) 4))) :
    W_167 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr h ⊢
  subst hs hT hb hp hr
  lrx [W_167, o10]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- Back from `call rax`: its `eax` to the slot, `jmp 171`. -/
theorem vc_250 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (w12 : ∀ i < 4, Foot Wl (Addr.add (A + 12#64) i))
    (h : ∀ g', Lk A T b p r g' → ∀ fl,
      Q 171 g' fl (Vst V (A + 12#64) (toBytesLE (BitVec.setWidth 32 g.rax) 4))) :
    W_250 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr h ⊢
  subst hs hT hb hp hr
  lrx [W_250, o10]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- `ebx` = `_inLim` 0: to 97. -/
theorem vc_171z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (f92 : ∀ i < 4, Foot F.data (Addr.add (T + 92#64) i)) (hl : (rdd(V, T + 92#64) == 0) = true)
    (h : ∀ g', g'.rsp = A → ∀ fl, Q 97 g' fl V) :
    W_171 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  lrx [W_171, o11, hl]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- `_inLim` not 0: `esi` = `_inPos`, to the copy (183). -/
theorem vc_171c {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (f92 : ∀ i < 4, Foot F.data (Addr.add (T + 92#64) i)) (f88 : ∀ i < 4, Foot F.data (Addr.add (T + 88#64) i))
    (hl : (rdd(V, T + 92#64) == 0) = false)
    (h : ∀ g', Lk A T b p r g' → g'.rsi = BitVec.setWidth 64 rdd(V, T + 88#64) →
      g'.rbx = BitVec.setWidth 64 rdd(V, T + 92#64) → ∀ fl, Q 183 g' fl V) :
    W_171 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  lrx [W_171, W_179, o11, o12, hl]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | lrc)

/-- The copy's registers: `cur` = `cu s (lim - pos)`, `rsi` = `_inBuf + pos`, `rdx` = `cur`, `r15d -= cur`,
`r13 += cur`, to the `call` of `memcpy` (211). -/
theorem vc_183 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p : Addr} {s lim pos : BitVec 32}
    (hL : Lk A T b p (BitVec.setWidth 64 s) g) (hbx : g.rbx = BitVec.setWidth 64 lim)
    (hsi : g.rsi = BitVec.setWidth 64 pos) (f96 : ∀ i < 8, Foot F.data (Addr.add (T + 96#64) i))
    (h : ∀ g', Lk A T b (p + BitVec.setWidth 64 (cu s (lim - pos))) (BitVec.setWidth 64 (s - cu s (lim - pos))) g' →
      g'.rsi = BitVec.setWidth 64 pos + rdq(V, T + 96#64) → g'.rdx = BitVec.setWidth 64 (cu s (lim - pos)) →
      ∀ fl, Q 211 g' fl V) :
    W_183 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr hbx hsi ⊢
  subst hs hT hb hp hr hbx hsi
  by_cases hA : s.toNat < (lim - pos).toNat
  · rw [show cu s (lim - pos) = s from if_pos (Nat.le_of_lt hA)] at h
    have e1 := eq_true hA
    lrx [W_183, o13, e1]
    all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | lrc)
  · by_cases hB : s = lim - pos
    · rw [show cu s (lim - pos) = s from if_pos (Nat.le_of_eq (congrArg BitVec.toNat hB))] at h
      have e1 := eq_false hA
      have e2 := eq_true hB
      lrx [W_183, o13, e1, e2]
      all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | lrc)
    · rw [show cu s (lim - pos) = lim - pos from
        if_neg fun hle => hB (BitVec.eq_of_toNat_eq (Nat.le_antisymm hle (Nat.not_lt.1 hA)))] at h
      have e1 := eq_false hA
      have e2 := eq_false hB
      lrx [W_183, o13, e1, e2]
      all_goals repeat' (first | refine h _ ?_ ?_ ?_ _ | lrc)

/-- After the `add`s: `test rbp, rbp`, null to 64. -/
theorem vc_224z {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (hbz : (b == 0) = true) (h : ∀ g', Lk A T b p r g' → ∀ fl, Q 64 g' fl V) :
    W_224 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  lrx [W_224, o2, hbz]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- Not null: to the `add` at 233. -/
theorem vc_224n {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {A T b p r : Addr} (hL : Lk A T b p r g)
    (hbz : (b == 0) = false) (h : ∀ g', Lk A T b p r g' → ∀ fl, Q 233 g' fl V) :
    W_224 F Wl Q g f V := by
  obtain ⟨hs, hT, hb, hp, hr⟩ := hL
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs hT hb hp hr ⊢
  subst hs hT hb hp hr
  lrx [W_224, o2, hbz]
  all_goals repeat' (first | refine h _ ?_ _ | lrc)

/-- `jmp 64`. -/
theorem vc_236 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 64 g fl V) :
    W_236 F Wl Q g f V :=
  h (rfz f)

/-- `eax` = the slot, `add rsp, 0x18` and the six pops to the `ret`. -/
theorem vc_97 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (p6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 24#64) →
      g'.rbp = rdq(V, g.rsp + 24#64 + 8) → g'.r12 = rdq(V, g.rsp + 24#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8) →
      g'.r15 = rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) → ∀ fl, Q 115 g' fl V) :
    W_97 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 p1 p2 p3 p4 p5 p6 h ⊢
  wpx [W_97, o7]
  all_goals repeat' (first | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ | lrc)

/-! ## The runs -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- A callee at `tg` from a `call` returning to `lri_at + r` (registers `G` there, bytes `W`): at its entry, and
from its return with the registers `Fr` keeps and its post `P` on the bytes, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (tg : Addr) (r : Nat) (G : Gprs) (W : Addr → Byte) (P : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (G.rsp - 8) (toBytesLE (lri_at.add r) 8)) →
    Y.cpu.rip = tg → Y.cpu.gpr = G.set 4 (G.rsp - 8) →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = lri_at.add r → Fr G Z.cpu.gpr → P W' → GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- From 97 (`rsp` = `aR S`, the stack `Stk`) to the return address `e₂.add j₂`. -/
theorem tail97 {W : Addr → Byte} {S : Addr} {g0 : Gprs} {Y : State} (c : Seg prof F Wl L s₀ o)
    (hin : CodeIn L lri_at lri) (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W)
    (hr : Y.cpu.rip = lri_at.add 97) (hs : Y.cpu.gpr.rsp = aR S) (hst : Stk W S g0 (e₂.add j₂))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (aR S + 12#64) i))
    (g1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)) (g2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i))
    (g3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i))
    (g4 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i))
    (g5 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i))
    (g6 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add S i)) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (k : ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W → Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hst
  have q1 : Y.cpu.gpr.rsp + 24#64 = S - 8 - 8 - 8 - 8 - 8 - 8 := by rw [hs, e24]
  have q2 : Y.cpu.gpr.rsp + 24#64 + 8 = S - 8 - 8 - 8 - 8 - 8 := by rw [q1, sa8]
  have q3 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 = S - 8 - 8 - 8 - 8 := by rw [q2, sa8]
  have q4 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 = S - 8 - 8 - 8 := by rw [q3, sa8]
  have q5 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 = S - 8 - 8 := by rw [q4, sa8]
  have q6 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 = S - 8 := by rw [q5, sa8]
  have q7 : Y.cpu.gpr.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 = S := by rw [q6, sa8]
  refine (c_97 prof).run c hin (fun j' g' _ V' => j' = 115 ∧ V' = W ∧ g'.rsp = S ∧
      g'.rbx = g0.rbx ∧ g'.rbp = g0.rbp ∧ g'.r12 = g0.r12 ∧ g'.r13 = g0.r13 ∧ g'.r14 = g0.r14 ∧
      g'.r15 = g0.r15) hK hA hr
    (vc_97 (by rw [hs]; exact f12) (by rw [q1]; exact g6) (by rw [q2]; exact g5) (by rw [q3]; exact g4)
      (by rw [q4]; exact g3) (by rw [q5]; exact g2) (by rw [q6]; exact g1)
      fun _ a1 a2 a3 a4 a5 a6 a7 _ => ⟨rfl, rfl, a1.trans q7, a2.trans (by rw [q1]; exact s6),
        a3.trans (by rw [q2]; exact s5), a4.trans (by rw [q3]; exact s4), a5.trans (by rw [q4]; exact s3),
        a6.trans (by rw [q5]; exact s2), a7.trans (by rw [q6]; exact s1)⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_115 _) (by rw [gs]; exact hl) hin₂ h₂
    (by rw [gs]; exact s7) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine k Z' t₂ hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [gs]
  · rw [hgZ']
    exact ⟨gb, gp, g12, g13, g14, g15⟩

/-- `ReadFromInputStream (this, data, size, processedSize)` from its entry (`X`'s registers `g0`, `S` = `g0.rsp`,
`T` = `g0.rdi`): the pushes' slots, the slot at `aR S + 12`, the `call`s' return address slot, `_inPos`/`_inLim`
(`T + 88`), `_inProcessed` (`T + 112`) and `*processedSize` (when not null) in what the run may store into;
`_inLim`, `_inBufSize`, `_inBuf`, `_inStream`, the vtable's entry and the return address readable. The memory
invariant `I`: of the bytes after the pushes (`hI0`), kept by the stores (`hI12`, `hIp`, `hI88`, `hI88q`, `hI112`),
giving the stack (`hIs`); the slot's store keeps `_inPos` (`h88`). The callees: `k1` (`CreateInputBuffer`), `k2`
(the direct `Read`, `_inPos` 0 from its return), `k3` (`call rax` at `eR`, the vtable's entry when not
`0x57fb60`, `htgt`), `k4` (`memcpy` of `cu s (_inLim - _inPos)` bytes from `_inBuf + _inPos`). At the return
address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were. -/
theorem lri_ok {g0 : Gprs} {I : (Addr → Byte) → Prop} {eR : Addr}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L lri_at lri)
    {code1 : List Byte} (hin1 : CodeIn L 0x57fcc0#64 code1) (hc1 : 0 < code1.length)
    {code2 : List Byte} (hin2 : CodeIn L 0x57f9b0#64 code2) (hc2 : 0 < code2.length)
    {codeR : List Byte} (hinR : CodeIn L eR codeR) (hcR : 0 < codeR.length)
    {code4 : List Byte} (hin4 : CodeIn L 0x401070#64 code4) (hc4 : 0 < code4.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lri_at) (hg0 : X.cpu.gpr = g0)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR g0.rsp - 8) i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (aR g0.rsp + 12#64) i))
    (w88 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 88#64) i))
    (w112 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 112#64) i))
    (wp : g0.rcx ≠ 0 → ∀ i < 4, Foot Wl (Addr.add g0.rcx i))
    (f92 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 92#64) i))
    (f76 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 76#64) i))
    (f96 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 96#64) i))
    (f256 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 256#64) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add g0.rsp i))
    (fv1 : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add rdq(W, g0.rdi + 256#64) i))
    (fv2 : ∀ W, I W → ∀ i < 8, Foot F.data (Addr.add (rdq(W, rdq(W, g0.rdi + 256#64)) + 24#64) i))
    (htgt : ∀ W, I W → Tg g0.rdi W ≠ 5765984#64 → Tg g0.rdi W = eR)
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hI0 : I (V1 V g0))
    (hI12 : ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W (aR g0.rsp + 12#64) bs))
    (hIp : g0.rcx ≠ 0 → ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W g0.rcx bs))
    (hI88 : ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W (g0.rdi + 88#64) bs))
    (hI88q : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rdi + 88#64) bs))
    (hI112 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rdi + 112#64) bs))
    (h88 : ∀ W (bs : List Byte), bs.length = 4 →
      rdd(Vst W (aR g0.rsp + 12#64) bs, g0.rdi + 88#64) = rdd(W, g0.rdi + 88#64))
    (hIs : ∀ W, I W → Stk W g0.rsp g0 (e₂.add j₂))
    (k1 : ∀ G : Gprs, G.rsp = aR g0.rsp → G.rdi = g0.rdi →
      KC prof F Wl L s₀ o gev gP gE 0x57fcc0#64 35 G (V1 V g0) I)
    (k2 : ∀ (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → G.rdi = rdq(W, g0.rdi + 256#64) - 56#64 →
      Ar g0.rdi W G → I W →
      KC prof F Wl L s₀ o gev gP gE 0x57f9b0#64 167 G W fun W' => I W' ∧ rdd(W', g0.rdi + 88#64) = 0)
    (k3 : ∀ (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp → G.rdi = rdq(W, g0.rdi + 256#64) →
      Ar g0.rdi W G → I W →
      KC prof F Wl L s₀ o gev gP gE eR 250 G W fun W' => I W' ∧ rdd(W', g0.rdi + 88#64) = 0)
    (k4 : ∀ (s : BitVec 32) (G : Gprs) (W : Addr → Byte), G.rsp = aR g0.rsp →
      G.rsi = BitVec.setWidth 64 rdd(W, g0.rdi + 88#64) + rdq(W, g0.rdi + 96#64) →
      G.rdx = BitVec.setWidth 64 (Cn g0.rdi s W) → I W →
      KC prof F Wl L s₀ o gev gP gE 0x401070#64 216 G W I)
    (kr : ∀ (W' : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = g0.rsp + 8 → KS g0 Z'.cpu.gpr →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have f12 : ∀ i < 4, Foot F.data (Addr.add (aR g0.rsp + 12#64) i) := fun i hi => c.hws _ (w12 i hi)
  have f88 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 88#64) i) := fun i hi => c.hws _ (w88 i (by omega))
  have w88d : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 88#64) i) := fun i hi => w88 i (by omega)
  have g1 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have g2 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have g3 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have g4 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs4 i hi)
  have g5 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs5 i hi)
  have g6 : ∀ i < 8, Foot F.data (Addr.add (g0.rsp - 8 - 8 - 8 - 8 - 8 - 8) i) :=
    fun i hi => c.hws _ (hs6 i hi)
  -- from 97
  have T97 : ∀ (Y : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W →
      Y.cpu.rip = lri_at.add 97 → Y.cpu.gpr.rsp = aR g0.rsp → I W → GoG prof L o gev gP gE Y t' :=
    fun Y W t' hKY hAY hrY hsY hIW => tail97 c hin hKY hAY hrY hsY (hIs W hIW) f12 g1 g2 g3 g4 g5 g6 hl hin₂ h₂
      fun Z' t'' a b d e => kr W Z' t'' a b d e
  -- the loop at 64, by induction on a bound of what is left
  have LP : ∀ (n : Nat) (Y : State) (W : Addr → Byte) (t' : Nat) (s : BitVec 32) (p : Addr), s.toNat < n →
      KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = lri_at.add 64 →
      Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) Y.cpu.gpr → I W → GoG prof L o gev gP gE Y t' := by
    intro n
    induction n with
    | zero => intro Y W t' s p hn; exact absurd hn (Nat.not_lt_zero _)
    | succ n ih =>
      -- the copy from 183
      have CP : ∀ (Y : State) (W : Addr → Byte) (t' : Nat) (s : BitVec 32) (p : Addr), s.toNat < n + 1 →
          s ≠ 0 → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = lri_at.add 183 →
          Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) Y.cpu.gpr →
          Y.cpu.gpr.rbx = BitVec.setWidth 64 rdd(W, g0.rdi + 92#64) →
          Y.cpu.gpr.rsi = BitVec.setWidth 64 rdd(W, g0.rdi + 88#64) →
          ¬rdd(W, g0.rdi + 88#64) = rdd(W, g0.rdi + 92#64) → I W → GoG prof L o gev gP gE Y t' := by
        intro Y W t' s p hn hs0 hKY hAY hrY hLY hbx hsi hne hIW
        refine (c_183 prof).run c hin (fun j' g' _ V' => j' = 211 ∧ V' = W ∧
            Lk (aR g0.rsp) g0.rdi g0.rcx (p + BitVec.setWidth 64 (Cn g0.rdi s W))
              (BitVec.setWidth 64 (s - Cn g0.rdi s W)) g' ∧
            g'.rsi = BitVec.setWidth 64 rdd(W, g0.rdi + 88#64) + rdq(W, g0.rdi + 96#64) ∧
            g'.rdx = BitVec.setWidth 64 (Cn g0.rdi s W)) hKY hAY hrY
          (vc_183 hLY hbx hsi f96 fun _ a1 a2 a3 _ => ⟨rfl, rfl, a1, a2, a3⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, uL, usi, udx⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        -- `memcpy`
        refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_211 _) hin4 hc4 (by decide)
          (by rw [uL.1]; exact hr8) ?_
        rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
        refine k4 s U.cpu.gpr W uL.1 usi udx hIW Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
        intro Z W' t₃ hKZ hAZ hrZ hfr hIW'
        have zL := Lk.fr uL hfr
        -- `_inPos += cur` (216)
        have he : eaD Z 14 88 = g0.rdi + 88#64 := by
          show Z.cpu.gpr.get (regOf 14) + BitVec.ofNat 64 88 = _
          rw [show Z.cpu.gpr.get (regOf 14) = Z.cpu.gpr.r14 from rfl, zL.2.1]
        refine c.s_add_mr32 hKZ hAZ hin (lt_len (by decide)) hrZ (add_216 _) (by rw [he]; exact w88d) ?_
        rw [he]
        suffices KK : ∀ bs : List Byte, bs.length = 4 → ContG prof F Wl L s₀ o gev gP gE
            (Vst W' (g0.rdi + 88#64) bs) (fun Y => Y.cpu.rip = lri_at.add (216 + 4) ∧ Y.cpu.gpr = Z.cpu.gpr) from
          KK _ (toBytesLE_length ..)
        intro bs1 hl1
        rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
        have hI1 := hI88 W' bs1 hl1 hIW'
        -- `_inProcessed += cur` (220)
        have he2 : eaD Y₃ 14 112 = g0.rdi + 112#64 := by
          show Y₃.cpu.gpr.get (regOf 14) + BitVec.ofNat 64 112 = _
          rw [show Y₃.cpu.gpr.get (regOf 14) = Y₃.cpu.gpr.r14 from rfl, hg₃, zL.2.1]
        refine c.s_add_mr64 hK₃ hA₃ hin (lt_len (by decide)) hr₃ (addq_220 _) (by rw [he2]; exact w112) ?_
        rw [he2]
        suffices KK : ∀ bs : List Byte, bs.length = 8 → ContG prof F Wl L s₀ o gev gP gE
            (Vst (Vst W' (g0.rdi + 88#64) bs1) (g0.rdi + 112#64) bs)
            (fun Y => Y.cpu.rip = lri_at.add (216 + 4 + 4) ∧ Y.cpu.gpr = Y₃.cpu.gpr) from
          KK _ (toBytesLE_length ..)
        intro bs2 hl2
        rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
        have hI2 := hI112 _ bs2 hl2 hI1
        have yL : Lk (aR g0.rsp) g0.rdi g0.rcx (p + BitVec.setWidth 64 (Cn g0.rdi s W))
            (BitVec.setWidth 64 (s - Cn g0.rdi s W)) Y₄.cpu.gpr := by rw [hg₄, hg₃]; exact zL
        have hlt : (s - Cn g0.rdi s W).toNat < n := cu_dec hs0 (sub_ne hne) hn
        by_cases hb0 : g0.rcx = 0
        · refine (c_224 prof).run c hin (fun j' g' _ V' => j' = 64 ∧
              V' = Vst (Vst W' (g0.rdi + 88#64) bs1) (g0.rdi + 112#64) bs2 ∧
              Lk (aR g0.rsp) g0.rdi g0.rcx (p + BitVec.setWidth 64 (Cn g0.rdi s W))
                (BitVec.setWidth 64 (s - Cn g0.rdi s W)) g') hK₄ hA₄ hr₄
            (vc_224z yL (beq_iff_eq.2 hb0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gL⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
          subst V₁ hgU₂
          exact ih U₂ _ t₆ _ _ hlt hKU₂ hAU₂ hrU₂ gL hI2
        · refine (c_224 prof).run c hin (fun j' g' _ V' => j' = 233 ∧
              V' = Vst (Vst W' (g0.rdi + 88#64) bs1) (g0.rdi + 112#64) bs2 ∧
              Lk (aR g0.rsp) g0.rdi g0.rcx (p + BitVec.setWidth 64 (Cn g0.rdi s W))
                (BitVec.setWidth 64 (s - Cn g0.rdi s W)) g') hK₄ hA₄ hr₄
            (vc_224n yL (beq_eq_false_iff_ne.2 hb0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gL⟩ U₂ t₆ hKU₂ hAU₂ hrU₂ hgU₂ -
          subst V₁ hgU₂
          -- `*processedSize += cur` (233)
          have he3 : eaD U₂ 5 0 = g0.rcx := by
            show U₂.cpu.gpr.get (regOf 5) + BitVec.ofNat 64 0 = _
            rw [show U₂.cpu.gpr.get (regOf 5) = U₂.cpu.gpr.rbp from rfl, gL.2.2.1, BitVec.add_zero]
          refine c.s_add_mr32 hKU₂ hAU₂ hin (lt_len (by decide)) hrU₂ (add_233 _) (by rw [he3]; exact wp hb0) ?_
          rw [he3]
          suffices KK : ∀ bs : List Byte, bs.length = 4 → ContG prof F Wl L s₀ o gev gP gE
              (Vst (Vst (Vst W' (g0.rdi + 88#64) bs1) (g0.rdi + 112#64) bs2) g0.rcx bs)
              (fun Y => Y.cpu.rip = lri_at.add (233 + 3) ∧ Y.cpu.gpr = U₂.cpu.gpr) from
            KK _ (toBytesLE_length ..)
          intro bs3 hl3
          rintro Y₅ t₇ hK₅ hA₅ ⟨hr₅, hg₅⟩
          refine (c_236 prof).run c hin (fun j' g' _ V' => j' = 64 ∧
              V' = Vst (Vst (Vst W' (g0.rdi + 88#64) bs1) (g0.rdi + 112#64) bs2) g0.rcx bs3 ∧
              g' = Y₅.cpu.gpr) hK₅ hA₅ hr₅ (vc_236 fun _ => ⟨rfl, rfl, rfl⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, hg'⟩ U₃ t₈ hKU₃ hAU₃ hrU₃ hgU₃ -
          subst V₁ hgU₃
          exact ih U₃ _ t₈ _ _ hlt hKU₃ hAU₃ hrU₃ (by rw [hg', hg₅]; exact gL) (hIp hb0 _ bs3 hl3 hI2)
      -- from 171, `_inPos` 0
      have RD : ∀ (Y : State) (W : Addr → Byte) (t' : Nat) (s : BitVec 32) (p : Addr), s.toNat < n + 1 →
          s ≠ 0 → KeptW Wl s₀ Y → Agree F Y.proc.mm.mem W → Y.cpu.rip = lri_at.add 171 →
          Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) Y.cpu.gpr → I W →
          rdd(W, g0.rdi + 88#64) = 0 → GoG prof L o gev gP gE Y t' := by
        intro Y W t' s p hn hs0 hKY hAY hrY hLY hIW h0
        by_cases hl0 : rdd(W, g0.rdi + 92#64) = 0
        · refine (c_171 prof).run c hin (fun j' g' _ V' => j' = 97 ∧ V' = W ∧ g'.rsp = aR g0.rsp) hKY hAY hrY
            (vc_171z hLY f92 (beq_iff_eq.2 hl0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
          subst V₁ hgU
          exact T97 U W t₁ hKU hAU hrU gs hIW
        · refine (c_171 prof).run c hin (fun j' g' _ V' => j' = 183 ∧ V' = W ∧
              Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) g' ∧
              g'.rsi = BitVec.setWidth 64 rdd(W, g0.rdi + 88#64) ∧
              g'.rbx = BitVec.setWidth 64 rdd(W, g0.rdi + 92#64)) hKY hAY hrY
            (vc_171c hLY f92 f88 (beq_eq_false_iff_ne.2 hl0) fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gL, gsi, gbx⟩ U t₁ hKU hAU hrU hgU -
          subst V₁ hgU
          exact CP U W t₁ s p hn hs0 hKU hAU hrU gL gbx gsi (fun e => hl0 (e.symm.trans h0)) hIW
      -- the head at 64
      intro Y W t' s p hn hKY hAY hrY hLY hIW
      by_cases hs0 : s = 0
      · refine (c_64 prof).run c hin (fun j' g' _ V' => j' = 97 ∧ V' = W ∧ g'.rsp = aR g0.rsp) hKY hAY hrY
          (vc_64z hLY (by rw [sw_64_32]; exact beq_iff_eq.2 hs0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        exact T97 U W t₁ hKU hAU hrU gs hIW
      have hz : (BitVec.setWidth 32 (BitVec.setWidth 64 s) == 0) = false := by
        rw [sw_64_32]; exact beq_eq_false_iff_ne.2 hs0
      by_cases heq : rdd(W, g0.rdi + 88#64) = rdd(W, g0.rdi + 92#64)
      · have hI1 : I (Z8 g0.rdi W) := hI88q W _ (toBytesLE_length _ _) hIW
        by_cases h12 : rdd(W, aR g0.rsp + 12#64) = 0
        · by_cases ht : Tg g0.rdi (Z8 g0.rdi W) = 5765984#64
          · -- the direct `Read`
            refine (c_64 prof).run c hin (fun j' g' _ V' => j' = 162 ∧ V' = Z8 g0.rdi W ∧
                Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) g' ∧
                g'.rdi = rdq(Z8 g0.rdi W, g0.rdi + 256#64) - 56#64 ∧ Ar g0.rdi (Z8 g0.rdi W) g') hKY hAY hrY
              (vc_64r hLY hz f88 f92 heq f12 w88 (beq_iff_eq.2 h12) fun _ a _ =>
                vc_120d a f256 f76 f96 (fv1 _ hI1) (fv2 _ hI1) ht fun _ b d e _ => ⟨rfl, rfl, b, d, e⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gL, gdi, gA⟩ U t₁ hKU hAU hrU hgU -
            subst V₁ hgU
            refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_162 _) hin2 hc2 (by decide)
              (by rw [gL.1]; exact hr8) ?_
            rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
            refine k2 U.cpu.gpr _ gL.1 gdi gA hI1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
            rintro Z W' t₃ hKZ hAZ hrZ hfr ⟨hIW', hp0⟩
            refine (c_167 prof).run c hin (fun j' g' _ V' => j' = 171 ∧
                V' = Vst W' (aR g0.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rax) 4) ∧
                Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) g') hKZ hAZ hrZ
              (vc_167 (Lk.fr gL hfr) w12 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gL'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
            subst V₁ hgU₂
            exact RD U₂ _ t₄ s p hn hs0 hKU₂ hAU₂ hrU₂ gL' (hI12 _ _ (toBytesLE_length ..) hIW')
              ((h88 _ _ (toBytesLE_length ..)).trans hp0)
          · -- `call rax`
            have hR := htgt _ hI1 ht
            refine (c_64 prof).run c hin (fun j' g' _ V' => j' = 248 ∧ V' = Z8 g0.rdi W ∧
                Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) g' ∧ g'.rax = Tg g0.rdi (Z8 g0.rdi W) ∧
                g'.rdi = rdq(Z8 g0.rdi W, g0.rdi + 256#64) ∧ Ar g0.rdi (Z8 g0.rdi W) g') hKY hAY hrY
              (vc_64r hLY hz f88 f92 heq f12 w88 (beq_iff_eq.2 h12) fun _ a _ =>
                vc_120i a f256 f76 f96 (fv1 _ hI1) (fv2 _ hI1) ht fun _ b d e f _ => ⟨rfl, rfl, b, d, e, f⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gL, gax, gdi, gA⟩ U t₁ hKU hAU hrU hgU -
            subst V₁ hgU
            refine c.s_callr hKU hAU hin (lt_len (by decide)) hrU (callr_248 _) hinR hcR
              (by rw [show U.cpu.gpr.get (regOf 0) = U.cpu.gpr.rax from rfl, gax]; exact hR)
              (by rw [gL.1]; exact hr8) ?_
            rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
            refine k3 U.cpu.gpr _ gL.1 gdi gA hI1 Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
            rintro Z W' t₃ hKZ hAZ hrZ hfr ⟨hIW', hp0⟩
            refine (c_250 prof).run c hin (fun j' g' _ V' => j' = 171 ∧
                V' = Vst W' (aR g0.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rax) 4) ∧
                Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) g') hKZ hAZ hrZ
              (vc_250 (Lk.fr gL hfr) w12 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
            rintro j' g fl V₁ ⟨rfl, hV₁, gL'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
            subst V₁ hgU₂
            exact RD U₂ _ t₄ s p hn hs0 hKU₂ hAU₂ hrU₂ gL' (hI12 _ _ (toBytesLE_length ..) hIW')
              ((h88 _ _ (toBytesLE_length ..)).trans hp0)
        · -- the slot not 0: to 97
          refine (c_64 prof).run c hin (fun j' g' _ V' => j' = 97 ∧ V' = Z8 g0.rdi W ∧ g'.rsp = aR g0.rsp)
            hKY hAY hrY
            (vc_64e hLY hz f88 f92 heq f12 w88 (beq_eq_false_iff_ne.2 h12) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
          rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U t₁ hKU hAU hrU hgU -
          subst V₁ hgU
          exact T97 U _ t₁ hKU hAU hrU gs hI1
      · -- something in the buffer: the copy
        refine (c_64 prof).run c hin (fun j' g' _ V' => j' = 183 ∧ V' = W ∧
            Lk (aR g0.rsp) g0.rdi g0.rcx p (BitVec.setWidth 64 s) g' ∧
            g'.rsi = BitVec.setWidth 64 rdd(W, g0.rdi + 88#64) ∧
            g'.rbx = BitVec.setWidth 64 rdd(W, g0.rdi + 92#64)) hKY hAY hrY
          (vc_64c hLY hz f88 f92 heq fun _ a b d _ => ⟨rfl, rfl, a, b, d⟩) ?_
        rintro j' g fl V₁ ⟨rfl, hV₁, gL, gsi, gbx⟩ U t₁ hKU hAU hrU hgU -
        subst V₁ hgU
        exact CP U W t₁ s p hn hs0 hKU hAU hrU gL gbx gsi heq hIW
  -- the entry
  have hrip' : X.cpu.rip = lri_at.add 0 := by rw [addr_add_zero]; exact hrip
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 30 ∧ V' = V1 V g0 ∧ g'.rdi = g0.rdi ∧
      Lk (aR g0.rsp) g0.rdi g0.rcx g0.rsi (BitVec.setWidth 64 (BitVec.setWidth 32 g0.rdx)) g') hK hA hrip'
    (by rw [hg0]; exact vc_0 hs1 hs2 hs3 hs4 hs5 hs6 fun _ a b _ => ⟨rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gL⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_30 _) hin1 hc1 (by decide)
    (by rw [gL.1]; exact hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  refine k1 U.cpu.gpr gL.1 gdi Y₂ t₂ hK₂ hA₂ hr₂ hg₂ ?_
  intro Z W' t₃ hKZ hAZ hrZ hfr hIW'
  have zL := Lk.fr gL hfr
  have hI12' := hI12 W' _ (toBytesLE_length (BitVec.setWidth 32 Z.cpu.gpr.rax) 4) hIW'
  by_cases hax : BitVec.setWidth 32 Z.cpu.gpr.rax = 0
  · by_cases hb0 : g0.rcx = 0
    · refine (c_35 prof).run c hin (fun j' g' _ V' => j' = 64 ∧
          V' = Vst W' (aR g0.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rax) 4) ∧
          Lk (aR g0.rsp) g0.rdi g0.rcx g0.rsi (BitVec.setWidth 64 (BitVec.setWidth 32 g0.rdx)) g') hKZ hAZ hrZ
        (vc_35z zL w12 (beq_iff_eq.2 hax) (beq_iff_eq.2 hb0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, gL'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁ hgU₂
      exact LP ((BitVec.setWidth 32 g0.rdx).toNat + 1) U₂ _ t₄ (BitVec.setWidth 32 g0.rdx) g0.rsi
        (Nat.lt_succ_self _) hKU₂ hAU₂ hrU₂ gL' hI12'
    · refine (c_35 prof).run c hin (fun j' g' _ V' => j' = 64 ∧
          V' = Vst (Vst W' (aR g0.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rax) 4)) g0.rcx
            (toBytesLE 0#32 4) ∧
          Lk (aR g0.rsp) g0.rdi g0.rcx g0.rsi (BitVec.setWidth 64 (BitVec.setWidth 32 g0.rdx)) g') hKZ hAZ hrZ
        (vc_35p zL w12 (beq_iff_eq.2 hax) (beq_eq_false_iff_ne.2 hb0) (wp hb0) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
      rintro j' g fl V₁ ⟨rfl, hV₁, gL'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₁ hgU₂
      exact LP ((BitVec.setWidth 32 g0.rdx).toNat + 1) U₂ _ t₄ (BitVec.setWidth 32 g0.rdx) g0.rsi
        (Nat.lt_succ_self _) hKU₂ hAU₂ hrU₂ gL' (hIp hb0 _ _ (toBytesLE_length _ _) hI12')
  · refine (c_35 prof).run c hin (fun j' g' _ V' => j' = 97 ∧
        V' = Vst W' (aR g0.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 Z.cpu.gpr.rax) 4) ∧
        g'.rsp = aR g0.rsp) hKZ hAZ hrZ
      (vc_35e zL w12 (beq_eq_false_iff_ne.2 hax) fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gs⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₁ hgU₂
    exact T97 U₂ _ t₄ hKU₂ hAU₂ hrU₂ gs hI12'

end FV7z.Lri
