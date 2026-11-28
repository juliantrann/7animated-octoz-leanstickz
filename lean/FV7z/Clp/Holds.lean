import FV7z.Clp.Cuts
import FV7z.Tiny.Tj
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.CallM
import FV7z.Lemmas.CallReg
import FV7z.Lemmas.SubMf
import FV7z.Tun.Inv
import FV7z.Ocv.Holds
/-!
# `CLocalProgress::Init`: the pieces (PLAN.md §M, M1)

7-Zip 26.06's `CLocalProgress::Init (this, progress, inSizeIsMain)` at `0x461ff0` in `7zzs`
(`CPP/7zip/Common/ProgressUtils.cpp`; `objdump -d`), `S` the stack pointer at the entry. Six registers pushed,
`rsp` = `S - 72` (`sp72`), `rbx` = `this`, `rbp` = `progress`, `r13` = `inSizeIsMain` (`edx`, zero-extended).
`_ratioProgress.Release ()` (`this + 24`): the compiler inlined `CLocalProgress::Release` (vtable slot 2 at
`0x462290`) four levels deep, each guarded by a compare of the vtable's slot with it (`call rax` when it differs);
a level's count (the 4 bytes at `q + 8`) is dropped by 1 and when it reaches 0 the object `q` is destroyed: its
vtable set back to `CMyUnknownImp`'s (`0x783be0`), its own `_ratioProgress` (`q + 24`) released (the next level,
at the fourth a virtual `Release`), then `_progress` (`q + 16`, a virtual `Release`), then `operator delete (q, 56)`
(`0x6014e0`). Then `_ratioProgress` = NULL (68), `progress->AddRef ()` (88), the old `_progress->Release ()`
(103), `_progress` = `progress`, `progress->QueryInterface (IID_ICompressProgressInfo, &_ratioProgress)` (128),
`_inSizeIsMain` = `inSizeIsMain` (the byte at `this + 14`), the pops and `ret`.

This file: the instructions outside the blocks (the calls, the `sub`s with their flags, the `ret`), the frame,
the call helpers (`cl_m`, `cl_r`, `cl_d` from a contract `Callc`) and the pieces' conditions (`vc_*`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Clp
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- `call [rax + 8]`. -/
def qcm8 : List Byte := [0xff, 0x50, 0x08]
theorem qcm8_0 : ∀ feat, Dec feat qcm8 0 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) := by dec_rfl
theorem wcallm_88 : qcm8 <+: clp.drop 88 := by decide +kernel
theorem callm_88 (feat : Features) : Dec feat clp 88 (FV7z.mk .call 64 [.mem (mbd 0 8 64)] 3) :=
  Dec.shift (j := 88) (k := 0) (qcm8_0 feat) wcallm_88 (Nat.zero_le _)

/-- `call [rax + 16]`. -/
def qcm16 : List Byte := [0xff, 0x50, 0x10]
theorem qcm16_0 : ∀ feat, Dec feat qcm16 0 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) := by dec_rfl
theorem wcallm_103 : qcm16 <+: clp.drop 103 := by decide +kernel
theorem callm_103 (feat : Features) : Dec feat clp 103 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 103) (k := 0) (qcm16_0 feat) wcallm_103 (Nat.zero_le _)
theorem wcallm_306 : qcm16 <+: clp.drop 306 := by decide +kernel
theorem callm_306 (feat : Features) : Dec feat clp 306 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 306) (k := 0) (qcm16_0 feat) wcallm_306 (Nat.zero_le _)
theorem wcallm_331 : qcm16 <+: clp.drop 331 := by decide +kernel
theorem callm_331 (feat : Features) : Dec feat clp 331 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 331) (k := 0) (qcm16_0 feat) wcallm_331 (Nat.zero_le _)
theorem wcallm_364 : qcm16 <+: clp.drop 364 := by decide +kernel
theorem callm_364 (feat : Features) : Dec feat clp 364 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 364) (k := 0) (qcm16_0 feat) wcallm_364 (Nat.zero_le _)
theorem wcallm_392 : qcm16 <+: clp.drop 392 := by decide +kernel
theorem callm_392 (feat : Features) : Dec feat clp 392 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 392) (k := 0) (qcm16_0 feat) wcallm_392 (Nat.zero_le _)
theorem wcallm_421 : qcm16 <+: clp.drop 421 := by decide +kernel
theorem callm_421 (feat : Features) : Dec feat clp 421 (FV7z.mk .call 64 [.mem (mbd 0 16 64)] 3) :=
  Dec.shift (j := 421) (k := 0) (qcm16_0 feat) wcallm_421 (Nat.zero_le _)

/-- `call [rax]`. -/
def qcm0 : List Byte := [0xff, 0x10]
theorem qcm0_0 : ∀ feat, Dec feat qcm0 0 (FV7z.mk .call 64 [.mem (mbd 0 0 64)] 2) := by dec_rfl
theorem wcallm_128 : qcm0 <+: clp.drop 128 := by decide +kernel
theorem callm_128 (feat : Features) : Dec feat clp 128 (FV7z.mk .call 64 [.mem (mbd 0 0 64)] 2) :=
  Dec.shift (j := 128) (k := 0) (qcm0_0 feat) wcallm_128 (Nat.zero_le _)

/-- `call rax`. -/
def qcr : List Byte := [0xff, 0xd0]
theorem qcr_0 : ∀ feat, Dec feat qcr 0 (FV7z.mk .call 64 [gr 64 0] 2) := by dec_rfl
theorem wcallr_451 : qcr <+: clp.drop 451 := by decide +kernel
theorem callr_451 (feat : Features) : Dec feat clp 451 (FV7z.mk .call 64 [gr 64 0] 2) :=
  Dec.shift (j := 451) (k := 0) (qcr_0 feat) wcallr_451 (Nat.zero_le _)
theorem wcallr_467 : qcr <+: clp.drop 467 := by decide +kernel
theorem callr_467 (feat : Features) : Dec feat clp 467 (FV7z.mk .call 64 [gr 64 0] 2) :=
  Dec.shift (j := 467) (k := 0) (qcr_0 feat) wcallr_467 (Nat.zero_le _)
theorem wcallr_483 : qcr <+: clp.drop 483 := by decide +kernel
theorem callr_483 (feat : Features) : Dec feat clp 483 (FV7z.mk .call 64 [gr 64 0] 2) :=
  Dec.shift (j := 483) (k := 0) (qcr_0 feat) wcallr_483 (Nat.zero_le _)
theorem wcallr_490 : qcr <+: clp.drop 490 := by decide +kernel
theorem callr_490 (feat : Features) : Dec feat clp 490 (FV7z.mk .call 64 [gr 64 0] 2) :=
  Dec.shift (j := 490) (k := 0) (qcr_0 feat) wcallr_490 (Nat.zero_le _)

/-- The `call` to `0x6014e0` at 347. -/
def qd347 : List Byte := [0xe8, 0x90, 0xf3, 0x19, 0x00]
theorem qd347_0 : ∀ feat, Dec feat qd347 0 (FV7z.mk .call 64 [.rel 1700752] 5) := by dec_rfl
theorem wcalld_347 : qd347 <+: clp.drop 347 := by decide +kernel
theorem calld_347 (feat : Features) : Dec feat clp 347 (FV7z.mk .call 64 [.rel 1700752] 5) :=
  Dec.shift (j := 347) (k := 0) (qd347_0 feat) wcalld_347 (Nat.zero_le _)
theorem tgt_347 : clp_at.add (347 + 5) + BitVec.ofNat 64 1700752 = 0x6014e0#64 := by decide

/-- The `call` to `0x6014e0` at 375. -/
def qd375 : List Byte := [0xe8, 0x74, 0xf3, 0x19, 0x00]
theorem qd375_0 : ∀ feat, Dec feat qd375 0 (FV7z.mk .call 64 [.rel 1700724] 5) := by dec_rfl
theorem wcalld_375 : qd375 <+: clp.drop 375 := by decide +kernel
theorem calld_375 (feat : Features) : Dec feat clp 375 (FV7z.mk .call 64 [.rel 1700724] 5) :=
  Dec.shift (j := 375) (k := 0) (qd375_0 feat) wcalld_375 (Nat.zero_le _)
theorem tgt_375 : clp_at.add (375 + 5) + BitVec.ofNat 64 1700724 = 0x6014e0#64 := by decide

/-- The `call` to `0x6014e0` at 403. -/
def qd403 : List Byte := [0xe8, 0x58, 0xf3, 0x19, 0x00]
theorem qd403_0 : ∀ feat, Dec feat qd403 0 (FV7z.mk .call 64 [.rel 1700696] 5) := by dec_rfl
theorem wcalld_403 : qd403 <+: clp.drop 403 := by decide +kernel
theorem calld_403 (feat : Features) : Dec feat clp 403 (FV7z.mk .call 64 [.rel 1700696] 5) :=
  Dec.shift (j := 403) (k := 0) (qd403_0 feat) wcalld_403 (Nat.zero_le _)
theorem tgt_403 : clp_at.add (403 + 5) + BitVec.ofNat 64 1700696 = 0x6014e0#64 := by decide

/-- The `call` to `0x6014e0` at 432. -/
def qd432 : List Byte := [0xe8, 0x3b, 0xf3, 0x19, 0x00]
theorem qd432_0 : ∀ feat, Dec feat qd432 0 (FV7z.mk .call 64 [.rel 1700667] 5) := by dec_rfl
theorem wcalld_432 : qd432 <+: clp.drop 432 := by decide +kernel
theorem calld_432 (feat : Features) : Dec feat clp 432 (FV7z.mk .call 64 [.rel 1700667] 5) :=
  Dec.shift (j := 432) (k := 0) (qd432_0 feat) wcalld_432 (Nat.zero_le _)
theorem tgt_432 : clp_at.add (432 + 5) + BitVec.ofNat 64 1700667 = 0x6014e0#64 := by decide

/-- `sub dword [r12 + 8], 1`. -/
def qs12 : List Byte := [0x41, 0x83, 0x6c, 0x24, 0x08, 0x01]
theorem qs12_0 : ∀ feat, Dec feat qs12 0 (FV7z.mk .sub 32 [.mem (mbd 12 8 32), .imm 32 1] 6) := by dec_rfl
theorem wsub_60 : qs12 <+: clp.drop 60 := by decide +kernel
theorem sub_60 (feat : Features) : Dec feat clp 60 (FV7z.mk .sub 32 [.mem (mbd 12 8 32), .imm 32 1] 6) :=
  Dec.shift (j := 60) (k := 0) (qs12_0 feat) wsub_60 (Nat.zero_le _)

/-- `sub dword [r14 + 8], 1`. -/
def qs14 : List Byte := [0x41, 0x83, 0x6e, 0x08, 0x01]
theorem qs14_0 : ∀ feat, Dec feat qs14 0 (FV7z.mk .sub 32 [.mem (mbd 14 8 32), .imm 32 1] 5) := by dec_rfl
theorem wsub_197 : qs14 <+: clp.drop 197 := by decide +kernel
theorem sub_197 (feat : Features) : Dec feat clp 197 (FV7z.mk .sub 32 [.mem (mbd 14 8 32), .imm 32 1] 5) :=
  Dec.shift (j := 197) (k := 0) (qs14_0 feat) wsub_197 (Nat.zero_le _)

/-- `sub dword [r15 + 8], 1`. -/
def qs15 : List Byte := [0x41, 0x83, 0x6f, 0x08, 0x01]
theorem qs15_0 : ∀ feat, Dec feat qs15 0 (FV7z.mk .sub 32 [.mem (mbd 15 8 32), .imm 32 1] 5) := by dec_rfl
theorem wsub_240 : qs15 <+: clp.drop 240 := by decide +kernel
theorem sub_240 (feat : Features) : Dec feat clp 240 (FV7z.mk .sub 32 [.mem (mbd 15 8 32), .imm 32 1] 5) :=
  Dec.shift (j := 240) (k := 0) (qs15_0 feat) wsub_240 (Nat.zero_le _)

/-- `sub dword [r8 + 8], 1`. -/
def qs8 : List Byte := [0x41, 0x83, 0x68, 0x08, 0x01]
theorem qs8_0 : ∀ feat, Dec feat qs8 0 (FV7z.mk .sub 32 [.mem (mbd 8 8 32), .imm 32 1] 5) := by dec_rfl
theorem wsub_279 : qs8 <+: clp.drop 279 := by decide +kernel
theorem sub_279 (feat : Features) : Dec feat clp 279 (FV7z.mk .sub 32 [.mem (mbd 8 8 32), .imm 32 1] 5) :=
  Dec.shift (j := 279) (k := 0) (qs8_0 feat) wsub_279 (Nat.zero_le _)

/-- The `ret`. -/
def qret : List Byte := [0xc3]
theorem qret_0 : ∀ feat, Dec feat qret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wret_148 : qret <+: clp.drop 148 := by decide +kernel
theorem ret_148 (feat : Features) : Dec feat clp 148 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 148) (k := 0) (qret_0 feat) wret_148 (Nat.zero_le _)

/-! ## The constants, the frame and the registers -/

/-- `CLocalProgress::Release`, what the vtables' slot 2 is compared with. -/
abbrev rlK : BitVec 64 := 4596368#64
/-- `CMyUnknownImp`'s vtable, what a destroyed object's vtable pointer is set to. -/
abbrev vtv : BitVec 64 := 7879648#64

theorem vtv_eq : (7879632#64 + 16#64 : BitVec 64) = 7879648#64 := rfl

/-- `rsp` after the pushes and `sub rsp, 24`. -/
abbrev sp72 (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 24#64

/-- `r13` after `mov r13d, edx`. -/
abbrev r13v (g : Gprs) : BitVec 64 := (g.rdx.setWidth 32).setWidth 64

/-- The bytes after the six pushes. -/
abbrev Vp6 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r15 8)) (g.rsp - 8 - 8) (toBytesLE g.r14 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the count at `q + 8` is dropped by 1. -/
abbrev Wdec (W : Addr → Byte) (q : Addr) : Addr → Byte :=
  Vst W (q + 8#64) (toBytesLE (rdd(W, q + 8#64) - 1#32) 4)

/-- The bytes after `q`'s vtable pointer is set to `vtv`. -/
abbrev Vv (V : Addr → Byte) (q : Addr) : Addr → Byte := Vst V q (toBytesLE (7879648#64 : BitVec 64) 8)

/-- The bytes after `x` is spilled to `[rsp + 8]`. -/
abbrev Wsp (S : Addr) (W : Addr → Byte) (x : BitVec 64) : Addr → Byte := Vst W (sp72 S + 8#64) (toBytesLE x 8)

/-- The bytes after `_inSizeIsMain` is stored. -/
abbrev Vb (g₀ : Gprs) (W : Addr → Byte) : Addr → Byte :=
  Vst W (g₀.rdi + 14#64) (toBytesLE ((r13v g₀).setWidth 8) 1)

/-- The registers after `add rsp, 24` and the six pops. -/
abbrev pops6 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rbx := rdq(V, g.rsp + 24#64),
      rsp := g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8,
      rbp := rdq(V, g.rsp + 24#64 + 8),
      r12 := rdq(V, g.rsp + 24#64 + 8 + 8),
      r13 := rdq(V, g.rsp + 24#64 + 8 + 8 + 8),
      r14 := rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8),
      r15 := rdq(V, g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) }

/-- The saved registers of `g₀` and the return address `ra` in the bytes `V`. -/
def Fr (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop :=
  rdq(V, g₀.rsp - 8 - 8 - 8 - 8 - 8 - 8) = g₀.rbx ∧ rdq(V, g₀.rsp - 8 - 8 - 8 - 8 - 8) = g₀.rbp ∧
    rdq(V, g₀.rsp - 8 - 8 - 8 - 8) = g₀.r12 ∧ rdq(V, g₀.rsp - 8 - 8 - 8) = g₀.r13 ∧
    rdq(V, g₀.rsp - 8 - 8) = g₀.r14 ∧ rdq(V, g₀.rsp - 8) = g₀.r15 ∧ rdq(V, g₀.rsp) = ra

/-- The registers kept throughout: `rsp` = `S - 72`, `rbx` = `this`, `rbp` = `progress`, `r13`. -/
def Rr (g₀ g : Gprs) : Prop :=
  g.rsp = sp72 g₀.rsp ∧ g.rbx = g₀.rdi ∧ g.rbp = g₀.rsi ∧ g.r13 = r13v g₀

/-- `Rr` and the first level's object in `r12`. -/
def L1 (g₀ : Gprs) (q1 : Addr) (g : Gprs) : Prop := Rr g₀ g ∧ g.r12 = q1
/-- `L1` and the second level's object in `r14`. -/
def L2 (g₀ : Gprs) (q1 q2 : Addr) (g : Gprs) : Prop := L1 g₀ q1 g ∧ g.r14 = q2
/-- `L2` and the third level's object in `r15`. -/
def L3 (g₀ : Gprs) (q1 q2 q3 : Addr) (g : Gprs) : Prop := L2 g₀ q1 q2 g ∧ g.r15 = q3

/-- The registers a call keeps, `rsp` as before it. -/
def Sk (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

theorem Rr.sk {g₀ g g' : Gprs} (h : Rr g₀ g) (k : Sk g g') : Rr g₀ g' :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1, k.2.2.2.2.1.trans h.2.2.2⟩
theorem L1.sk {g₀ g g' : Gprs} {q1 : Addr} (h : L1 g₀ q1 g) (k : Sk g g') : L1 g₀ q1 g' :=
  ⟨h.1.sk k, k.2.2.2.1.trans h.2⟩
theorem L2.sk {g₀ g g' : Gprs} {q1 q2 : Addr} (h : L2 g₀ q1 q2 g) (k : Sk g g') : L2 g₀ q1 q2 g' :=
  ⟨h.1.sk k, k.2.2.2.2.2.1.trans h.2⟩
theorem L3.sk {g₀ g g' : Gprs} {q1 q2 q3 : Addr} (h : L3 g₀ q1 q2 q3 g) (k : Sk g g') : L3 g₀ q1 q2 q3 g' :=
  ⟨h.1.sk k, k.2.2.2.2.2.2.trans h.2⟩

/-- What a destroyed object's code touches: the count (stored), `_progress` and `_ratioProgress` (read), the
vtable pointer (stored). -/
def Ofp (F : Footprint) (Wl : List Rgn) (q : Addr) : Prop :=
  (∀ i < 4, Foot Wl (Addr.add (q + 8#64) i)) ∧ (∀ i < 8, Foot F.data (Addr.add (q + 16#64) i)) ∧
    (∀ i < 8, Foot F.data (Addr.add (q + 24#64) i)) ∧ (∀ i < 8, Foot Wl (Addr.add q i))

/-- What a virtual call on `d` reads: the vtable pointer at `d` and slot 2 (`+ 16`). -/
def Vf (F : Footprint) (W : Addr → Byte) (d : Addr) : Prop :=
  (∀ i < 8, Foot F.data (Addr.add d i)) ∧ (∀ i < 8, Foot F.data (Addr.add (rdq(W, d) + 16#64) i))

/-- Code at `f`. -/
def CodeOK (L : List (Addr × List Byte)) (f : Addr) : Prop := ∃ code, CodeIn L f code ∧ 0 < code.length

theorem a24 (x : Addr) : x - 24#64 + 24#64 = x := BitVec.sub_add_cancel _ _

/-- A load of the spilled word. -/
theorem rdself {S : Addr} {W : Addr → Byte} {x : BitVec 64} (ns : (sp72 S + 8#64).toNat + 8 ≤ 2 ^ 64) :
    rdq(Wsp S W x, sp72 S + 8#64) = x := by
  show ofBytesLE 64 (List.map (Vst W (sp72 S + 8#64) (toBytesLE x 8)) (byteAddrs (sp72 S + 8#64) 8)) = x
  rw [Tun.rd_Vst_self W _ _ (toBytesLE_length _ _) ns, ofBytesLE_toBytesLE (w := 64) (n := 8) rfl]

/-- The closer of the pieces' conditions. -/
local macro "ccl" : tactic => `(tactic| (all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | (intro h; exact absurd h (by decide))
    | apply And.intro
    | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

section
variable {g : Gprs} {f : Rflags} {V : Addr → Byte}

/-- The entry with `_ratioProgress` NULL: to 76. -/
theorem vc_0z {c : BitVec 64} (hc : rdq(Vp6 V g, g.rdi + 24#64) = c) (h0 : c = 0)
    (fc : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 76 ∧ V' = Vp6 V g ∧ Rr g g') g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp6] at hc fc w1 w2 w3 w4 w5 w6 ⊢
  have e : (c == 0) = true := beq_iff_eq.2 h0
  wpx [W_0, W_36, W_448, o0, o1, o26, Rr, hc, e, BitVec.and_self, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ccl

/-- The entry, `_ratioProgress` = `c` not NULL, its `Release` not `CLocalProgress`'s: to the `call rax` at
451. -/
theorem vc_0m {c vt x : BitVec 64} (hc : rdq(Vp6 V g, g.rdi + 24#64) = c) (h0 : c ≠ 0)
    (hv : rdq(Vp6 V g, c) = vt) (hx : rdq(Vp6 V g, vt + 16#64) = x) (hne : x ≠ 4596368#64)
    (fc : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i)) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 451 ∧ V' = Vp6 V g ∧ Rr g g' ∧ g'.r12 = c ∧ g'.rdi = c ∧ g'.rax = x)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp6] at hc hv hx fc fv fx w1 w2 w3 w4 w5 w6 ⊢
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = false := decide_eq_false hne
  wpx [W_0, W_36, W_448, o0, o1, o26, Rr, hc, hv, hx, e, e2, BitVec.and_self, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ccl

/-- The entry, `_ratioProgress` = `c` not NULL with `CLocalProgress::Release`: to the `sub` at 60. -/
theorem vc_0k {c vt x : BitVec 64} (hc : rdq(Vp6 V g, g.rdi + 24#64) = c) (h0 : c ≠ 0)
    (hv : rdq(Vp6 V g, c) = vt) (hx : rdq(Vp6 V g, vt + 16#64) = x) (heq : x = 4596368#64)
    (fc : ∀ i < 8, Foot F.data (Addr.add (g.rdi + 24#64) i)) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 60 ∧ V' = Vp6 V g ∧ Rr g g' ∧ g'.r12 = c ∧ g'.rdx = 4596368#64) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vp6] at hc hv hx fc fv fx w1 w2 w3 w4 w5 w6 ⊢
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = true := decide_eq_true heq
  wpx [W_0, W_36, W_448, o0, o1, o26, Rr, hc, hv, hx, e, e2, BitVec.and_self, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 66, the count not 0: to 68. -/
theorem vc_66n (hz : f.zf = false) :
    W_66 F Wl (fun j' g' _ V' => j' = 68 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_66, hz, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 66, the count 0, the next level NULL: to 408. -/
theorem vc_66z0 {c : BitVec 64} (hz : f.zf = true)
    (hc : rdq(V, g.r12 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r12 i)) (h0 : c = 0) :
    W_66 F Wl (fun j' g' _ V' => j' = 408 ∧
      g' = { g with rsi := 7879632#64, rcx := 7879648#64, r14 := c } ∧ V' = Vv V g.r12) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq ⊢
  have e : (c == 0) = true := beq_iff_eq.2 h0
  wpx [W_66, W_152, W_181, W_480, o9, o10, o28, hz, hc, e, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 66, the count 0, the next level `c` not NULL, not `CLocalProgress::Release`: to the `call rax` at 483. -/
theorem vc_66zm {c vt x : BitVec 64} (hz : f.zf = true)
    (hc : rdq(V, g.r12 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r12 i)) (h0 : c ≠ 0)
    (hdx : g.rdx = 4596368#64) (hv : rdq(Vv V g.r12, c) = vt) (hx : rdq(Vv V g.r12, vt + 16#64) = x)
    (hne : x ≠ 4596368#64) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i)) :
    W_66 F Wl (fun j' g' _ V' => j' = 483 ∧
      g' = { g with rsi := 7879632#64, rcx := 7879648#64, r14 := c, rax := x, rdi := c } ∧
      V' = Vv V g.r12) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hdx hv hx ⊢
  subst hdx
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = false := decide_eq_false hne
  wpx [W_66, W_152, W_181, W_480, o9, o10, o28, hz, hc, hv, hx, e, e2, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 66, the count 0, the next level `c` not NULL, `CLocalProgress::Release`: to the `sub` at 197. -/
theorem vc_66zk {c vt x : BitVec 64} (hz : f.zf = true)
    (hc : rdq(V, g.r12 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r12 i)) (h0 : c ≠ 0)
    (hdx : g.rdx = 4596368#64) (hv : rdq(Vv V g.r12, c) = vt) (hx : rdq(Vv V g.r12, vt + 16#64) = x)
    (heq : x = 4596368#64) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i)) :
    W_66 F Wl (fun j' g' _ V' => j' = 197 ∧
      g' = { g with rsi := 7879632#64, rcx := 7879648#64, r14 := c, rax := x } ∧
      V' = Vv V g.r12) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hdx hv hx ⊢
  subst hdx
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = true := decide_eq_true heq
  wpx [W_66, W_152, W_181, W_480, o9, o10, o28, hz, hc, hv, hx, e, e2, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 202, the count not 0: to 408. -/
theorem vc_202n (hz : f.zf = false) :
    W_202 F Wl (fun j' g' _ V' => j' = 408 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_202, hz, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 202, the count 0, the next level NULL: to 380. -/
theorem vc_202z0 {c : BitVec 64} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hc : rdq(V, g.r14 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r14 i)) (h0 : c = 0) :
    W_202 F Wl (fun j' g' _ V' => j' = 380 ∧
      g' = { g with r15 := c } ∧ V' = Vv V g.r14) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hcx ⊢
  subst hcx
  have e : (c == 0) = true := beq_iff_eq.2 h0
  wpx [W_202, W_208, W_224, W_464, o11, o12, o27, hz, hc, e, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 202, the count 0, the next level `c` not NULL, not `CLocalProgress::Release`: to the `call rax` at 467. -/
theorem vc_202zm {c vt x : BitVec 64} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hc : rdq(V, g.r14 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r14 i)) (h0 : c ≠ 0)
    (hdx : g.rdx = 4596368#64) (hv : rdq(Vv V g.r14, c) = vt) (hx : rdq(Vv V g.r14, vt + 16#64) = x)
    (hne : x ≠ 4596368#64) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i)) :
    W_202 F Wl (fun j' g' _ V' => j' = 467 ∧
      g' = { g with r15 := c, rax := x, rdi := c } ∧
      V' = Vv V g.r14) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hdx hv hx hcx ⊢
  subst hcx
  subst hdx
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = false := decide_eq_false hne
  wpx [W_202, W_208, W_224, W_464, o11, o12, o27, hz, hc, hv, hx, e, e2, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 202, the count 0, the next level `c` not NULL, `CLocalProgress::Release`: to the `sub` at 240. -/
theorem vc_202zk {c vt x : BitVec 64} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hc : rdq(V, g.r14 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r14 i)) (h0 : c ≠ 0)
    (hdx : g.rdx = 4596368#64) (hv : rdq(Vv V g.r14, c) = vt) (hx : rdq(Vv V g.r14, vt + 16#64) = x)
    (heq : x = 4596368#64) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i)) :
    W_202 F Wl (fun j' g' _ V' => j' = 240 ∧
      g' = { g with r15 := c, rax := x } ∧
      V' = Vv V g.r14) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hdx hv hx hcx ⊢
  subst hcx
  subst hdx
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = true := decide_eq_true heq
  wpx [W_202, W_208, W_224, W_464, o11, o12, o27, hz, hc, hv, hx, e, e2, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 245, the count not 0: to 380. -/
theorem vc_245n (hz : f.zf = false) :
    W_245 F Wl (fun j' g' _ V' => j' = 380 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_245, hz, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 245, the count 0, the next level NULL: to 352. -/
theorem vc_245z0 {c : BitVec 64} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hc : rdq(V, g.r15 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r15 i)) (h0 : c = 0) :
    W_245 F Wl (fun j' g' _ V' => j' = 352 ∧
      g' = { g with r8 := c } ∧ V' = Vv V g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hcx ⊢
  subst hcx
  have e : (c == 0) = true := beq_iff_eq.2 h0
  wpx [W_245, W_251, W_263, W_487, o13, o14, o29, hz, hc, e, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 245, the count 0, the next level `c` not NULL, not `CLocalProgress::Release`: to the `call rax` at 490. -/
theorem vc_245zm {c vt x : BitVec 64} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hc : rdq(V, g.r15 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r15 i)) (h0 : c ≠ 0)
    (hdx : g.rdx = 4596368#64) (hv : rdq(Vv V g.r15, c) = vt) (hx : rdq(Vv V g.r15, vt + 16#64) = x)
    (hne : x ≠ 4596368#64) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i)) :
    W_245 F Wl (fun j' g' _ V' => j' = 490 ∧
      g' = { g with r8 := c, rax := x, rdi := c } ∧
      V' = Vv V g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hdx hv hx hcx ⊢
  subst hcx
  subst hdx
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = false := decide_eq_false hne
  wpx [W_245, W_251, W_263, W_487, o13, o14, o29, hz, hc, hv, hx, e, e2, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 245, the count 0, the next level `c` not NULL, `CLocalProgress::Release`: to the `sub` at 279. -/
theorem vc_245zk {c vt x : BitVec 64} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hc : rdq(V, g.r15 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r15 i)) (h0 : c ≠ 0)
    (hdx : g.rdx = 4596368#64) (hv : rdq(Vv V g.r15, c) = vt) (hx : rdq(Vv V g.r15, vt + 16#64) = x)
    (heq : x = 4596368#64) (fv : ∀ i < 8, Foot F.data (Addr.add c i))
    (fx : ∀ i < 8, Foot F.data (Addr.add (vt + 16#64) i)) :
    W_245 F Wl (fun j' g' _ V' => j' = 279 ∧
      g' = { g with r8 := c, rax := x } ∧
      V' = Vv V g.r15) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hdx hv hx hcx ⊢
  subst hcx
  subst hdx
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  have e2 : decide (x = 4596368#64) = true := decide_eq_true heq
  wpx [W_245, W_251, W_263, W_487, o13, o14, o29, hz, hc, hv, hx, e, e2, vtv_eq,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 284, the count not 0: to 352. -/
theorem vc_284n (hz : f.zf = false) :
    W_284 F Wl (fun j' g' _ V' => j' = 352 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_284, hz, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 284, the count 0, `_ratioProgress` NULL: to 314. -/
theorem vc_284z0 {c : BitVec 64} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hc : rdq(V, g.r8 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r8 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r8 i)) (h0 : c = 0) :
    W_284 F Wl (fun j' g' _ V' => j' = 314 ∧ g' = { g with rdi := c } ∧ V' = Vv V g.r8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv] at hc fc wq hcx ⊢
  subst hcx
  have e : (c == 0) = true := beq_iff_eq.2 h0
  wpx [W_284, W_286, W_298, o15, o16, hz, hc, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 284, the count 0, `_ratioProgress` = `c` not NULL: its vtable in `rax`, `r8` spilled; to the `call` at 306. -/
theorem vc_284zn {c v : BitVec 64} {S : Addr} (hz : f.zf = true) (hcx : g.rcx = 7879648#64)
    (hs : g.rsp = sp72 S)
    (hc : rdq(V, g.r8 + 24#64) = c) (fc : ∀ i < 8, Foot F.data (Addr.add (g.r8 + 24#64) i))
    (wq : ∀ i < 8, Foot Wl (Addr.add g.r8 i)) (h0 : c ≠ 0) (hv : rdq(Vv V g.r8, c) = v)
    (fv : ∀ i < 8, Foot F.data (Addr.add c i)) (ws : ∀ i < 8, Foot Wl (Addr.add (sp72 S + 8#64) i)) :
    W_284 F Wl (fun j' g' _ V' => j' = 306 ∧ g' = { g with rdi := c, rax := v } ∧
      V' = Wsp S (Vv V g.r8) g.r8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vv, Wsp] at hc fc wq hcx hs hv ⊢
  subst hcx hs
  have e : (c == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_284, W_286, W_298, o15, o16, hz, hc, hv, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 309 and 334: `r8` reloaded; to 314 and 339. -/
theorem vc_309 {x : BitVec 64} (hx : rdq(V, g.rsp + 8#64) = x)
    (fs : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_309 F Wl (fun j' g' _ V' => j' = 314 ∧ g' = { g with r8 := x } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hx fs ⊢
  wpx [W_309, o17, hx]
  ccl

theorem vc_334 {x : BitVec 64} (hx : rdq(V, g.rsp + 8#64) = x)
    (fs : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_334 F Wl (fun j' g' _ V' => j' = 339 ∧ g' = { g with r8 := x } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hx fs ⊢
  wpx [W_334, o17, hx]
  ccl

/-- 314, the fourth level's `_progress` NULL: to 339. -/
theorem vc_314z {d : BitVec 64} (hd : rdq(V, g.r8 + 16#64) = d) (h0 : d = 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r8 + 16#64) i)) :
    W_314 F Wl (fun j' g' _ V' => j' = 339 ∧ g' = { g with rdi := d } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd ⊢
  have e : (d == 0) = true := beq_iff_eq.2 h0
  wpx [W_314, W_323, o18, o16, hd, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 314, the fourth level's `_progress` = `d` not NULL: its vtable in `rax`, `r8` spilled; to the `call` at 331. -/
theorem vc_314n {d v : BitVec 64} {S : Addr} (hs : g.rsp = sp72 S) (hd : rdq(V, g.r8 + 16#64) = d) (h0 : d ≠ 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r8 + 16#64) i)) (hv : rdq(V, d) = v)
    (fv : ∀ i < 8, Foot F.data (Addr.add d i)) (ws : ∀ i < 8, Foot Wl (Addr.add (sp72 S + 8#64) i)) :
    W_314 F Wl (fun j' g' _ V' => j' = 331 ∧ g' = { g with rdi := d, rax := v } ∧ V' = Wsp S V g.r8) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Wsp] at hs hd fd hv fv ws ⊢
  subst hs
  have e : (d == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_314, W_323, o18, o16, hd, hv, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 339: `esi` = 56, `rdi` = `r8`; to the `call` to `operator delete` at 347. -/
theorem vc_339 : W_339 F Wl (fun j' g' _ V' => j' = 347 ∧ g' = { g with rsi := 56#64, rdi := g.r8 } ∧ V' = V)
    g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_339, o19, BitVec.reduceSetWidth]
  ccl

/-- 367: `esi` = 56, `rdi` = `r15`; to the `call` to `operator delete` at 375. -/
theorem vc_367 : W_367 F Wl (fun j' g' _ V' => j' = 375 ∧ g' = { g with rsi := 56#64, rdi := g.r15 } ∧ V' = V)
    g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_367, o21, BitVec.reduceSetWidth]
  ccl

/-- 395: `esi` = 56, `rdi` = `r14`; to the `call` to `operator delete` at 403. -/
theorem vc_395 : W_395 F Wl (fun j' g' _ V' => j' = 403 ∧ g' = { g with rsi := 56#64, rdi := g.r14 } ∧ V' = V)
    g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_395, o23, BitVec.reduceSetWidth]
  ccl

/-- 424: `esi` = 56, `rdi` = `r12`; to the `call` to `operator delete` at 432. -/
theorem vc_424 : W_424 F Wl (fun j' g' _ V' => j' = 432 ∧ g' = { g with rsi := 56#64, rdi := g.r12 } ∧ V' = V)
    g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_424, o25, BitVec.reduceSetWidth]
  ccl

/-- 352, `_progress` (of `r15`) NULL: to 367. -/
theorem vc_352z {d : BitVec 64} (hd : rdq(V, g.r15 + 16#64) = d) (h0 : d = 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 16#64) i)) :
    W_352 F Wl (fun j' g' _ V' => j' = 367 ∧ g' = { g with rdi := d } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd ⊢
  have e : (d == 0) = true := beq_iff_eq.2 h0
  wpx [W_352, W_361, o20, o6, hd, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 352, `_progress` (of `r15`) = `d` not NULL: its vtable in `rax`; to the `call` at 364. -/
theorem vc_352n {d v : BitVec 64} (hd : rdq(V, g.r15 + 16#64) = d) (h0 : d ≠ 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r15 + 16#64) i)) (hv : rdq(V, d) = v)
    (fv : ∀ i < 8, Foot F.data (Addr.add d i)) :
    W_352 F Wl (fun j' g' _ V' => j' = 364 ∧ g' = { g with rdi := d, rax := v } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd hv fv ⊢
  have e : (d == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_352, W_361, o20, o6, hd, hv, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 380, `_progress` (of `r14`) NULL: to 395. -/
theorem vc_380z {d : BitVec 64} (hd : rdq(V, g.r14 + 16#64) = d) (h0 : d = 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 16#64) i)) :
    W_380 F Wl (fun j' g' _ V' => j' = 395 ∧ g' = { g with rdi := d } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd ⊢
  have e : (d == 0) = true := beq_iff_eq.2 h0
  wpx [W_380, W_389, o22, o6, hd, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 380, `_progress` (of `r14`) = `d` not NULL: its vtable in `rax`; to the `call` at 392. -/
theorem vc_380n {d v : BitVec 64} (hd : rdq(V, g.r14 + 16#64) = d) (h0 : d ≠ 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r14 + 16#64) i)) (hv : rdq(V, d) = v)
    (fv : ∀ i < 8, Foot F.data (Addr.add d i)) :
    W_380 F Wl (fun j' g' _ V' => j' = 392 ∧ g' = { g with rdi := d, rax := v } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd hv fv ⊢
  have e : (d == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_380, W_389, o22, o6, hd, hv, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 408, `_progress` (of `r12`) NULL: to 424. -/
theorem vc_408z {d : BitVec 64} (hd : rdq(V, g.r12 + 16#64) = d) (h0 : d = 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 16#64) i)) :
    W_408 F Wl (fun j' g' _ V' => j' = 424 ∧ g' = { g with rdi := d } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd ⊢
  have e : (d == 0) = true := beq_iff_eq.2 h0
  wpx [W_408, W_418, o24, o6, hd, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 408, `_progress` (of `r12`) = `d` not NULL: its vtable in `rax`; to the `call` at 421. -/
theorem vc_408n {d v : BitVec 64} (hd : rdq(V, g.r12 + 16#64) = d) (h0 : d ≠ 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 16#64) i)) (hv : rdq(V, d) = v)
    (fv : ∀ i < 8, Foot F.data (Addr.add d i)) :
    W_408 F Wl (fun j' g' _ V' => j' = 421 ∧ g' = { g with rdi := d, rax := v } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd hv fv ⊢
  have e : (d == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_408, W_418, o24, o6, hd, hv, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 68: `_ratioProgress` = NULL; to 76. -/
theorem vc_68 (w : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 24#64) i)) :
    W_68 F Wl (fun j' g' _ V' => j' = 76 ∧ g' = g ∧ V' = Vst V (g.rbx + 24#64) (toBytesLE (0#64 : BitVec 64) 8))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w ⊢
  wpx [W_68, o2]
  ccl

/-- 76, `progress` not NULL: its vtable in `rax`, `rdi` = `progress`; to the `call` (`AddRef`) at 88. -/
theorem vc_76 {v : BitVec 64} (hp : g.rbp ≠ 0) (hv : rdq(V, g.rbp) = v) (fv : ∀ i < 8, Foot F.data (Addr.add g.rbp i)) :
    W_76 F Wl (fun j' g' _ V' => j' = 88 ∧ g' = { g with rax := v, rdi := g.rbp } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hp hv fv ⊢
  have e : (rbp == 0) = false := beq_eq_false_iff_ne.2 hp
  wpx [W_76, W_81, o3, o4, hv, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 91, the old `_progress` NULL: to 106. -/
theorem vc_91z {d : BitVec 64} (hd : rdq(V, g.rbx + 16#64) = d) (h0 : d = 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 16#64) i)) :
    W_91 F Wl (fun j' g' _ V' => j' = 106 ∧ g' = { g with rdi := d } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd ⊢
  have e : (d == 0) = true := beq_iff_eq.2 h0
  wpx [W_91, W_100, o5, o6, hd, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 91, the old `_progress` = `d` not NULL: its vtable in `rax`; to the `call` (`Release`) at 103. -/
theorem vc_91n {d v : BitVec 64} (hd : rdq(V, g.rbx + 16#64) = d) (h0 : d ≠ 0)
    (fd : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 16#64) i)) (hv : rdq(V, d) = v)
    (fv : ∀ i < 8, Foot F.data (Addr.add d i)) :
    W_91 F Wl (fun j' g' _ V' => j' = 103 ∧ g' = { g with rdi := d, rax := v } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hd fd hv fv ⊢
  have e : (d == 0) = false := beq_eq_false_iff_ne.2 h0
  wpx [W_91, W_100, o5, o6, hd, hv, e,
    BitVec.and_self, Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, false_implies,
    eq_self_iff_true, true_implies, implies_true]
  ccl

/-- 106: `_progress` = `progress`, the arguments of `QueryInterface`; to the `call` at 128. -/
theorem vc_106 {v : BitVec 64} (hv : rdq(V, g.rbp) = v) (fv : ∀ i < 8, Foot F.data (Addr.add g.rbp i))
    (w : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 16#64) i)) :
    W_106 F Wl (fun j' g' _ V' => j' = 128 ∧
      g' = { g with rax := v, rdx := g.rbx + 24#64, rdi := g.rbp, rsi := 7255904#64 } ∧
      V' = Vst V (g.rbx + 16#64) (toBytesLE g.rbp 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hv fv w ⊢
  wpx [W_106, o7, hv]
  ccl

set_option maxHeartbeats 4000000 in
/-- 130: `_inSizeIsMain` stored, the pops; to the `ret` at 148 (each register of the state there by an equation). -/
theorem vc_130e {Q : Post} (w : ∀ i < 1, Foot Wl (Addr.add (g.rbx + 14#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (l5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (l6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ (g' : Gprs) (V' : Addr → Byte), V' = Vst V (g.rbx + 14#64) (toBytesLE (g.r13.setWidth 8) 1) →
      g'.rax = g.rax → g'.rcx = g.rcx → g'.rdx = g.rdx → g'.rbx = rdq(V', g.rsp + 24#64) →
      g'.rsp = g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8 + 8 → g'.rbp = rdq(V', g.rsp + 24#64 + 8) →
      g'.rsi = g.rsi → g'.rdi = g.rdi → g'.r8 = g.r8 → g'.r9 = g.r9 → g'.r10 = g.r10 → g'.r11 = g.r11 →
      g'.r12 = rdq(V', g.rsp + 24#64 + 8 + 8) → g'.r13 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8) →
      g'.r14 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8 + 8) → g'.r15 = rdq(V', g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) →
      ∀ fl, Q 148 g' fl V') : W_130 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w l1 l2 l3 l4 l5 l6 h ⊢
  wpx [W_130, o8]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact w
    | with_reducible exact l1
    | with_reducible exact l2
    | with_reducible exact l3
    | with_reducible exact l4
    | with_reducible exact l5
    | with_reducible exact l6
    | exact trivial
    | apply And.intro
    | intro _)
  all_goals first | rfl | assumption

/-- 130: `_inSizeIsMain` stored, the pops; to the `ret` at 148. -/
theorem vc_130 {Q : Post} (w : ∀ i < 1, Foot Wl (Addr.add (g.rbx + 14#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8) i))
    (l4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8) i))
    (l5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8) i))
    (l6 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8 + 8 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 148 (pops6 (Vst V (g.rbx + 14#64) (toBytesLE (g.r13.setWidth 8) 1)) g) fl
      (Vst V (g.rbx + 14#64) (toBytesLE (g.r13.setWidth 8) 1))) : W_130 F Wl Q g f V := by
  refine vc_130e w l1 l2 l3 l4 l5 l6 ?_
  intro g' V' hV h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 fl
  subst hV
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := g'
  dsimp only at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  subst h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  exact h fl

/-- The `jmp`s. -/
theorem vc_437 : W_437 F Wl (fun j' g' _ V' => j' = 68 ∧ g' = g ∧ V' = V) g f V := by
  unfold W_437; exact ⟨rfl, rfl, rfl⟩
theorem vc_453 : W_453 F Wl (fun j' g' _ V' => j' = 68 ∧ g' = g ∧ V' = V) g f V := by
  unfold W_453; exact ⟨rfl, rfl, rfl⟩
theorem vc_469 : W_469 F Wl (fun j' g' _ V' => j' = 380 ∧ g' = g ∧ V' = V) g f V := by
  unfold W_469; exact ⟨rfl, rfl, rfl⟩
theorem vc_485 : W_485 F Wl (fun j' g' _ V' => j' = 408 ∧ g' = g ∧ V' = V) g f V := by
  unfold W_485; exact ⟨rfl, rfl, rfl⟩
theorem vc_492 : W_492 F Wl (fun j' g' _ V' => j' = 352 ∧ g' = g ∧ V' = V) g f V := by
  unfold W_492; exact ⟨rfl, rfl, rfl⟩

end

/-! ## The calls -/

/-- What the code asks of a function it calls at `f` from `rsp` = `S - 72` (the return address `ra` pushed at
`S - 80`), with the arguments `A` and the bytes `V`: the run goes on to the goal if it does from every state at `ra`
with bytes `V'` for which `P` holds, the registers a call keeps and the spill slot `[S - 64]` as in `V`. -/
def Callc (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S f : Addr) (A : Gprs → Prop) (V : Addr → Byte) (P : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t : Nat) (ra : Addr), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst V (sp72 S - 8) (toBytesLE ra 8)) → Y.cpu.rip = f → Y.cpu.gpr.rsp = sp72 S - 8 →
    A Y.cpu.gpr →
    (∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → P V' →
      Z.cpu.rip = ra → Ocv.Bk Y.cpu.gpr Z.cpu.gpr → rdq(V', sp72 S + 8#64) = rdq(V, sp72 S + 8#64) →
      GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

section
variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S f : Addr} {A : Gprs → Prop} {W : Addr → Byte} {P : (Addr → Byte) → Prop} {U : State} {t j : Nat}

/-- The rest of the run after a call at `j` of length `len`, from the state `U` before it. -/
abbrev Aft (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (W : Addr → Byte) (P : (Addr → Byte) → Prop) (U : State) (j : Nat) : Prop :=
  ∀ (Z : State) (W' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' → P W' →
    Z.cpu.rip = clp_at.add j → Sk U.cpu.gpr Z.cpu.gpr → rdq(W', sp72 S + 8#64) = rdq(W, sp72 S + 8#64) →
    GoG prof L o gev gP gE Z t'

theorem aft_sk {Y Z : State} (hs : U.cpu.gpr.rsp = sp72 S) (hsY : Y.cpu.gpr.rsp = sp72 S - 8)
    (hgY : Y.cpu.gpr = U.cpu.gpr.set 4 (U.cpu.gpr.rsp - 8)) (h : Ocv.Bk Y.cpu.gpr Z.cpu.gpr) :
    Sk U.cpu.gpr Z.cpu.gpr := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h
  refine ⟨?_, b2.trans (by rw [hgY]; try rfl), b3.trans (by rw [hgY]; try rfl), b4.trans (by rw [hgY]; try rfl),
    b5.trans (by rw [hgY]; try rfl), b6.trans (by rw [hgY]; try rfl), b7.trans (by rw [hgY]; try rfl)⟩
  rw [b1, hsY, Ocv.a1s, hs]

/-- A `call [b + d]` at `j`, the target `f` read at `a`. -/
theorem cl_m {b d len : Nat} {a : Addr} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L clp_at clp)
    (hK : KeptW Wl s₀ U) (hA : Agree F U.proc.mm.mem W) (hrip : U.cpu.rip = clp_at.add j) (hj : j < clp.length)
    (hd : Dec prof.feat clp j (FV7z.mk .call 64 [.mem (mbd b d 64)] len)) (hb : eaD U b d = a)
    (hl : ∀ i < 8, Foot F.data (Addr.add a i)) (hc : CodeOK L f) (ht : rdq(W, a) = f)
    (hs : U.cpu.gpr.rsp = sp72 S) (wc : ∀ i < 8, Foot Wl (Addr.add (sp72 S - 8) i))
    (kc : Callc prof F Wl L s₀ o gev gP gE S f A W P) (ha : A (U.cpu.gpr.set 4 (U.cpu.gpr.rsp - 8)))
    (k : Aft prof F Wl L s₀ o gev gP gE S W P U (j + len)) : GoG prof L o gev gP gE U t := by
  obtain ⟨code, hcI, hc0⟩ := hc
  refine c.s_callM hK hA hin hj hrip hd (by rw [hb]; exact hl) hcI hc0 (by rw [hb]; exact ht)
    (by rw [hs]; exact wc) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  rw [hs] at hAY
  have hsY : Y.cpu.gpr.rsp = sp72 S - 8 := (congrArg Gprs.rsp hgY).trans (congrArg (fun x : Addr => x - 8) hs)
  refine kc Y t₁ (clp_at.add (j + len)) hKY hAY hrY hsY (by rw [hgY]; exact ha) ?_
  intro Z W' t' hKZ hAZ hP hrZ hb' hsp
  exact k Z W' t' hKZ hAZ hP hrZ (aft_sk hs hsY hgY hb') hsp

/-- A `call rax` at `j`, `rax` = `f`. -/
theorem cl_r {len : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L clp_at clp)
    (hK : KeptW Wl s₀ U) (hA : Agree F U.proc.mm.mem W) (hrip : U.cpu.rip = clp_at.add j) (hj : j < clp.length)
    (hd : Dec prof.feat clp j (FV7z.mk .call 64 [gr 64 0] len)) (hc : CodeOK L f) (ht : U.cpu.gpr.rax = f)
    (hs : U.cpu.gpr.rsp = sp72 S) (wc : ∀ i < 8, Foot Wl (Addr.add (sp72 S - 8) i))
    (kc : Callc prof F Wl L s₀ o gev gP gE S f A W P) (ha : A (U.cpu.gpr.set 4 (U.cpu.gpr.rsp - 8)))
    (k : Aft prof F Wl L s₀ o gev gP gE S W P U (j + len)) : GoG prof L o gev gP gE U t := by
  obtain ⟨code, hcI, hc0⟩ := hc
  refine c.s_callr hK hA hin hj hrip hd hcI hc0 (by exact ht) (by rw [hs]; exact wc) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  rw [hs] at hAY
  have hsY : Y.cpu.gpr.rsp = sp72 S - 8 := (congrArg Gprs.rsp hgY).trans (congrArg (fun x : Addr => x - 8) hs)
  refine kc Y t₁ (clp_at.add (j + len)) hKY hAY hrY hsY (by rw [hgY]; exact ha) ?_
  intro Z W' t' hKZ hAZ hP hrZ hb' hsp
  exact k Z W' t' hKZ hAZ hP hrZ (aft_sk hs hsY hgY hb') hsp

/-- A `call 0x6014e0` (`operator delete (void *, size_t)`) at `j`. -/
theorem cl_d {rel : Nat} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L clp_at clp)
    (hin2 : CodeIn L 0x6014e0#64 Tiny.c6014e0)
    (hK : KeptW Wl s₀ U) (hA : Agree F U.proc.mm.mem W) (hrip : U.cpu.rip = clp_at.add j) (hj : j < clp.length)
    (hd : Dec prof.feat clp j (FV7z.mk .call 64 [.rel rel] 5))
    (htg : clp_at.add (j + 5) + BitVec.ofNat 64 rel = 0x6014e0#64)
    (hs : U.cpu.gpr.rsp = sp72 S) (wc : ∀ i < 8, Foot Wl (Addr.add (sp72 S - 8) i))
    (kc : Callc prof F Wl L s₀ o gev gP gE S 0x6014e0#64 A W P) (ha : A (U.cpu.gpr.set 4 (U.cpu.gpr.rsp - 8)))
    (k : Aft prof F Wl L s₀ o gev gP gE S W P U (j + 5)) : GoG prof L o gev gP gE U t := by
  refine c.s_call hK hA hin hj hrip hd hin2 (by decide) htg (by rw [hs]; exact wc) ?_
  rintro Y t₁ hKY hAY ⟨hrY, hgY⟩
  rw [hs] at hAY
  have hsY : Y.cpu.gpr.rsp = sp72 S - 8 := (congrArg Gprs.rsp hgY).trans (congrArg (fun x : Addr => x - 8) hs)
  refine kc Y t₁ (clp_at.add (j + 5)) hKY hAY hrY hsY (by rw [hgY]; exact ha) ?_
  intro Z W' t' hKZ hAZ hP hrZ hb' hsp
  exact k Z W' t' hKZ hAZ hP hrZ (aft_sk hs hsY hgY hb') hsp

end

end FV7z.Clp
