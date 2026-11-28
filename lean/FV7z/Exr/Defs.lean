import FV7z.Exr.Cuts
import FV7z.Api.Holds
import FV7z.Lemmas.AddMi64
import FV7z.Tun.Inv
/-!
# `CExtractCallbackConsole::ExtractResult`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `CExtractCallbackConsole::ExtractResult (result)` (`CPP/7zip/UI/Console/ExtractCallbackConsole.cpp`;
`objdump -d`) at `0x5e82c0` in `7zzs`: `this` = `rdi` (`rbx` from 11 on), `result` = `esi` (`r12d`). `S` the stack
pointer at the entry: three pushes (`r12`, `rbp`, `rbx`) and 32 bytes of frame (`aR S`): the stack guard
(`fs:0x28`) at `aR S + 24`, a local `AString` (the message of `HResultToMessage`) at `aR S`. The callees:
`CCriticalSection::Enter` at `0x448b60` (41) and `Leave` at `0x448b80` (197), `CStdOutStream::Flush` at
`0x5a1440` (75, 388), `endl` at `0x5a1470` (123, 281, 376, 535, 603), `fwrite` at `0x624e40` (307, 527, 580, 653),
`HResultToMessage` at `0x5a1ae0` (338), `CStdOutStream::operator<< (const char *)` at `0x5a1530` (350),
`delete []` at `0x6014f0` (364), `CPercentPrinter::ClosePrint` at `0x5f67c0` (409) and
`CStdOutStream::operator<< (UInt64)` at `0x5a1a70` (595). The counters at `this + 408` (110, 265), `this + 416`
(482) and `this + 392` (616) by hand (`add qword [rbx + d], 1`, `Seg.s_add_mi64`); the break counter
`NConsoleClose::g_BreakCounter` is the 4 bytes at `0x79f088`.

- The `call`s (`call_*`, `tgt_*`), the `add`s (`add_*`), the `ret` (`ret_233`).
- `aR`, `P3`, `V0`, `q1`..`q4`: the frame, the bytes after the pushes and after the prologue, the pops' addresses.
- `Fm`, `Fr`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the stack, a callee as a continuation,
  the hypotheses of the runs; `callK`: a `call` and the run from its return.
- `estep`: one step of the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Exr
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `CCriticalSection::Enter` (41). -/
def pc41 : List Byte := [0xe8, 0x72, 0x08, 0xe6, 0xff]
theorem pc41_0 : ∀ feat, Dec feat pc41 0 (FV7z.mk .call 64 [.rel 18446744073707849842] 5) := by dec_rfl
theorem wc_41 : pc41 <+: exr.drop 41 := by decide +kernel
theorem call_41 (feat : Features) : Dec feat exr 41 (FV7z.mk .call 64 [.rel 18446744073707849842] 5) :=
  Dec.shift (j := 41) (k := 0) (pc41_0 feat) wc_41 (Nat.zero_le _)
theorem tgt_41 : exr_at.add (41 + 5) + BitVec.ofNat 64 18446744073707849842 = 0x448b60#64 := by decide

/-- The `call` of `CStdOutStream::Flush` (75). -/
def pc75 : List Byte := [0xe8, 0x30, 0x91, 0xfb, 0xff]
theorem pc75_0 : ∀ feat, Dec feat pc75 0 (FV7z.mk .call 64 [.rel 18446744073709261104] 5) := by dec_rfl
theorem wc_75 : pc75 <+: exr.drop 75 := by decide +kernel
theorem call_75 (feat : Features) : Dec feat exr 75 (FV7z.mk .call 64 [.rel 18446744073709261104] 5) :=
  Dec.shift (j := 75) (k := 0) (pc75_0 feat) wc_75 (Nat.zero_le _)
theorem tgt_75 : exr_at.add (75 + 5) + BitVec.ofNat 64 18446744073709261104 = 0x5a1440#64 := by decide

/-- The `call` of `endl` (123). -/
def pc123 : List Byte := [0xe8, 0x30, 0x91, 0xfb, 0xff]
theorem pc123_0 : ∀ feat, Dec feat pc123 0 (FV7z.mk .call 64 [.rel 18446744073709261104] 5) := by dec_rfl
theorem wc_123 : pc123 <+: exr.drop 123 := by decide +kernel
theorem call_123 (feat : Features) : Dec feat exr 123 (FV7z.mk .call 64 [.rel 18446744073709261104] 5) :=
  Dec.shift (j := 123) (k := 0) (pc123_0 feat) wc_123 (Nat.zero_le _)
theorem tgt_123 : exr_at.add (123 + 5) + BitVec.ofNat 64 18446744073709261104 = 0x5a1470#64 := by decide

/-- The `call` of `CCriticalSection::Leave` (197). -/
def pc197 : List Byte := [0xe8, 0xf6, 0x07, 0xe6, 0xff]
theorem pc197_0 : ∀ feat, Dec feat pc197 0 (FV7z.mk .call 64 [.rel 18446744073707849718] 5) := by dec_rfl
theorem wc_197 : pc197 <+: exr.drop 197 := by decide +kernel
theorem call_197 (feat : Features) : Dec feat exr 197 (FV7z.mk .call 64 [.rel 18446744073707849718] 5) :=
  Dec.shift (j := 197) (k := 0) (pc197_0 feat) wc_197 (Nat.zero_le _)
theorem tgt_197 : exr_at.add (197 + 5) + BitVec.ofNat 64 18446744073707849718 = 0x448b80#64 := by decide

/-- The `call` of `endl` (281). -/
def pc281 : List Byte := [0xe8, 0x92, 0x90, 0xfb, 0xff]
theorem pc281_0 : ∀ feat, Dec feat pc281 0 (FV7z.mk .call 64 [.rel 18446744073709260946] 5) := by dec_rfl
theorem wc_281 : pc281 <+: exr.drop 281 := by decide +kernel
theorem call_281 (feat : Features) : Dec feat exr 281 (FV7z.mk .call 64 [.rel 18446744073709260946] 5) :=
  Dec.shift (j := 281) (k := 0) (pc281_0 feat) wc_281 (Nat.zero_le _)
theorem tgt_281 : exr_at.add (281 + 5) + BitVec.ofNat 64 18446744073709260946 = 0x5a1470#64 := by decide

/-- The `call` of `fwrite` (307). -/
def pc307 : List Byte := [0xe8, 0x48, 0xca, 0x03, 0x00]
theorem pc307_0 : ∀ feat, Dec feat pc307 0 (FV7z.mk .call 64 [.rel 248392] 5) := by dec_rfl
theorem wc_307 : pc307 <+: exr.drop 307 := by decide +kernel
theorem call_307 (feat : Features) : Dec feat exr 307 (FV7z.mk .call 64 [.rel 248392] 5) :=
  Dec.shift (j := 307) (k := 0) (pc307_0 feat) wc_307 (Nat.zero_le _)
theorem tgt_307 : exr_at.add (307 + 5) + BitVec.ofNat 64 248392 = 0x624e40#64 := by decide

/-- The `call` of `HResultToMessage` (338). -/
def pc338 : List Byte := [0xe8, 0xc9, 0x96, 0xfb, 0xff]
theorem pc338_0 : ∀ feat, Dec feat pc338 0 (FV7z.mk .call 64 [.rel 18446744073709262537] 5) := by dec_rfl
theorem wc_338 : pc338 <+: exr.drop 338 := by decide +kernel
theorem call_338 (feat : Features) : Dec feat exr 338 (FV7z.mk .call 64 [.rel 18446744073709262537] 5) :=
  Dec.shift (j := 338) (k := 0) (pc338_0 feat) wc_338 (Nat.zero_le _)
theorem tgt_338 : exr_at.add (338 + 5) + BitVec.ofNat 64 18446744073709262537 = 0x5a1ae0#64 := by decide

/-- The `call` of `CStdOutStream::operator<< (const char *)` (350). -/
def pc350 : List Byte := [0xe8, 0x0d, 0x91, 0xfb, 0xff]
theorem pc350_0 : ∀ feat, Dec feat pc350 0 (FV7z.mk .call 64 [.rel 18446744073709261069] 5) := by dec_rfl
theorem wc_350 : pc350 <+: exr.drop 350 := by decide +kernel
theorem call_350 (feat : Features) : Dec feat exr 350 (FV7z.mk .call 64 [.rel 18446744073709261069] 5) :=
  Dec.shift (j := 350) (k := 0) (pc350_0 feat) wc_350 (Nat.zero_le _)
theorem tgt_350 : exr_at.add (350 + 5) + BitVec.ofNat 64 18446744073709261069 = 0x5a1530#64 := by decide

/-- The `call` of `delete []` (364). -/
def pc364 : List Byte := [0xe8, 0xbf, 0x90, 0x01, 0x00]
theorem pc364_0 : ∀ feat, Dec feat pc364 0 (FV7z.mk .call 64 [.rel 102591] 5) := by dec_rfl
theorem wc_364 : pc364 <+: exr.drop 364 := by decide +kernel
theorem call_364 (feat : Features) : Dec feat exr 364 (FV7z.mk .call 64 [.rel 102591] 5) :=
  Dec.shift (j := 364) (k := 0) (pc364_0 feat) wc_364 (Nat.zero_le _)
theorem tgt_364 : exr_at.add (364 + 5) + BitVec.ofNat 64 102591 = 0x6014f0#64 := by decide

/-- The `call` of `endl` (376). -/
def pc376 : List Byte := [0xe8, 0x33, 0x90, 0xfb, 0xff]
theorem pc376_0 : ∀ feat, Dec feat pc376 0 (FV7z.mk .call 64 [.rel 18446744073709260851] 5) := by dec_rfl
theorem wc_376 : pc376 <+: exr.drop 376 := by decide +kernel
theorem call_376 (feat : Features) : Dec feat exr 376 (FV7z.mk .call 64 [.rel 18446744073709260851] 5) :=
  Dec.shift (j := 376) (k := 0) (pc376_0 feat) wc_376 (Nat.zero_le _)
theorem tgt_376 : exr_at.add (376 + 5) + BitVec.ofNat 64 18446744073709260851 = 0x5a1470#64 := by decide

/-- The `call` of `CStdOutStream::Flush` (388). -/
def pc388 : List Byte := [0xe8, 0xf7, 0x8f, 0xfb, 0xff]
theorem pc388_0 : ∀ feat, Dec feat pc388 0 (FV7z.mk .call 64 [.rel 18446744073709260791] 5) := by dec_rfl
theorem wc_388 : pc388 <+: exr.drop 388 := by decide +kernel
theorem call_388 (feat : Features) : Dec feat exr 388 (FV7z.mk .call 64 [.rel 18446744073709260791] 5) :=
  Dec.shift (j := 388) (k := 0) (pc388_0 feat) wc_388 (Nat.zero_le _)
theorem tgt_388 : exr_at.add (388 + 5) + BitVec.ofNat 64 18446744073709260791 = 0x5a1440#64 := by decide

/-- The `call` of `CPercentPrinter::ClosePrint` (409). -/
def pc409 : List Byte := [0xe8, 0x62, 0xe3, 0x00, 0x00]
theorem pc409_0 : ∀ feat, Dec feat pc409 0 (FV7z.mk .call 64 [.rel 58210] 5) := by dec_rfl
theorem wc_409 : pc409 <+: exr.drop 409 := by decide +kernel
theorem call_409 (feat : Features) : Dec feat exr 409 (FV7z.mk .call 64 [.rel 58210] 5) :=
  Dec.shift (j := 409) (k := 0) (pc409_0 feat) wc_409 (Nat.zero_le _)
theorem tgt_409 : exr_at.add (409 + 5) + BitVec.ofNat 64 58210 = 0x5f67c0#64 := by decide

/-- The `call` of `fwrite` (527). -/
def pc527 : List Byte := [0xe8, 0x6c, 0xc9, 0x03, 0x00]
theorem pc527_0 : ∀ feat, Dec feat pc527 0 (FV7z.mk .call 64 [.rel 248172] 5) := by dec_rfl
theorem wc_527 : pc527 <+: exr.drop 527 := by decide +kernel
theorem call_527 (feat : Features) : Dec feat exr 527 (FV7z.mk .call 64 [.rel 248172] 5) :=
  Dec.shift (j := 527) (k := 0) (pc527_0 feat) wc_527 (Nat.zero_le _)
theorem tgt_527 : exr_at.add (527 + 5) + BitVec.ofNat 64 248172 = 0x624e40#64 := by decide

/-- The `call` of `endl` (535). -/
def pc535 : List Byte := [0xe8, 0x94, 0x8f, 0xfb, 0xff]
theorem pc535_0 : ∀ feat, Dec feat pc535 0 (FV7z.mk .call 64 [.rel 18446744073709260692] 5) := by dec_rfl
theorem wc_535 : pc535 <+: exr.drop 535 := by decide +kernel
theorem call_535 (feat : Features) : Dec feat exr 535 (FV7z.mk .call 64 [.rel 18446744073709260692] 5) :=
  Dec.shift (j := 535) (k := 0) (pc535_0 feat) wc_535 (Nat.zero_le _)
theorem tgt_535 : exr_at.add (535 + 5) + BitVec.ofNat 64 18446744073709260692 = 0x5a1470#64 := by decide

/-- The `call` of `fwrite` (580). -/
def pc580 : List Byte := [0xe8, 0x37, 0xc9, 0x03, 0x00]
theorem pc580_0 : ∀ feat, Dec feat pc580 0 (FV7z.mk .call 64 [.rel 248119] 5) := by dec_rfl
theorem wc_580 : pc580 <+: exr.drop 580 := by decide +kernel
theorem call_580 (feat : Features) : Dec feat exr 580 (FV7z.mk .call 64 [.rel 248119] 5) :=
  Dec.shift (j := 580) (k := 0) (pc580_0 feat) wc_580 (Nat.zero_le _)
theorem tgt_580 : exr_at.add (580 + 5) + BitVec.ofNat 64 248119 = 0x624e40#64 := by decide

/-- The `call` of `CStdOutStream::operator<< (UInt64)` (595). -/
def pc595 : List Byte := [0xe8, 0x58, 0x95, 0xfb, 0xff]
theorem pc595_0 : ∀ feat, Dec feat pc595 0 (FV7z.mk .call 64 [.rel 18446744073709262168] 5) := by dec_rfl
theorem wc_595 : pc595 <+: exr.drop 595 := by decide +kernel
theorem call_595 (feat : Features) : Dec feat exr 595 (FV7z.mk .call 64 [.rel 18446744073709262168] 5) :=
  Dec.shift (j := 595) (k := 0) (pc595_0 feat) wc_595 (Nat.zero_le _)
theorem tgt_595 : exr_at.add (595 + 5) + BitVec.ofNat 64 18446744073709262168 = 0x5a1a70#64 := by decide

/-- The `call` of `endl` (603). -/
def pc603 : List Byte := [0xe8, 0x50, 0x8f, 0xfb, 0xff]
theorem pc603_0 : ∀ feat, Dec feat pc603 0 (FV7z.mk .call 64 [.rel 18446744073709260624] 5) := by dec_rfl
theorem wc_603 : pc603 <+: exr.drop 603 := by decide +kernel
theorem call_603 (feat : Features) : Dec feat exr 603 (FV7z.mk .call 64 [.rel 18446744073709260624] 5) :=
  Dec.shift (j := 603) (k := 0) (pc603_0 feat) wc_603 (Nat.zero_le _)
theorem tgt_603 : exr_at.add (603 + 5) + BitVec.ofNat 64 18446744073709260624 = 0x5a1470#64 := by decide

/-- The `call` of `fwrite` (653). -/
def pc653 : List Byte := [0xe8, 0xee, 0xc8, 0x03, 0x00]
theorem pc653_0 : ∀ feat, Dec feat pc653 0 (FV7z.mk .call 64 [.rel 248046] 5) := by dec_rfl
theorem wc_653 : pc653 <+: exr.drop 653 := by decide +kernel
theorem call_653 (feat : Features) : Dec feat exr 653 (FV7z.mk .call 64 [.rel 248046] 5) :=
  Dec.shift (j := 653) (k := 0) (pc653_0 feat) wc_653 (Nat.zero_le _)
theorem tgt_653 : exr_at.add (653 + 5) + BitVec.ofNat 64 248046 = 0x624e40#64 := by decide

/-- `add qword [rbx + 0x198], 1` (110). -/
def pa110 : List Byte := [0x48, 0x83, 0x83, 0x98, 0x01, 0x00, 0x00, 0x01]
theorem pa110_0 : ∀ feat, Dec feat pa110 0 (FV7z.mk .add 64 [.mem (mbd 3 408 64), .imm 64 1] 8) := by dec_rfl
theorem wa_110 : pa110 <+: exr.drop 110 := by decide +kernel
theorem add_110 (feat : Features) : Dec feat exr 110 (FV7z.mk .add 64 [.mem (mbd 3 408 64), .imm 64 1] 8) :=
  Dec.shift (j := 110) (k := 0) (pa110_0 feat) wa_110 (Nat.zero_le _)

/-- `add qword [rbx + 0x198], 1` (265). -/
def pa265 : List Byte := [0x48, 0x83, 0x83, 0x98, 0x01, 0x00, 0x00, 0x01]
theorem pa265_0 : ∀ feat, Dec feat pa265 0 (FV7z.mk .add 64 [.mem (mbd 3 408 64), .imm 64 1] 8) := by dec_rfl
theorem wa_265 : pa265 <+: exr.drop 265 := by decide +kernel
theorem add_265 (feat : Features) : Dec feat exr 265 (FV7z.mk .add 64 [.mem (mbd 3 408 64), .imm 64 1] 8) :=
  Dec.shift (j := 265) (k := 0) (pa265_0 feat) wa_265 (Nat.zero_le _)

/-- `add qword [rbx + 0x1a0], 1` (482). -/
def pa482 : List Byte := [0x48, 0x83, 0x83, 0xa0, 0x01, 0x00, 0x00, 0x01]
theorem pa482_0 : ∀ feat, Dec feat pa482 0 (FV7z.mk .add 64 [.mem (mbd 3 416 64), .imm 64 1] 8) := by dec_rfl
theorem wa_482 : pa482 <+: exr.drop 482 := by decide +kernel
theorem add_482 (feat : Features) : Dec feat exr 482 (FV7z.mk .add 64 [.mem (mbd 3 416 64), .imm 64 1] 8) :=
  Dec.shift (j := 482) (k := 0) (pa482_0 feat) wa_482 (Nat.zero_le _)

/-- `add qword [rbx + 0x188], 1` (616). -/
def pa616 : List Byte := [0x48, 0x83, 0x83, 0x88, 0x01, 0x00, 0x00, 0x01]
theorem pa616_0 : ∀ feat, Dec feat pa616 0 (FV7z.mk .add 64 [.mem (mbd 3 392 64), .imm 64 1] 8) := by dec_rfl
theorem wa_616 : pa616 <+: exr.drop 616 := by decide +kernel
theorem add_616 (feat : Features) : Dec feat exr 616 (FV7z.mk .add 64 [.mem (mbd 3 392 64), .imm 64 1] 8) :=
  Dec.shift (j := 616) (k := 0) (pa616_0 feat) wa_616 (Nat.zero_le _)


/-- The `ret` (233). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_233 : pret <+: exr.drop 233 := by decide +kernel
theorem ret_233 (feat : Features) : Dec feat exr 233 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 233) (k := 0) (pret_0 feat) w_233 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three pushes and `sub rsp, 0x20`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 32#64

/-- The bytes after the three pushes (`r12`, `rbp`, `rbx`). -/
abbrev P3 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P3 V g) (aR g.rsp + 24#64) (toBytesLE rdq(P3 V g, fb + 40#64) 8)

theorem q1 (S : Addr) : aR S + 32#64 = S - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 32#64 + 8 = S - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 32#64 + 8 + 8 = S - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 32#64 + 8 + 8 + 8 = S := by rw [q3, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` = `this`, `r13`..`r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdi ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `r13`..`r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.2.1.trans h.2.2.1, hk.2.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the three saved registers, the return address, the
stack guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8) = g0.rbp ∧ rdq(W, S - 8) = g0.r12 ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 24#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (exr_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = exr_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`fb` the `fs` base, `S`, `g0` the entry's stack pointer and
registers, `e₂.add j₂` the return address, `I` the invariant of the bytes; `so`, `se` the streams `_so`, `_se`
at `this + 264`, `this + 272`, `p72`, `p88` the buffers at `this + 72`, `this + 88`, all four kept by `I`). The
fields of the object below 456 may be read (`hrd`); the five fields it stores into (`w80`..`w416`) and the two
buffers (`w72`, `w88`) may be stored into, and the stores keep `I` (`c80`..`c88`); the streams may be read when
not null (`hso`, `hse`), the break counter may be read (`hbr`); the callees keep `I`, from any return offset. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop)
    (so se p72 p88 : Addr) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L exr_at exr
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 24#64) i)
  fl0 : ∀ i < 8, Foot F.data (Addr.add (aR S) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  hrd : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 456 → ∀ i < n, Foot F.data (Addr.add (g0.rdi + k) i)
  hbr : ∀ i < 4, Foot F.data (Addr.add 7991432#64 i)
  w80 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 80#64) i)
  w96 : ∀ i < 4, Foot Wl (Addr.add (g0.rdi + 96#64) i)
  w392 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 392#64) i)
  w408 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 408#64) i)
  w416 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 416#64) i)
  w72 : ∀ i < 1, Foot Wl (Addr.add p72 i)
  w88 : ∀ i < 4, Foot Wl (Addr.add p88 i)
  c80 : ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W (g0.rdi + 80#64) bs)
  c96 : ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W (g0.rdi + 96#64) bs)
  c392 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rdi + 392#64) bs)
  c408 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rdi + 408#64) bs)
  c416 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rdi + 416#64) bs)
  c72 : ∀ W (bs : List Byte), bs.length = 1 → I W → I (Vst W p72 bs)
  c88 : ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W p88 bs)
  s264 : ∀ W, I W → rdq(W, g0.rdi + 264#64) = so
  s272 : ∀ W, I W → rdq(W, g0.rdi + 272#64) = se
  s72 : ∀ W, I W → rdq(W, g0.rdi + 72#64) = p72
  s88 : ∀ W, I W → rdq(W, g0.rdi + 88#64) = p88
  hso : so ≠ 0 → ∀ i < 8, Foot F.data (Addr.add so i)
  hse : se ≠ 0 → ∀ i < 8, Foot F.data (Addr.add se i)
  cS : ∃ code : List Byte, CodeIn L 0x448b60#64 code ∧ 0 < code.length
  cL : ∃ code : List Byte, CodeIn L 0x448b80#64 code ∧ 0 < code.length
  cH : ∃ code : List Byte, CodeIn L 0x5a1440#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x5a1470#64 code ∧ 0 < code.length
  cW : ∃ code : List Byte, CodeIn L 0x624e40#64 code ∧ 0 < code.length
  cM : ∃ code : List Byte, CodeIn L 0x5a1ae0#64 code ∧ 0 < code.length
  cO : ∃ code : List Byte, CodeIn L 0x5a1530#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cC : ∃ code : List Byte, CodeIn L 0x5f67c0#64 code ∧ 0 < code.length
  cQ : ∃ code : List Byte, CodeIn L 0x5a1a70#64 code ∧ 0 < code.length
  kS : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x448b60#64 j W (fun _ => True) (fun _ => True)
  kL : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x448b80#64 j W (fun _ => True) (fun _ => True)
  kH : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1440#64 j W (fun _ => True) (fun _ => True)
  kE : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1470#64 j W (fun _ => True) (fun _ => True)
  kW : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x624e40#64 j W (fun _ => True) (fun _ => True)
  kM : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1ae0#64 j W (fun _ => True) (fun _ => True)
  kO : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1530#64 j W (fun _ => True) (fun _ => True)
  kD : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 j W (fun _ => True) (fun _ => True)
  kC : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5f67c0#64 j W (fun _ => True) (fun _ => True)
  kQ : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a1a70#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {so se p72 p88 : Addr} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I so se p72 p88)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = exr_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < exr.length) (hd : Dec prof.feat exr j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : exr_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = exr_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ

end Runs

/-! ## Tactics -/

/-- One step of the closers of the pieces. -/
macro "estep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

end FV7z.Exr
