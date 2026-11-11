import FV7z.Prepare.Aes
import FV7z.Lemmas.FnReg
import FV7z.Prepare.Black2sp
/-!
# `AesGenTables` (PLAN.md G2, "Dispatch theo CPUID", 7-Zip)

`AesGenTables` (`C/Aes.c`, `0x41e540`): two loops of 256 rounds fill `InvS` (`0x794680`, 256 bytes) and the
encryption and decryption tables (`0x794780` to `0x796780`) from `Sbox` (`0x6d8040`). Then it sets `g_AesCbc_Decode`
(`0x7a7e10`), `g_AesCbc_Encode` (`0x7a7e00`), `g_AesCtr_Code` (`0x7a7e08`) and `g_Aes_SupportedFunctions_Flags`
(`0x7a7e18`, 4 bytes):
* `AesCbc_Decode`, `AesCbc_Encode`, `AesCtr_Code` (`0x41e0c0`, `0x41e040`, `0x41e4b0`) with flags 0, or
* if `CPU_IsSupported_AES()`, the AES-NI code (`0x41e990`, `0x41edb0`, `0x41ee50`) with flags 4, or
* if also `CPU_IsSupported_VAES_AVX2()`, the 256-bit VAES `Decode` and `Ctr` (`0x41ebc0`, `0x41f0b0`) with flags 12.

The table values are not followed: only where the loops store, which is inside the tables.
-/
namespace FV7z.Prepare
open ZellicX86 Decode FV7z.Leaf FV7z.Fn

@[simp] theorem set_r5 (g : Gprs) (v : BitVec 64) : g.set (regOf 5) v = { g with rbp := v } := rfl
@[simp] theorem set_r12 (g : Gprs) (v : BitVec 64) : g.set (regOf 12) v = { g with r12 := v } := rfl
@[simp] theorem get_r9 (g : Gprs) : g.get (regOf 9) = g.r9 := rfl
@[simp] theorem set_r9 (g : Gprs) (v : BitVec 64) : g.set (regOf 9) v = { g with r9 := v } := rfl
@[simp] theorem get_r12 (g : Gprs) : g.get (regOf 12) = g.r12 := rfl

/-- `P` holds after any write to a register the table loops compute in. -/
def Scr (P : Gprs → Prop) : Prop :=
  ∀ {r : Nat}, (r = 0 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 10 ∨ r = 11 ∨ r = 12) → ∀ g v, P g → P (g.set (regOf r) v)

variable {prof : Profile}

/-! ## The straight runs of the second loop -/

theorem blk_93 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 93 155 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_93 _) wr_movzx_rr8 (hP (by decide)) (show 93 < aesg.length by omega) <|
    .step (aesg_96 _) wr_lea32 (hP (by decide)) (show 96 < aesg.length by omega) <|
    .step (aesg_99 _) wr_mov_rr32 (hP (by decide)) (show 99 < aesg.length by omega) <|
    .step (aesg_102 _) wr_mov_rr32 (hP (by decide)) (show 102 < aesg.length by omega) <|
    .step (aesg_105 _) wr_xor_ri32 (hP (by decide)) (show 105 < aesg.length by omega) <|
    .step (aesg_109 _) wr_test_rr8 (hP (by decide)) (show 109 < aesg.length by omega) <|
    .step (aesg_111 _) wr_mov_rr32 (hP (by decide)) (show 111 < aesg.length by omega) <|
    .step (aesg_113 _) wr_cmov32 (hP (by decide)) (show 113 < aesg.length by omega) <|
    .step (aesg_117 _) (wr_shl32 (by decide)) (hP (by decide)) (show 117 < aesg.length by omega) <|
    .step (aesg_120 _) wr_mov_rr32 (hP (by decide)) (show 120 < aesg.length by omega) <|
    .step (aesg_123 _) (wr_shl32 (by decide)) (hP (by decide)) (show 123 < aesg.length by omega) <|
    .step (aesg_127 _) wr_mov_rr32 (hP (by decide)) (show 127 < aesg.length by omega) <|
    .step (aesg_129 _) wr_or_rr32 (hP (by decide)) (show 129 < aesg.length by omega) <|
    .step (aesg_131 _) wr_movzx_rr8 (hP (by decide)) (show 131 < aesg.length by omega) <|
    .step (aesg_134 _) wr_or_rr32 (hP (by decide)) (show 134 < aesg.length by omega) <|
    .step (aesg_137 _) wr_xor_rr32 (hP (by decide)) (show 137 < aesg.length by omega) <|
    .step (aesg_140 _) wr_or_rr32 (hP (by decide)) (show 140 < aesg.length by omega) <|
    .step (aesg_142 _) wr_mov_rr32 (hP (by decide)) (show 142 < aesg.length by omega) <|
    .step (aesg_145 _) (wr_shl32 (by decide)) (hP (by decide)) (show 145 < aesg.length by omega) <|
    .step (aesg_149 _) wr_or_rr32 (hP (by decide)) (show 149 < aesg.length by omega) <|
    .step (aesg_152 _) wr_mov_rr32 (hP (by decide)) (show 152 < aesg.length by omega) <|
    .done _

theorem blk_157 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 157 177 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_157 _) wr_mov_rr32 (hP (by decide)) (show 157 < aesg.length by omega) <|
    .step (aesg_159 _) (wr_shl32 (by decide)) (hP (by decide)) (show 159 < aesg.length by omega) <|
    .step (aesg_163 _) (wr_shl32 (by decide)) (hP (by decide)) (show 163 < aesg.length by omega) <|
    .step (aesg_166 _) wr_or_rr32 (hP (by decide)) (show 166 < aesg.length by omega) <|
    .step (aesg_169 _) wr_or_rr32 (hP (by decide)) (show 169 < aesg.length by omega) <|
    .step (aesg_171 _) wr_or_rr32 (hP (by decide)) (show 171 < aesg.length by omega) <|
    .step (aesg_174 _) wr_or_rr32 (hP (by decide)) (show 174 < aesg.length by omega) <|
    .done _

theorem blk_189 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 189 224 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_189 _) wr_mov_rr32 (hP (by decide)) (show 189 < aesg.length by omega) <|
    .step (aesg_192 _) (wr_shl32 (by decide)) (hP (by decide)) (show 192 < aesg.length by omega) <|
    .step (aesg_195 _) (wr_shl32 (by decide)) (hP (by decide)) (show 195 < aesg.length by omega) <|
    .step (aesg_199 _) wr_or_rr32 (hP (by decide)) (show 199 < aesg.length by omega) <|
    .step (aesg_201 _) wr_or_rr32 (hP (by decide)) (show 201 < aesg.length by omega) <|
    .step (aesg_204 _) wr_mov_rr32 (hP (by decide)) (show 204 < aesg.length by omega) <|
    .step (aesg_207 _) (wr_shl32 (by decide)) (hP (by decide)) (show 207 < aesg.length by omega) <|
    .step (aesg_211 _) (wr_shl32 (by decide)) (hP (by decide)) (show 211 < aesg.length by omega) <|
    .step (aesg_214 _) wr_or_rr32 (hP (by decide)) (show 214 < aesg.length by omega) <|
    .step (aesg_217 _) wr_or_rr32 (hP (by decide)) (show 217 < aesg.length by omega) <|
    .step (aesg_220 _) wr_lea32 (hP (by decide)) (show 220 < aesg.length by omega) <|
    .done _

theorem blk_230 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 230 232 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_230 _) wr_mov_rr32 (hP (by decide)) (show 230 < aesg.length by omega) <|
    .done _

theorem blk_239 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 239 297 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_239 _) wr_xor_ri32 (hP (by decide)) (show 239 < aesg.length by omega) <|
    .step (aesg_242 _) wr_test_rr8 (hP (by decide)) (show 242 < aesg.length by omega) <|
    .step (aesg_245 _) wr_cmov32 (hP (by decide)) (show 245 < aesg.length by omega) <|
    .step (aesg_248 _) wr_lea32 (hP (by decide)) (show 248 < aesg.length by omega) <|
    .step (aesg_252 _) wr_mov_rr32 (hP (by decide)) (show 252 < aesg.length by omega) <|
    .step (aesg_255 _) wr_and_ri32 (hP (by decide)) (show 255 < aesg.length by omega) <|
    .step (aesg_261 _) wr_mov_rr32 (hP (by decide)) (show 261 < aesg.length by omega) <|
    .step (aesg_263 _) wr_xor_ri32 (hP (by decide)) (show 263 < aesg.length by omega) <|
    .step (aesg_266 _) wr_test_ri8 (hP (by decide)) (show 266 < aesg.length by omega) <|
    .step (aesg_270 _) wr_cmov32 (hP (by decide)) (show 270 < aesg.length by omega) <|
    .step (aesg_273 _) wr_lea32 (hP (by decide)) (show 273 < aesg.length by omega) <|
    .step (aesg_277 _) wr_and_ri32 (hP (by decide)) (show 277 < aesg.length by omega) <|
    .step (aesg_284 _) wr_mov_rr32 (hP (by decide)) (show 284 < aesg.length by omega) <|
    .step (aesg_287 _) wr_xor_ri32 (hP (by decide)) (show 287 < aesg.length by omega) <|
    .step (aesg_290 _) wr_test_ri8 (hP (by decide)) (show 290 < aesg.length by omega) <|
    .step (aesg_293 _) wr_cmov32 (hP (by decide)) (show 293 < aesg.length by omega) <|
    .done _

theorem blk_305 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 305 367 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_305 _) wr_movzx_rr8 (hP (by decide)) (show 305 < aesg.length by omega) <|
    .step (aesg_309 _) wr_xor_rr32 (hP (by decide)) (show 309 < aesg.length by omega) <|
    .step (aesg_312 _) wr_xor_rr32 (hP (by decide)) (show 312 < aesg.length by omega) <|
    .step (aesg_315 _) wr_xor_rr32 (hP (by decide)) (show 315 < aesg.length by omega) <|
    .step (aesg_318 _) wr_movzx_rr8 (hP (by decide)) (show 318 < aesg.length by omega) <|
    .step (aesg_322 _) wr_mov_rr32 (hP (by decide)) (show 322 < aesg.length by omega) <|
    .step (aesg_324 _) wr_movzx_rr8 (hP (by decide)) (show 324 < aesg.length by omega) <|
    .step (aesg_327 _) wr_xor_rr32 (hP (by decide)) (show 327 < aesg.length by omega) <|
    .step (aesg_329 _) wr_xor_rr32 (hP (by decide)) (show 329 < aesg.length by omega) <|
    .step (aesg_332 _) wr_xor_rr32 (hP (by decide)) (show 332 < aesg.length by omega) <|
    .step (aesg_335 _) wr_mov_rr32 (hP (by decide)) (show 335 < aesg.length by omega) <|
    .step (aesg_338 _) wr_movzx_rr8 (hP (by decide)) (show 338 < aesg.length by omega) <|
    .step (aesg_341 _) (wr_shl32 (by decide)) (hP (by decide)) (show 341 < aesg.length by omega) <|
    .step (aesg_345 _) wr_mov_rr32 (hP (by decide)) (show 345 < aesg.length by omega) <|
    .step (aesg_347 _) wr_or_rr32 (hP (by decide)) (show 347 < aesg.length by omega) <|
    .step (aesg_350 _) (wr_shl32 (by decide)) (hP (by decide)) (show 350 < aesg.length by omega) <|
    .step (aesg_353 _) wr_or_rr32 (hP (by decide)) (show 353 < aesg.length by omega) <|
    .step (aesg_356 _) wr_mov_rr32 (hP (by decide)) (show 356 < aesg.length by omega) <|
    .step (aesg_359 _) (wr_shl32 (by decide)) (hP (by decide)) (show 359 < aesg.length by omega) <|
    .step (aesg_362 _) wr_or_rr32 (hP (by decide)) (show 362 < aesg.length by omega) <|
    .step (aesg_365 _) wr_mov_rr32 (hP (by decide)) (show 365 < aesg.length by omega) <|
    .done _

theorem blk_371 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 371 402 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_371 _) wr_mov_rr32 (hP (by decide)) (show 371 < aesg.length by omega) <|
    .step (aesg_374 _) (wr_shl32 (by decide)) (hP (by decide)) (show 374 < aesg.length by omega) <|
    .step (aesg_377 _) (wr_shl32 (by decide)) (hP (by decide)) (show 377 < aesg.length by omega) <|
    .step (aesg_381 _) wr_or_rr32 (hP (by decide)) (show 381 < aesg.length by omega) <|
    .step (aesg_384 _) wr_or_rr32 (hP (by decide)) (show 384 < aesg.length by omega) <|
    .step (aesg_387 _) wr_mov_rr32 (hP (by decide)) (show 387 < aesg.length by omega) <|
    .step (aesg_389 _) (wr_shl32 (by decide)) (hP (by decide)) (show 389 < aesg.length by omega) <|
    .step (aesg_392 _) wr_or_rr32 (hP (by decide)) (show 392 < aesg.length by omega) <|
    .step (aesg_395 _) wr_mov_rr32 (hP (by decide)) (show 395 < aesg.length by omega) <|
    .step (aesg_398 _) (wr_shl32 (by decide)) (hP (by decide)) (show 398 < aesg.length by omega) <|
    .done _

theorem blk_409 {P : Gprs → Prop} (hP : Scr P) : WRun prof aesg P 409 446 := by
  have hl : aesg.length = 617 := aesg_length
  exact
    .step (aesg_409 _) wr_mov_rr32 (hP (by decide)) (show 409 < aesg.length by omega) <|
    .step (aesg_412 _) (wr_shl32 (by decide)) (hP (by decide)) (show 412 < aesg.length by omega) <|
    .step (aesg_415 _) (wr_shl32 (by decide)) (hP (by decide)) (show 415 < aesg.length by omega) <|
    .step (aesg_419 _) wr_or_rr32 (hP (by decide)) (show 419 < aesg.length by omega) <|
    .step (aesg_422 _) (wr_shl32 (by decide)) (hP (by decide)) (show 422 < aesg.length by omega) <|
    .step (aesg_425 _) wr_or_rr32 (hP (by decide)) (show 425 < aesg.length by omega) <|
    .step (aesg_428 _) wr_or_rr32 (hP (by decide)) (show 428 < aesg.length by omega) <|
    .step (aesg_431 _) wr_mov_rr32 (hP (by decide)) (show 431 < aesg.length by omega) <|
    .step (aesg_433 _) (wr_shl32 (by decide)) (hP (by decide)) (show 433 < aesg.length by omega) <|
    .step (aesg_436 _) (wr_shl32 (by decide)) (hP (by decide)) (show 436 < aesg.length by omega) <|
    .step (aesg_439 _) wr_or_rr32 (hP (by decide)) (show 439 < aesg.length by omega) <|
    .step (aesg_441 _) wr_or_rr32 (hP (by decide)) (show 441 < aesg.length by omega) <|
    .step (aesg_444 _) wr_or_rr32 (hP (by decide)) (show 444 < aesg.length by omega) <|
    .done _


/-! ## The contract -/

/-- What it writes: the tables, `[0x794680, 0x796780)`, and the four globals, `[0x7a7e00, 0x7a7e1c)`. -/
def agW (_ : State) : List Rgn := [⟨0x794680, 0x2100⟩, ⟨0x7a7e00, 28⟩]

/-- What it reads besides: the canary (its callees read it), and `Sbox`. -/
def agR (s : State) : List Rgn := [⟨Addr.add s.cpu.seg.fsBase 40, 8⟩, ⟨0x6d8040, 256⟩]

/-- The canary apart from the stack it uses; the tables and globals apart from that stack and the return address's
slot. -/
def agPre (s : State) : Prop :=
  ((Addr.add s.cpu.seg.fsBase 40).toNat + 8 ≤ s.cpu.gpr.rsp.toNat - 136 ∨
    s.cpu.gpr.rsp.toNat ≤ (Addr.add s.cpu.seg.fsBase 40).toNat) ∧
  (0x7a7e1c + 136 ≤ s.cpu.gpr.rsp.toNat ∨ s.cpu.gpr.rsp.toNat + 8 ≤ 0x794680)

/-- The three outcomes: `Decode`, `Encode`, `Ctr`, flags. -/
def agVals (prof : Profile) (d e c : BitVec 64) (f : BitVec 32) : Prop :=
  (d = 0x41e0c0 ∧ e = 0x41e040 ∧ c = 0x41e4b0 ∧ f = 0) ∨
  (d = 0x41e990 ∧ e = 0x41edb0 ∧ c = 0x41ee50 ∧ f = 4 ∧ prof.feat.aes = true) ∨
  (d = 0x41ebc0 ∧ e = 0x41edb0 ∧ c = 0x41f0b0 ∧ f = 12 ∧ prof.feat.aes = true ∧ prof.feat.vaes = true ∧
    prof.feat.avx2 = true ∧ prof.feat.avx = true)

/-- At the return: the portable code, or the AES-NI code on a processor with AES, or the VAES code on one with AES,
VAES, AVX2 and AVX. -/
def agPost (prof : Profile) (_ Y : State) : Prop :=
  agVals prof (ptrAt 0x7a7e10 Y) (ptrAt 0x7a7e00 Y) (ptrAt 0x7a7e08 Y)
    (ofBytesLE 32 (readBytes Y.proc.mm.mem 0x7a7e18 4))

/-- The contract: a stack of 136 bytes (its three saved registers, a return address, `CPU_IsSupported_VAES_AVX2`'s
104 with what it calls), the tables and globals written, the canary and `Sbox` read. -/
abbrev agC (prof : Profile) : Contract := fn 136 agW agR agPre (agPost prof)

/-! ## Invariants -/

/-- The call's `rsp` is `p + 136`; the stack `[p, p + 144)` apart from the tables and globals. -/
structure AgEnv (s₀ : State) (p : Addr) : Prop where
  lo : s₀.cpu.gpr.rsp - BitVec.ofNat 64 136 = p
  sp : s₀.cpu.gpr.rsp = p.add 136
  fit : p.toNat + 144 ≤ 2 ^ 64
  apart : 0x7a7e1c ≤ p.toNat ∨ p.toNat + 144 ≤ 0x794680

/-- `rbx`, `rbp`, `r12` of the call in their slots. -/
def Stk (s₀ : State) (p : Addr) (V : Addr → Byte) : Prop :=
  ofBytesLE 64 ((byteAddrs (p.add 112) 8).map V) = s₀.cpu.gpr.rbx ∧
  ofBytesLE 64 ((byteAddrs (p.add 120) 8).map V) = s₀.cpu.gpr.rbp ∧
  ofBytesLE 64 ((byteAddrs (p.add 128) 8).map V) = s₀.cpu.gpr.r12

/-- The registers kept through the body: `rsp` below the saved registers, and the other callee-saved ones. -/
structure Base (s₀ : State) (p : Addr) (g : Gprs) : Prop where
  sp : g.rsp = p.add 112
  r13 : g.r13 = s₀.cpu.gpr.r13
  r14 : g.r14 = s₀.cpu.gpr.r14
  r15 : g.r15 = s₀.cpu.gpr.r15

/-- In the second loop: the round in `rdi`, the two table pointers in `rsi` and `rcx`, `InvS` in `r8`, `Sbox` in
`r9`. -/
structure G2 (s₀ : State) (p a b c : Addr) (g : Gprs) : Prop where
  rdi : g.rdi = a
  rsi : g.rsi = b
  rcx : g.rcx = c
  r8 : g.r8 = 0x794680
  r9 : g.r9 = 0x6d8040
  base : Base s₀ p g

theorem G2.scr {s₀ : State} {p a b c : Addr} : Scr (G2 s₀ p a b c) := by
  intro r hr g v h
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨h.rdi, h.rsi, h.rcx, h.r8, h.r9, ⟨h.base.sp, h.base.r13, h.base.r14, h.base.r15⟩⟩

theorem G2.of_eq {s₀ : State} {p a b c : Addr} {g g' : Gprs} (hp : G2 s₀ p a b c g) (h : g' = g) :
    G2 s₀ p a b c g' := h ▸ hp

theorem ofNat_succ64' (i : Nat) : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem G2.add_rdi {s₀ : State} {p b c : Addr} {g : Gprs} {i : Nat} (h : G2 s₀ p (BitVec.ofNat 64 i) b c g) :
    G2 s₀ p (BitVec.ofNat 64 (i + 1)) b c (g.set (regOf 7) (g.get (regOf 7) + BitVec.ofNat 64 1)) :=
  ⟨by simp only [set_r7, get_r7]; rw [h.rdi, ofNat_succ64'], h.rsi, h.rcx, h.r8, h.r9,
    ⟨h.base.sp, h.base.r13, h.base.r14, h.base.r15⟩⟩

theorem add_addn (a : Addr) (n m : Nat) : a.add n + BitVec.ofNat 64 m = a.add (n + m) := by
  rw [← addr_add_add]; rfl

theorem add_m4 (a : Addr) (n : Nat) : a.add (n + 4) + BitVec.ofNat 64 18446744073709551612 = a.add n := by
  rw [← addr_add_add]
  show a.add n + BitVec.ofNat 64 4 + BitVec.ofNat 64 18446744073709551612 = a.add n
  rw [BitVec.add_assoc, show BitVec.ofNat 64 4 + BitVec.ofNat 64 18446744073709551612 = 0#64 by decide, BitVec.add_zero]

theorem ofNat_succ64 (i : Nat) : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem G2.add_rsi {s₀ : State} {p a c : Addr} {g : Gprs} {n : Nat} (h : G2 s₀ p a (Addr.add 0x794680 n) c g) :
    G2 s₀ p a (Addr.add 0x794680 (n + 4)) c (g.set (regOf 6) (g.get (regOf 6) + BitVec.ofNat 64 4)) :=
  ⟨h.rdi, by simp only [set_r6, get_r6]; rw [h.rsi, add_addn], h.rcx, h.r8, h.r9,
    ⟨h.base.sp, h.base.r13, h.base.r14, h.base.r15⟩⟩

theorem G2.add_rcx {s₀ : State} {p a b : Addr} {g : Gprs} {n : Nat} (h : G2 s₀ p a b (Addr.add 0x794680 n) g) :
    G2 s₀ p a b (Addr.add 0x794680 (n + 4)) (g.set (regOf 1) (g.get (regOf 1) + BitVec.ofNat 64 4)) :=
  ⟨h.rdi, h.rsi, by simp only [set_r1, get_r1]; rw [h.rcx, add_addn], h.r8, h.r9,
    ⟨h.base.sp, h.base.r13, h.base.r14, h.base.r15⟩⟩

theorem ofNat_eq256 {i : Nat} (h : i + 1 ≤ 256) : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 256 ↔ i + 1 = 256 :=
  ⟨fun e => by have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega,
    fun e => by rw [e]⟩

theorem zx8 (x : BitVec 8) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem tnT {n : Nat} (h : n < 0x2100) : (Addr.add 0x794680 n).toNat = 0x794680 + n :=
  toNat_add_of_fits (n := 0x2100) h (by decide)

theorem Stk.st {s₀ : State} {p : Addr} {V : Addr → Byte} (h : Stk s₀ p V) (hp : p.toNat + 136 ≤ 2 ^ 64)
    {a : Addr} {m w : Nat} (v : BitVec w) (ha : a.toNat + m ≤ 2 ^ 64)
    (hap : a.toNat + m ≤ p.toNat + 112 ∨ p.toNat + 136 ≤ a.toNat) : Stk s₀ p (Vst V a (toBytesLE v m)) := by
  have e1 : (p.add 112).toNat = p.toNat + 112 := toNat_addn (n := 136) (by omega) hp
  have e2 : (p.add 120).toNat = p.toNat + 120 := toNat_addn (n := 136) (by omega) hp
  have e3 : (p.add 128).toNat = p.toNat + 128 := toNat_addn (n := 136) (by omega) hp
  refine ⟨?_, ?_, ?_⟩
  · rw [rd_apart v ha (by omega) (by omega)]; exact h.1
  · rw [rd_apart v ha (by omega) (by omega)]; exact h.2.1
  · rw [rd_apart v ha (by omega) (by omega)]; exact h.2.2

/-- A store into the tables or globals keeps the saved registers. -/
theorem Stk.stW {s₀ : State} {p : Addr} {V : Addr → Byte} (h : Stk s₀ p V) (hE : AgEnv s₀ p)
    {a : Addr} {m w : Nat} (v : BitVec w) (ha : 0x794680 ≤ a.toNat) (hb : a.toNat + m ≤ 0x7a7e1c) :
    Stk s₀ p (Vst V a (toBytesLE v m)) :=
  h.st (by have := hE.fit; omega) v (by omega) (by have := hE.apart; omega)

theorem Stk.stT {s₀ : State} {p : Addr} {V : Addr → Byte} (h : Stk s₀ p V) (hE : AgEnv s₀ p)
    {n m w : Nat} (hn : n + m ≤ 0x2100) (hm : 0 < m) (v : BitVec w) :
    Stk s₀ p (Vst V (Addr.add 0x794680 n) (toBytesLE v m)) :=
  h.stW hE v (by rw [tnT (by omega)]; omega) (by rw [tnT (by omega)]; omega)

/-- A callee's stores, below the saved registers, keep them. -/
theorem Stk.keep {s₀ : State} {p : Addr} {V V' : Addr → Byte} (h : Stk s₀ p V) (hp : p.toNat + 136 ≤ 2 ^ 64)
    {q : Addr} {n : Nat} (hV : ∀ x, (∀ i < n, x ≠ q.add i) → V' x = V x) (hq : q.toNat + n ≤ p.toNat + 112) :
    Stk s₀ p V' := by
  have key : ∀ d, 112 ≤ d → d + 8 ≤ 136 → (byteAddrs (p.add d) 8).map V' = (byteAddrs (p.add d) 8).map V := by
    intro d h1 h2
    apply List.map_congr_left
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_byteAddrs.1 hx
    refine hV _ fun i hi e => ?_
    have := congrArg BitVec.toNat e
    rw [addr_add_add, toNat_addn (n := 136) (by omega) hp, toNat_addn hi (by omega)] at this
    omega
  exact ⟨(congrArg _ (key 112 (by omega) (by omega))).trans h.1, (congrArg _ (key 120 (by omega) (by omega))).trans h.2.1,
    (congrArg _ (key 128 (by omega) (by omega))).trans h.2.2⟩

variable {L : List (Addr × List Byte)} {s₀ : State} {ra : Addr} {o : Oracle}

theorem agT {n : Nat} (h : n < 0x2100) : Foot (ws 136 agW s₀) (Addr.add 0x794680 n) :=
  ⟨⟨0x794680, 0x2100⟩, by simp [agW], mem_add_of_fits h (by decide)⟩

theorem agG {n : Nat} (h : n < 28) : Foot (ws 136 agW s₀) (Addr.add 0x7a7e00 n) :=
  ⟨⟨0x7a7e00, 28⟩, by simp [agW], mem_add_of_fits h (by decide)⟩

theorem agS {n : Nat} (h : n < 256) :
    Foot (fp 136 agW agR agPre (agPost prof) L s₀).data (Addr.add 0x6d8040 n) :=
  ⟨⟨0x6d8040, 256⟩, by simp [Footprint.data, Contract.footprint, fn, agR], mem_add_of_fits h (by decide)⟩

theorem agK {p : Addr} (hE : AgEnv s₀ p) {n : Nat} (h : n < 136) : Foot (ws 136 agW s₀) (p.add n) :=
  ⟨below s₀ 136, by simp, by simp only [below, hE.lo]; exact mem_add_of_fits h (by have := hE.fit; omega)⟩

theorem agPost_of {s₀ Y : State} {d e c : BitVec 64} {f : BitVec 32}
    (hd : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x7a7e10 8) = d)
    (he : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x7a7e00 8) = e)
    (hc : ofBytesLE 64 (readBytes Y.proc.mm.mem 0x7a7e08 8) = c)
    (hf : ofBytesLE 32 (readBytes Y.proc.mm.mem 0x7a7e18 4) = f) (h : agVals prof d e c f) :
    agPost prof s₀ Y := by
  unfold agPost ptrAt; rw [hd, he, hc, hf]; exact h

/-! ## The first loop: `InvS[Sbox[i]] = i` -/

theorem agLoop1 (c : Call prof 136 agW agR agPre (agPost prof) 0x41e540 L s₀ ra o) (hin : CodeIn L 0x41e540 aesg)
    {p : Addr} (hE : AgEnv s₀ p)
    (next : ∀ (V : Addr → Byte) Y t, KeptW (ws 136 agW s₀) s₀ Y →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) Y.proc.mm.mem V → Y.cpu.rip = (0x41e540 : Addr).add 52 →
      Base s₀ p Y.cpu.gpr → Y.cpu.gpr.r8 = 0x794680 → Stk s₀ p V →
      Go prof 136 agW agR agPre (agPost prof) L s₀ ra o Y t) :
    ∀ n i, n + i = 255 → ∀ (V : Addr → Byte) X t d, KeptW (ws 136 agW s₀) s₀ X →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x41e540 : Addr).add 36 →
      Base s₀ p X.cpu.gpr → X.cpu.gpr.rax = BitVec.ofNat 64 i → d < 256 → X.cpu.gpr.rdx = BitVec.ofNat 64 d →
      X.cpu.gpr.rcx = 0x6d8040 → X.cpu.gpr.r8 = 0x794680 → Stk s₀ p V →
      Go prof 136 agW agR agPre (agPost prof) L s₀ ra o X t := by
  have hl : aesg.length = 617 := aesg_length
  have body : ∀ i, i < 256 → ∀ (V : Addr → Byte) X t d, KeptW (ws 136 agW s₀) s₀ X →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x41e540 : Addr).add 36 →
      Base s₀ p X.cpu.gpr → X.cpu.gpr.rax = BitVec.ofNat 64 i → d < 256 → X.cpu.gpr.rdx = BitVec.ofNat 64 d →
      X.cpu.gpr.rcx = 0x6d8040 → X.cpu.gpr.r8 = 0x794680 → Stk s₀ p V →
      (i + 1 < 256 → ∀ (V : Addr → Byte) X t d, KeptW (ws 136 agW s₀) s₀ X →
        Agree (fp 136 agW agR agPre (agPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x41e540 : Addr).add 36 →
        Base s₀ p X.cpu.gpr → X.cpu.gpr.rax = BitVec.ofNat 64 (i + 1) → d < 256 → X.cpu.gpr.rdx = BitVec.ofNat 64 d →
        X.cpu.gpr.rcx = 0x6d8040 → X.cpu.gpr.r8 = 0x794680 → Stk s₀ p V →
        Go prof 136 agW agR agPre (agPost prof) L s₀ ra o X t) →
      Go prof 136 agW agR agPre (agPost prof) L s₀ ra o X t := by
    intro i hi V X t d hK hA hr hb hax hd hdx hcx hr8 hS more
    -- `mov [r8 + rdx], al`
    have he : eaI X 8 2 0 = Addr.add 0x794680 d := by simp [eaI, hdx, hr8, Addr.add]
    refine c.s_mov_m8i hK hA hin (by omega) hr (aesg_36 _) (by rw [he]; exact agT (by omega)) ?_
    have hS1 := hS.stT hE (n := d) (m := 1) (by omega) (by omega) (rv X 8 0)
    rw [he]
    rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
    -- `add rax, 1`, `cmp rax, 256`, `jne`
    refine c.s_add_ri64 hK1 hA1 hin (by omega) hr1 (aesg_40 _) ?_
    rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    have hY2 : Y2.cpu.gpr = { X.cpu.gpr with rax := BitVec.ofNat 64 (i + 1) } := by
      rw [hg2, hg1, set_r0, get_r0, hax, ofNat_succ64]
    refine c.s_cmp_ri64 hK2 hA2 hin (by omega) hr2 (aesg_44 _) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hg3, hf3⟩
    have hz : Y3.cpu.rflags.cond 5 = !decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 256) := by
      simp [Rflags.cond, hf3, rv, hY2]
    refine c.s_jcc hK3 hA3 hin (by omega) hr3 (aesg_50 _) (tgt := 32) rfl (by omega) (fun hc => ?_) (fun _ => ?_)
    · -- the next round: `movzx edx, byte [rcx + rax]`
      have hne : i + 1 < 256 := by
        rw [hz] at hc
        refine Nat.lt_of_le_of_ne (by omega) fun h => ?_
        rw [h] at hc
        simp at hc
      rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
      have hl4 : eaI Y4 1 0 0 = Addr.add 0x6d8040 (i + 1) := by simp [eaI, hg4, hg3, hY2, hcx, Addr.add]
      refine c.s_movzx8_i hK4 hA4 hin (by omega) hr4 (aesg_32 _) (by rw [hl4]; exact agS hne) ?_
      rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
      obtain ⟨x, hx⟩ : ∃ x : BitVec 8, Y5.cpu.gpr = Y4.cpu.gpr.set (regOf 2) ((x.setWidth 32).setWidth 64) :=
        ⟨_, hg5⟩
      refine more hne _ Y5 t5 x.toNat hK5 hA5 hr5 ?_ ?_ x.isLt ?_ ?_ ?_ hS1
      · rw [hx, hg4, hg3, hY2]; exact ⟨hb.sp, hb.r13, hb.r14, hb.r15⟩
      · rw [hx, hg4, hg3, hY2]; rfl
      · rw [hx, set_r2, zx8]
      · rw [hx, hg4, hg3, hY2]; exact hcx
      · rw [hx, hg4, hg3, hY2]; exact hr8
    · -- the last round
      rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
      refine next _ Y4 t4 hK4 hA4 hr4 ?_ ?_ hS1
      · rw [hg4, hg3, hY2]; exact ⟨hb.sp, hb.r13, hb.r14, hb.r15⟩
      · rw [hg4, hg3, hY2]; exact hr8
  intro n
  induction n with
  | zero =>
    intro i hi V X t d hK hA hr hb hax hd hdx hcx hr8 hS
    exact body i (by omega) V X t d hK hA hr hb hax hd hdx hcx hr8 hS (fun h => absurd h (by omega))
  | succ n ih =>
    intro i hi V X t d hK hA hr hb hax hd hdx hcx hr8 hS
    exact body i (by omega) V X t d hK hA hr hb hax hd hdx hcx hr8 hS (fun _ => ih (i + 1) (by omega))


/-- `mov [b + d], r32` into the tables. -/
theorem agSt (c : Call prof 136 agW agR agPre (agPost prof) 0x41e540 L s₀ ra o) (hin : CodeIn L 0x41e540 aesg)
    {p : Addr} (hE : AgEnv s₀ p) {X : State} {t j b d r len n : Nat} {V : Addr → Byte}
    (hK : KeptW (ws 136 agW s₀) s₀ X) (hA : Agree (fp 136 agW agR agPre (agPost prof) L s₀) X.proc.mm.mem V)
    (hrip : X.cpu.rip = (0x41e540 : Addr).add j) (hj : j < 617)
    (hd : Dec prof.feat aesg j (FV7z.mk .mov 32 [.mem (mbd b d 32), gr 32 r] len))
    (hea : eaD X b d = Addr.add 0x794680 n) (hn : n + 4 ≤ 0x2100) (hS : Stk s₀ p V)
    (k' : ∀ V' : Addr → Byte, Stk s₀ p V' → Cont prof 136 agW agR agPre (agPost prof) L s₀ ra o V'
      fun Y => Y.cpu.rip = (0x41e540 : Addr).add (j + len) ∧ Y.cpu.gpr = X.cpu.gpr) :
    Go prof 136 agW agR agPre (agPost prof) L s₀ ra o X t :=
  c.s_mov_mr hK hA hin (by rw [aesg_length]; exact hj) hrip (Or.inl rfl) hd
    (fun i hi => by rw [hea, addr_add_add]; exact agT (by omega))
    (by rw [hea]; exact k' _ (hS.stT hE (by omega) (by omega) _))

theorem eaD_of {X : State} {b d n : Nat} {v : Addr} (h : X.cpu.gpr.get (regOf b) = Addr.add v n) :
    eaD X b d = Addr.add v (n + d) := by
  simp only [eaD, h]; exact add_addn v n d

/-! ## The second loop: the encryption and decryption tables -/

theorem agLoop2 (c : Call prof 136 agW agR agPre (agPost prof) 0x41e540 L s₀ ra o) (hin : CodeIn L 0x41e540 aesg)
    {p : Addr} (hE : AgEnv s₀ p)
    (next : ∀ (V : Addr → Byte) Y t, KeptW (ws 136 agW s₀) s₀ Y →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) Y.proc.mm.mem V → Y.cpu.rip = (0x41e540 : Addr).add 476 →
      Base s₀ p Y.cpu.gpr → Stk s₀ p V → Go prof 136 agW agR agPre (agPost prof) L s₀ ra o Y t) :
    ∀ n i, n + i = 255 → ∀ (V : Addr → Byte) X t, KeptW (ws 136 agW s₀) s₀ X →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x41e540 : Addr).add 93 →
      G2 s₀ p (BitVec.ofNat 64 i) (Addr.add 0x794680 (256 + 4 * i)) (Addr.add 0x794680 (4352 + 4 * i))
        X.cpu.gpr → Stk s₀ p V →
      Go prof 136 agW agR agPre (agPost prof) L s₀ ra o X t := by
  have hl : aesg.length = 617 := aesg_length
  have body : ∀ i, i < 256 → ∀ (V : Addr → Byte) X t, KeptW (ws 136 agW s₀) s₀ X →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x41e540 : Addr).add 93 →
      G2 s₀ p (BitVec.ofNat 64 i) (Addr.add 0x794680 (256 + 4 * i)) (Addr.add 0x794680 (4352 + 4 * i))
        X.cpu.gpr → Stk s₀ p V →
      (i + 1 < 256 → ∀ (V : Addr → Byte) X t, KeptW (ws 136 agW s₀) s₀ X →
        Agree (fp 136 agW agR agPre (agPost prof) L s₀) X.proc.mm.mem V → X.cpu.rip = (0x41e540 : Addr).add 93 →
        G2 s₀ p (BitVec.ofNat 64 (i + 1)) (Addr.add 0x794680 (256 + 4 * (i + 1)))
          (Addr.add 0x794680 (4352 + 4 * (i + 1))) X.cpu.gpr → Stk s₀ p V →
        Go prof 136 agW agR agPre (agPost prof) L s₀ ra o X t) →
      Go prof 136 agW agR agPre (agPost prof) L s₀ ra o X t := by
    intro i hi V X t hK hA hr hP hS more
    refine c.s_wrun (blk_93 G2.scr) hin hK hA hr hP ?_
    rintro Y1 t1 hK1 hA1 ⟨hr1, hP1⟩
    refine agSt c hin hE hK1 hA1 hr1 (by omega) (aesg_155 _) (eaD_of ((get_r1 _).trans hP1.rcx)) (by omega) hS ?_
    rintro V2 hS2 Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
    refine c.s_wrun (blk_157 G2.scr) hin hK2 hA2 hr2 (hP1.of_eq hg2) ?_
    rintro Y3 t3 hK3 hA3 ⟨hr3, hP3⟩
    -- `movzx r12d, byte [r8 + rdi]`, from `InvS`
    have hl3 : eaI Y3 8 7 0 = Addr.add 0x794680 i := by simp [eaI, hP3.r8, hP3.rdi, Addr.add]
    refine c.s_movzx8_i hK3 hA3 hin (by omega) hr3 (aesg_177 _) (by rw [hl3]; exact c.hws _ (agT (by omega))) ?_
    rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
    have hP4 := (G2.scr (by decide) _ _ hP3).of_eq hg4
    refine agSt c hin hE hK4 hA4 hr4 (by omega) (aesg_182 _) (eaD_of ((get_r1 _).trans hP4.rcx)) (by omega) hS2 ?_
    rintro V5 hS5 Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
    refine c.s_wrun (blk_189 G2.scr) hin hK5 hA5 hr5 (hP4.of_eq hg5) ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hP6⟩
    refine agSt c hin hE hK6 hA6 hr6 (by omega) (aesg_224 _) (eaD_of ((get_r1 _).trans hP6.rcx)) (by omega) hS5 ?_
    rintro V7 hS7 Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    refine c.s_wrun (blk_230 G2.scr) hin hK7 hA7 hr7 (hP6.of_eq hg7) ?_
    rintro Y8 t8 hK8 hA8 ⟨hr8, hP8⟩
    refine agSt c hin hE hK8 hA8 hr8 (by omega) (aesg_232 _) (eaD_of ((get_r1 _).trans hP8.rcx)) (by omega) hS7 ?_
    rintro V9 hS9 Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine c.s_wrun (blk_239 G2.scr) hin hK9 hA9 hr9 (hP8.of_eq hg9) ?_
    rintro Y10 t10 hK10 hA10 ⟨hr10, hP10⟩
    -- `add rdi, 1`, `add rsi, 4`
    refine c.s_add_ri64 hK10 hA10 hin (by omega) hr10 (aesg_297 _) ?_
    rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
    have hP11 := hP10.add_rdi.of_eq hg11
    refine c.s_add_ri64 hK11 hA11 hin (by omega) hr11 (aesg_301 _) ?_
    rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
    have hP12 := hP11.add_rsi.of_eq hg12
    refine c.s_wrun (blk_305 G2.scr) hin hK12 hA12 hr12 hP12 ?_
    rintro Y13 t13 hK13 hA13 ⟨hr13, hP13⟩
    have e13 : eaD Y13 6 18446744073709551612 = Addr.add 0x794680 (256 + 4 * i) := by
      simp only [eaD, get_r6, hP13.rsi]; exact add_m4 _ _
    refine agSt c hin hE hK13 hA13 hr13 (by omega) (aesg_367 _) e13 (by omega) hS9 ?_
    rintro V14 hS14 Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
    refine c.s_wrun (blk_371 G2.scr) hin hK14 hA14 hr14 (hP13.of_eq hg14) ?_
    rintro Y15 t15 hK15 hA15 ⟨hr15, hP15⟩
    refine agSt c hin hE hK15 hA15 hr15 (by omega) (aesg_402 _) (eaD_of ((get_r6 _).trans hP15.rsi)) (by omega)
      hS14 ?_
    rintro V16 hS16 Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
    refine c.s_wrun (blk_409 G2.scr) hin hK16 hA16 hr16 (hP15.of_eq hg16) ?_
    rintro Y17 t17 hK17 hA17 ⟨hr17, hP17⟩
    refine agSt c hin hE hK17 hA17 hr17 (by omega) (aesg_446 _) (eaD_of ((get_r6 _).trans hP17.rsi)) (by omega)
      hS16 ?_
    rintro V18 hS18 Y18 t18 hK18 hA18 ⟨hr18, hg18⟩
    have hP18 := hP17.of_eq hg18
    refine agSt c hin hE hK18 hA18 hr18 (by omega) (aesg_453 _) (eaD_of ((get_r6 _).trans hP18.rsi)) (by omega)
      hS18 ?_
    rintro V19 hS19 Y19 t19 hK19 hA19 ⟨hr19, hg19⟩
    -- `add rcx, 4`, `cmp rdi, 256`, `jne`
    refine c.s_add_ri64 hK19 hA19 hin (by omega) hr19 (aesg_459 _) ?_
    rintro Y20 t20 hK20 hA20 ⟨hr20, hg20⟩
    have hP20 := (hP18.of_eq hg19).add_rcx.of_eq hg20
    refine c.s_cmp_ri64 hK20 hA20 hin (by omega) hr20 (aesg_463 _) ?_
    rintro Y21 t21 hK21 hA21 ⟨hr21, hg21, hf21⟩
    have hP21 := hP20.of_eq hg21
    have hz : Y21.cpu.rflags.cond 5 = !decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 256) := by
      simp [Rflags.cond, hf21, rv, hP20.rdi]
    refine c.s_jcc hK21 hA21 hin (by omega) hr21 (aesg_470 _) (tgt := 88) rfl (by omega) (fun hc => ?_) (fun _ => ?_)
    · -- the next round: `movzx edx, byte [r9 + rdi]`
      have hne : i + 1 < 256 := by
        rw [hz] at hc
        refine Nat.lt_of_le_of_ne (by omega) fun h => ?_
        rw [h] at hc
        simp at hc
      rintro Y22 t22 hK22 hA22 ⟨hr22, hg22⟩
      have hP22 := hP21.of_eq hg22
      have hl22 : eaI Y22 9 7 0 = Addr.add 0x6d8040 (i + 1) := by simp [eaI, hP22.r9, hP22.rdi, Addr.add]
      refine c.s_movzx8_i hK22 hA22 hin (by omega) hr22 (aesg_88 _) (by rw [hl22]; exact agS hne) ?_
      rintro Y23 t23 hK23 hA23 ⟨hr23, hg23⟩
      refine more hne _ Y23 t23 hK23 hA23 hr23 ?_ hS19
      have h1 : 256 + 4 * (i + 1) = 256 + 4 * i + 4 := by omega
      have h2 : 4352 + 4 * (i + 1) = 4352 + 4 * i + 0 + 4 := by omega
      rw [h1, h2]
      exact (G2.scr (by decide) _ _ hP22).of_eq hg23
    · -- the last round
      rintro Y22 t22 hK22 hA22 ⟨hr22, hg22⟩
      exact next _ Y22 t22 hK22 hA22 hr22 (hP21.of_eq hg22).base hS19
  intro n
  induction n with
  | zero =>
    intro i hi V X t hK hA hr hP hS
    exact body i (by omega) V X t hK hA hr hP hS (fun h => absurd h (by omega))
  | succ n ih =>
    intro i hi V X t hK hA hr hP hS
    exact body i (by omega) V X t hK hA hr hP hS (fun _ => ih (i + 1) (by omega))


/-! ## The choice, the stores, the return -/

/-- From `mov rax, &g_AesCbc_Decode` (offset 508), with the three pointers in `rdi`, `rsi`, `rcx` and the flags in
`edx`. -/
theorem agFin (c : Call prof 136 agW agR agPre (agPost prof) 0x41e540 L s₀ ra o) (hin : CodeIn L 0x41e540 aesg)
    {p : Addr} (hE : AgEnv s₀ p) :
    ∀ (V : Addr → Byte) Y t, KeptW (ws 136 agW s₀) s₀ Y →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) Y.proc.mm.mem V → Y.cpu.rip = (0x41e540 : Addr).add 508 →
      Base s₀ p Y.cpu.gpr → Stk s₀ p V →
      agVals prof Y.cpu.gpr.rdi Y.cpu.gpr.rsi Y.cpu.gpr.rcx (Y.cpu.gpr.rdx.setWidth 32) →
      Go prof 136 agW agR agPre (agPost prof) L s₀ ra o Y t := by
  intro V Y1 t1 hK1 hA1 hr1 hb1 hS1 hv
  have hl : aesg.length = 617 := aesg_length
  have hgl : ∀ (a : Addr) (n : Nat), Addr.add 0x7a7e00 n = a → ∀ m, n + m ≤ 28 → ∀ i < m,
      Foot (ws 136 agW s₀) (a.add i) := by
    rintro a n rfl m hm i hi; rw [addr_add_add]; exact agG (by omega)
  have hfit := hE.fit
  have hpn : ∀ d, d < 144 → (p.add d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  -- the four stores
  refine c.s_mov_ri64 hK1 hA1 hin (by omega) hr1 (aesg_508 _) ?_
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have e2 : eaD Y2 0 0 = 0x7a7e10 := by simp [eaD, hg2]
  refine c.s_mov_mr hK2 hA2 hin (by omega) hr2 (Or.inr rfl) (aesg_515 _)
    (by rw [e2]; exact hgl _ 16 (by decide) 8 (by omega)) ?_
  rw [e2]
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_mov_ri64 hK3 hA3 hin (by omega) hr3 (aesg_518 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  have e4 : eaD Y4 0 0 = 0x7a7e00 := by simp [eaD, hg4]
  refine c.s_mov_mr hK4 hA4 hin (by omega) hr4 (Or.inr rfl) (aesg_525 _)
    (by rw [e4]; exact hgl _ 0 (by decide) 8 (by omega)) ?_
  rw [e4]
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
  refine c.s_mov_ri64 hK5 hA5 hin (by omega) hr5 (aesg_528 _) ?_
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  have e6 : eaD Y6 0 0 = 0x7a7e08 := by simp [eaD, hg6]
  refine c.s_mov_mr hK6 hA6 hin (by omega) hr6 (Or.inr rfl) (aesg_535 _)
    (by rw [e6]; exact hgl _ 8 (by decide) 8 (by omega)) ?_
  rw [e6]
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
  refine c.s_mov_ri64 hK7 hA7 hin (by omega) hr7 (aesg_538 _) ?_
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  have e8 : eaD Y8 0 0 = 0x7a7e18 := by simp [eaD, hg8]
  refine c.s_mov_mr hK8 hA8 hin (by omega) hr8 (Or.inl rfl) (aesg_545 _)
    (by rw [e8]; exact hgl _ 24 (by decide) 4 (by omega)) ?_
  rw [e8]
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  have hS9 := (((hS1.stW hE (rv Y2 64 7) (a := 0x7a7e10) (m := 64 / 8) (by decide) (by decide)).stW hE
    (rv Y4 64 6) (a := 0x7a7e00) (m := 64 / 8) (by decide) (by decide)).stW hE
    (rv Y6 64 1) (a := 0x7a7e08) (m := 64 / 8) (by decide) (by decide)).stW hE
    (rv Y8 32 2) (a := 0x7a7e18) (m := 32 / 8) (by decide) (by decide)
  have hsp9 : Y9.cpu.gpr.rsp = p.add 112 := by
    simp [hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hb1.sp]
  -- `pop rbx`, `pop rbp`, `pop r12`, `ret`
  refine c.s_pop hK9 hA9 hin (by omega) hr9 (aesg_547 _)
    (fun i hi => by rw [hsp9, addr_add_add]; exact c.hws _ (agK hE (by omega))) ?_
  rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
  have hsp10 : Y10.cpu.gpr.rsp = p.add 120 := by rw [hg10]; simp [hsp9]; exact add_add8 p 112
  refine c.s_pop hK10 hA10 hin (by omega) hr10 (aesg_548 _)
    (fun i hi => by rw [hsp10, addr_add_add]; exact c.hws _ (agK hE (by omega))) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
  have hsp11 : Y11.cpu.gpr.rsp = p.add 128 := by rw [hg11]; simp [hsp10]; exact add_add8 p 120
  refine c.s_pop hK11 hA11 hin (by omega) hr11 (aesg_549 _)
    (fun i hi => by rw [hsp11, addr_add_add]; exact c.hws _ (agK hE (by omega))) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
  have hsp12 : Y12.cpu.gpr.rsp = p.add 136 := by rw [hg12]; simp [hsp11]; exact add_add8 p 128
  refine c.ret hK12 (callee_of ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ (hsp12.trans hE.sp.symm)) hin (by omega) hr12 (aesg_551 _)
    fun M hM => ?_
  · rw [hg12, hg11, hg10, hsp9]; simpa using hS9.1
  · rw [hg12, hg11, hsp10]; simpa using hS9.2.1
  · rw [hg12, hsp11]; simpa using hS9.2.2
  · simp [hg12, hg11, hg10, hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hb1.r13]
  · simp [hg12, hg11, hg10, hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hb1.r14]
  · simp [hg12, hg11, hg10, hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hb1.r15]
  · have hAM := c.agreeK hK12 hA12 hM
    refine agPost_of ?_ ?_ ?_ ?_ hv
    · show ofBytesLE 64 (readBytes M 0x7a7e10 8) = _
      rw [hAM.read (fun i hi => c.hws _ (hgl _ 16 (by decide) 8 (by omega) i hi)),
        rd_apart (a := 0x7a7e18) (m := 32 / 8) (b := 0x7a7e10) (n := 8) _ (by decide) (by decide) (by decide),
        rd_apart (a := 0x7a7e08) (m := 64 / 8) (b := 0x7a7e10) (n := 8) _ (by decide) (by decide) (by decide),
        rd_apart (a := 0x7a7e00) (m := 64 / 8) (b := 0x7a7e10) (n := 8) _ (by decide) (by decide) (by decide)]
      refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
      simp [rv, hg2]
    · show ofBytesLE 64 (readBytes M 0x7a7e00 8) = _
      rw [hAM.read (fun i hi => c.hws _ (hgl _ 0 (by decide) 8 (by omega) i hi)),
        rd_apart (a := 0x7a7e18) (m := 32 / 8) (b := 0x7a7e00) (n := 8) _ (by decide) (by decide) (by decide),
        rd_apart (a := 0x7a7e08) (m := 64 / 8) (b := 0x7a7e00) (n := 8) _ (by decide) (by decide) (by decide)]
      refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
      simp [rv, hg4, hg3, hg2]
    · show ofBytesLE 64 (readBytes M 0x7a7e08 8) = _
      rw [hAM.read (fun i hi => c.hws _ (hgl _ 8 (by decide) 8 (by omega) i hi)),
        rd_apart (a := 0x7a7e18) (m := 32 / 8) (b := 0x7a7e08) (n := 8) _ (by decide) (by decide) (by decide)]
      refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
      simp [rv, hg6, hg5, hg4, hg3, hg2]
    · show ofBytesLE 32 (readBytes M 0x7a7e18 4) = _
      rw [hAM.read (fun i hi => c.hws _ (hgl _ 24 (by decide) 4 (by omega) i hi))]
      refine (read_Vst_self (by rfl) _ (by decide)).trans ?_
      simp [rv, hg8, hg7, hg6, hg5, hg4, hg3, hg2]


/-- From `call CPU_IsSupported_AES` (offset 476). -/
theorem agTail (hpc : prof.Consistent) (c : Call prof 136 agW agR agPre (agPost prof) 0x41e540 L s₀ ra o)
    (hin : CodeIn L 0x41e540 aesg) (hinA : CodeIn L 0x4242f0 aes) (hinV : CodeIn L 0x4245a0 vaes)
    (hinX : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid)
    {p : Addr} (hE : AgEnv s₀ p) :
    ∀ (V : Addr → Byte) Y t, KeptW (ws 136 agW s₀) s₀ Y →
      Agree (fp 136 agW agR agPre (agPost prof) L s₀) Y.proc.mm.mem V → Y.cpu.rip = (0x41e540 : Addr).add 476 →
      Base s₀ p Y.cpu.gpr → Stk s₀ p V → Go prof 136 agW agR agPre (agPost prof) L s₀ ra o Y t := by
  intro V Y1 t1 hK1 hA1 hr1 hb1 hS1
  have hl : aesg.length = 617 := aesg_length
  have hfit := hE.fit
  have hpn : ∀ d, d < 144 → (p.add d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  have hs0 : s₀.cpu.gpr.rsp.toNat = p.toNat + 136 := by rw [hE.sp]; exact hpn 136 (by omega)
  -- the canary
  have hcr : (⟨Addr.add s₀.cpu.seg.fsBase 40, 8⟩ : Rgn) ∈ (fp 136 agW agR agPre (agPost prof) L s₀).data := by
    simp [Footprint.data, Contract.footprint, fn, agR]
  have hcf : (Addr.add s₀.cpu.seg.fsBase 40).toNat + 8 ≤ 2 ^ 64 :=
    c.call.foot.fits _ (List.mem_append_left _ hcr)
  have hcn : ∀ i < 8, Foot (fp 136 agW agR agPre (agPost prof) L s₀).data
      (Addr.add (Addr.add s₀.cpu.seg.fsBase 40) i) := fun i hi => ⟨_, hcr, mem_add_of_fits hi hcf⟩
  have hca0 := c.call.pre.1
  rw [hs0] at hca0
  -- `call CPU_IsSupported_AES`
  refine c.s_call hK1 hA1 hin (by omega) hr1 (aesg_476 _) hinA (by rw [aes_length]; omega) (by decide)
    (fun i hi => by rw [hb1.sp, add_sub8 p (m := 104) rfl, addr_add_add]; exact agK hE (by omega)) ?_
  rw [hb1.sp, add_sub8 p (m := 104) rfl]
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  have hsp2 : Y2.cpu.gpr.rsp = p.add 104 := by rw [hg2, set_4]
  have hS2 := hS1.st (by omega) (a := p.add 104) (m := 8) (Addr.add 0x41e540 (476 + 5))
    (by rw [hpn 104 (by omega)]; omega) (by rw [hpn 104 (by omega)]; omega)
  refine sub_bit c aes_shape hK2 hA2 hinA hinC hr2 (fun i hi => by
      rw [hsp2, add_sub_lit p (n := 104) (d := 56) (by omega), addr_add_add]; exact agK hE (by omega))
    (fun i hi => by rw [hsp2, addr_add_add]; exact c.hws _ (agK hE (by omega)))
    hcn (by rw [hsp2, hpn 104 (by omega)]; omega) (by rw [hsp2, hpn 104 (by omega)]; omega) hcf
    (by rw [hsp2, hpn 104 (by omega)]; omega) hin (j₂ := 481) (by omega)
    (by rw [hsp2]; exact read_Vst_self (by rfl) _ (by rw [hpn 104 (by omega)]; omega)) ?_
  intro V3 hV3 Y3 t3 hK3 hA3 ⟨hr3, hsp3, hsv3, hax3⟩
  rw [hsp2, add_sub_lit p (n := 104) (d := 56) (by omega)] at hV3
  have hS3 := hS2.keep (by omega) hV3 (by rw [hpn 48 (by omega)]; omega)
  rw [hsp2, add_add8] at hsp3
  have hb3 : Base s₀ p Y3.cpu.gpr := by
    refine ⟨hsp3, ?_, ?_, ?_⟩
    · rw [hsv3.2.2.2.1, hg2]; exact hb1.r13
    · rw [hsv3.2.2.2.2.1, hg2]; exact hb1.r14
    · rw [hsv3.2.2.2.2.2, hg2]; exact hb1.r15
  -- `test eax, eax`, `jne`
  refine c.s_test_rr32 hK3 hA3 hin (by omega) hr3 (aesg_481 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4, hz4⟩
  refine c.s_jcc hK4 hA4 hin (by omega) hr4 (aesg_483 _) (tgt := 552) rfl (by omega) (fun hc => ?_) fun hc => ?_
  · -- AES: `call CPU_IsSupported_VAES_AVX2`
    have haes : prof.feat.aes = true := hpc.aes (hax3 fun h0 => by
      simp only [Rflags.cond, hz4, Bool.not_eq_true'] at hc
      simp [rv, h0] at hc)
    rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
    have hsp5 : Y5.cpu.gpr.rsp = p.add 112 := by rw [hg5, hg4, hsp3]
    refine c.s_call hK5 hA5 hin (by omega) hr5 (aesg_552 _) hinV (by rw [vaes_length]; omega) (by decide)
      (fun i hi => by rw [hsp5, add_sub8 p (m := 104) rfl, addr_add_add]; exact agK hE (by omega)) ?_
    rw [hsp5, add_sub8 p (m := 104) rfl]
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    have hsp6 : Y6.cpu.gpr.rsp = p.add 104 := by rw [hg6, set_4]
    have hS6 := hS3.st (by omega) (a := p.add 104) (m := 8) (Addr.add 0x41e540 (552 + 5))
      (by rw [hpn 104 (by omega)]; omega) (by rw [hpn 104 (by omega)]; omega)
    refine sub_vaes c hpc hK6 hA6 hinV hinX hinM hinC hr6 (fun i hi => by
        rw [hsp6, add_sub_lit p (n := 104) (d := 104) (by omega), addr_add_add]; exact agK hE (by omega))
      (fun i hi => by rw [hsp6, addr_add_add]; exact c.hws _ (agK hE (by omega)))
      hcn (by rw [hsp6, hpn 104 (by omega)]; omega) (by rw [hsp6, hpn 104 (by omega)]; omega) hcf
      (by rw [hsp6, hpn 104 (by omega)]; omega) hin (j₂ := 557) (by omega)
      (by rw [hsp6]; exact read_Vst_self (by rfl) _ (by rw [hpn 104 (by omega)]; omega)) ?_
    intro V7 hV7 Y7 t7 hK7 hA7 ⟨hr7, hsp7, hsv7, hax7⟩
    rw [hsp6, add_sub_lit p (n := 104) (d := 104) (by omega)] at hV7
    have hS7 := hS6.keep (q := p.add 0) (by omega) hV7 (by rw [hpn 0 (by omega)]; omega)
    rw [hsp6, add_add8] at hsp7
    have hb7 : Base s₀ p Y7.cpu.gpr := by
      refine ⟨hsp7, ?_, ?_, ?_⟩
      · rw [hsv7.2.2.2.1, hg6, hg5, hg4]; exact hb3.r13
      · rw [hsv7.2.2.2.2.1, hg6, hg5, hg4]; exact hb3.r14
      · rw [hsv7.2.2.2.2.2, hg6, hg5, hg4]; exact hb3.r15
    -- `test eax, eax`, `je`
    refine c.s_test_rr32 hK7 hA7 hin (by omega) hr7 (aesg_557 _) ?_
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8, hz8⟩
    refine c.s_jcc hK8 hA8 hin (by omega) hr8 (aesg_559 _) (tgt := 589) rfl (by omega) (fun _ => ?_) fun hc8 => ?_
    · -- AES only
      rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
      refine c.s_mov_ri64 hK9 hA9 hin (by omega) hr9 (aesg_589 _) ?_
      rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
      refine c.s_mov_ri64 hK10 hA10 hin (by omega) hr10 (aesg_596 _) ?_
      rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
      refine c.s_mov_ri32 hK11 hA11 hin (by omega) hr11 (aesg_603 _) ?_
      rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
      refine c.s_mov_ri64 hK12 hA12 hin (by omega) hr12 (aesg_608 _) ?_
      rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
      refine c.s_jmp hK13 hA13 hin (by omega) hr13 (aesg_615 _) (tgt := 508) rfl (by omega) ?_
      rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
      refine agFin c hin hE _ Y14 t14 hK14 hA14 hr14 ?_ hS7 ?_
      · rw [hg14, hg13, hg12, hg11, hg10, hg9, hg8]; exact ⟨hb7.sp, hb7.r13, hb7.r14, hb7.r15⟩
      · refine Or.inr (Or.inl ⟨?_, ?_, ?_, ?_, haes⟩) <;> simp [hg14, hg13, hg12, hg11, hg10]
    · -- VAES
      have hne : Y7.cpu.gpr.rax.setWidth 32 ≠ 0 := fun h0 => by
        simp only [Rflags.cond, hz8] at hc8
        simp [rv, h0] at hc8
      obtain ⟨h5, h9, h28, hen⟩ := hax7 hne
      rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
      refine c.s_mov_ri64 hK9 hA9 hin (by omega) hr9 (aesg_561 _) ?_
      rintro Y10 t10 hK10 hA10 ⟨hr10, hg10⟩
      refine c.s_mov_ri64 hK10 hA10 hin (by omega) hr10 (aesg_568 _) ?_
      rintro Y11 t11 hK11 hA11 ⟨hr11, hg11⟩
      refine c.s_mov_ri32 hK11 hA11 hin (by omega) hr11 (aesg_575 _) ?_
      rintro Y12 t12 hK12 hA12 ⟨hr12, hg12⟩
      refine c.s_mov_ri64 hK12 hA12 hin (by omega) hr12 (aesg_580 _) ?_
      rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
      refine c.s_jmp hK13 hA13 hin (by omega) hr13 (aesg_587 _) (tgt := 508) rfl (by omega) ?_
      rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
      refine agFin c hin hE _ Y14 t14 hK14 hA14 hr14 ?_ hS7 ?_
      · rw [hg14, hg13, hg12, hg11, hg10, hg9, hg8]; exact ⟨hb7.sp, hb7.r13, hb7.r14, hb7.r15⟩
      · refine Or.inr (Or.inr ⟨?_, ?_, ?_, ?_, haes, hpc.vaes h9 hen, hpc.avx2 h5 hen, hpc.avx h28 hen⟩) <;>
          simp [hg14, hg13, hg12, hg11, hg10]
  · -- no AES: the portable code
    rintro Y5 t5 hK5 hA5 ⟨hr5, hg5⟩
    refine c.s_mov_ri64 hK5 hA5 hin (by omega) hr5 (aesg_485 _) ?_
    rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
    refine c.s_mov_ri64 hK6 hA6 hin (by omega) hr6 (aesg_492 _) ?_
    rintro Y7 t7 hK7 hA7 ⟨hr7, hg7⟩
    refine c.s_xor_rr32 hK7 hA7 hin (by omega) hr7 (aesg_499 _) ?_
    rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
    refine c.s_mov_ri64 hK8 hA8 hin (by omega) hr8 (aesg_501 _) ?_
    rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
    refine agFin c hin hE _ Y9 t9 hK9 hA9 hr9 ?_ hS3 ?_
    · rw [hg9, hg8, hg7, hg6, hg5, hg4]; exact ⟨hb3.sp, hb3.r13, hb3.r14, hb3.r15⟩
    · refine Or.inl ⟨?_, ?_, ?_, ?_⟩ <;> simp [rv, hg9, hg8, hg7, hg6]


/-! ## `AesGenTables` -/

theorem agRun (hpc : prof.Consistent) (c : Call prof 136 agW agR agPre (agPost prof) 0x41e540 L s₀ ra o)
    (hin : CodeIn L 0x41e540 aesg) (hinA : CodeIn L 0x4242f0 aes) (hinV : CodeIn L 0x4245a0 vaes)
    (hinX : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) (t : Nat) :
    Go prof 136 agW agR agPre (agPost prof) L s₀ ra o s₀ t := by
  have hl : aesg.length = 617 := aesg_length
  have hK0 : KeptW (ws 136 agW s₀) s₀ s₀ := KeptW.refl _ _
  have hA0 : Agree (fp 136 agW agR agPre (agPost prof) L s₀) s₀.proc.mm.mem
      (fun a => s₀.proc.mm.mem.readByte a) := fun _ _ => rfl
  obtain ⟨hpt0, hsf0⟩ := Call.frame_arith c.frame_fits
  have hap := c.call.pre.2
  generalize hpd : s₀.cpu.gpr.rsp - BitVec.ofNat 64 136 = p at hpt0
  have hsp : s₀.cpu.gpr.rsp = Addr.add p 136 := by rw [← hpd]; exact sub_add_self _ _
  have hfit : p.toNat + 144 ≤ 2 ^ 64 := by omega
  have hE : AgEnv s₀ p := ⟨hpd, hsp, hfit, by omega⟩
  have hpn : ∀ d, d < 144 → (Addr.add p d).toNat = p.toNat + d := fun d hd => toNat_addn hd hfit
  -- `endbr64`, `push r12`, `xor eax, eax`, `mov edx, 99`, `lea r8, InvS`, `push rbp`, `lea rcx, Sbox`, `push rbx`
  refine c.s_endbr hK0 hA0 hin (by omega) (by rw [addr_add_zero]; exact c.call.shape.1) (aesg_0 _) ?_
  rintro Y1 t1 hK1 hA1 ⟨hr1, hg1⟩
  have hsp1 : Y1.cpu.gpr.rsp = Addr.add p 136 := by rw [hg1, hsp]
  refine c.s_push hK1 hA1 hin (by omega) hr1 (aesg_4 _)
    (fun i hi => by rw [hsp1, add_sub8 p (m := 128) rfl, addr_add_add]; exact agK hE (by omega)) ?_
  rw [hsp1, add_sub8 p (m := 128) rfl]
  rintro Y2 t2 hK2 hA2 ⟨hr2, hg2⟩
  refine c.s_xor_rr32 hK2 hA2 hin (by omega) hr2 (aesg_6 _) ?_
  rintro Y3 t3 hK3 hA3 ⟨hr3, hg3⟩
  refine c.s_mov_ri32 hK3 hA3 hin (by omega) hr3 (aesg_8 _) ?_
  rintro Y4 t4 hK4 hA4 ⟨hr4, hg4⟩
  refine c.s_lea_rip hK4 hA4 hin (by omega) hr4 (aesg_13 _) (v := 0x794680) (by decide) ?_
  rintro Y5 t5 hK5 hA5 ⟨hr5, hg5, -⟩
  have hsp5 : Y5.cpu.gpr.rsp = Addr.add p 128 := by simp [hg5, hg4, hg3, hg2]
  refine c.s_push hK5 hA5 hin (by omega) hr5 (aesg_20 _)
    (fun i hi => by rw [hsp5, add_sub8 p (m := 120) rfl, addr_add_add]; exact agK hE (by omega)) ?_
  rw [hsp5, add_sub8 p (m := 120) rfl]
  rintro Y6 t6 hK6 hA6 ⟨hr6, hg6⟩
  refine c.s_lea_rip hK6 hA6 hin (by omega) hr6 (aesg_21 _) (v := 0x6d8040) (by decide) ?_
  rintro Y7 t7 hK7 hA7 ⟨hr7, hg7, -⟩
  have hsp7 : Y7.cpu.gpr.rsp = Addr.add p 120 := by simp [hg7, hg6]
  refine c.s_push hK7 hA7 hin (by omega) hr7 (aesg_28 _)
    (fun i hi => by rw [hsp7, add_sub8 p (m := 112) rfl, addr_add_add]; exact agK hE (by omega)) ?_
  rw [hsp7, add_sub8 p (m := 112) rfl]
  rintro Y8 t8 hK8 hA8 ⟨hr8, hg8⟩
  refine c.s_jmp hK8 hA8 hin (by omega) hr8 (aesg_29 _) (tgt := 36) rfl (by omega) ?_
  rintro Y9 t9 hK9 hA9 ⟨hr9, hg9⟩
  have hS9 : Stk s₀ p (Vst (Vst (Vst (fun a => s₀.proc.mm.mem.readByte a) (Addr.add p 128)
      (toBytesLE (Y1.cpu.gpr.get (regOf 12)) 8)) (Addr.add p 120) (toBytesLE (Y5.cpu.gpr.get (regOf 5)) 8))
      (Addr.add p 112) (toBytesLE (Y7.cpu.gpr.get (regOf 3)) 8)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [read_Vst_self (by rfl) _ (by rw [hpn 112 (by omega)]; omega)]
      simp [hg7, hg6, hg5, hg4, hg3, hg2, hg1]
    · rw [rd_apart (a := Addr.add p 112) (m := 8) (b := Addr.add p 120) (n := 8) _ (by rw [hpn 112 (by omega)]; omega)
        (by rw [hpn 120 (by omega)]; omega) (by rw [hpn 112 (by omega), hpn 120 (by omega)]; omega),
        read_Vst_self (by rfl) _ (by rw [hpn 120 (by omega)]; omega)]
      simp [hg5, hg4, hg3, hg2, hg1]
    · rw [rd_apart (a := Addr.add p 112) (m := 8) (b := Addr.add p 128) (n := 8) _ (by rw [hpn 112 (by omega)]; omega)
        (by rw [hpn 128 (by omega)]; omega) (by rw [hpn 112 (by omega), hpn 128 (by omega)]; omega),
        rd_apart (a := Addr.add p 120) (m := 8) (b := Addr.add p 128) (n := 8) _ (by rw [hpn 120 (by omega)]; omega)
        (by rw [hpn 128 (by omega)]; omega) (by rw [hpn 120 (by omega), hpn 128 (by omega)]; omega),
        read_Vst_self (by rfl) _ (by rw [hpn 128 (by omega)]; omega)]
      simp [hg1]
  -- the first loop, from round 0 with `edx = 99`
  refine agLoop1 c hin hE ?_ 255 0 rfl _ Y9 t9 99 hK9 hA9 hr9 ?_ (by simp [hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2])
    (by omega) (by simp [hg9, hg8, hg7, hg6, hg5, hg4, hg3]) (by simp [hg9, hg8, hg7])
    (by simp [hg9, hg8, hg7, hg6, hg5]) hS9
  rotate_left
  · refine ⟨by simp [hg9, hg8], ?_, ?_, ?_⟩ <;>
      simp [hg9, hg8, hg7, hg6, hg5, hg4, hg3, hg2, hg1]
  -- between the loops: `lea rsi`, `lea rcx`, `xor edi, edi`, `mov edx, 99`, `lea r9, Sbox`, `jmp`
  intro V10 Y10 t10 hK10 hA10 hr10 hb10 hr810 hS10
  refine c.s_lea_rip hK10 hA10 hin (by omega) hr10 (aesg_52 _) (v := 0x794780) (by decide) ?_
  rintro Y11 t11 hK11 hA11 ⟨hr11, hg11, -⟩
  refine c.s_lea_rip hK11 hA11 hin (by omega) hr11 (aesg_59 _) (v := 0x795780) (by decide) ?_
  rintro Y12 t12 hK12 hA12 ⟨hr12, hg12, -⟩
  refine c.s_xor_rr32 hK12 hA12 hin (by omega) hr12 (aesg_66 _) ?_
  rintro Y13 t13 hK13 hA13 ⟨hr13, hg13⟩
  refine c.s_mov_ri32 hK13 hA13 hin (by omega) hr13 (aesg_68 _) ?_
  rintro Y14 t14 hK14 hA14 ⟨hr14, hg14⟩
  refine c.s_lea_rip hK14 hA14 hin (by omega) hr14 (aesg_73 _) (v := 0x6d8040) (by decide) ?_
  rintro Y15 t15 hK15 hA15 ⟨hr15, hg15, -⟩
  refine c.s_jmp hK15 hA15 hin (by omega) hr15 (aesg_80 _) (tgt := 93) rfl (by omega) ?_
  rintro Y16 t16 hK16 hA16 ⟨hr16, hg16⟩
  -- the second loop, from round 0
  refine agLoop2 c hin hE (agTail hpc c hin hinA hinV hinX hinM hinC hE) 255 0 rfl _ Y16 t16 hK16 hA16 hr16
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ hS10
  · simp [hg16, hg15, hg14, hg13]
  · simp [hg16, hg15, hg14, hg13, hg12, hg11]; decide
  · simp [hg16, hg15, hg14, hg13, hg12]; decide
  · simp [hg16, hg15, hg14, hg13, hg12, hg11, hr810]
  · simp [hg16, hg15]
  · exact ⟨by simp [hg16, hg15, hg14, hg13, hg12, hg11, hb10.sp], by simp [hg16, hg15, hg14, hg13, hg12, hg11, hb10.r13],
      by simp [hg16, hg15, hg14, hg13, hg12, hg11, hb10.r14], by simp [hg16, hg15, hg14, hg13, hg12, hg11, hb10.r15]⟩

/-- `AesGenTables`, at `0x41e540`, with its callees' code: on a consistent profile, every call returns, with the AES
pointers and flags the portable ones, or the AES-NI ones on a processor with AES, or the VAES ones on one with AES,
VAES, AVX2 and AVX. -/
theorem aesGenTables (prof : Profile) (hpc : prof.Consistent) {L : List (Addr × List Byte)}
    (hin : CodeIn L 0x41e540 aesg) (hinA : CodeIn L 0x4242f0 aes) (hinV : CodeIn L 0x4245a0 vaes)
    (hinX : CodeIn L 0x424440 avx) (hinM : CodeIn L 0x4242b0 maxf) (hinC : CodeIn L 0x424290 cpuid) :
    ImplementsCall prof 0x41e540 L (agC prof) := by
  intro s₀ ra hcall
  have hfr := Call.frame_arith (k := 136) (s := s₀)
    (hcall.foot.fits (frame s₀ 136) (by simp [Footprint.data, Contract.footprint, fn]))
  have hslot : ∀ i < 8, ¬ Foot (agW s₀) (Addr.add s₀.cpu.gpr.rsp i) := by
    rintro i hi ⟨r, hr, hm⟩
    have hg := hcall.pre.2
    have e1 : (0x794680 : Addr).toNat = 0x794680 := rfl
    have e2 : (0x7a7e00 : Addr).toNat = 0x7a7e00 := rfl
    simp only [agW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      simp only [Rgn.Mem, toNat_add_of_fits hi hfr.2, e1, e2] at hm <;> omega
  exact reachOrEndsIn_of_runsFrom fun o ho t =>
    agRun hpc (Call.of hcall ho hslot) hin hinA hinV hinX hinM hinC t

end FV7z.Prepare
