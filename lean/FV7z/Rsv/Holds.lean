import FV7z.Rsv.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
/-!
# `CDirItems::ReserveDown` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `CDirItems::ReserveDown ()` (`CPP/7zip/UI/Common/EnumDirItems.cpp`; `objdump -d`) at `0x5c03e0` in
`7zzs`: `this` = `rdi` (`rbx`). `CRecordVector::ReserveDown` (`CPP/Common/MyVector.h`) in line for four vectors,
each `_items` (8 bytes), `_size` at `+ 8` and `_capacity` at `+ 0xc` (4 bytes): `Prefixes` at `this` (8-byte
items), `PhyParents` at `+ 0x10` (4-byte), `LogParents` at `+ 0x20` (4-byte), `Items` at `+ 0x30` (8-byte). `S` the
stack pointer and `g0` the registers at the entry: three pushes (`r12`, `rbp`, `rbx`, `aR S`), no frame. For each
vector, from its cut point (0 after the pushes, 45, 77, 113): `_size` = `_capacity` to the next one (45, 77, 113, the
epilogue 149); else a `_size` not 0 to `operator new []` (`0x6029b0`; calls at 220, 164, 332, 276), from its return
(225, 169, 337, 281) the old `_items` in `r12`, `memcpy` (`0x401070`; 244, 189, 357, 301), from its return (249,
194, 362, 306) `delete []` of the old array (`0x6014f0`; 252, 197, 365, 309), from its return (257, 202, 370, 314)
`edi` = `_size` again; a `_size` of 0 with `_items` not null to `delete []` the same way (the stubs at 400, 416, 432,
384 jump to 249, 194, 362, 306), with `_items` null on; then (39, 70, 106, 142) `_items` = `rbp` (the new array or
0) and `_capacity` = `_size` stored. At 149 the pops, the `ret` (153).

The callees are continuations (`KC`, as in `FV7z/Api/Holds.lean`), for any return offset; what the code stores and
what the callees store are tracked by an invariant `I` the caller chooses: it holds after the pushes (`hI0`), every
callee returns with it, it gives the saved registers and the return address (`Stk`), and it is kept by a store of
`n` bytes at `a` when `Ok a n` (`hcl`); `Ok` gives the store's footprint (`hok`) and holds for each vector's
`_items` and `_capacity` (`o0`, `o12`, `o16`, `o28`, `o32`, `o44`, `o48`, `o60`); the `_size`s are read only (`f8`,
`f24`, `f40`, `f56`).

- `Fm`, `Fr`, `KS`, `Stk`, `KC`, `Ev`: the frame, what a piece keeps, the callee-saved registers, the stack, the
  callees, the hypotheses of the runs; `callK`: a `call` and the callee's return.
- `vc_*`: the pieces; `tail149` and `from*`: the runs from the cut points.
- `rsv_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Rsv
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` at 164: `operator new []`. -/
def pc164 : List Byte := [0xe8, 0x27, 0x25, 0x04, 0x00]
theorem pc164_0 : ∀ feat, Dec feat pc164 0 (FV7z.mk .call 64 [.rel 271655] 5) := by dec_rfl
theorem wc_164 : pc164 <+: rsv.drop 164 := by decide +kernel
theorem call_164 (feat : Features) : Dec feat rsv 164 (FV7z.mk .call 64 [.rel 271655] 5) :=
  Dec.shift (j := 164) (k := 0) (pc164_0 feat) wc_164 (Nat.zero_le _)
theorem tgt_164 : rsv_at.add (164 + 5) + BitVec.ofNat 64 271655 = 0x6029b0#64 := by decide

/-- The `call` at 189: `memcpy`. -/
def pc189 : List Byte := [0xe8, 0xce, 0x0b, 0xe4, 0xff]
theorem pc189_0 : ∀ feat, Dec feat pc189 0 (FV7z.mk .call 64 [.rel 18446744073707719630] 5) := by dec_rfl
theorem wc_189 : pc189 <+: rsv.drop 189 := by decide +kernel
theorem call_189 (feat : Features) : Dec feat rsv 189 (FV7z.mk .call 64 [.rel 18446744073707719630] 5) :=
  Dec.shift (j := 189) (k := 0) (pc189_0 feat) wc_189 (Nat.zero_le _)
theorem tgt_189 : rsv_at.add (189 + 5) + BitVec.ofNat 64 18446744073707719630 = 0x401070#64 := by decide

/-- The `call` at 197: `operator delete []`. -/
def pc197 : List Byte := [0xe8, 0x46, 0x10, 0x04, 0x00]
theorem pc197_0 : ∀ feat, Dec feat pc197 0 (FV7z.mk .call 64 [.rel 266310] 5) := by dec_rfl
theorem wc_197 : pc197 <+: rsv.drop 197 := by decide +kernel
theorem call_197 (feat : Features) : Dec feat rsv 197 (FV7z.mk .call 64 [.rel 266310] 5) :=
  Dec.shift (j := 197) (k := 0) (pc197_0 feat) wc_197 (Nat.zero_le _)
theorem tgt_197 : rsv_at.add (197 + 5) + BitVec.ofNat 64 266310 = 0x6014f0#64 := by decide

/-- The `call` at 220: `operator new []`. -/
def pc220 : List Byte := [0xe8, 0xef, 0x24, 0x04, 0x00]
theorem pc220_0 : ∀ feat, Dec feat pc220 0 (FV7z.mk .call 64 [.rel 271599] 5) := by dec_rfl
theorem wc_220 : pc220 <+: rsv.drop 220 := by decide +kernel
theorem call_220 (feat : Features) : Dec feat rsv 220 (FV7z.mk .call 64 [.rel 271599] 5) :=
  Dec.shift (j := 220) (k := 0) (pc220_0 feat) wc_220 (Nat.zero_le _)
theorem tgt_220 : rsv_at.add (220 + 5) + BitVec.ofNat 64 271599 = 0x6029b0#64 := by decide

/-- The `call` at 244: `memcpy`. -/
def pc244 : List Byte := [0xe8, 0x97, 0x0b, 0xe4, 0xff]
theorem pc244_0 : ∀ feat, Dec feat pc244 0 (FV7z.mk .call 64 [.rel 18446744073707719575] 5) := by dec_rfl
theorem wc_244 : pc244 <+: rsv.drop 244 := by decide +kernel
theorem call_244 (feat : Features) : Dec feat rsv 244 (FV7z.mk .call 64 [.rel 18446744073707719575] 5) :=
  Dec.shift (j := 244) (k := 0) (pc244_0 feat) wc_244 (Nat.zero_le _)
theorem tgt_244 : rsv_at.add (244 + 5) + BitVec.ofNat 64 18446744073707719575 = 0x401070#64 := by decide

/-- The `call` at 252: `operator delete []`. -/
def pc252 : List Byte := [0xe8, 0x0f, 0x10, 0x04, 0x00]
theorem pc252_0 : ∀ feat, Dec feat pc252 0 (FV7z.mk .call 64 [.rel 266255] 5) := by dec_rfl
theorem wc_252 : pc252 <+: rsv.drop 252 := by decide +kernel
theorem call_252 (feat : Features) : Dec feat rsv 252 (FV7z.mk .call 64 [.rel 266255] 5) :=
  Dec.shift (j := 252) (k := 0) (pc252_0 feat) wc_252 (Nat.zero_le _)
theorem tgt_252 : rsv_at.add (252 + 5) + BitVec.ofNat 64 266255 = 0x6014f0#64 := by decide

/-- The `call` at 276: `operator new []`. -/
def pc276 : List Byte := [0xe8, 0xb7, 0x24, 0x04, 0x00]
theorem pc276_0 : ∀ feat, Dec feat pc276 0 (FV7z.mk .call 64 [.rel 271543] 5) := by dec_rfl
theorem wc_276 : pc276 <+: rsv.drop 276 := by decide +kernel
theorem call_276 (feat : Features) : Dec feat rsv 276 (FV7z.mk .call 64 [.rel 271543] 5) :=
  Dec.shift (j := 276) (k := 0) (pc276_0 feat) wc_276 (Nat.zero_le _)
theorem tgt_276 : rsv_at.add (276 + 5) + BitVec.ofNat 64 271543 = 0x6029b0#64 := by decide

/-- The `call` at 301: `memcpy`. -/
def pc301 : List Byte := [0xe8, 0x5e, 0x0b, 0xe4, 0xff]
theorem pc301_0 : ∀ feat, Dec feat pc301 0 (FV7z.mk .call 64 [.rel 18446744073707719518] 5) := by dec_rfl
theorem wc_301 : pc301 <+: rsv.drop 301 := by decide +kernel
theorem call_301 (feat : Features) : Dec feat rsv 301 (FV7z.mk .call 64 [.rel 18446744073707719518] 5) :=
  Dec.shift (j := 301) (k := 0) (pc301_0 feat) wc_301 (Nat.zero_le _)
theorem tgt_301 : rsv_at.add (301 + 5) + BitVec.ofNat 64 18446744073707719518 = 0x401070#64 := by decide

/-- The `call` at 309: `operator delete []`. -/
def pc309 : List Byte := [0xe8, 0xd6, 0x0f, 0x04, 0x00]
theorem pc309_0 : ∀ feat, Dec feat pc309 0 (FV7z.mk .call 64 [.rel 266198] 5) := by dec_rfl
theorem wc_309 : pc309 <+: rsv.drop 309 := by decide +kernel
theorem call_309 (feat : Features) : Dec feat rsv 309 (FV7z.mk .call 64 [.rel 266198] 5) :=
  Dec.shift (j := 309) (k := 0) (pc309_0 feat) wc_309 (Nat.zero_le _)
theorem tgt_309 : rsv_at.add (309 + 5) + BitVec.ofNat 64 266198 = 0x6014f0#64 := by decide

/-- The `call` at 332: `operator new []`. -/
def pc332 : List Byte := [0xe8, 0x7f, 0x24, 0x04, 0x00]
theorem pc332_0 : ∀ feat, Dec feat pc332 0 (FV7z.mk .call 64 [.rel 271487] 5) := by dec_rfl
theorem wc_332 : pc332 <+: rsv.drop 332 := by decide +kernel
theorem call_332 (feat : Features) : Dec feat rsv 332 (FV7z.mk .call 64 [.rel 271487] 5) :=
  Dec.shift (j := 332) (k := 0) (pc332_0 feat) wc_332 (Nat.zero_le _)
theorem tgt_332 : rsv_at.add (332 + 5) + BitVec.ofNat 64 271487 = 0x6029b0#64 := by decide

/-- The `call` at 357: `memcpy`. -/
def pc357 : List Byte := [0xe8, 0x26, 0x0b, 0xe4, 0xff]
theorem pc357_0 : ∀ feat, Dec feat pc357 0 (FV7z.mk .call 64 [.rel 18446744073707719462] 5) := by dec_rfl
theorem wc_357 : pc357 <+: rsv.drop 357 := by decide +kernel
theorem call_357 (feat : Features) : Dec feat rsv 357 (FV7z.mk .call 64 [.rel 18446744073707719462] 5) :=
  Dec.shift (j := 357) (k := 0) (pc357_0 feat) wc_357 (Nat.zero_le _)
theorem tgt_357 : rsv_at.add (357 + 5) + BitVec.ofNat 64 18446744073707719462 = 0x401070#64 := by decide

/-- The `call` at 365: `operator delete []`. -/
def pc365 : List Byte := [0xe8, 0x9e, 0x0f, 0x04, 0x00]
theorem pc365_0 : ∀ feat, Dec feat pc365 0 (FV7z.mk .call 64 [.rel 266142] 5) := by dec_rfl
theorem wc_365 : pc365 <+: rsv.drop 365 := by decide +kernel
theorem call_365 (feat : Features) : Dec feat rsv 365 (FV7z.mk .call 64 [.rel 266142] 5) :=
  Dec.shift (j := 365) (k := 0) (pc365_0 feat) wc_365 (Nat.zero_le _)
theorem tgt_365 : rsv_at.add (365 + 5) + BitVec.ofNat 64 266142 = 0x6014f0#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_153 : pret <+: rsv.drop 153 := by decide +kernel
theorem ret_153 (feat : Features) : Dec feat rsv 153 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 153) (k := 0) (pret_0 feat) wt_153 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the three pushes. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8

/-- The bytes after the three pushes (`r12`, `rbp`, `rbx`). -/
abbrev P3 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

theorem q1 (S : Addr) : aR S + 8 = S - 8 - 8 := by
  show S - 8 - 8 - 8 + 8 = _; bv_omega
theorem q2 (S : Addr) : aR S + 8 + 8 = S - 8 := by
  show S - 8 - 8 - 8 + 8 + 8 = _; bv_omega
theorem q3 (S : Addr) : aR S + 8 + 8 + 8 = S := by
  show S - 8 - 8 - 8 + 8 + 8 + 8 = _; bv_omega

/-- The frame from the prologue on: `rsp` = `aR S`, `rbx` = `this`, `r13`, `r14`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdi ∧ g.r13 = g0.r13 ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `r13`, `r14`, `r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- The callee-saved registers as in `g`. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.trans h.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.2.2.1.trans h.2.2.1, hk.2.2.2.2.1.trans h.2.2.2.1, hk.2.2.2.2.2.trans h.2.2.2.2⟩

/-- The stack (`ra` the return address): the three saved registers and the return address. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8) = g0.rbp ∧ rdq(W, S - 8) = g0.r12 ∧ rdq(W, S) = ra

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`): at its entry, and from its return at `j` with
`rsp` = `aR S`, the callee-saved registers as at its entry and the invariant `I`, the run goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (I : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (rsv_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = rsv_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes, `Ok` the stores that keep it). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop)
    (Ok : Addr → Nat → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L rsv_at rsv
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0 (e₂.add j₂)
  hok : ∀ a n, Ok a n → ∀ i < n, Foot Wl (Addr.add a i)
  hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
    I (Vst W a bs)
  o0 : Ok g0.rdi 8
  o12 : Ok (g0.rdi + 12#64) 4
  o16 : Ok (g0.rdi + 16#64) 8
  o28 : Ok (g0.rdi + 28#64) 4
  o32 : Ok (g0.rdi + 32#64) 8
  o44 : Ok (g0.rdi + 44#64) 4
  o48 : Ok (g0.rdi + 48#64) 8
  o60 : Ok (g0.rdi + 60#64) 4
  f8 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 8#64) i)
  f24 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 24#64) i)
  f40 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 40#64) i)
  f56 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 56#64) i)
  fb3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb1 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cN : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length
  cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  kN : ∀ W j, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6029b0#64 j W
  kM : ∀ W j, I W → KC prof F Wl L s₀ o gev gP gE S I 0x401070#64 j W
  kD : ∀ W j, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 j W
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn} {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop}

/-- The pushes, `rbx` = `this`, `Prefixes`' `_size` compared with its `_capacity`: equal to 45; else a `_size` not 0
to `operator new []` (220, `rdi` = 8 times it), else `_items` not null to 249 (`r12` = `_items`, `rbp` = 0), else to
39. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 8#64) i))
    (fc : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 12#64) i)) (fi : ∀ i < 8, Foot F.data (Addr.add g.rdi i))

    (h45 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 45 g' fl (P3 V g))
    (h220 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 220 g' fl (P3 V g))
    (h249 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 249 g' fl (P3 V g))
    (h39 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdi → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 39 g' fl (P3 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P3] at hs1 hs2 hs3 fz fc fi h45 h220 h249 h39 ⊢
  wpx [W_0, W_19, W_27, W_216, W_400, o0, o1, o2, o18, o25, Op.shl64]
  all_goals repeat' (first
    | refine h45 _ ?_ ?_ ?_ ?_ ?_ _
    | refine h220 _ ?_ ?_ ?_ ?_ ?_ _
    | refine h249 _ ?_ ?_ ?_ ?_ ?_ _
    | refine h39 _ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact fz
    | with_reducible exact fc
    | with_reducible exact fi
    | apply And.intro
    | intro _)

/-- `Prefixes`' `_items` = `rbp`, `_capacity` = `_size`: to 45. -/
theorem vc_39 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (wi : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (wc : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 12#64) i))
    (oi : Ok g.rbx 8) (oc : Ok (g.rbx + 12#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 45 g' fl V') :
    W_39 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at wi wc oi oc h ⊢
  wpx [W_39, o3]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible exact wi
    | with_reducible exact wc
    | with_reducible exact oi
    | with_reducible exact oc
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | apply And.intro
    | intro _)

/-- Back from `operator new []`: `r12` = `Prefixes`' old `_items`, `rdi` = `rbp` = the new array, `rsi` = the old
one, `rdx` = the bytes: to `memcpy` (244). -/
theorem vc_225 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fi : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 244 g' fl V) :
    W_225 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fi fz h ⊢
  wpx [W_225, o19, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fi
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- `rdi` = the old array, to `delete []` (252). -/
theorem vc_249 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 252 g' fl V) :
    W_249 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_249, o16]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- Back from `delete []`: `edi` = `Prefixes`' `_size`, to 39. -/
theorem vc_257 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i)) (h : ∀ g', Fr g g' → ∀ fl, Q 39 g' fl V) :
    W_257 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fz h ⊢
  wpx [W_257, o20]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- `PhyParents`' `_size` compared with its `_capacity`: equal to 77; else a `_size` not 0 to `operator new []`
(164), else `_items` not null to 194, else to 70. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 24#64) i))
    (fc : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 28#64) i))
    (fi : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 16#64) i))
    (hn : ∀ g', Fr g g' → ∀ fl, Q 77 g' fl V) (ha : ∀ g', Fr g g' → ∀ fl, Q 164 g' fl V)
    (hd : ∀ g', Fr g g' → ∀ fl, Q 194 g' fl V) (hs : ∀ g', Fr g g' → ∀ fl, Q 70 g' fl V) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fz fc fi hn ha hd hs ⊢
  wpx [W_45, W_53, W_57, W_160, W_416, o4, o1, o5, o14, o25, Op.shl64]
  all_goals repeat' (first
    | refine hn _ ?_ _
    | refine ha _ ?_ _
    | refine hd _ ?_ _
    | refine hs _ ?_ _
    | with_reducible rfl
    | with_reducible exact fz
    | with_reducible exact fc
    | with_reducible exact fi
    | apply And.intro
    | intro _)

/-- `PhyParents`' `_items` = `rbp`, `_capacity` = `_size`: to 77. -/
theorem vc_70 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (wi : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 16#64) i)) (wc : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 28#64) i))
    (oi : Ok (g.rbx + 16#64) 8) (oc : Ok (g.rbx + 28#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 77 g' fl V') :
    W_70 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at wi wc oi oc h ⊢
  wpx [W_70, o6]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible exact wi
    | with_reducible exact wc
    | with_reducible exact oi
    | with_reducible exact oc
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | apply And.intro
    | intro _)

/-- Back from `operator new []`: `r12` = `PhyParents`' old `_items`, `rdi` = `rbp` = the new array, `rsi` = the old
one, `rdx` = the bytes: to `memcpy` (189). -/
theorem vc_169 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fi : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 16#64) i))
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 24#64) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 189 g' fl V) :
    W_169 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fi fz h ⊢
  wpx [W_169, o15, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fi
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- `rdi` = the old array, to `delete []` (197). -/
theorem vc_194 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 197 g' fl V) :
    W_194 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_194, o16]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- Back from `delete []`: `edi` = `PhyParents`' `_size`, to 70. -/
theorem vc_202 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 24#64) i)) (h : ∀ g', Fr g g' → ∀ fl, Q 70 g' fl V) :
    W_202 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fz h ⊢
  wpx [W_202, o17]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- `LogParents`' `_size` compared with its `_capacity`: equal to 113; else a `_size` not 0 to `operator new []`
(332), else `_items` not null to 362, else to 106. -/
theorem vc_77 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 40#64) i))
    (fc : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 44#64) i))
    (fi : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 32#64) i))
    (hn : ∀ g', Fr g g' → ∀ fl, Q 113 g' fl V) (ha : ∀ g', Fr g g' → ∀ fl, Q 332 g' fl V)
    (hd : ∀ g', Fr g g' → ∀ fl, Q 362 g' fl V) (hs : ∀ g', Fr g g' → ∀ fl, Q 106 g' fl V) :
    W_77 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fz fc fi hn ha hd hs ⊢
  wpx [W_77, W_85, W_93, W_328, W_432, o7, o1, o8, o14, o25, Op.shl64]
  all_goals repeat' (first
    | refine hn _ ?_ _
    | refine ha _ ?_ _
    | refine hd _ ?_ _
    | refine hs _ ?_ _
    | with_reducible rfl
    | with_reducible exact fz
    | with_reducible exact fc
    | with_reducible exact fi
    | apply And.intro
    | intro _)

/-- `LogParents`' `_items` = `rbp`, `_capacity` = `_size`: to 113. -/
theorem vc_106 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (wi : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 32#64) i)) (wc : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 44#64) i))
    (oi : Ok (g.rbx + 32#64) 8) (oc : Ok (g.rbx + 44#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 113 g' fl V') :
    W_106 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at wi wc oi oc h ⊢
  wpx [W_106, o9]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible exact wi
    | with_reducible exact wc
    | with_reducible exact oi
    | with_reducible exact oc
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | apply And.intro
    | intro _)

/-- Back from `operator new []`: `r12` = `LogParents`' old `_items`, `rdi` = `rbp` = the new array, `rsi` = the old
one, `rdx` = the bytes: to `memcpy` (357). -/
theorem vc_337 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fi : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 32#64) i))
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 40#64) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 357 g' fl V) :
    W_337 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fi fz h ⊢
  wpx [W_337, o23, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fi
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- `rdi` = the old array, to `delete []` (365). -/
theorem vc_362 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 365 g' fl V) :
    W_362 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_362, o16]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- Back from `delete []`: `edi` = `LogParents`' `_size`, to 106. -/
theorem vc_370 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 40#64) i)) (h : ∀ g', Fr g g' → ∀ fl, Q 106 g' fl V) :
    W_370 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fz h ⊢
  wpx [W_370, o24]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- `Items`' `_size` compared with its `_capacity`: equal to 149; else a `_size` not 0 to `operator new []`
(276), else `_items` not null to 306, else to 142. -/
theorem vc_113 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 56#64) i))
    (fc : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 60#64) i))
    (fi : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 48#64) i))
    (hn : ∀ g', Fr g g' → ∀ fl, Q 149 g' fl V) (ha : ∀ g', Fr g g' → ∀ fl, Q 276 g' fl V)
    (hd : ∀ g', Fr g g' → ∀ fl, Q 306 g' fl V) (hs : ∀ g', Fr g g' → ∀ fl, Q 142 g' fl V) :
    W_113 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fz fc fi hn ha hd hs ⊢
  wpx [W_113, W_121, W_129, W_272, W_384, o10, o1, o11, o18, o25, Op.shl64]
  all_goals repeat' (first
    | refine hn _ ?_ _
    | refine ha _ ?_ _
    | refine hd _ ?_ _
    | refine hs _ ?_ _
    | with_reducible rfl
    | with_reducible exact fz
    | with_reducible exact fc
    | with_reducible exact fi
    | apply And.intro
    | intro _)

/-- `Items`' `_items` = `rbp`, `_capacity` = `_size`: to 149. -/
theorem vc_142 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (wi : ∀ i < 8, Foot Wl (Addr.add (g.rbx + 48#64) i)) (wc : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 60#64) i))
    (oi : Ok (g.rbx + 48#64) 8) (oc : Ok (g.rbx + 60#64) 4) (hI : I V)
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (h : ∀ g' V', I V' → Fr g g' → ∀ fl, Q 149 g' fl V') :
    W_142 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at wi wc oi oc h ⊢
  wpx [W_142, o12]
  all_goals repeat' (first
    | refine h _ _ ?_ ?_ _
    | with_reducible exact wi
    | with_reducible exact wc
    | with_reducible exact oi
    | with_reducible exact oc
    | with_reducible rfl
    | with_reducible exact hI
    | refine hcl _ _ _ _ (toBytesLE_length _ _) ?_ ?_
    | apply And.intro
    | intro _)

/-- Back from `operator new []`: `r12` = `Items`' old `_items`, `rdi` = `rbp` = the new array, `rsi` = the old
one, `rdx` = the bytes: to `memcpy` (301). -/
theorem vc_281 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fi : ∀ i < 8, Foot F.data (Addr.add (g.rbx + 48#64) i))
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 56#64) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 301 g' fl V) :
    W_281 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fi fz h ⊢
  wpx [W_281, o21, Op.shl64]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fi
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- `rdi` = the old array, to `delete []` (309). -/
theorem vc_306 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 309 g' fl V) :
    W_306 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_306, o16]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- Back from `delete []`: `edi` = `Items`' `_size`, to 142. -/
theorem vc_314 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fz : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 56#64) i)) (h : ∀ g', Fr g g' → ∀ fl, Q 142 g' fl V) :
    W_314 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fz h ⊢
  wpx [W_314, o22]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact fz
    | apply And.intro
    | intro _)

/-- The three pops, to the `ret`. -/
theorem vc_149 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp) → g'.rbp = rdq(V, g.rsp + 8) →
      g'.r12 = rdq(V, g.rsp + 8 + 8) → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 153 g' fl V) :
    W_149 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 f3 h ⊢
  wpx [W_149, o13]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | apply And.intro
    | intro _)

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Ok : Addr → Nat → Prop} {Y : State} {t : Nat} {W : Addr → Byte}

/-- A store's footprint in `F.data`. -/
theorem Ev.fd (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) {a : Addr} {n : Nat} (h : Ok a n) :
    ∀ i < n, Foot F.data (Addr.add a i) := fun i hi => E.c.hws _ (E.hok _ _ h i hi)

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) {U : State} {t₁ : Nat} {j R : Nat}
    {ent : Addr} (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W)
    (hrU : U.cpu.rip = rsv_at.add j) (hs : U.cpu.gpr.rsp = aR S) (hj : j < rsv.length)
    (hd : Dec prof.feat rsv j (FV7z.mk .call 64 [.rel R] 5)) (htgt : rsv_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S I ent (j + 5) W)
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = rsv_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ

/-- From 149: the pops, the `ret`, to `kr`. -/
theorem tail149 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 149) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨ms, mx, m13, m14, m15⟩ := hm
  refine (c_149 prof).run E.c E.hin (fun j' g' _ V' => j' = 153 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 8 + 8) ∧
      g'.r13 = Y.cpu.gpr.r13 ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_149 (by rw [ms]; exact E.fb3) (by rw [ms, q1]; exact E.fb2) (by rw [ms, q2]; exact E.fb1)
      fun _ a b d e i j k _ => ⟨rfl, rfl, a, b, d, e, i, j, k⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gx, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  obtain ⟨s1, s2, s3, s4⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp) = g0.rbx := by rw [ms]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 8) = g0.rbp := by rw [ms, q1]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 8 + 8) = g0.r12 := by rw [ms, q2]; exact s3
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q3 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_153 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s4) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gx.trans e1, gp.trans e2, g12.trans e3, g13.trans m13, g14.trans m14, g15.trans m15⟩

/-- From 142: `Items`' `_items` and `_capacity` stored, to 149. -/
theorem from142 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 142) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_142 prof).run E.c E.hin (fun j' g' _ V' => j' = 149 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_142 (by rw [hm.2.1]; exact E.hok _ _ E.o48) (by rw [hm.2.1]; exact E.hok _ _ E.o60)
      (by rw [hm.2.1]; exact E.o48) (by rw [hm.2.1]; exact E.o60) hIW E.hcl fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact tail149 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 314 (back from `delete []`): `edi` = `_size`, to 142. -/
theorem from314 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 314) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_314 prof).run E.c E.hin (fun j' g' _ V' => j' = 142 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_314 (by rw [hm.2.1]; exact E.f56) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from142 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 306: `delete []` of the old array (`kD`), from its return 314. -/
theorem from306 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 306) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_306 prof).run E.c E.hin (fun j' g' _ V' => j' = 309 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_306 fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_309 _) tgt_309 E.cD (E.kD _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from314 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 281 (back from `operator new []`): `memcpy` (`kM`), from its return 306. -/
theorem from281 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 281) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_281 prof).run E.c E.hin (fun j' g' _ V' => j' = 301 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_281 (by rw [hm.2.1]; exact E.fd E.o48) (by rw [hm.2.1]; exact E.f56) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_301 _) tgt_301 E.cM (E.kM _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from306 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 113: `Items`: to 149, or `operator new []` (`kN`) and from its return 281, or to 306, or to 142. -/
theorem from113 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 113) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_113 prof).run E.c E.hin
    (fun j' g' _ V' => I V' ∧ Fr Y.cpu.gpr g' ∧ (j' = 149 ∨ j' = 276 ∨ j' = 306 ∨ j' = 142)) hK hA hr
    (vc_113 (by rw [hm.2.1]; exact E.f56) (by rw [hm.2.1]; exact E.fd E.o60) (by rw [hm.2.1]; exact E.fd E.o48)
      (fun _ e _ => ⟨hIW, e, Or.inl rfl⟩) (fun _ e _ => ⟨hIW, e, Or.inr (Or.inl rfl)⟩)
      (fun _ e _ => ⟨hIW, e, Or.inr (Or.inr (Or.inl rfl))⟩)
      (fun _ e _ => ⟨hIW, e, Or.inr (Or.inr (Or.inr rfl))⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl | rfl | rfl
  · exact tail149 E hKU hAU hrU hmU hI1
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_276 _) tgt_276 E.cN (E.kN _ _ hI1) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from281 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · exact from306 E hKU hAU hrU hmU hI1
  · exact from142 E hKU hAU hrU hmU hI1

/-- From 106: `LogParents`' `_items` and `_capacity` stored, to 113. -/
theorem from106 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 106) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_106 prof).run E.c E.hin (fun j' g' _ V' => j' = 113 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_106 (by rw [hm.2.1]; exact E.hok _ _ E.o32) (by rw [hm.2.1]; exact E.hok _ _ E.o44)
      (by rw [hm.2.1]; exact E.o32) (by rw [hm.2.1]; exact E.o44) hIW E.hcl fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from113 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 370 (back from `delete []`): `edi` = `_size`, to 106. -/
theorem from370 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 370) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_370 prof).run E.c E.hin (fun j' g' _ V' => j' = 106 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_370 (by rw [hm.2.1]; exact E.f40) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from106 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 362: `delete []` of the old array (`kD`), from its return 370. -/
theorem from362 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 362) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_362 prof).run E.c E.hin (fun j' g' _ V' => j' = 365 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_362 fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_365 _) tgt_365 E.cD (E.kD _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from370 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 337 (back from `operator new []`): `memcpy` (`kM`), from its return 362. -/
theorem from337 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 337) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_337 prof).run E.c E.hin (fun j' g' _ V' => j' = 357 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_337 (by rw [hm.2.1]; exact E.fd E.o32) (by rw [hm.2.1]; exact E.f40) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_357 _) tgt_357 E.cM (E.kM _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from362 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 77: `LogParents`: to 113, or `operator new []` (`kN`) and from its return 337, or to 362, or to 106. -/
theorem from77 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 77) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_77 prof).run E.c E.hin
    (fun j' g' _ V' => I V' ∧ Fr Y.cpu.gpr g' ∧ (j' = 113 ∨ j' = 332 ∨ j' = 362 ∨ j' = 106)) hK hA hr
    (vc_77 (by rw [hm.2.1]; exact E.f40) (by rw [hm.2.1]; exact E.fd E.o44) (by rw [hm.2.1]; exact E.fd E.o32)
      (fun _ e _ => ⟨hIW, e, Or.inl rfl⟩) (fun _ e _ => ⟨hIW, e, Or.inr (Or.inl rfl)⟩)
      (fun _ e _ => ⟨hIW, e, Or.inr (Or.inr (Or.inl rfl))⟩)
      (fun _ e _ => ⟨hIW, e, Or.inr (Or.inr (Or.inr rfl))⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl | rfl | rfl
  · exact from113 E hKU hAU hrU hmU hI1
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_332 _) tgt_332 E.cN (E.kN _ _ hI1) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from337 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · exact from362 E hKU hAU hrU hmU hI1
  · exact from106 E hKU hAU hrU hmU hI1

/-- From 70: `PhyParents`' `_items` and `_capacity` stored, to 77. -/
theorem from70 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 70) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_70 prof).run E.c E.hin (fun j' g' _ V' => j' = 77 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_70 (by rw [hm.2.1]; exact E.hok _ _ E.o16) (by rw [hm.2.1]; exact E.hok _ _ E.o28)
      (by rw [hm.2.1]; exact E.o16) (by rw [hm.2.1]; exact E.o28) hIW E.hcl fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from77 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 202 (back from `delete []`): `edi` = `_size`, to 70. -/
theorem from202 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 202) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_202 prof).run E.c E.hin (fun j' g' _ V' => j' = 70 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_202 (by rw [hm.2.1]; exact E.f24) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from70 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 194: `delete []` of the old array (`kD`), from its return 202. -/
theorem from194 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 194) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_194 prof).run E.c E.hin (fun j' g' _ V' => j' = 197 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_194 fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_197 _) tgt_197 E.cD (E.kD _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from202 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 169 (back from `operator new []`): `memcpy` (`kM`), from its return 194. -/
theorem from169 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 169) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_169 prof).run E.c E.hin (fun j' g' _ V' => j' = 189 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_169 (by rw [hm.2.1]; exact E.fd E.o16) (by rw [hm.2.1]; exact E.f24) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_189 _) tgt_189 E.cM (E.kM _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from194 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 45: `PhyParents`: to 77, or `operator new []` (`kN`) and from its return 169, or to 194, or to 70. -/
theorem from45 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 45) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_45 prof).run E.c E.hin
    (fun j' g' _ V' => I V' ∧ Fr Y.cpu.gpr g' ∧ (j' = 77 ∨ j' = 164 ∨ j' = 194 ∨ j' = 70)) hK hA hr
    (vc_45 (by rw [hm.2.1]; exact E.f24) (by rw [hm.2.1]; exact E.fd E.o28) (by rw [hm.2.1]; exact E.fd E.o16)
      (fun _ e _ => ⟨hIW, e, Or.inl rfl⟩) (fun _ e _ => ⟨hIW, e, Or.inr (Or.inl rfl)⟩)
      (fun _ e _ => ⟨hIW, e, Or.inr (Or.inr (Or.inl rfl))⟩)
      (fun _ e _ => ⟨hIW, e, Or.inr (Or.inr (Or.inr rfl))⟩)) ?_
  rintro j' g fl V₁ ⟨hI1, gf, hj⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  rcases hj with rfl | rfl | rfl | rfl
  · exact from77 E hKU hAU hrU hmU hI1
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_164 _) tgt_164 E.cN (E.kN _ _ hI1) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from169 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · exact from194 E hKU hAU hrU hmU hI1
  · exact from70 E hKU hAU hrU hmU hI1

/-- From 39: `Prefixes`' `_items` and `_capacity` stored, to 45. -/
theorem from39 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 39) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_39 prof).run E.c E.hin (fun j' g' _ V' => j' = 45 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_39 (by rw [hm.2.1]; exact E.hok _ _ E.o0) (by rw [hm.2.1]; exact E.hok _ _ E.o12)
      (by rw [hm.2.1]; exact E.o0) (by rw [hm.2.1]; exact E.o12) hIW E.hcl fun _ V' hI e _ => ⟨rfl, hI, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from45 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 257 (back from `delete []`): `edi` = `_size`, to 39. -/
theorem from257 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 257) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_257 prof).run E.c E.hin (fun j' g' _ V' => j' = 39 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_257 (by rw [hm.2.1]; exact E.f8) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from39 E hKU hAU hrU (Fm.fr hm gf) hI1

/-- From 249: `delete []` of the old array (`kD`), from its return 257. -/
theorem from249 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 249) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_249 prof).run E.c E.hin (fun j' g' _ V' => j' = 252 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_249 fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_252 _) tgt_252 E.cD (E.kD _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from257 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

/-- From 225 (back from `operator new []`): `memcpy` (`kM`), from its return 249. -/
theorem from225 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I Ok) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = rsv_at.add 225) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_225 prof).run E.c E.hin (fun j' g' _ V' => j' = 244 ∧ I V' ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_225 (by rw [hm.2.1]; exact E.fd E.o0) (by rw [hm.2.1]; exact E.f8) fun _ e _ => ⟨rfl, hIW, e⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hI1, gf⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_244 _) tgt_244 E.cM (E.kM _ _ hI1) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from249 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `CDirItems::ReserveDown ()` (`this` = `rdi`) from its entry, `I` an invariant of the bytes kept by the stores
`Ok` allows (`hcl`, `hok`): the pushes' slots and the calls' return address slot in what the run may store into,
the return address readable; `Ok` for each vector's `_items` and `_capacity` (`o0`, `o12`, `o16`, `o28`, `o32`,
`o44`, `o48`, `o60`), each `_size` readable (`f8`, `f24`, `f40`, `f56`). `I` holds after the pushes (`hI0`) and gives
the stack (`hI`). The callees, each for any return offset, from its return with `rsp` as it was, the callee-saved
registers as at its entry and `I`: `operator new []` (`kN`), `memcpy` (`kM`), `delete []` (`kD`). At the return
address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were, bytes with `I`. -/
theorem rsv_ok {I : (Addr → Byte) → Prop} {Ok : Addr → Nat → Prop} {e₂ : Addr} {code₂ : List Byte}
    {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L rsv_at rsv)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = rsv_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hok : ∀ a n, Ok a n → ∀ i < n, Foot Wl (Addr.add a i))
    (hcl : ∀ (W : Addr → Byte) (a : Addr) (n : Nat) (bs : List Byte), bs.length = n → Ok a n → I W →
      I (Vst W a bs))
    (o0 : Ok X.cpu.gpr.rdi 8) (o12 : Ok (X.cpu.gpr.rdi + 12#64) 4) (o16 : Ok (X.cpu.gpr.rdi + 16#64) 8)
    (o28 : Ok (X.cpu.gpr.rdi + 28#64) 4) (o32 : Ok (X.cpu.gpr.rdi + 32#64) 8) (o44 : Ok (X.cpu.gpr.rdi + 44#64) 4)
    (o48 : Ok (X.cpu.gpr.rdi + 48#64) 8) (o60 : Ok (X.cpu.gpr.rdi + 60#64) 4)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (f24 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 24#64) i))
    (f40 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 40#64) i))
    (f56 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 56#64) i))
    (hI : ∀ W, I W → Stk W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) (hI0 : I (P3 V X.cpu.gpr))
    (cN : ∃ code : List Byte, CodeIn L 0x6029b0#64 code ∧ 0 < code.length)
    (cM : ∃ code : List Byte, CodeIn L 0x401070#64 code ∧ 0 < code.length)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (kN : ∀ W j, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6029b0#64 j W)
    (kM : ∀ W j, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x401070#64 j W)
    (kD : ∀ W j, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6014f0#64 j W)
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I Ok :=
    { c := c, hin := hin, hin₂ := hin₂, h₂ := h₂, hI := hI, hok := hok, hcl := hcl,
      o0 := o0, o12 := o12, o16 := o16, o28 := o28, o32 := o32, o44 := o44, o48 := o48, o60 := o60,
      f8 := f8, f24 := f24, f40 := f40, f56 := f56,
      fb3 := fun i hi => c.hws _ (hs3 i hi), fb2 := fun i hi => c.hws _ (hs2 i hi),
      fb1 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8, cN := cN, cM := cM, cD := cD,
      kN := kN, kM := kM, kD := kD, kr := kr }
  -- the prologue and `Prefixes`
  refine (c_0 prof).run c hin (fun j' g' _ V' => V' = P3 V X.cpu.gpr ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧
      (j' = 45 ∨ j' = 220 ∨ j' = 249 ∨ j' = 39)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 f8 (fun i hi => c.hws _ (hok _ _ o12 i hi)) (fun i hi => c.hws _ (hok _ _ o0 i hi))
      (fun _ a b d e i _ => ⟨rfl, ⟨a, b, d, e, i⟩, Or.inl rfl⟩)
      (fun _ a b d e i _ => ⟨rfl, ⟨a, b, d, e, i⟩, Or.inr (Or.inl rfl)⟩)
      (fun _ a b d e i _ => ⟨rfl, ⟨a, b, d, e, i⟩, Or.inr (Or.inr (Or.inl rfl))⟩)
      (fun _ a b d e i _ => ⟨rfl, ⟨a, b, d, e, i⟩, Or.inr (Or.inr (Or.inr rfl))⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, hmY, hj⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hj with rfl | rfl | rfl | rfl
  · exact from45 E hKY hAY hrY hmY hI0
  · refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_220 _) tgt_220 E.cN (E.kN _ _ hI0) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from225 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ
  · exact from249 E hKY hAY hrY hmY hI0
  · exact from39 E hKY hAY hrY hmY hI0

end FV7z.Rsv
