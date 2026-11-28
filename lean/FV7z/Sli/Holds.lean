import FV7z.Sli.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.SubMr64
/-!
# `CDirItems::SetLinkInfo` (PLAN.md §M, M1): the run through the callees

7-Zip 26.06's `HRESULT CDirItems::SetLinkInfo (CDirItem &dirItem, const CFileInfo &fi, const FString &phyPrefix)`
(`CPP/7zip/UI/Common/EnumDirItems.cpp`; `objdump -d`) at `0x5c0e20` in `7zzs`: `this` = `rdi` (`rbp`), `dirItem` =
`rsi` (`r12`), `fi` = `rdx` (`rbx`), `phyPrefix` = `rcx`. `S` the stack pointer and `g0` the registers at the entry:
`push r14, r13, r12, rbp, rbx; sub rsp, 0x30` (`aR S`), the stack guard (`fs:0x28`) at `aR S + 40`, a local
`FString` (the path) at `aR S + 16` (`r13`), a word at `aR S + 12`. `SymLinks` (the byte at `this + 64`) 0 or `fi`
not a link (`fi.st_mode & S_IFMT` at `fi + 72` not `S_IFLNK`) to 62 with `eax` = 0; else (96) `path = phyPrefix +
fi.Name` (117, `0x44c2b0`), `GetReparseData (path, dirItem.ReparseData)` (122..132, `0x5a22b0`, `rsi` = `dirItem +
120`): true (137..144) `this->_totalSize -= fi.Size` (by hand: `sub [rbp + 0x60], rax`, `Seg.s_sub_mr64`, `rax` =
`[fi]`), `eax` = 0 (148); false (184) the error's code (`0x5a0200`) in `r14d`, `ReparseData`'s buffer freed (202,
`0x6014f0`, unless null) and cleared (207), `ReparseData`'s size cleared and `AddError (this, path, code)` (216..237,
`0x5c0170`), to 150. At 150 the path's buffer freed (164, `0x6014f0`, `eax` kept at `aR S + 12`) unless null, to 62:
the guard's check, the epilogue, the `ret` (94). Not covered: `__stack_chk_fail` (244), the landing pad after it
(the generated code stops at 249 of the 261 bytes).

The callees are continuations (`KC`, as in `FV7z/Dfn/Holds.lean`): each is given its arguments and the bytes, and
from its return the run goes on with `rsp` as it was and the callee-saved registers (`KS`) as at the `call`. The
bytes are tracked by an invariant `I` the caller chooses: the bytes after the prologue have it (`hI0`), every callee
returns with it, the stores keep it (`hI12`, `hI96`, `hI120`, `hI128`), and it gives the saved registers, the return
address and the stack guard (`Stk`); the word's store keeps the path's buffer pointer (`h16`). `r15` is not saved:
it is kept by every piece and callee (`Fm`, `KS`).

- `aR`, `P5`, `V0`, `q1`–`q6`: the frame, the bytes after the pushes and after the prologue, the pops' addresses.
- `Fm`, `Fr`, `KS`, `Stk`, `KC`, `Ev`: the frame's registers, what a piece keeps, the callee-saved registers, the
  stack, the callees, the hypotheses of the runs; `callK`: a `call` and the callee's return.
- `vc_*`: the pieces; `tail62`, `from150`, `from216`, `from189`, `from137`, `from122`: the runs from the cut points.
- `sli_ok`: from the entry to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Sli
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of the concatenation `phyPrefix + fi.Name`. -/
def pc117 : List Byte := [0xe8, 0x16, 0xb4, 0xe8, 0xff]
theorem pc117_0 : ∀ feat, Dec feat pc117 0 (FV7z.mk .call 64 [.rel 18446744073708024854] 5) := by dec_rfl
theorem wc_117 : pc117 <+: sli.drop 117 := by decide +kernel
theorem call_117 (feat : Features) : Dec feat sli 117 (FV7z.mk .call 64 [.rel 18446744073708024854] 5) :=
  Dec.shift (j := 117) (k := 0) (pc117_0 feat) wc_117 (Nat.zero_le _)
theorem tgt_117 : sli_at.add (117 + 5) + BitVec.ofNat 64 18446744073708024854 = 0x44c2b0#64 := by decide

/-- The `call` of `GetReparseData`. -/
def pc132 : List Byte := [0xe8, 0x07, 0x14, 0xfe, 0xff]
theorem pc132_0 : ∀ feat, Dec feat pc132 0 (FV7z.mk .call 64 [.rel 18446744073709425671] 5) := by dec_rfl
theorem wc_132 : pc132 <+: sli.drop 132 := by decide +kernel
theorem call_132 (feat : Features) : Dec feat sli 132 (FV7z.mk .call 64 [.rel 18446744073709425671] 5) :=
  Dec.shift (j := 132) (k := 0) (pc132_0 feat) wc_132 (Nat.zero_le _)
theorem tgt_132 : sli_at.add (132 + 5) + BitVec.ofNat 64 18446744073709425671 = 0x5a22b0#64 := by decide

/-- `sub qword [rbp + 0x60], rax`. -/
def ps144 : List Byte := [0x48, 0x29, 0x45, 0x60]
theorem ps144_0 : ∀ feat, Dec feat ps144 0 (FV7z.mk .sub 64 [.mem (mbd 5 96 64), gr 64 0] 4) := by dec_rfl
theorem ws_144 : ps144 <+: sli.drop 144 := by decide +kernel
theorem sub_144 (feat : Features) : Dec feat sli 144 (FV7z.mk .sub 64 [.mem (mbd 5 96 64), gr 64 0] 4) :=
  Dec.shift (j := 144) (k := 0) (ps144_0 feat) ws_144 (Nat.zero_le _)

/-- The `call` of `delete []` of the path's buffer. -/
def pc164 : List Byte := [0xe8, 0x27, 0x06, 0x04, 0x00]
theorem pc164_0 : ∀ feat, Dec feat pc164 0 (FV7z.mk .call 64 [.rel 263719] 5) := by dec_rfl
theorem wc_164 : pc164 <+: sli.drop 164 := by decide +kernel
theorem call_164 (feat : Features) : Dec feat sli 164 (FV7z.mk .call 64 [.rel 263719] 5) :=
  Dec.shift (j := 164) (k := 0) (pc164_0 feat) wc_164 (Nat.zero_le _)
theorem tgt_164 : sli_at.add (164 + 5) + BitVec.ofNat 64 263719 = 0x6014f0#64 := by decide

/-- The `call` of the error's code. -/
def pc184 : List Byte := [0xe8, 0x23, 0xf3, 0xfd, 0xff]
theorem pc184_0 : ∀ feat, Dec feat pc184 0 (FV7z.mk .call 64 [.rel 18446744073709417251] 5) := by dec_rfl
theorem wc_184 : pc184 <+: sli.drop 184 := by decide +kernel
theorem call_184 (feat : Features) : Dec feat sli 184 (FV7z.mk .call 64 [.rel 18446744073709417251] 5) :=
  Dec.shift (j := 184) (k := 0) (pc184_0 feat) wc_184 (Nat.zero_le _)
theorem tgt_184 : sli_at.add (184 + 5) + BitVec.ofNat 64 18446744073709417251 = 0x5a0200#64 := by decide

/-- The `call` of `delete []` of `ReparseData`'s buffer. -/
def pc202 : List Byte := [0xe8, 0x01, 0x06, 0x04, 0x00]
theorem pc202_0 : ∀ feat, Dec feat pc202 0 (FV7z.mk .call 64 [.rel 263681] 5) := by dec_rfl
theorem wc_202 : pc202 <+: sli.drop 202 := by decide +kernel
theorem call_202 (feat : Features) : Dec feat sli 202 (FV7z.mk .call 64 [.rel 263681] 5) :=
  Dec.shift (j := 202) (k := 0) (pc202_0 feat) wc_202 (Nat.zero_le _)
theorem tgt_202 : sli_at.add (202 + 5) + BitVec.ofNat 64 263681 = 0x6014f0#64 := by decide

/-- The `call` of `AddError`. -/
def pc237 : List Byte := [0xe8, 0x5e, 0xf2, 0xff, 0xff]
theorem pc237_0 : ∀ feat, Dec feat pc237 0 (FV7z.mk .call 64 [.rel 18446744073709548126] 5) := by dec_rfl
theorem wc_237 : pc237 <+: sli.drop 237 := by decide +kernel
theorem call_237 (feat : Features) : Dec feat sli 237 (FV7z.mk .call 64 [.rel 18446744073709548126] 5) :=
  Dec.shift (j := 237) (k := 0) (pc237_0 feat) wc_237 (Nat.zero_le _)
theorem tgt_237 : sli_at.add (237 + 5) + BitVec.ofNat 64 18446744073709548126 = 0x5c0170#64 := by decide

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wt_94 : pret <+: sli.drop 94 := by decide +kernel
theorem ret_94 (feat : Features) : Dec feat sli 94 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 94) (k := 0) (pret_0 feat) wt_94 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the five pushes and `sub rsp, 0x30`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 48#64

/-- The bytes after the five pushes (`r14`, `r13`, `r12`, `rbp`, `rbx`). -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (g.rsp - 8 - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes after the prologue: the pushes, the stack guard stored. -/
abbrev V0 (fb : Addr) (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (P5 V g) (aR g.rsp + 40#64) (toBytesLE rdq(P5 V g, fb + 40#64) 8)

theorem q1 (S : Addr) : aR S + 48#64 = S - 8 - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 48#64 + 8 = S - 8 - 8 - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 48#64 + 8 + 8 = S - 8 - 8 - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 = S - 8 - 8 := by rw [q3, BitVec.sub_add_cancel]
theorem q5 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 + 8 = S - 8 := by rw [q4, BitVec.sub_add_cancel]
theorem q6 (S : Addr) : aR S + 48#64 + 8 + 8 + 8 + 8 + 8 = S := by rw [q5, BitVec.sub_add_cancel]

/-- The frame from 96 on: `rsp` = `aR S`, `rbx` = `fi`, `rbp` = `this`, `r12` = `dirItem`, `r13` = the path,
`r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.rbx = g0.rdx ∧ g.rbp = g0.rdi ∧ g.r12 = g0.rsi ∧ g.r13 = aR S + 16#64 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx`, `rbp`, `r12`, `r13`, `r15`. -/
abbrev Fr (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r15 = g.r15

/-- The callee-saved registers as in `g`. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem Fm.fr {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fr g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.1.trans h.2.2.2.1,
    h'.2.2.2.2.1.trans h.2.2.2.2.1, h'.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.1.trans h.2.1, hk.2.1.trans h.2.2.1, hk.2.2.1.trans h.2.2.2.1, hk.2.2.2.1.trans h.2.2.2.2.1,
    hk.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-- The stack (`fb` the `fs` base, `ra` the return address): the five saved registers, the return address, the stack
guard as at `fs:0x28`. -/
abbrev Stk (fb : Addr) (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, S - 8 - 8 - 8 - 8 - 8) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8 - 8) = g0.r13 ∧ rdq(W, S - 8) = g0.r14 ∧ rdq(W, S) = ra ∧
    rdq(W, aR S + 40#64) = rdq(W, fb + 40#64)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry and the invariant `I`, the run goes on
to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (I : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (sli_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = sli_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes). -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (fb S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hfs : s₀.cpu.seg.fsBase = fb
  hin : CodeIn L sli_at sli
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk fb W S g0 (e₂.add j₂)
  hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)
  fg : ∀ i < 8, Foot F.data (Addr.add (aR S + 40#64) i)
  f16 : ∀ i < 8, Foot F.data (Addr.add (aR S + 16#64) i)
  w12 : ∀ i < 4, Foot Wl (Addr.add (aR S + 12#64) i)
  fb40 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8 - 8) i)
  fb32 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb24 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb16 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb8 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  fx : ∀ i < 8, Foot F.data (Addr.add g0.rdx i)
  w96 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 96#64) i)
  w120 : ∀ i < 8, Foot Wl (Addr.add (g0.rsi + 120#64) i)
  w128 : ∀ i < 8, Foot Wl (Addr.add (g0.rsi + 128#64) i)
  hI12 : ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W (aR S + 12#64) bs)
  hI96 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rdi + 96#64) bs)
  hI120 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rsi + 120#64) bs)
  hI128 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (g0.rsi + 128#64) bs)
  h16 : ∀ W (bs : List Byte), bs.length = 4 → rdq(Vst W (aR S + 12#64) bs, aR S + 16#64) = rdq(W, aR S + 16#64)
  cC : ∃ code : List Byte, CodeIn L 0x5a22b0#64 code ∧ 0 < code.length
  cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length
  cE : ∃ code : List Byte, CodeIn L 0x5a0200#64 code ∧ 0 < code.length
  cA : ∃ code : List Byte, CodeIn L 0x5c0170#64 code ∧ 0 < code.length
  k132 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a22b0#64 137 W
    (fun g => g.rdi = rdq(W, aR S + 16#64) ∧ g.rsi = g0.rsi + 120#64)
  k164 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 169 W (fun g => g.rdi = rdq(W, aR S + 16#64))
  k184 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5a0200#64 189 W (fun _ => True)
  k202 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x6014f0#64 207 W (fun g => g.rdi = rdq(W, g0.rsi + 120#64))
  k237 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x5c0170#64 242 W
    (fun g => g.rdi = g0.rdi ∧ g.rsi = aR S + 16#64)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W →
    GoG prof L o gev gP gE Z' t'

/-! ## The pieces -/

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- The prologue (the guard's value named `cn`), `eax` = 0, `SymLinks` 0 to 62 (176); else `rbx` = `fi`, not a link
to 62, else (96) `r13` = `rdi` = the path, `r12` = `dirItem`, `rbp` = `this`, `rsi` = `phyPrefix`, `rdx` =
`fi.Name`, to the concatenation's `call` (117). -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {cn : BitVec 64}
    (hcn : rdq(P5 V g, fb + 40#64) = cn)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR g.rsp + 40#64) i))
    (f64 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 64#64) i))
    (f72 : ∀ i < 4, Foot F.data (Addr.add (g.rdx + 72#64) i))
    (h62 : ∀ g', g'.rsp = aR g.rsp → g'.r15 = g.r15 →
      ∀ fl, Q 62 g' fl (Vst (P5 V g) (aR g.rsp + 40#64) (toBytesLE cn 8)))
    (h117 : ∀ g', g'.rsp = aR g.rsp → g'.rbx = g.rdx → g'.rbp = g.rdi → g'.r12 = g.rsi →
      g'.r13 = aR g.rsp + 16#64 → g'.r15 = g.r15 → g'.rdi = aR g.rsp + 16#64 → g'.rsi = g.rcx →
      g'.rdx = g.rdx + 104#64 → ∀ fl, Q 117 g' fl (Vst (P5 V g) (aR g.rsp + 40#64) (toBytesLE cn 8))) :
    W_0 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, P5] at hcn hs1 hs2 hs3 hs4 hs5 hw f64 f72 h62 h117 ⊢
  wpx [W_0, W_176, W_42, W_96, o0, o8, o1, o4, Op.ldf, Op.cmpmi, hcn]
  all_goals repeat' (first
    | refine h62 _ ?_ ?_ _
    | refine h117 _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | with_reducible exact hs5
    | with_reducible exact hcl
    | with_reducible exact hw
    | with_reducible exact f64
    | with_reducible exact f72
    | apply And.intro
    | intro _)

/-- The stack guard checked (as at `fs:0x28`: `jne` not taken), `add rsp, 0x30`, the five pops, to the `ret`. -/
theorem vc_62 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hc : rdq(V, g.rsp + 40#64) = rdq(V, fb + 40#64)) (f40 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (fcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8 + 8) i))
    (f5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 48#64 + 8 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 48#64 + 8 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 48#64) →
      g'.rbp = rdq(V, g.rsp + 48#64 + 8) → g'.r12 = rdq(V, g.rsp + 48#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 48#64 + 8 + 8 + 8) → g'.r14 = rdq(V, g.rsp + 48#64 + 8 + 8 + 8 + 8) →
      g'.r15 = g.r15 → ∀ fl, Q 94 g' fl V) :
    W_62 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f40 f1 f2 f3 f4 f5 h ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_62, W_82, o2, o3, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f40
    | with_reducible exact fcl
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | with_reducible exact f5
    | apply And.intro
    | intro _)

/-- `rdi` = the path's buffer, `rsi` = `&dirItem.ReparseData`, to `GetReparseData` (132). -/
theorem vc_122 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i))
    (h : ∀ g', g'.rdi = rdq(V, g.rsp + 16#64) → g'.rsi = g.r12 + 120#64 → Fr g g' → ∀ fl, Q 132 g' fl V) :
    W_122 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 h ⊢
  wpx [W_122, o5]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | apply And.intro
    | intro _)

/-- `test al, al`: 0 to the error's code (184), else `rax` = `fi.Size` to the `sub` (144). -/
theorem vc_137 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fx : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (h184 : ∀ g', Fr g g' → ∀ fl, Q 184 g' fl V)
    (h144 : ∀ g', g'.rax = rdq(V, g.rbx) → Fr g g' → ∀ fl, Q 144 g' fl V) :
    W_137 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fx h184 h144 ⊢
  wpx [W_137, W_141, o6, o7]
  all_goals repeat' (first
    | refine h184 _ ?_ _
    | refine h144 _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact fx
    | apply And.intro
    | intro _)

/-- `eax` = 0, to 150. -/
theorem vc_148 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ g', Fr g g' → ∀ fl, Q 150 g' fl V) :
    W_148 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  wpx [W_148, o8]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | apply And.intro
    | intro _)

/-- The path's buffer: null to 62, else `eax` kept in the word, to `delete []` (164). -/
theorem vc_150 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f16 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 16#64) i)) (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 12#64) i))
    (h62 : ∀ g', Fr g g' → ∀ fl, Q 62 g' fl V)
    (h164 : ∀ g', g'.rdi = rdq(V, g.rsp + 16#64) → Fr g g' →
      ∀ fl, Q 164 g' fl (Vst V (g.rsp + 12#64) (toBytesLE (BitVec.setWidth 32 g.rax) 4))) :
    W_150 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f16 w12 h62 h164 ⊢
  wpx [W_150, W_160, o9, o10]
  all_goals repeat' (first
    | refine h62 _ ?_ _
    | refine h164 _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f16
    | with_reducible exact w12
    | apply And.intro
    | intro _)

/-- `eax` = the word, `jmp` to 62. -/
theorem vc_169 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f12 : ∀ i < 4, Foot F.data (Addr.add (g.rsp + 12#64) i)) (h : ∀ g', Fr g g' → ∀ fl, Q 62 g' fl V) :
    W_169 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f12 h ⊢
  wpx [W_169, o11]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact f12
    | apply And.intro
    | intro _)

/-- `r14d` = the code, `ReparseData`'s buffer: null to 216, else to `delete []` (202). -/
theorem vc_189 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f120 : ∀ i < 8, Foot F.data (Addr.add (g.r12 + 120#64) i))
    (h216 : ∀ g', Fr g g' → ∀ fl, Q 216 g' fl V)
    (h202 : ∀ g', g'.rdi = rdq(V, g.r12 + 120#64) → Fr g g' → ∀ fl, Q 202 g' fl V) :
    W_189 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f120 h216 h202 ⊢
  wpx [W_189, o12]
  all_goals repeat' (first
    | refine h216 _ ?_ _
    | refine h202 _ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact f120
    | apply And.intro
    | intro _)

/-- `ReparseData`'s buffer cleared, to 216. -/
theorem vc_207 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w120 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 120#64) i))
    (h : ∀ g', Fr g g' → ∀ fl, Q 216 g' fl (Vst V (g.r12 + 120#64) (toBytesLE 0#64 8))) :
    W_207 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w120 h ⊢
  wpx [W_207, o13]
  all_goals repeat' (first
    | refine h _ ?_ _
    | with_reducible rfl
    | with_reducible exact w120
    | apply And.intro
    | intro _)

/-- `edx` = the code, `rsi` = the path, `rdi` = `this`, `ReparseData`'s size cleared, to `AddError` (237). -/
theorem vc_216 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w128 : ∀ i < 8, Foot Wl (Addr.add (g.r12 + 128#64) i))
    (h : ∀ g', g'.rdi = g.rbp → g'.rsi = g.r13 → Fr g g' →
      ∀ fl, Q 237 g' fl (Vst V (g.r12 + 128#64) (toBytesLE 0#64 8))) :
    W_216 fb F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w128 h ⊢
  wpx [W_216, o14]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ _
    | with_reducible rfl
    | with_reducible exact w128
    | apply And.intro
    | intro _)

/-- `jmp` to 150. -/
theorem vc_242 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ fl, Q 150 g fl V) :
    W_242 fb F Wl Q g f V := h _

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {fb S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {Y : State} {t : Nat} {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) {U : State} {t₁ : Nat} {j R : Nat}
    {ent : Addr} {A : Gprs → Prop} (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W)
    (hrU : U.cpu.rip = sli_at.add j) (hs : U.cpu.gpr.rsp = aR S) (hj : j < sli.length)
    (hd : Dec prof.feat sli j (FV7z.mk .call 64 [.rel R] 5)) (htgt : sli_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S I ent (j + 5) W A) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = sli_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → I W' →
      GoG prof L o gev gP gE Z t'') :
    GoG prof L o gev gP gE U t₁ := by
  have hU : U.cpu.gpr.rsp - 8 = aR S - 8 := by rw [hs]
  obtain ⟨cc, hinc, hcc⟩ := hc
  refine E.c.s_call hKU hAU E.hin hj hrU hd hinc hcc htgt (by rw [hU]; exact E.hr8) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hU] at hA₂
  refine k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂]; exact hU) (by rw [hg₂, hU]; exact hA) ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  rw [hg₂] at hkZ
  exact h Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ

/-- From 62 (`rsp` = `aR S`, `r15` as at the entry, the bytes `W` with `I`): the guard's check, the epilogue, the
`ret`, to `kr`. -/
theorem tail62 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sli_at.add 62) (ms : Y.cpu.gpr.rsp = aR S)
    (m15 : Y.cpu.gpr.r15 = g0.r15) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := E.hI W hIW
  have e1 : rdq(W, Y.cpu.gpr.rsp + 48#64) = g0.rbx := by rw [ms, q1]; exact s1
  have e2 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) = g0.rbp := by rw [ms, q2]; exact s2
  have e3 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) = g0.r12 := by rw [ms, q3]; exact s3
  have e4 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8) = g0.r13 := by rw [ms, q4]; exact s4
  have e5 : rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 + 8) = g0.r14 := by rw [ms, q5]; exact s5
  refine (c_62 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 94 ∧ V' = W ∧
      g'.rsp = Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W, Y.cpu.gpr.rsp + 48#64) ∧
      g'.rbp = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8) ∧ g'.r12 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8) ∧
      g'.r13 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8) ∧ g'.r14 = rdq(W, Y.cpu.gpr.rsp + 48#64 + 8 + 8 + 8 + 8) ∧
      g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_62 (by rw [ms]; exact s7) (by rw [ms]; exact E.fg) E.hcl (by rw [ms, q1]; exact E.fb40)
      (by rw [ms, q2]; exact E.fb32) (by rw [ms, q3]; exact E.fb24) (by rw [ms, q4]; exact E.fb16)
      (by rw [ms, q5]; exact E.fb8)
      fun _ a b d e f g h _ => ⟨rfl, rfl, a, b, d, e, f, g, h⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q6 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_94 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU]; exact s6) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W Z' t₂ hKZ' hAZ' hrZ' ?_ ?_ hIW
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans e5, g15.trans m15⟩

/-- From 150: the path's buffer, null to 62, else `delete []` (`k164`, the word stored), from its return (169) `eax`
= the word, to 62. -/
theorem from150 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sli_at.add 150) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_150 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => Fr Y.cpu.gpr g' ∧ ((j' = 62 ∧ V' = W) ∨
      (j' = 164 ∧ V' = Vst W (aR S + 12#64) (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rax) 4) ∧
        g'.rdi = rdq(W, aR S + 16#64)))) hK hA hr
    (vc_150 (by rw [hm.1]; exact E.f16) (by rw [hm.1]; exact E.w12) (fun _ a _ => ⟨a, Or.inl ⟨rfl, rfl⟩⟩)
      (fun _ a b _ => ⟨b, Or.inr ⟨rfl, by rw [hm.1], by rw [a, hm.1]⟩⟩)) ?_
  rintro j' g fl V₁ ⟨gf, ⟨rfl, hV₁⟩ | ⟨rfl, hV₁, gdi⟩⟩ U t₁ hKU hAU hrU hgU -
  · subst V₁ hgU
    have hmU := Fm.fr hm gf
    exact tail62 E hKU hAU hrU hmU.1 hmU.2.2.2.2.2 hIW
  · subst V₁ hgU
    have hmU := Fm.fr hm gf
    have hI1 := E.hI12 W (toBytesLE (BitVec.setWidth 32 Y.cpu.gpr.rax) 4) (toBytesLE_length _ _) hIW
    refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_164 _) tgt_164 E.cD (E.k164 _ hI1)
      (gdi.trans (E.h16 W _ (toBytesLE_length _ _)).symm) ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    have hmZ := fm_ret hmU hsZ hkZ
    refine (c_169 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 62 ∧ V' = W' ∧ Fr Z.cpu.gpr g')
      hKZ hAZ hrZ (vc_169 (by rw [hmZ.1]; exact fun i hi => E.c.hws _ (E.w12 i hi))
        fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₁ hgU₂
    have hm2 := Fm.fr hmZ gf'
    exact tail62 E hKU₂ hAU₂ hrU₂ hm2.1 hm2.2.2.2.2.2 hIZ

/-- From 216: `ReparseData`'s size cleared, `AddError` (`k237`), from its return (242) to 150. -/
theorem from216 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sli_at.add 216) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_216 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 237 ∧
      V' = Vst W (g0.rsi + 128#64) (toBytesLE 0#64 8) ∧ g'.rdi = g0.rdi ∧ g'.rsi = aR S + 16#64 ∧
      Fr Y.cpu.gpr g') hK hA hr
    (vc_216 (by rw [hm.2.2.2.1]; exact E.w128)
      fun _ a b d _ => ⟨rfl, by rw [hm.2.2.2.1], a.trans hm.2.2.1, b.trans hm.2.2.2.2.1, d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gsi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_237 _) tgt_237 E.cA
    (E.k237 _ (E.hI128 W (toBytesLE 0#64 8) (toBytesLE_length _ _) hIW)) ⟨gdi, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  have hmZ := fm_ret hmU hsZ hkZ
  refine (c_242 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 150 ∧ g' = Z.cpu.gpr ∧ V' = W')
    hKZ hAZ hrZ (vc_242 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
  subst V₁
  exact from150 E hKU₂ hAU₂ hrU₂ (by rw [hgU₂]; exact hmZ) hIZ

/-- From 189 (back from the error's code): `ReparseData`'s buffer, null to 216, else `delete []` (`k202`) and from
its return (207) the buffer cleared, to 216. -/
theorem from189 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sli_at.add 189) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_189 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 216 ∨ (j' = 202 ∧ g'.rdi = rdq(W, g0.rsi + 120#64)))) hK hA hr
    (vc_189 (by rw [hm.2.2.2.1]; exact fun i hi => E.c.hws _ (E.w120 i hi)) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ a b _ => ⟨rfl, b, Or.inr ⟨rfl, by rw [a, hm.2.2.2.1]⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with rfl | ⟨rfl, gdi⟩
  · exact from216 E hKU hAU hrU hmU hIW
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_202 _) tgt_202 E.cD (E.k202 _ hIW) gdi ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    have hmZ := fm_ret hmU hsZ hkZ
    refine (c_207 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 216 ∧
        V' = Vst W' (g0.rsi + 120#64) (toBytesLE 0#64 8) ∧ Fr Z.cpu.gpr g') hKZ hAZ hrZ
      (vc_207 (by rw [hmZ.2.2.2.1]; exact E.w120) fun _ a _ => ⟨rfl, by rw [hmZ.2.2.2.1], a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₁ hgU₂
    exact from216 E hKU₂ hAU₂ hrU₂ (Fm.fr hmZ gf') (E.hI120 W' (toBytesLE 0#64 8) (toBytesLE_length _ _) hIZ)

/-- From 137 (back from `GetReparseData`): false to the error's code (`k184`) and 189; true `_totalSize -=
fi.Size` (144, `Seg.s_sub_mr64`), `eax` = 0 (148), to 150. -/
theorem from137 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sli_at.add 137) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_137 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => V' = W ∧ Fr Y.cpu.gpr g' ∧
      (j' = 184 ∨ (j' = 144 ∧ g'.rax = rdq(W, g0.rdx)))) hK hA hr
    (vc_137 (by rw [hm.2.1]; exact E.fx) (fun _ a _ => ⟨rfl, a, Or.inl rfl⟩)
      (fun _ a b _ => ⟨rfl, b, Or.inr ⟨rfl, by rw [a, hm.2.1]⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gf, hpost⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  rcases hpost with rfl | ⟨rfl, gax⟩
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_184 _) tgt_184 E.cE (E.k184 _ hIW) trivial ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from189 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ
  · have he : eaD U 5 96 = g0.rdi + 96#64 := by
      show U.cpu.gpr.get (regOf 5) + BitVec.ofNat 64 96 = _
      rw [show U.cpu.gpr.get (regOf 5) = U.cpu.gpr.rbp from rfl, hmU.2.2.1]
    refine E.c.s_sub_mr64 hKU hAU E.hin (lt_len (by decide)) hrU (sub_144 _) (by rw [he]; exact E.w96) ?_
    rw [he]
    suffices KK : ∀ bs : List Byte, bs.length = 8 → ContG prof F Wl L s₀ o gev gP gE
        (Vst W (g0.rdi + 96#64) bs) (fun Y => Y.cpu.rip = sli_at.add (144 + 4) ∧ Y.cpu.gpr = U.cpu.gpr) from
      KK _ (toBytesLE_length ..)
    intro bs hl
    rintro Y₃ t₃ hK₃ hA₃ ⟨hr₃, hg₃⟩
    refine (c_148 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 150 ∧ V' = Vst W (g0.rdi + 96#64) bs ∧
        Fr Y₃.cpu.gpr g') hK₃ hA₃ hr₃ (vc_148 fun _ a _ => ⟨rfl, rfl, a⟩) ?_
    rintro j' g fl V₁ ⟨rfl, hV₁, gf'⟩ U₂ t₄ hKU₂ hAU₂ hrU₂ hgU₂ -
    subst V₁ hgU₂
    exact from150 E hKU₂ hAU₂ hrU₂ (Fm.fr (by rw [hg₃]; exact hmU) gf') (E.hI96 W bs hl hIW)

/-- From 122 (back from the concatenation): `GetReparseData` (`k132`), from its return 137. -/
theorem from122 (E : Ev prof F Wl L s₀ o gev gP gE fb S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = sli_at.add 122) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  refine (c_122 prof fb).run E.c E.hfs E.hin (fun j' g' _ V' => j' = 132 ∧ V' = W ∧
      g'.rdi = rdq(W, aR S + 16#64) ∧ g'.rsi = g0.rsi + 120#64 ∧ Fr Y.cpu.gpr g') hK hA hr
    (vc_122 (by rw [hm.1]; exact E.f16)
      fun _ a b d _ => ⟨rfl, rfl, by rw [a, hm.1], by rw [b, hm.2.2.2.1], d⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gdi, gsi, gf⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU := Fm.fr hm gf
  refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_132 _) tgt_132 E.cC (E.k132 _ hIW) ⟨gdi, gsi⟩ ?_
  intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
  exact from137 E hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ

end Runs

/-! ## From the entry -/

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `SetLinkInfo (this, dirItem, fi, phyPrefix)` from its entry (`X`'s registers, `S` = their `rsp`, `fb` the `fs`
base): the pushes' slots, the guard's slot, the word at `aR S + 12`, the `call`s' return address slot,
`this->_totalSize` (`this + 96`), `dirItem.ReparseData`'s buffer and size (`dirItem + 120`, `+ 128`) in what the run
may store into; the guard at `fs:0x28`, `SymLinks`, `fi.st_mode`, `fi.Size`, the path's buffer pointer and the
return address readable. The bytes' invariant `I`: of the bytes after the prologue (`hI0`), kept by the stores,
giving the stack (`hI`); the word's store keeps the path's buffer pointer (`h16`). The callees (`KC`): `k117` the
concatenation, `k132` `GetReparseData`, `k164`/`k202` `delete []`, `k184` the error's code, `k237` `AddError`. At
the return address (`kr`): `rsp` 8 above the entry's, the callee-saved registers as they were. -/
theorem sli_ok {fb : Addr} {I : (Addr → Byte) → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}
    (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L sli_at sli)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = sli_at)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (hs5 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8) i))
    (hw : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 40#64) i))
    (f16 : ∀ i < 8, Foot F.data (Addr.add (aR X.cpu.gpr.rsp + 16#64) i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (aR X.cpu.gpr.rsp + 12#64) i))
    (hr8 : ∀ i < 8, Foot Wl (Addr.add (aR X.cpu.gpr.rsp - 8) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (f64 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rdi + 64#64) i))
    (f72 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdx + 72#64) i))
    (fx : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (w96 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rdi + 96#64) i))
    (w120 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsi + 120#64) i))
    (w128 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsi + 128#64) i))
    (hI : ∀ W, I W → Stk fb W X.cpu.gpr.rsp X.cpu.gpr (e₂.add j₂)) (hI0 : I (V0 fb V X.cpu.gpr))
    (hI12 : ∀ W (bs : List Byte), bs.length = 4 → I W → I (Vst W (aR X.cpu.gpr.rsp + 12#64) bs))
    (hI96 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (X.cpu.gpr.rdi + 96#64) bs))
    (hI120 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (X.cpu.gpr.rsi + 120#64) bs))
    (hI128 : ∀ W (bs : List Byte), bs.length = 8 → I W → I (Vst W (X.cpu.gpr.rsi + 128#64) bs))
    (h16 : ∀ W (bs : List Byte), bs.length = 4 →
      rdq(Vst W (aR X.cpu.gpr.rsp + 12#64) bs, aR X.cpu.gpr.rsp + 16#64) = rdq(W, aR X.cpu.gpr.rsp + 16#64))
    (cP : ∃ code : List Byte, CodeIn L 0x44c2b0#64 code ∧ 0 < code.length)
    (cC : ∃ code : List Byte, CodeIn L 0x5a22b0#64 code ∧ 0 < code.length)
    (cD : ∃ code : List Byte, CodeIn L 0x6014f0#64 code ∧ 0 < code.length)
    (cE : ∃ code : List Byte, CodeIn L 0x5a0200#64 code ∧ 0 < code.length)
    (cA : ∃ code : List Byte, CodeIn L 0x5c0170#64 code ∧ 0 < code.length)
    (k117 : KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x44c2b0#64 122 (V0 fb V X.cpu.gpr)
      (fun g => g.rdi = aR X.cpu.gpr.rsp + 16#64 ∧ g.rsi = X.cpu.gpr.rcx ∧ g.rdx = X.cpu.gpr.rdx + 104#64))
    (k132 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x5a22b0#64 137 W
      (fun g => g.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64) ∧ g.rsi = X.cpu.gpr.rsi + 120#64))
    (k164 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6014f0#64 169 W
      (fun g => g.rdi = rdq(W, aR X.cpu.gpr.rsp + 16#64)))
    (k184 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x5a0200#64 189 W (fun _ => True))
    (k202 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x6014f0#64 207 W
      (fun g => g.rdi = rdq(W, X.cpu.gpr.rsi + 120#64)))
    (k237 : ∀ W, I W → KC prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp I 0x5c0170#64 242 W
      (fun g => g.rdi = X.cpu.gpr.rdi ∧ g.rsi = aR X.cpu.gpr.rsp + 16#64))
    (kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
      Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = X.cpu.gpr.rsp + 8 → KS X.cpu.gpr Z'.cpu.gpr → I W →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have E : Ev prof F Wl L s₀ o gev gP gE fb X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I :=
    { c := c, hfs := hfs, hin := hin, hin₂ := hin₂, h₂ := h₂, hI := hI, hcl := hcl,
      fg := fun i hi => c.hws _ (hw i hi), f16 := f16, w12 := w12,
      fb40 := fun i hi => c.hws _ (hs5 i hi), fb32 := fun i hi => c.hws _ (hs4 i hi),
      fb24 := fun i hi => c.hws _ (hs3 i hi), fb16 := fun i hi => c.hws _ (hs2 i hi),
      fb8 := fun i hi => c.hws _ (hs1 i hi), hl := hl, hr8 := hr8, fx := fx, w96 := w96, w120 := w120,
      w128 := w128, hI12 := hI12, hI96 := hI96, hI120 := hI120, hI128 := hI128, h16 := h16,
      cC := cC, cD := cD, cE := cE, cA := cA, k132 := k132, k164 := k164, k184 := k184, k202 := k202,
      k237 := k237, kr := kr }
  -- the prologue, to 62 or to the concatenation's `call`
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => V' = V0 fb V X.cpu.gpr ∧ g'.rsp = aR X.cpu.gpr.rsp ∧
      g'.r15 = X.cpu.gpr.r15 ∧ (j' = 62 ∨ (j' = 117 ∧ Fm X.cpu.gpr.rsp X.cpu.gpr g' ∧
        g'.rdi = aR X.cpu.gpr.rsp + 16#64 ∧ g'.rsi = X.cpu.gpr.rcx ∧ g'.rdx = X.cpu.gpr.rdx + 104#64))) hK hA
    (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl hs1 hs2 hs3 hs4 hs5 hcl hw f64 f72 (fun _ a b _ => ⟨rfl, a, b, Or.inl rfl⟩)
      (fun _ a b d e i m gdi gsi gdx _ => ⟨rfl, a, m, Or.inr ⟨rfl, ⟨a, b, d, e, i, m⟩, gdi, gsi, gdx⟩⟩)) ?_
  rintro j' g fl V₁ ⟨hV₁, gs, g15, hpost⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hpost with rfl | ⟨rfl, hmY, gdi, gsi, gdx⟩
  · exact tail62 E hKY hAY hrY gs g15 hI0
  · refine callK E hKY hAY hrY hmY.1 (lt_len (by decide)) (call_117 _) tgt_117 cP k117 ⟨gdi, gsi, gdx⟩ ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hIZ
    exact from122 E hKZ hAZ hrZ (fm_ret hmY hsZ hkZ) hIZ

end FV7z.Sli
