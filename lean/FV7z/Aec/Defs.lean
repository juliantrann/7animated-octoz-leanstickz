import FV7z.Aec.Cuts
import FV7z.Api.Holds
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `CArchiveExtractCallback::CArchiveExtractCallback`: the instructions outside the blocks, the frame (PLAN.md §M, M1)

7-Zip 26.06's `CArchiveExtractCallback::CArchiveExtractCallback ()` (`CPP/7zip/UI/Common/ArchiveExtractCallback.cpp`;
`objdump -d`) at `0x5b0040` in `7zzs`: `this` = `rdi` (`rbx` after 23), 704 bytes of fields stored. `S` the stack
pointer at the entry: five pushes (`r14`, `r13`, `r12`, `rbp`, `rbx`), no frame of its own (`aR S`). The callees: the
string set-up at `0x44c360` (`AString::AString ()`, `Nst`; the `call`s at 203, 215, 334, 400, 412, 555),
`UString::UString ()` at `0x44d3e0` (252, 286, 298, 652), `operator new` at `0x602970` (521) and the
`CLocalProgress` constructor at `0x461fa0` (532); `add dword [rbp + 8], 1` (537, `Seg.s_add_mi32`) is the new
object's `AddRef`.

- The `call`s (`call_*`, `tgt_*`), the `add` (`add_537`), the `ret` (`ret_687`).
- `aR`, `r1`..`r5`: the frame; `P5`: the bytes after the pushes; `St`: the stack the run keeps; `Nw`: what
  `operator new` gives (the new object's `RefCount` to store into); `KC`: a callee as a continuation (as in Cps).
- `Ev`: the hypotheses of the runs; `callK`: a `call` and the run from its return.
- `astep`: one step of the closers of the pieces.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Aec
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of the string set-up (203). -/
def pc203 : List Byte := [0xe8, 0x50, 0xc2, 0xe9, 0xff]
theorem pc203_0 : ∀ feat, Dec feat pc203 0 (FV7z.mk .call 64 [.rel 18446744073708094032] 5) := by dec_rfl
theorem wc_203 : pc203 <+: aec.drop 203 := by decide +kernel
theorem call_203 (feat : Features) : Dec feat aec 203 (FV7z.mk .call 64 [.rel 18446744073708094032] 5) :=
  Dec.shift (j := 203) (k := 0) (pc203_0 feat) wc_203 (Nat.zero_le _)
theorem tgt_203 : aec_at.add (203 + 5) + BitVec.ofNat 64 18446744073708094032 = 0x44c360#64 := by decide

/-- The `call` of the string set-up (215). -/
def pc215 : List Byte := [0xe8, 0x44, 0xc2, 0xe9, 0xff]
theorem pc215_0 : ∀ feat, Dec feat pc215 0 (FV7z.mk .call 64 [.rel 18446744073708094020] 5) := by dec_rfl
theorem wc_215 : pc215 <+: aec.drop 215 := by decide +kernel
theorem call_215 (feat : Features) : Dec feat aec 215 (FV7z.mk .call 64 [.rel 18446744073708094020] 5) :=
  Dec.shift (j := 215) (k := 0) (pc215_0 feat) wc_215 (Nat.zero_le _)
theorem tgt_215 : aec_at.add (215 + 5) + BitVec.ofNat 64 18446744073708094020 = 0x44c360#64 := by decide

/-- The `call` of `UString::UString ()` (252). -/
def pc252 : List Byte := [0xe8, 0x9f, 0xd2, 0xe9, 0xff]
theorem pc252_0 : ∀ feat, Dec feat pc252 0 (FV7z.mk .call 64 [.rel 18446744073708098207] 5) := by dec_rfl
theorem wc_252 : pc252 <+: aec.drop 252 := by decide +kernel
theorem call_252 (feat : Features) : Dec feat aec 252 (FV7z.mk .call 64 [.rel 18446744073708098207] 5) :=
  Dec.shift (j := 252) (k := 0) (pc252_0 feat) wc_252 (Nat.zero_le _)
theorem tgt_252 : aec_at.add (252 + 5) + BitVec.ofNat 64 18446744073708098207 = 0x44d3e0#64 := by decide

/-- The `call` of `UString::UString ()` (286). -/
def pc286 : List Byte := [0xe8, 0x7d, 0xd2, 0xe9, 0xff]
theorem pc286_0 : ∀ feat, Dec feat pc286 0 (FV7z.mk .call 64 [.rel 18446744073708098173] 5) := by dec_rfl
theorem wc_286 : pc286 <+: aec.drop 286 := by decide +kernel
theorem call_286 (feat : Features) : Dec feat aec 286 (FV7z.mk .call 64 [.rel 18446744073708098173] 5) :=
  Dec.shift (j := 286) (k := 0) (pc286_0 feat) wc_286 (Nat.zero_le _)
theorem tgt_286 : aec_at.add (286 + 5) + BitVec.ofNat 64 18446744073708098173 = 0x44d3e0#64 := by decide

/-- The `call` of `UString::UString ()` (298). -/
def pc298 : List Byte := [0xe8, 0x71, 0xd2, 0xe9, 0xff]
theorem pc298_0 : ∀ feat, Dec feat pc298 0 (FV7z.mk .call 64 [.rel 18446744073708098161] 5) := by dec_rfl
theorem wc_298 : pc298 <+: aec.drop 298 := by decide +kernel
theorem call_298 (feat : Features) : Dec feat aec 298 (FV7z.mk .call 64 [.rel 18446744073708098161] 5) :=
  Dec.shift (j := 298) (k := 0) (pc298_0 feat) wc_298 (Nat.zero_le _)
theorem tgt_298 : aec_at.add (298 + 5) + BitVec.ofNat 64 18446744073708098161 = 0x44d3e0#64 := by decide

/-- The `call` of the string set-up (334). -/
def pc334 : List Byte := [0xe8, 0xcd, 0xc1, 0xe9, 0xff]
theorem pc334_0 : ∀ feat, Dec feat pc334 0 (FV7z.mk .call 64 [.rel 18446744073708093901] 5) := by dec_rfl
theorem wc_334 : pc334 <+: aec.drop 334 := by decide +kernel
theorem call_334 (feat : Features) : Dec feat aec 334 (FV7z.mk .call 64 [.rel 18446744073708093901] 5) :=
  Dec.shift (j := 334) (k := 0) (pc334_0 feat) wc_334 (Nat.zero_le _)
theorem tgt_334 : aec_at.add (334 + 5) + BitVec.ofNat 64 18446744073708093901 = 0x44c360#64 := by decide

/-- The `call` of the string set-up (400). -/
def pc400 : List Byte := [0xe8, 0x8b, 0xc1, 0xe9, 0xff]
theorem pc400_0 : ∀ feat, Dec feat pc400 0 (FV7z.mk .call 64 [.rel 18446744073708093835] 5) := by dec_rfl
theorem wc_400 : pc400 <+: aec.drop 400 := by decide +kernel
theorem call_400 (feat : Features) : Dec feat aec 400 (FV7z.mk .call 64 [.rel 18446744073708093835] 5) :=
  Dec.shift (j := 400) (k := 0) (pc400_0 feat) wc_400 (Nat.zero_le _)
theorem tgt_400 : aec_at.add (400 + 5) + BitVec.ofNat 64 18446744073708093835 = 0x44c360#64 := by decide

/-- The `call` of the string set-up (412). -/
def pc412 : List Byte := [0xe8, 0x7f, 0xc1, 0xe9, 0xff]
theorem pc412_0 : ∀ feat, Dec feat pc412 0 (FV7z.mk .call 64 [.rel 18446744073708093823] 5) := by dec_rfl
theorem wc_412 : pc412 <+: aec.drop 412 := by decide +kernel
theorem call_412 (feat : Features) : Dec feat aec 412 (FV7z.mk .call 64 [.rel 18446744073708093823] 5) :=
  Dec.shift (j := 412) (k := 0) (pc412_0 feat) wc_412 (Nat.zero_le _)
theorem tgt_412 : aec_at.add (412 + 5) + BitVec.ofNat 64 18446744073708093823 = 0x44c360#64 := by decide

/-- The `call` of `operator new` (521). -/
def pc521 : List Byte := [0xe8, 0x22, 0x27, 0x05, 0x00]
theorem pc521_0 : ∀ feat, Dec feat pc521 0 (FV7z.mk .call 64 [.rel 337698] 5) := by dec_rfl
theorem wc_521 : pc521 <+: aec.drop 521 := by decide +kernel
theorem call_521 (feat : Features) : Dec feat aec 521 (FV7z.mk .call 64 [.rel 337698] 5) :=
  Dec.shift (j := 521) (k := 0) (pc521_0 feat) wc_521 (Nat.zero_le _)
theorem tgt_521 : aec_at.add (521 + 5) + BitVec.ofNat 64 337698 = 0x602970#64 := by decide

/-- The `call` of `CLocalProgress::CLocalProgress ()` (532). -/
def pc532 : List Byte := [0xe8, 0x47, 0x1d, 0xeb, 0xff]
theorem pc532_0 : ∀ feat, Dec feat pc532 0 (FV7z.mk .call 64 [.rel 18446744073708182855] 5) := by dec_rfl
theorem wc_532 : pc532 <+: aec.drop 532 := by decide +kernel
theorem call_532 (feat : Features) : Dec feat aec 532 (FV7z.mk .call 64 [.rel 18446744073708182855] 5) :=
  Dec.shift (j := 532) (k := 0) (pc532_0 feat) wc_532 (Nat.zero_le _)
theorem tgt_532 : aec_at.add (532 + 5) + BitVec.ofNat 64 18446744073708182855 = 0x461fa0#64 := by decide

/-- The `call` of the string set-up (555). -/
def pc555 : List Byte := [0xe8, 0xf0, 0xc0, 0xe9, 0xff]
theorem pc555_0 : ∀ feat, Dec feat pc555 0 (FV7z.mk .call 64 [.rel 18446744073708093680] 5) := by dec_rfl
theorem wc_555 : pc555 <+: aec.drop 555 := by decide +kernel
theorem call_555 (feat : Features) : Dec feat aec 555 (FV7z.mk .call 64 [.rel 18446744073708093680] 5) :=
  Dec.shift (j := 555) (k := 0) (pc555_0 feat) wc_555 (Nat.zero_le _)
theorem tgt_555 : aec_at.add (555 + 5) + BitVec.ofNat 64 18446744073708093680 = 0x44c360#64 := by decide

/-- The `call` of `UString::UString ()` (652). -/
def pc652 : List Byte := [0xe8, 0x0f, 0xd1, 0xe9, 0xff]
theorem pc652_0 : ∀ feat, Dec feat pc652 0 (FV7z.mk .call 64 [.rel 18446744073708097807] 5) := by dec_rfl
theorem wc_652 : pc652 <+: aec.drop 652 := by decide +kernel
theorem call_652 (feat : Features) : Dec feat aec 652 (FV7z.mk .call 64 [.rel 18446744073708097807] 5) :=
  Dec.shift (j := 652) (k := 0) (pc652_0 feat) wc_652 (Nat.zero_le _)
theorem tgt_652 : aec_at.add (652 + 5) + BitVec.ofNat 64 18446744073708097807 = 0x44d3e0#64 := by decide

[131, 69, 8, 1] 195
/-- `add dword [rbp + 8], 1` (537). -/
def pad : List Byte := [0x83, 0x45, 0x08, 0x01]
theorem pad_0 : ∀ feat, Dec feat pad 0 (FV7z.mk .add 32 [.mem (mbd 5 8 32), .imm 32 1] 4) := by dec_rfl
theorem w_537 : pad <+: aec.drop 537 := by decide +kernel
theorem add_537 (feat : Features) : Dec feat aec 537 (FV7z.mk .add 32 [.mem (mbd 5 8 32), .imm 32 1] 4) :=
  Dec.shift (j := 537) (k := 0) (pad_0 feat) w_537 (Nat.zero_le _)

/-- The `ret` (687). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_687 : pret <+: aec.drop 687 := by decide +kernel
theorem ret_687 (feat : Features) : Dec feat aec 687 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 687) (k := 0) (pret_0 feat) w_687 (Nat.zero_le _)

/-! ## The frame -/

/-- The stack pointer after the five pushes. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8

theorem r1 (S : Addr) : aR S + 8 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem r2 (S : Addr) : S - 8 - 8 - 8 - 8 + 8 = S - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem r3 (S : Addr) : S - 8 - 8 - 8 + 8 = S - 8 - 8 := BitVec.sub_add_cancel _ _
theorem r4 (S : Addr) : S - 8 - 8 + 8 = S - 8 := BitVec.sub_add_cancel _ _
theorem r5 (S : Addr) : S - 8 + 8 = S := BitVec.sub_add_cancel _ _

/-- The bytes after the five pushes. -/
abbrev P5 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r14 8)) (g.rsp - 8 - 8) (toBytesLE g.r13 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbp 8))
    (aR g.rsp) (toBytesLE g.rbx 8)

/-- The stack (`ra` the return address): the five saved registers, the return address. -/
abbrev St (W : Addr → Byte) (S : Addr) (g0 : Gprs) (ra : Addr) : Prop :=
  rdq(W, aR S) = g0.rbx ∧ rdq(W, S - 8 - 8 - 8 - 8) = g0.rbp ∧ rdq(W, S - 8 - 8 - 8) = g0.r12 ∧
    rdq(W, S - 8 - 8) = g0.r13 ∧ rdq(W, S - 8) = g0.r14 ∧ rdq(W, S) = ra

/-- What `operator new` gives at `p`: the 4 bytes at `p + 8` (`RefCount`) to store into, the stores keeping `I`. -/
abbrev Nw (Wl : List Rgn) (I : (Addr → Byte) → Prop) (p : Addr) : Prop :=
  (∀ i < 4, Foot Wl (Addr.add (p + 8#64) i)) ∧
    ∀ (W : Addr → Byte) (bs : List Byte), bs.length = 4 → I W → I (Vst W (p + 8#64) bs)

/-- A callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (aec_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = aec_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs from the cut points (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂`
the return address, `I` the invariant of the bytes): the stores into the object at `this` = `g0.rdi` (its 704 bytes)
keep `I` (`hcl`), and so do the callees, from any return offset. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) : Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L aec_at aec
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → St W S g0 (e₂.add j₂)
  hob : ∀ (k : BitVec 64) (n : Nat), k.toNat + n ≤ 704 → ∀ i < n, Foot Wl (Addr.add (g0.rdi + k) i)
  hcl : ∀ (W : Addr → Byte) (k : BitVec 64) (n : Nat) (bs : List Byte), bs.length = n → k.toNat + n ≤ 704 →
    I W → I (Vst W (g0.rdi + k) bs)
  hs1 : ∀ i < 8, Foot Wl (Addr.add (S - 8) i)
  hs2 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8) i)
  hs3 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8) i)
  hs4 : ∀ i < 8, Foot Wl (Addr.add (S - 8 - 8 - 8 - 8) i)
  hs5 : ∀ i < 8, Foot Wl (Addr.add (aR S) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  cA : ∃ code : List Byte, CodeIn L 0x44c360#64 code ∧ 0 < code.length
  cU : ∃ code : List Byte, CodeIn L 0x44d3e0#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x602970#64 code ∧ 0 < code.length
  cL : ∃ code : List Byte, CodeIn L 0x461fa0#64 code ∧ 0 < code.length
  kA : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44c360#64 j W (fun _ => True) (fun _ => True)
  kU : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x44d3e0#64 j W (fun _ => True) (fun _ => True)
  kN : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x602970#64 j W (fun _ => True) (fun g => Nw Wl I g.rax)
  kL : ∀ j W, I W → KC prof F Wl L s₀ o gev gP gE S I 0x461fa0#64 j W (fun _ => True) (fun _ => True)
  kr : ∀ (W : Addr → Byte) (Z' : State) (t' : Nat), KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W →
    Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr → I W → GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = aec_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < aec.length) (hd : Dec prof.feat aec j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : aec_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = aec_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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
macro "astep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | apply And.intro
  | intro _)

end FV7z.Aec
