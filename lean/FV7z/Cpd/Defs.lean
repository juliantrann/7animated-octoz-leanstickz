import FV7z.Cpd.Cuts
import FV7z.Tiny.Tj
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
import FV7z.Ocv.Holds
/-!
# `NCommandLineParser::CParser::~CParser`: the frame and the callees (PLAN.md §M, M1)

7-Zip 26.06's `CParser::~CParser (this)` at `0x5a0500` in `7zzs` (`CPP/Common/CommandLineParser.cpp`; `objdump -d`),
`S` the stack pointer at the entry: `r14`, `r13`, `r12`, `rbp`, `rbx` pushed (`rsp` = `S - 40` after them), the calls'
return addresses at `S - 48`.

- `Fr`: the saved registers and the return address in the bytes; `Kf`: those 48 bytes kept; `Kp`, `Bk`: the
  registers a call keeps; `Rs`: the registers kept by the body (`rsp` below the pushes, `r12` = `this`, `r15`);
  `pk V it k`: `_items[k]`; `pops5`: the registers after the pops.
- `Call1 S f ra A V P`: from `f` with `rsp` = `S - 48`, the return address `ra` at `S - 48`, the arguments `A` and
  the bytes `V`, the run goes on to the goal if it does from every state at `ra` with bytes `V'`, `P V'`, the
  registers a call keeps (`Bk`) and the saved registers and the return address as in `V` (`Kf`); `AtJ j P`: from
  the offset `j` with registers and bytes for which `P` holds, the run goes on to the goal.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Cpd
/-! ## The frame and the registers -/

/-- The saved registers of `g₀` and the return address `ra` in the bytes `V`. -/
def Fr (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop :=
  rdq(V, g₀.rsp - 8) = g₀.r14 ∧ rdq(V, g₀.rsp - 8 - 8) = g₀.r13 ∧ rdq(V, g₀.rsp - 8 - 8 - 8) = g₀.r12 ∧
    rdq(V, g₀.rsp - 8 - 8 - 8 - 8) = g₀.rbp ∧ rdq(V, g₀.rsp - 8 - 8 - 8 - 8 - 8) = g₀.rbx ∧ rdq(V, g₀.rsp) = ra

/-- The 48 bytes from `S - 40` as in `V`. -/
def Kf (S : Addr) (V V' : Addr → Byte) : Prop :=
  rdq(V', S - 8) = rdq(V, S - 8) ∧ rdq(V', S - 8 - 8) = rdq(V, S - 8 - 8) ∧
    rdq(V', S - 8 - 8 - 8) = rdq(V, S - 8 - 8 - 8) ∧ rdq(V', S - 8 - 8 - 8 - 8) = rdq(V, S - 8 - 8 - 8 - 8) ∧
    rdq(V', S - 8 - 8 - 8 - 8 - 8) = rdq(V, S - 8 - 8 - 8 - 8 - 8) ∧ rdq(V', S) = rdq(V, S)

theorem Fr.kf {g₀ : Gprs} {ra : Addr} {V V' : Addr → Byte} (h : Fr g₀ ra V) (k : Kf g₀.rsp V V') : Fr g₀ ra V' :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1, k.2.2.2.1.trans h.2.2.2.1,
    k.2.2.2.2.1.trans h.2.2.2.2.1, k.2.2.2.2.2.trans h.2.2.2.2.2⟩

/-- The registers a function keeps. -/
def Kp (g₀ g : Gprs) : Prop :=
  g.rbx = g₀.rbx ∧ g.rbp = g₀.rbp ∧ g.r12 = g₀.r12 ∧ g.r13 = g₀.r13 ∧ g.r14 = g₀.r14 ∧ g.r15 = g₀.r15

/-- The registers after a `ret`, from those at the entry. -/
def Bk (g₀ g : Gprs) : Prop := g.rsp = g₀.rsp + 8 ∧ Kp g₀ g

/-- The registers kept from 170 on: `rsp` below the pushes, `r12` = `this`, `r15`. -/
def Rs (g₀ g : Gprs) : Prop := g.rsp = g₀.rsp - 8 - 8 - 8 - 8 - 8 ∧ g.r12 = g₀.rdi ∧ g.r15 = g₀.r15

/-- `_items[k]`. -/
abbrev pk (V : Addr → Byte) (it : BitVec 64) (k : Nat) : BitVec 64 := rdq(V, it + BitVec.ofNat 64 (8 * k))

/-- The registers after `pop rbx; pop rbp; pop r12; pop r13; pop r14`. -/
abbrev pops5 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      rbx := rdq(V, g.rsp),
      rbp := rdq(V, g.rsp + 8),
      rsp := g.rsp + 8 + 8 + 8 + 8 + 8,
      r12 := rdq(V, g.rsp + 8 + 8),
      r13 := rdq(V, g.rsp + 8 + 8 + 8),
      r14 := rdq(V, g.rsp + 8 + 8 + 8 + 8) }

theorem a5s (x : Addr) : x - 8 - 8 - 8 - 8 - 8 + 8 = x - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a4s (x : Addr) : x - 8 - 8 - 8 - 8 + 8 = x - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a3s (x : Addr) : x - 8 - 8 - 8 + 8 = x - 8 - 8 := BitVec.sub_add_cancel _ _
theorem a2s (x : Addr) : x - 8 - 8 + 8 = x - 8 := BitVec.sub_add_cancel _ _
theorem a1s (x : Addr) : x - 8 + 8 = x := BitVec.sub_add_cancel _ _

/-- What the code asks of a function it calls at `f` with the return address `ra` (pushed at `S - 48`), the
arguments `A` and the bytes `V`: the run goes on to the goal if it does from every state at `ra` with bytes `V'`
for which `P` holds, the registers a call keeps and the saved registers and the return address as in `V`. -/
def Call1 (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S f ra : Addr) (A : Gprs → Prop) (V : Addr → Byte) (P : (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (t : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst V (S - 8 - 8 - 8 - 8 - 8 - 8) (toBytesLE ra 8)) →
    Y.cpu.rip = f → Y.cpu.gpr.rsp = S - 8 - 8 - 8 - 8 - 8 - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (V' : Addr → Byte) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → P V' →
      Z.cpu.rip = ra → Bk Y.cpu.gpr Z.cpu.gpr → Kf S V V' → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- From offset `j` with registers and bytes for which `P` holds, the run goes on to the goal. -/
def AtJ (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop) (j : Nat)
    (P : Gprs → (Addr → Byte) → Prop) : Prop :=
  ∀ (Y : State) (V : Addr → Byte) (t : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V →
    Y.cpu.rip = cpd_at.add j → P Y.cpu.gpr V → GoG prof L o gev gP gE Y t

end FV7z.Cpd
