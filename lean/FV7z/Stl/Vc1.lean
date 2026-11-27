import FV7z.Stl.Steps
import FV7z.Mcn.Vc
/-!
# `____strtoul_l_internal`: the straight pieces, part 1 (PLAN.md §M, M1)

The pieces of glibc 2.31's `____strtoul_l_internal (nptr, endptr, base, group, loc)` (at `0x6238b0`; `rdi = p`,
`rsi = E`, `edx = base`, `ecx = group`, `r8 = loc`). After the prologue (six pushes, `sub rsp, 0x28`, `S88`):
`r13 = p`, `r14 = 0`, `[rsp + 8] = E`. The scanner's position is `rbx`, its byte `cl`; in the digit loop the position
is `rdi`, `r10` the `toupper` table (`CU`, the qword at `0x7914d8`), `r11` the ctype table (`CB`, at `0x7914c8`),
`rbp = 0`.

Each lemma states one cut point's piece; where the way out does not matter to the proof, its post is a disjunction
of the exits (with the branch's condition when a later read needs it), so no branch condition has to be given in
the form the `wp` prints it. The result value is not followed.

- `vc_0`: the pushes, the `E` slot, the base check (to 432), the first byte; a space to 80, else to 99.
- `vc_80`: the next byte; a space to 80, else 99.
  `vc_99z`, `vc_99n`: no byte (to 448 if `E = 0`, else 790), the sign, to 133.
- `vc_150`: base 10 (`eax = 8`), to 171. `vc_216`, `vc_223`: `CU`, `CB`, `rdi = rbx`, to the digit loop (296).
- the digit loop: `vc_296` (a digit or a letter to 332, else 368), `vc_332` (to 368, 265 or 345), `vc_265`,
  `vc_345` (the next byte; 0 ends at 368), `vc_291` (to 296).
- `vc_368z`, `vc_368n`: no digit (to 748), else the end stored at `E` if `E ≠ 0`, to 390.
- `vc_432` (`errno = EINVAL`), `vc_448` (the pops, to the `ret` at 462), `vc_745`, `vc_790` (`*E = p`),
  `vc_927`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Mcn (fr6)
set_option linter.unusedVariables false
namespace FV7z.Stl

variable {F : Footprint} {Wl : List Rgn}

/-- The `rsp` after the prologue (six pushes, `sub rsp, 0x28`). -/
abbrev S88 (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8 - 8 - 40#64

/-- A byte read. -/
abbrev rb (V : Addr → Byte) (a : Addr) : BitVec 8 := ofBytesLE 8 (List.map V (byteAddrs a 1))

/-- The bytes after the prologue: the pushes and `E` at `S88 S + 8`. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (fr6 V g.rsp g.r15 g.r14 g.r13 g.r12 g.rbp g.rbx) (S88 g.rsp + 8#64) (toBytesLE g.rsi 8)

/-- The locale's ctype table `B` (the qword at `loc + 104`). -/
abbrev Bt (V : Addr → Byte) (g : Gprs) : Addr := rdq(V, g.r8 + 104#64)

/-- The `toupper` and ctype tables of the digit loop. -/
abbrev Cu (V : Addr → Byte) : Addr := rdq(V, 7935192#64)
abbrev Cb (V : Addr → Byte) : Addr := rdq(V, 7935176#64)

/-- The registers the digit loop keeps. -/
abbrev Lg (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r10 = g.r10 ∧ g'.r11 = g.r11 ∧ g'.r13 = g.r13 ∧
    g'.r14 = g.r14

set_option maxHeartbeats 4000000 in
/-- The prologue, the base check, the first byte. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hc : BitVec.setWidth 32 g.rcx = 0#32)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (w3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (w4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (w5 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8) i))
    (w6 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8 - 8 - 8) i))
    (w7 : ∀ i < 8, Foot Wl (Addr.add (S88 g.rsp + 8#64) i)) (fp : ∀ i < 1, Foot F.data (Addr.add g.rdi i))
    (f104 : ∀ i < 8, Foot F.data (Addr.add (g.r8 + 104#64) i))
    (fB : ∀ i < 1, Foot F.data
      (Addr.add (Bt (V1 V g) g + BitVec.signExtend 64 (rb (V1 V g) g.rdi) * 2#64 + 1#64) i)) :
    W_0 fb F Wl (fun j g' _ V' => V' = V1 V g ∧ g'.rsp = S88 g.rsp ∧ g'.r13 = g.rdi ∧ g'.r14 = 0#64 ∧
      g'.rdx = g.rdx ∧ (j = 432 ∨ (g'.rbx = g.rdi ∧ g'.rsi = Bt (V1 V g) g ∧
        g'.rcx = BitVec.signExtend 64 (rb (V1 V g) g.rdi) ∧ (j = 99 ∨ (j = 80 ∧
          (rb (V1 V g) (Bt (V1 V g) g + BitVec.signExtend 64 (rb (V1 V g) g.rdi) * 2#64 + 1#64) &&& 32#8 == 0)
            = false))))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [S88, V1, Bt, rb] at hc w1 w2 w3 w4 w5 w6 w7 fp f104 fB ⊢
  mcx +contextual [W_0, W_40, W_49, W_58, o0, o1, o2, o3, fr6, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr,
    Op.testmi, Op.stfi, Op.ldzxa, Op.sxr, hc, w1, w2, w3, w4, w5, w6, w7, fp, f104, fB]

set_option maxHeartbeats 2000000 in
/-- The space loop: the next byte. -/
theorem vc_80 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 1, Foot F.data (Addr.add (g.rbx + 1#64) i))
    (f2 : ∀ i < 1, Foot F.data (Addr.add (g.rsi + BitVec.signExtend 64 (rb V (g.rbx + 1#64)) * 2#64 + 1#64) i)) :
    W_80 fb F Wl (fun j g' _ V' => V' = V ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx + 1#64 ∧ g'.rsi = g.rsi ∧
      g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.rdx = g.rdx ∧ g'.rcx = BitVec.signExtend 64 (rb V (g.rbx + 1#64)) ∧
      (j = 99 ∨ (j = 80 ∧
        (!rb V (g.rsi + BitVec.signExtend 64 (rb V (g.rbx + 1#64)) * 2#64 + 1#64) &&& 32#8 == 0) = true))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb] at f1 f2 ⊢
  mcx +contextual [W_80, o4, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa,
    Op.sxr, f1, f2]

/-- The ways from 99 to 133: the sign `-` (`[rsp + 20] = 1`), `+`, or none (`[rsp + 20] = 0`). -/
abbrev P133 (V : Addr → Byte) (g g' : Gprs) (V' : Addr → Byte) : Prop :=
  (V' = Vst V (g.rsp + 20#64) (toBytesLE (1#32) 4) ∧ g'.rbx = g.rbx + 1#64 ∧
      g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (rb V (g.rbx + 1#64)))) ∨
    (V' = Vst V (g.rsp + 20#64) (toBytesLE (0#32) 4) ∧ g'.rbx = g.rbx + 1#64 ∧
      g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (rb (Vst V (g.rsp + 20#64) (toBytesLE (0#32) 4))
        (g.rbx + 1#64)))) ∨
    (V' = Vst V (g.rsp + 20#64) (toBytesLE (0#32) 4) ∧ g' = g)

set_option maxHeartbeats 2000000 in
/-- `E = 0`: no byte to 448, or the sign; to 133. -/
theorem vc_99z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : rdq(V, g.rsp + 8#64) = 0#64)
    (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f1m : BitVec.setWidth 8 g.rcx = 45#8 → ∀ i < 1, Foot F.data (Addr.add (g.rbx + 1#64) i))
    (f1p : BitVec.setWidth 8 g.rcx = 43#8 → ∀ i < 1, Foot F.data (Addr.add (g.rbx + 1#64) i))
    (w20 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 20#64) i)) :
    W_99 fb F Wl (fun j g' _ V' => g'.rsp = g.rsp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.rdx = g.rdx ∧
      ((j = 448 ∧ V' = V) ∨
        (j = 133 ∧ (BitVec.setWidth 8 g.rcx &&& BitVec.setWidth 8 g.rcx == 0) = false ∧
          P133 V g g' V'))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb, P133] at hz fE f1m f1p w20 ⊢
  mcx +contextual [W_99, W_107, W_116, W_496, W_672, W_969, W_981, o5, o6, o7, o38, o41, o43, o52, Op.ldsxq,
    Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.sxr, Op.cmpm, hz, fE, f1m, f1p, w20]

set_option maxHeartbeats 2000000 in
/-- `E ≠ 0`: no byte to 790, or the sign; to 133. -/
theorem vc_99n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hn : ¬ rdq(V, g.rsp + 8#64) = 0#64)
    (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f1m : BitVec.setWidth 8 g.rcx = 45#8 → ∀ i < 1, Foot F.data (Addr.add (g.rbx + 1#64) i))
    (f1p : BitVec.setWidth 8 g.rcx = 43#8 → ∀ i < 1, Foot F.data (Addr.add (g.rbx + 1#64) i))
    (w20 : ∀ i < 4, Foot Wl (Addr.add (g.rsp + 20#64) i)) :
    W_99 fb F Wl (fun j g' _ V' => g'.rsp = g.rsp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.rdx = g.rdx ∧
      ((j = 790 ∧ V' = V ∧ g' = g) ∨
        (j = 133 ∧ (BitVec.setWidth 8 g.rcx &&& BitVec.setWidth 8 g.rcx == 0) = false ∧
          P133 V g g' V'))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [rb, P133] at hn fE f1m f1p w20 ⊢
  mcx +contextual [W_99, W_107, W_116, W_496, W_672, W_969, W_981, o5, o6, o7, o38, o41, o43, o52, Op.ldsxq,
    Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.sxr, Op.cmpm, hn, fE, f1m, f1p, w20]

/-- Base 10 (or 0 without a `0`): `eax = 8`, `edx = 10`; to 171. -/
theorem vc_150 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hr : g.r14 = 0#64) :
    W_150 fb F Wl (fun j g' _ V' => j = 171 ∧ V' = V ∧ g'.rax = 8#64 ∧ g'.rdx = 10#64 ∧ g'.rbp = 0#64 ∧
      g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rcx = g.rcx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hr ⊢
  mcx +contextual [W_150, W_159, o10, o11, hr]

/-- `r10 = CU`; to 223. -/
theorem vc_216 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fU : ∀ i < 8, Foot F.data (Addr.add 7935192#64 i)) :
    W_216 fb F Wl (fun j g' _ V' => j = 223 ∧ V' = V ∧ g'.r10 = Cu V ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧
      g'.rcx = g.rcx ∧ g'.rbp = g.rbp ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cu] at fU ⊢
  mcx +contextual [W_216, o14, Op.ldsxq, Op.ldzx, Op.lda, fU]

/-- `r11 = CB`, `[rsp + 24] = rbp - 1`, `rdi = rbx`; to the digit loop (296). -/
theorem vc_223 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fC : ∀ i < 8, Foot F.data (Addr.add 7935176#64 i)) (w24 : ∀ i < 8, Foot Wl (Addr.add (g.rsp + 24#64) i)) :
    W_223 fb F Wl (fun j g' _ V' => j = 296 ∧
      V' = Vst V (g.rsp + 24#64) (toBytesLE (g.rbp + 18446744073709551615#64) 8) ∧ g'.rdi = g.rbx ∧
      g'.r11 = Cb V ∧ g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rcx = g.rcx ∧ g'.rbp = g.rbp ∧ g'.r10 = g.r10 ∧
      g'.r13 = g.r13 ∧ g'.r14 = g.r14) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Cb] at fC w24 ⊢
  mcx +contextual [W_223, o15, Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.sxr, fC, w24]

/-- The full list of the pieces' instructions, with the two `Gprs` steps `sk0x` (`cdqe`) and `ite_mk0` (`cmov`
to `rax`). -/
theorem sk0x (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15).set 0 v =
      Gprs.mk v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := rfl

theorem ite_mk0 (c : Prop) [Decidable c] (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 v : BitVec 64) :
    (if c then Gprs.mk v a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      else Gprs.mk a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) =
    Gprs.mk (if c then v else a0) a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 := by
  split <;> rfl

macro "stlx" cfg:Lean.Parser.Tactic.optConfig "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| mcx $cfg [Op.ldsxq, Op.ldzx, Op.lda, Op.lea, Op.cmpmi, Op.zxr, Op.testmi, Op.stfi, Op.ldzxa, Op.cdqe,
    Op.sxr, Op.neg, Op.imul64, Op.cmpm, Op.cmov64, FV7z.Stl.sk0x, FV7z.Stl.ite_mk0, $ls,*])

set_option linter.unusedSimpArgs false

set_option maxHeartbeats 2000000 in
/-- The digit loop: a digit or a letter to 332, else 368 (`rbp = 0`: never to 512). -/
theorem vc_296 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hbp : g.rbp = 0#64)
    (fC : ∀ i < 1, Foot F.data
      (Addr.add (g.r11 + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 g.rcx)) * 2#64 + 1#64) i))
    (fU : ∀ i < 4, Foot F.data
      (Addr.add (g.r10 + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 g.rcx)) * 4#64) i)) :
    W_296 fb F Wl (fun j g' _ V' => (j = 332 ∨ j = 368) ∧ V' = V ∧ Lg g g' ∧ g'.rdi = g.rdi) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lg] at hbp fC fU ⊢
  stlx +contextual [W_296, W_305, W_314, W_317, W_325, o20, o21, o22, o23, o24, hbp, fC, fU]

set_option maxHeartbeats 2000000 in
/-- To 368 (not a digit of the base), 265 (no overflow) or 345. -/
theorem vc_332 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f18 : ∀ i < 1, Foot F.data (Addr.add (g.rsp + 18#64) i)) :
    W_332 fb F Wl (fun j g' _ V' => (j = 368 ∨ j = 265 ∨ j = 345) ∧ V' = V ∧ Lg g g' ∧ g'.rdi = g.rdi)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lg] at f18 ⊢
  stlx +contextual [W_332, W_340, W_256, W_258, o16, o25, o26, f18]

set_option maxHeartbeats 2000000 in
/-- The value times the base plus the digit; the next byte: 0 to 368, else 291. -/
theorem vc_265 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 1#64) i)) :
    W_265 fb F Wl (fun j g' _ V' => V' = V ∧ Lg g g' ∧ g'.rdi = g.rdi + 1#64 ∧
      g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (rb V (g.rdi + 1#64))) ∧ (j = 368 ∨ (j = 291 ∧
        (BitVec.setWidth 8 (BitVec.setWidth 32 (rb V (g.rdi + 1#64))) &&&
          BitVec.setWidth 8 (BitVec.setWidth 32 (rb V (g.rdi + 1#64))) == 0) = false))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lg, rb] at f1 ⊢
  stlx +contextual [W_265, W_279, o17, o18, f1]

set_option maxHeartbeats 2000000 in
/-- Overflow (`r9d = 1`); the next byte: not 0 to 291, else 368. -/
theorem vc_345 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (f1 : ∀ i < 1, Foot F.data (Addr.add (g.rdi + 1#64) i)) :
    W_345 fb F Wl (fun j g' _ V' => V' = V ∧ Lg g g' ∧ g'.rdi = g.rdi + 1#64 ∧
      g'.rcx = BitVec.setWidth 64 (BitVec.setWidth 32 (rb V (g.rdi + 1#64))) ∧ (j = 368 ∨ (j = 291 ∧
        (!BitVec.setWidth 8 (BitVec.setWidth 32 (rb V (g.rdi + 1#64))) &&&
          BitVec.setWidth 8 (BitVec.setWidth 32 (rb V (g.rdi + 1#64))) == 0) = true))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Lg, rb] at f1 ⊢
  stlx +contextual [W_345, W_366, o27, o28, f1]

/-- `rdi = r14` (never: `r14 = 0`) to 368, else 296. -/
theorem vc_291 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_291 fb F Wl (fun j g' _ V' => (j = 368 ∨ j = 296) ∧ V' = V ∧ g' = g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stlx +contextual [W_291, o19]

set_option maxHeartbeats 2000000 in
/-- No digit: to 748; else (`E = 0`) to 390. -/
theorem vc_368z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : rdq(V, g.rsp + 8#64) = 0#64)
    (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i)) :
    W_368 fb F Wl (fun j g' _ V' => (j = 748 ∧ V' = V ∧ g' = g) ∨
      (j = 390 ∧ V' = V ∧ g'.rsp = g.rsp ∧ g'.r9 = g.r9)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz fE ⊢
  stlx +contextual [W_368, W_377, W_387, o29, o30, o31, hz, fE]

set_option maxHeartbeats 2000000 in
/-- No digit: to 748; else (`E ≠ 0`) the end stored at `E`, to 390. -/
theorem vc_368n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hn : (rdq(V, g.rsp + 8#64) == 0) = false) (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (wE : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rsp + 8#64)) i)) :
    W_368 fb F Wl (fun j g' _ V' => (j = 748 ∧ V' = V ∧ g' = g) ∨
      (j = 390 ∧ V' = Vst V (rdq(V, g.rsp + 8#64)) (toBytesLE g.rdi 8) ∧ g'.rsp = g.rsp ∧ g'.r9 = g.r9))
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hn fE wE ⊢
  stlx +contextual [W_368, W_377, W_387, o29, o30, o31, hn, fE, wE]

/-- `errno = EINVAL`; to 448. -/
theorem vc_432 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (ef : ∀ i < 4, Foot Wl (Addr.add (fb + 18446744073709551544#64) i)) :
    W_432 fb F Wl (fun j g' _ V' => j = 448 ∧ V' = Vst V (fb + 18446744073709551544#64) (toBytesLE (22#32) 4) ∧
      g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stlx +contextual [W_432, o34, ef]

set_option maxHeartbeats 2000000 in
/-- `add rsp, 0x28`, the pops; to the `ret` (462). -/
theorem vc_448 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (p0 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8) i))
    (p4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8) i))
    (p5 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8) i)) :
    W_448 fb F Wl (fun j g' _ V' => j = 462 ∧ V' = V ∧ g'.rsp = g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8 + 8 ∧
      g'.rbx = rdq(V, g.rsp + 40#64) ∧ g'.rbp = rdq(V, g.rsp + 40#64 + 8) ∧
      g'.r12 = rdq(V, g.rsp + 40#64 + 8 + 8) ∧ g'.r13 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8) ∧
      g'.r14 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8) ∧ g'.r15 = rdq(V, g.rsp + 40#64 + 8 + 8 + 8 + 8 + 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at p0 p1 p2 p3 p4 p5 ⊢
  stlx +contextual [W_448, o35, p0, p1, p2, p3, p4, p5]

/-- `rdi = rbx`; to 748. -/
theorem vc_745 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_745 fb F Wl (fun j g' _ V' => j = 748 ∧ V' = V ∧ g'.rdi = g.rbx ∧ g'.rsp = g.rsp ∧ g'.r13 = g.r13)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stlx +contextual [W_745, o42]

set_option maxHeartbeats 2000000 in
/-- `*E = p`; to 448. -/
theorem vc_790 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (fE : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (wE : ∀ i < 8, Foot Wl (Addr.add (rdq(V, g.rsp + 8#64)) i)) :
    W_790 fb F Wl (fun j g' _ V' => j = 448 ∧ V' = Vst V (rdq(V, g.rsp + 8#64)) (toBytesLE g.r13 8) ∧
      g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at fE wE ⊢
  stlx +contextual [W_790, o46, fE, wE]

/-- `eax = 0`; to 448. -/
theorem vc_927 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} :
    W_927 fb F Wl (fun j g' _ V' => j = 448 ∧ V' = V ∧ g'.rsp = g.rsp) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  stlx +contextual [W_927, o52]

end FV7z.Stl
