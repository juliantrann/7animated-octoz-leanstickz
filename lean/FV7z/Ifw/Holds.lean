import FV7z.Ifw.Cuts
import FV7z.Api.Holds
import FV7z.Tun.Inv
import FV7z.Lemmas.OrMi32
/-!
# `_IO_new_file_write (f, data, n)` (0x6287d0): from the entry to the return (PLAN.md §M, M1)

glibc's `_IO_new_file_write` (`libio/fileops.c`, static in 7-Zip 26.06's `7zzs`; `objdump -d`) at `0x6287d0`: `f` =
`rdi` (`r13`), `data` = `rsi` (`rbp`), `n` = `rdx` (`r12`, `to_do` in `rbx`). Four pushes (`r13`, `r12`, `rbp`, `rbx`)
and 8 bytes of frame (`aR S`); `n <= 0` (20) to the end (107) with 0; the loop head (61): `edi` = `f->_fileno`,
`__write_nocancel (fd, data, to_do)` (`call` 78, `0x666210`) when `f->_flags2 & 2`, else `__write` (`call` 40,
`0x5ff270`); a negative count (45, 83) sets `_IO_ERR_SEEN` (`or dword [r13], 0x20`, 96, `Seg.s_or_mi32`); else
`to_do -= count`, `data += count` (50), the head again while `to_do > 0`; the end (107) adds `n - to_do` to
`f->_offset` (the 8 bytes at `f + 144`) unless negative; the pops and the `ret` (139).

The callees are hypotheses (`Ev.kW`, `Ev.kN`): called with `rdx` = `d`, they return a negative count or one in
`1 .. d` (`Bw d`), so the loop ends: by induction on `to_do` (`loop`). A count of 0 (the loop would not end) is
left out by that hypothesis. The bytes: `I` at the head, kept by the callees; the end's stores touch only `f`'s
first 4 bytes and the 8 at `f + 144` (`Out`), apart from the saved registers and the return address (`Ap5`).

- `call_40`, `call_78`, `or_96`, `ret_139`: the instructions outside the blocks.
- `aR`, `V0`, `q1`..`q5`, `Fm`, `Fk`, `Stk`, `Ap5`, `Out`, `Bw`, `KC`, `Ev`, `callK`: the frame, the bytes after the
  pushes, the pops' addresses, the frame's registers, what a piece keeps, the stack, the slots apart from the
  stores, the bytes at the end, the callees' counts, the callee as a continuation, the hypotheses, a `call`.
- `vc_0`, `vc_45`, `vc_50`, `vc_61`, `vc_83`, `vc_101`, `vc_107`, `vc_129`: the pieces.
- `ifw_ok`: from the entry (`S` = the entry's `rsp`, `g0` = its registers, `I` of the bytes after the pushes, `V0`)
  to the return (`Ev.kr`: `rsp` 8 up, the callee-saved registers as at the entry, bytes `W'` as some `W` with `I`
  but for `f`'s flags and offset) or a callee's goal. The count returned is not stated.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Api (KS)
namespace FV7z.Ifw
set_option linter.unusedVariables false

/-! ## The instructions outside the blocks -/

/-- The `call` of `__write` (40). -/
def pc40 : List Byte := [0xe8, 0x73, 0x6a, 0xfd, 0xff]
theorem pc40_0 : ∀ feat, Dec feat pc40 0 (FV7z.mk .call 64 [.rel 18446744073709382259] 5) := by dec_rfl
theorem wc_40 : pc40 <+: ifw.drop 40 := by decide +kernel
theorem call_40 (feat : Features) : Dec feat ifw 40 (FV7z.mk .call 64 [.rel 18446744073709382259] 5) :=
  Dec.shift (j := 40) (k := 0) (pc40_0 feat) wc_40 (Nat.zero_le _)
theorem tgt_40 : ifw_at.add (40 + 5) + BitVec.ofNat 64 18446744073709382259 = 0x5ff270#64 := by decide

/-- The `call` of `__write_nocancel` (78). -/
def pc78 : List Byte := [0xe8, 0xed, 0xd9, 0x03, 0x00]
theorem pc78_0 : ∀ feat, Dec feat pc78 0 (FV7z.mk .call 64 [.rel 252397] 5) := by dec_rfl
theorem wc_78 : pc78 <+: ifw.drop 78 := by decide +kernel
theorem call_78 (feat : Features) : Dec feat ifw 78 (FV7z.mk .call 64 [.rel 252397] 5) :=
  Dec.shift (j := 78) (k := 0) (pc78_0 feat) wc_78 (Nat.zero_le _)
theorem tgt_78 : ifw_at.add (78 + 5) + BitVec.ofNat 64 252397 = 0x666210#64 := by decide

/-- `or dword [r13 + 0], 0x20` (96). -/
def por : List Byte := [0x41, 0x83, 0x4d, 0x00, 0x20]
theorem por_0 : ∀ feat, Dec feat por 0 (FV7z.mk .or 32 [.mem (mbd 13 0 32), .imm 32 32] 5) := by dec_rfl
theorem wo_96 : por <+: ifw.drop 96 := by decide +kernel
theorem or_96 (feat : Features) : Dec feat ifw 96 (FV7z.mk .or 32 [.mem (mbd 13 0 32), .imm 32 32] 5) :=
  Dec.shift (j := 96) (k := 0) (por_0 feat) wo_96 (Nat.zero_le _)

/-- The `ret` (139). -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_139 : pret <+: ifw.drop 139 := by decide +kernel
theorem ret_139 (feat : Features) : Dec feat ifw 139 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 139) (k := 0) (pret_0 feat) w_139 (Nat.zero_le _)

theorem eaD13 (s : State) : eaD s 13 0 = s.cpu.gpr.r13 := by
  show s.cpu.gpr.get (regOf 13) + BitVec.ofNat 64 0 = _
  generalize s.cpu.gpr = g
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  rw [gk13]
  exact BitVec.add_zero _

theorem set4_rdx (g : Gprs) (v : BitVec 64) : (g.set 4 v).rdx = g.rdx := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  rfl

/-! ## The frame -/

/-- The stack pointer after the four pushes and `sub rsp, 8`. -/
abbrev aR (S : Addr) : Addr := S - 8 - 8 - 8 - 8 - 8#64

/-- The bytes after the four pushes (`r13`, `r12`, `rbp`, `rbx`). -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

theorem q1 (S : Addr) : aR S + 8#64 = S - 8 - 8 - 8 - 8 := BitVec.sub_add_cancel _ _
theorem q2 (S : Addr) : aR S + 8#64 + 8 = S - 8 - 8 - 8 := by rw [q1, BitVec.sub_add_cancel]
theorem q3 (S : Addr) : aR S + 8#64 + 8 + 8 = S - 8 - 8 := by rw [q2, BitVec.sub_add_cancel]
theorem q4 (S : Addr) : aR S + 8#64 + 8 + 8 + 8 = S - 8 := by rw [q3, BitVec.sub_add_cancel]
theorem q5 (S : Addr) : aR S + 8#64 + 8 + 8 + 8 + 8 = S := by rw [q4, BitVec.sub_add_cancel]

/-- The frame from the prologue on: `rsp` = `aR S`, `r13` = `f`, `r14`, `r15` as at the entry. -/
abbrev Fm (S : Addr) (g0 g : Gprs) : Prop :=
  g.rsp = aR S ∧ g.r13 = g0.rdi ∧ g.r14 = g0.r14 ∧ g.r15 = g0.r15

/-- What a piece keeps: `rsp`, `rbx` (`to_do`), `r13`..`r15`. -/
abbrev Fk (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

theorem fm_fk {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (h' : Fk g g') : Fm S g0 g' :=
  ⟨h'.1.trans h.1, h'.2.2.1.trans h.2.1, h'.2.2.2.1.trans h.2.2.1, h'.2.2.2.2.trans h.2.2.2⟩

/-- Back from a callee: `rsp` as before the `call`, the callee-saved registers kept. -/
theorem fm_ret {S : Addr} {g0 g g' : Gprs} (h : Fm S g0 g) (hs : g'.rsp = aR S) (hk : KS g g') : Fm S g0 g' :=
  ⟨hs, hk.2.2.2.1.trans h.2.1, hk.2.2.2.2.1.trans h.2.2.1, hk.2.2.2.2.2.trans h.2.2.2⟩

/-- The stack: the four saved registers. -/
abbrev Stk (W : Addr → Byte) (S : Addr) (g0 : Gprs) : Prop :=
  rdq(W, S - 8) = g0.r13 ∧ rdq(W, S - 8 - 8) = g0.r12 ∧ rdq(W, S - 8 - 8 - 8) = g0.rbp ∧
    rdq(W, S - 8 - 8 - 8 - 8) = g0.rbx

/-- The 8 bytes at `x` apart from the `n` at `a`. -/
abbrev Ap (x a : Addr) (n : Nat) : Prop := ∀ c < 8, ∀ i < n, Addr.add x c ≠ Addr.add a i

/-- The four slots and the return address apart from the `n` bytes at `a`. -/
abbrev Ap5 (S a : Addr) (n : Nat) : Prop :=
  Ap (S - 8) a n ∧ Ap (S - 8 - 8) a n ∧ Ap (S - 8 - 8 - 8) a n ∧ Ap (S - 8 - 8 - 8 - 8) a n ∧ Ap S a n

/-- The bytes `W'` as `W` but for `f`'s first 4 bytes (`_flags`) and the 8 at `f + 144` (`_offset`). -/
abbrev Out (W W' : Addr → Byte) (f : Addr) : Prop :=
  ∀ a, (∀ i < 4, a ≠ Addr.add f i) → (∀ i < 8, a ≠ Addr.add (f + 144#64) i) → W' a = W a

theorem out_rfl {W : Addr → Byte} {f : Addr} : Out W W f := fun _ _ _ => rfl

theorem out_or {W : Addr → Byte} {f : Addr} {bs : List Byte} (hb : bs.length = 4) : Out W (Vst W f bs) f :=
  fun _ h1 _ => Vst_apart _ _ _ _ fun i hi => h1 i (hb ▸ hi)

theorem out_st {W W₁ : Addr → Byte} {f : Addr} {bs : List Byte} (h : Out W W₁ f) (hb : bs.length = 8) :
    Out W (Vst W₁ (f + 144#64) bs) f :=
  fun a h1 h2 => (Vst_apart _ _ _ _ fun i hi => h2 i (hb ▸ hi)).trans (h a h1 h2)

theorem rd_out {W W' : Addr → Byte} {f x : Addr} (h : Out W W' f) (h1 : Ap x f 4) (h2 : Ap x (f + 144#64) 8) :
    rdq(W', x) = rdq(W, x) := by
  congr 1
  refine List.map_congr_left fun y hy => ?_
  obtain ⟨c, hc, rfl⟩ := mem_byteAddrs.1 hy
  exact h _ (fun i hi => h1 c hc i hi) fun i hi => h2 c hc i hi

/-- A callee's count (`rax`) for `to_do` = `d`: negative, or in `1 .. d`. -/
abbrev Bw (d : BitVec 64) (g : Gprs) : Prop :=
  g.rax.msb = true ∨ (g.rax ≠ 0 ∧ g.rax.toNat ≤ d.toNat)

/-- The callee from the `call` before `j` (entry `ent`, the bytes `W`, the registers `A`): at its entry, and from its
return at `j` with `rsp` = `aR S`, the callee-saved registers as at its entry, `B` and the invariant `J`, the run
goes on to the goal. -/
def KC (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (J : (Addr → Byte) → Prop) (ent : Addr) (j : Nat) (W : Addr → Byte) (A B : Gprs → Prop) : Prop :=
  ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
    Agree F Y.proc.mm.mem (Vst W (aR S - 8) (toBytesLE (ifw_at.add j) 8)) →
    Y.cpu.rip = ent → Y.cpu.gpr.rsp = aR S - 8 → A Y.cpu.gpr →
    (∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = ifw_at.add j → Z.cpu.gpr.rsp = aR S → KS Y.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
      GoG prof L o gev gP gE Z t'') →
    GoG prof L o gev gP gE Y t'

/-! ## The hypotheses of the runs -/

/-- The hypotheses of the runs (`S`, `g0` the entry's stack pointer and registers, `e₂.add j₂` the return address,
`I` the invariant of the bytes at the head): the saved registers and the return address in the bytes with `I`, apart
from `f`'s flags and offset (`ap0`, `ap1`) and readable; the `call`'s slot; `f`'s fields readable or writable; the
callees' code, their counts (`Bw`) and `I` kept; the return. -/
structure Ev (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State)
    (o : Oracle) (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (S : Addr) (g0 : Gprs) (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat) (I : (Addr → Byte) → Prop) :
    Prop where
  c : Seg prof F Wl L s₀ o
  hin : CodeIn L ifw_at ifw
  hin₂ : CodeIn L e₂ code₂
  h₂ : j₂ < code₂.length
  hI : ∀ W, I W → Stk W S g0 ∧ rdq(W, S) = e₂.add j₂
  ap0 : Ap5 S g0.rdi 4
  ap1 : Ap5 S (g0.rdi + 144#64) 8
  fb1 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8 - 8) i)
  fb2 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8 - 8) i)
  fb3 : ∀ i < 8, Foot F.data (Addr.add (S - 8 - 8) i)
  fb4 : ∀ i < 8, Foot F.data (Addr.add (S - 8) i)
  hl : ∀ i < 8, Foot F.data (Addr.add S i)
  hr8 : ∀ i < 8, Foot Wl (Addr.add (aR S - 8) i)
  f112 : ∀ i < 4, Foot F.data (Addr.add (g0.rdi + 112#64) i)
  f116 : ∀ i < 1, Foot F.data (Addr.add (g0.rdi + 116#64) i)
  f144 : ∀ i < 8, Foot F.data (Addr.add (g0.rdi + 144#64) i)
  w144 : ∀ i < 8, Foot Wl (Addr.add (g0.rdi + 144#64) i)
  w0 : ∀ i < 4, Foot Wl (Addr.add g0.rdi i)
  cW : ∃ code : List Byte, CodeIn L 0x5ff270#64 code ∧ 0 < code.length
  cN : ∃ code : List Byte, CodeIn L 0x666210#64 code ∧ 0 < code.length
  kW : ∀ j W (d : BitVec 64), I W →
    KC prof F Wl L s₀ o gev gP gE S I 0x5ff270#64 j W (fun g => g.rdx = d) (Bw d)
  kN : ∀ j W (d : BitVec 64), I W →
    KC prof F Wl L s₀ o gev gP gE S I 0x666210#64 j W (fun g => g.rdx = d) (Bw d)
  kr : ∀ (W W' : Addr → Byte) (Z' : State) (t' : Nat), I W → Out W W' g0.rdi → KeptW Wl s₀ Z' →
    Agree F Z'.proc.mm.mem W' → Z'.cpu.rip = e₂.add j₂ → Z'.cpu.gpr.rsp = S + 8 → KS g0 Z'.cpu.gpr →
    GoG prof L o gev gP gE Z' t'

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {W : Addr → Byte}

/-- A `call` at `j` (`rsp` = `aR S`, the bytes `W`) of the callee `k`, and from its return at `j + 5`. -/
theorem callK (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I)
    {J : (Addr → Byte) → Prop} {U : State} {t₁ : Nat} {j R : Nat} {ent : Addr} {A B : Gprs → Prop}
    (hKU : KeptW Wl s₀ U) (hAU : Agree F U.proc.mm.mem W) (hrU : U.cpu.rip = ifw_at.add j)
    (hs : U.cpu.gpr.rsp = aR S) (hj : j < ifw.length) (hd : Dec prof.feat ifw j (FV7z.mk .call 64 [.rel R] 5))
    (htgt : ifw_at.add (j + 5) + BitVec.ofNat 64 R = ent)
    (hc : ∃ code : List Byte, CodeIn L ent code ∧ 0 < code.length)
    (k : KC prof F Wl L s₀ o gev gP gE S J ent (j + 5) W A B) (hA : A (U.cpu.gpr.set 4 (aR S - 8)))
    (h : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      Z.cpu.rip = ifw_at.add (j + 5) → Z.cpu.gpr.rsp = aR S → KS U.cpu.gpr Z.cpu.gpr → B Z.cpu.gpr → J W' →
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

/-! ## The pieces -/

/-- One step of the closers of the pieces. -/
macro "ostep" : tactic => `(tactic| first
  | with_reducible rfl
  | with_reducible assumption
  | exact rfl
  | apply And.intro
  | intro _)

section Pieces
variable {F : Footprint} {Wl : List Rgn}

/-- `endbr64`, the four pushes, `r13` = `f`, `sub rsp, 8`, `test rdx, rdx`: `n <= 0` to 107 (`eax` = 0), else
`rbp` = `data`, `r12` = `rbx` = `n`, to the head at 61. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i))
    (h107 : ∀ g', g'.rsp = aR g.rsp → g'.r13 = g.rdi → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 107 g' fl (V0 V g))
    (h61 : ∀ g', g'.rsp = aR g.rsp → g'.r13 = g.rdi → g'.r14 = g.r14 → g'.r15 = g.r15 →
      ∀ fl, Q 61 g' fl (V0 V g)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [aR, V0] at hs1 hs2 hs3 hs4 h107 h61 ⊢
  wpx [W_0, W_152, W_26, o0, o1, o10]
  all_goals repeat' (first
    | refine h107 _ ?_ ?_ ?_ ?_ _
    | refine h61 _ ?_ ?_ ?_ ?_ _
    | with_reducible exact hs1
    | with_reducible exact hs2
    | with_reducible exact hs3
    | with_reducible exact hs4
    | ostep)

/-- Back from `__write`: `test rax, rax`; negative to 96, else (`rax` not negative) to 50. -/
theorem vc_45 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h96 : ∀ fl, Q 96 g fl V)
    (h50 : g.rax.msb = false → ∀ fl, Q 50 g fl V) :
    W_45 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h50
  by_cases hm : rax.msb = true
  · wpx [W_45, o2, hm, BitVec.and_self, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first | exact h96 _ | apply And.intro | intro _)
  · have hm' : rax.msb = false := by simpa using hm
    wpx [W_45, o2, hm', BitVec.and_self, Bool.false_eq_true, false_implies, implies_true]
    all_goals repeat' (first | exact h50 hm' _ | apply And.intro | intro _)

/-- Back from `__write_nocancel`: `test rax, rax`; not negative to 50, else the `nop` and 96. -/
theorem vc_83 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h96 : ∀ fl, Q 96 g fl V)
    (h50 : g.rax.msb = false → ∀ fl, Q 50 g fl V) :
    W_83 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h50
  by_cases hm : rax.msb = true
  · wpx [W_83, W_88, o2, o5, hm, BitVec.and_self, Bool.not_true, Bool.false_eq_true, false_implies,
      implies_true]
    all_goals repeat' (first | exact h96 _ | apply And.intro | intro _)
  · have hm' : rax.msb = false := by simpa using hm
    wpx [W_83, W_88, o2, o5, hm', BitVec.and_self, Bool.not_false, Bool.true_eq_false, false_implies,
      implies_true]
    all_goals repeat' (first | exact h50 hm' _ | apply And.intro | intro _)

/-- `to_do -= count`, `data += count`, `test rbx, rbx`: `to_do <= 0` to 107 (`rax` = `n - to_do`), else the head. -/
theorem vc_50 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h107 : ∀ g', g'.rsp = g.rsp → g'.r13 = g.r13 → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 107 g' fl V)
    (h61 : ∀ g', g'.rsp = g.rsp → g'.rbx = g.rbx - g.rax → g'.r13 = g.r13 → g'.r14 = g.r14 →
      g'.r15 = g.r15 → ∀ fl, Q 61 g' fl V) :
    W_50 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h107 h61 ⊢
  wpx [W_50, W_144, o3, o6]
  all_goals repeat' (first
    | refine h107 _ ?_ ?_ ?_ ?_ _
    | refine h61 _ ?_ ?_ ?_ ?_ ?_ _
    | ostep)

/-- The head: `edi` = `f->_fileno`, `rdx` = `to_do`, `rsi` = `data`, `f->_flags2 & 2`: 0 to the `call` of `__write`
at 40, else to the `call` of `__write_nocancel` at 78. -/
theorem vc_61 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f112 : ∀ i < 4, Foot F.data (Addr.add (g.r13 + 112#64) i))
    (f116 : ∀ i < 1, Foot F.data (Addr.add (g.r13 + 116#64) i))
    (h40 : ∀ g', Fk g g' → g'.rdx = g.rbx → ∀ fl, Q 40 g' fl V)
    (h78 : ∀ g', Fk g g' → g'.rdx = g.rbx → ∀ fl, Q 78 g' fl V) :
    W_61 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f112 f116 h40 h78 ⊢
  wpx [W_61, o4, Op.testmi]
  all_goals repeat' (first
    | refine h40 _ ?_ ?_ _
    | refine h78 _ ?_ ?_ _
    | with_reducible exact f112
    | with_reducible exact f116
    | exact f112 _ (by assumption)
    | exact f116 _ (by assumption)
    | ostep)

/-- After the `or`: `rax` = `n - to_do`, to 107. -/
theorem vc_101 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} (h : ∀ g', Fk g g' → ∀ fl, Q 107 g' fl V) :
    W_101 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_101, o6]
  all_goals repeat' (first
    | refine h _ ?_ _
    | ostep)

/-- The end: `f->_offset` negative to 129, else `f->_offset += rax` and 129. -/
theorem vc_107 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f144 : ∀ i < 8, Foot F.data (Addr.add (g.r13 + 144#64) i))
    (w144 : ∀ i < 8, Foot Wl (Addr.add (g.r13 + 144#64) i))
    (ha : ∀ g', Fk g g' → ∀ fl, Q 129 g' fl V)
    (hb : ∀ g' (x : BitVec 64), Fk g g' → ∀ fl, Q 129 g' fl (Vst V (g.r13 + 144#64) (toBytesLE x 8))) :
    W_107 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f144 w144 ha hb ⊢
  wpx [W_107, W_119, o7, o8]
  all_goals repeat' (first
    | refine ha _ ?_ _
    | refine hb _ _ ?_ _
    | with_reducible exact f144
    | with_reducible exact w144
    | exact f144 _ (by assumption)
    | exact w144 _ (by assumption)
    | ostep)

/-- `add rsp, 8`, the four pops, to the `ret` at 139. -/
theorem vc_129 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (f2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (f4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ g', g'.rsp = g.rsp + 8#64 + 8 + 8 + 8 + 8 → g'.rbx = rdq(V, g.rsp + 8#64) →
      g'.rbp = rdq(V, g.rsp + 8#64 + 8) → g'.r12 = rdq(V, g.rsp + 8#64 + 8 + 8) →
      g'.r13 = rdq(V, g.rsp + 8#64 + 8 + 8 + 8) → g'.r14 = g.r14 → g'.r15 = g.r15 → ∀ fl, Q 139 g' fl V) :
    W_129 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f1 f2 f3 f4 h ⊢
  wpx [W_129, o9]
  all_goals repeat' (first
    | refine h _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ _
    | with_reducible exact f1
    | with_reducible exact f2
    | with_reducible exact f3
    | with_reducible exact f4
    | ostep)

end Pieces

/-! ## The runs -/

section Runs
variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {S : Addr} {g0 : Gprs} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat} {I : (Addr → Byte) → Prop}
  {X Y : State} {t : Nat} {V W W₁ : Addr → Byte}

/-- From 129: `add rsp, 8`, the pops, the `ret`, to `kr`. -/
theorem from129 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W₁) (hr : Y.cpu.rip = ifw_at.add 129) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W)
    (ho : Out W W₁ g0.rdi) :
    GoG prof L o gev gP gE Y t := by
  obtain ⟨⟨s1, s2, s3, s4⟩, hra⟩ := E.hI W hIW
  obtain ⟨a1, a2, a3, a4, a5⟩ := E.ap0
  obtain ⟨b1, b2, b3, b4, b5⟩ := E.ap1
  have ms := hm.1
  have e1 : rdq(W₁, Y.cpu.gpr.rsp + 8#64) = g0.rbx := by rw [ms, q1, rd_out ho a4 b4]; exact s4
  have e2 : rdq(W₁, Y.cpu.gpr.rsp + 8#64 + 8) = g0.rbp := by rw [ms, q2, rd_out ho a3 b3]; exact s3
  have e3 : rdq(W₁, Y.cpu.gpr.rsp + 8#64 + 8 + 8) = g0.r12 := by rw [ms, q3, rd_out ho a2 b2]; exact s2
  have e4 : rdq(W₁, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) = g0.r13 := by rw [ms, q4, rd_out ho a1 b1]; exact s1
  refine (c_129 prof).run E.c E.hin (fun j' g' _ V' => j' = 139 ∧ V' = W₁ ∧
      g'.rsp = Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8 + 8 ∧ g'.rbx = rdq(W₁, Y.cpu.gpr.rsp + 8#64) ∧
      g'.rbp = rdq(W₁, Y.cpu.gpr.rsp + 8#64 + 8) ∧ g'.r12 = rdq(W₁, Y.cpu.gpr.rsp + 8#64 + 8 + 8) ∧
      g'.r13 = rdq(W₁, Y.cpu.gpr.rsp + 8#64 + 8 + 8 + 8) ∧ g'.r14 = Y.cpu.gpr.r14 ∧ g'.r15 = Y.cpu.gpr.r15)
    hK hA hr
    (vc_129 (by rw [ms, q1]; exact E.fb1) (by rw [ms, q2]; exact E.fb2) (by rw [ms, q3]; exact E.fb3)
      (by rw [ms, q4]; exact E.fb4) fun _ a b c d e m n _ => ⟨rfl, rfl, a, b, c, d, e, m, n⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hV₁, gs, gb, gp, g12, g13, g14, g15⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hsU : U.cpu.gpr.rsp = S := by rw [gs, ms]; exact q5 S
  refine E.c.s_ret hKU hAU E.hin (lt_len (by decide)) hrU (ret_139 _) (by rw [hsU]; exact E.hl) E.hin₂ E.h₂
    (by rw [hsU, rd_out ho a5 b5]; exact hra) ?_
  rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine E.kr W W₁ Z' t₂ hIW ho hKZ' hAZ' hrZ' ?_ ?_
  · rw [hgZ']
    show U.cpu.gpr.rsp + 8 = _
    rw [hsU]
  · rw [hgZ']
    exact ⟨gb.trans e1, gp.trans e2, g12.trans e3, g13.trans e4, g14.trans hm.2.2.1, g15.trans hm.2.2.2⟩

/-- From 107 (the end, the bytes `W₁` as `W` with `I` but for `f`'s flags and offset): to 129. -/
theorem fromE (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W₁) (hr : Y.cpu.rip = ifw_at.add 107) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W)
    (ho : Out W W₁ g0.rdi) :
    GoG prof L o gev gP gE Y t := by
  refine (c_107 prof).run E.c E.hin (fun j' g' _ V' => j' = 129 ∧ Fk Y.cpu.gpr g' ∧ Out W V' g0.rdi) hK hA hr
    (vc_107 (by rw [hm.2.1]; exact E.f144) (by rw [hm.2.1]; exact E.w144) (fun _ a _ => ⟨rfl, a, ho⟩)
      fun _ x a _ => ⟨rfl, a, by rw [hm.2.1]; exact out_st ho (toBytesLE_length _ _)⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hk, ho'⟩ U t₁ hKU hAU hrU hgU -
  subst hgU
  exact from129 E hKU hAU hrU (fm_fk hm hk) hIW ho'

/-- From 96 (a negative count, the bytes `W` with `I`): `_IO_ERR_SEEN` set, `rax` = `n - to_do`, to 107. -/
theorem from96 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ifw_at.add 96) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W) :
    GoG prof L o gev gP gE Y t := by
  have he : eaD Y 13 0 = g0.rdi := (eaD13 Y).trans hm.2.1
  refine E.c.s_or_mi32 hK hA E.hin (lt_len (by decide)) hr (or_96 _) (by rw [he]; exact E.w0) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [he] at hA₂
  refine (c_101 prof).run E.c E.hin (fun j' g' _ V' => j' = 107 ∧ Fk Y₂.cpu.gpr g' ∧ V' = _) hK₂ hA₂ hr₂
    (vc_101 fun _ a _ => ⟨rfl, a, rfl⟩) ?_
  rintro j' g fl V₁ ⟨rfl, hk, hV₁⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  exact fromE E hKU hAU hrU (fm_fk (by rw [hg₂]; exact hm) hk) hIW (out_or (toBytesLE_length _ _))

/-- From 50 (a count `rax` in `1 .. to_do`, `to_do` = `d`): to 107, or the head with `to_do` less (`H61`). -/
theorem from50 (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) {d : BitVec 64} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ifw_at.add 50) (hm : Fm S g0 Y.cpu.gpr) (hIW : I W)
    (hd : Y.cpu.gpr.rbx = d) (hc : Y.cpu.gpr.rax ≠ 0 ∧ Y.cpu.gpr.rax.toNat ≤ d.toNat)
    (H61 : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = ifw_at.add 61 →
      Fm S g0 Z.cpu.gpr → Z.cpu.gpr.rbx.toNat < d.toNat → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine (c_50 prof).run E.c E.hin (fun j' g' _ V' => V' = W ∧ Fm S g0 g' ∧
      (j' = 107 ∨ (j' = 61 ∧ g'.rbx = Y.cpu.gpr.rbx - Y.cpu.gpr.rax))) hK hA hr
    (vc_50 (fun _ a b c e _ => ⟨rfl, ⟨a.trans hm.1, b.trans hm.2.1, c.trans hm.2.2.1, e.trans hm.2.2.2⟩,
        .inl rfl⟩)
      fun _ a x b c e _ => ⟨rfl, ⟨a.trans hm.1, b.trans hm.2.1, c.trans hm.2.2.1, e.trans hm.2.2.2⟩,
        .inr ⟨rfl, x⟩⟩)
    ?_
  rintro j' g fl V₁ ⟨hV₁, hmg, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | ⟨rfl, hb⟩
  · exact fromE E hKU hAU hrU hmg hIW out_rfl
  · refine H61 U t₁ hKU hAU hrU hmg ?_
    have h0 : Y.cpu.gpr.rax.toNat ≠ 0 := fun h => hc.1 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    have hle : Y.cpu.gpr.rax.toNat ≤ Y.cpu.gpr.rbx.toNat := by rw [hd]; exact hc.2
    have hs : (Y.cpu.gpr.rbx - Y.cpu.gpr.rax).toNat = Y.cpu.gpr.rbx.toNat - Y.cpu.gpr.rax.toNat :=
      BitVec.toNat_sub_of_le hle
    rw [hb, hs, ← hd]
    omega

/-- Back from a callee (45 or 83, the piece `vc`): a negative count to 96, else 50. -/
theorem fromR (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) {d : BitVec 64} {j : Nat} {Wp : Wpt}
    (cp : Sp prof ifw ifw_at j Wp)
    (vc : ∀ {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}, (∀ fl, Q 96 g fl V) →
      (g.rax.msb = false → ∀ fl, Q 50 g fl V) → Wp F Wl Q g f V)
    (hK : KeptW Wl s₀ Y) (hA : Agree F Y.proc.mm.mem W) (hr : Y.cpu.rip = ifw_at.add j) (hm : Fm S g0 Y.cpu.gpr)
    (hIW : I W) (hd : Y.cpu.gpr.rbx = d) (hB : Bw d Y.cpu.gpr)
    (H61 : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W → Z.cpu.rip = ifw_at.add 61 →
      Fm S g0 Z.cpu.gpr → Z.cpu.gpr.rbx.toNat < d.toNat → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE Y t := by
  refine cp.run E.c E.hin (fun j' g' _ V' => V' = W ∧ g' = Y.cpu.gpr ∧
      (j' = 96 ∨ (j' = 50 ∧ Y.cpu.gpr.rax.msb = false))) hK hA hr
    (vc (fun _ => ⟨rfl, rfl, .inl rfl⟩) fun h _ => ⟨rfl, rfl, .inr ⟨rfl, h⟩⟩) ?_
  rintro j' g fl V₁ ⟨hV₁, hg, hj⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  rcases hj with rfl | ⟨rfl, hms⟩
  · exact from96 E hKU hAU hrU (by rw [hg]; exact hm) hIW
  · have hc : Y.cpu.gpr.rax ≠ 0 ∧ Y.cpu.gpr.rax.toNat ≤ d.toNat := hB.resolve_left (by rw [hms]; decide)
    refine from50 E hKU hAU hrU (by rw [hg]; exact hm) hIW (by rw [hg]; exact hd) (by rw [hg]; exact hc) H61

/-- The loop from its head (61, `to_do` = `rbx`, the bytes with `I`): by induction on `to_do`. -/
theorem loop (E : Ev prof F Wl L s₀ o gev gP gE S g0 e₂ code₂ j₂ I) :
    ∀ (m : Nat) (Y : State) (W : Addr → Byte) (t : Nat), Y.cpu.gpr.rbx.toNat = m → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem W → Y.cpu.rip = ifw_at.add 61 → Fm S g0 Y.cpu.gpr → I W →
      GoG prof L o gev gP gE Y t := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro Y W t hm0 hK hA hr hF hIW
  refine (c_61 prof).run E.c E.hin (fun j' g' _ V' => (j' = 40 ∨ j' = 78) ∧ V' = W ∧ Fk Y.cpu.gpr g' ∧
      g'.rdx = Y.cpu.gpr.rbx) hK hA hr
    (vc_61 (by rw [hF.2.1]; exact E.f112) (by rw [hF.2.1]; exact E.f116) (fun _ a b _ => ⟨.inl rfl, rfl, a, b⟩)
      fun _ a b _ => ⟨.inr rfl, rfl, a, b⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hk, hdx⟩ U t₁ hKU hAU hrU hgU -
  subst V₁ hgU
  have hmU : Fm S g0 U.cpu.gpr := fm_fk hF hk
  have hA' : (U.cpu.gpr.set 4 (aR S - 8)).rdx = Y.cpu.gpr.rbx := by rw [set4_rdx]; exact hdx
  have H : ∀ (Z : State) (W' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem W' →
      KS U.cpu.gpr Z.cpu.gpr → (Z' : State) → ∀ t', KeptW Wl s₀ Z' → Agree F Z'.proc.mm.mem W' →
      Z'.cpu.rip = ifw_at.add 61 → Fm S g0 Z'.cpu.gpr → I W' → Z'.cpu.gpr.rbx.toNat < Y.cpu.gpr.rbx.toNat →
      GoG prof L o gev gP gE Z' t' :=
    fun _ W' _ _ _ _ Z' t' hK' hA'' hr' hF' hI' hl => ih _ (hm0 ▸ hl) Z' W' t' rfl hK' hA'' hr' hF' hI'
  rcases hj with rfl | rfl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_40 _) tgt_40 E.cW (E.kW _ _ _ hIW) hA' ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact fromR E (c_45 prof) vc_45 hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ (hkZ.1.trans hk.2.1) hBZ
      fun Z' t' hK' hA'' hr' hF' hl => H Z W' t₃ hKZ hAZ hkZ Z' t' hK' hA'' hr' hF' hIZ hl
  · refine callK E hKU hAU hrU hmU.1 (lt_len (by decide)) (call_78 _) tgt_78 E.cN (E.kN _ _ _ hIW) hA' ?_
    intro Z W' t₃ hKZ hAZ hrZ hsZ hkZ hBZ hIZ
    exact fromR E (c_83 prof) vc_83 hKZ hAZ hrZ (fm_ret hmU hsZ hkZ) hIZ (hkZ.1.trans hk.2.1) hBZ
      fun Z' t' hK' hA'' hr' hF' hl => H Z W' t₃ hKZ hAZ hkZ Z' t' hK' hA'' hr' hF' hIZ hl

/-- `_IO_new_file_write (f, data, n)` from its entry (`X`'s registers, `S` = their `rsp`; the pushes' slots in what
the run may store into, `I` of the bytes after the pushes). -/
theorem ifw_ok (E : Ev prof F Wl L s₀ o gev gP gE X.cpu.gpr.rsp X.cpu.gpr e₂ code₂ j₂ I)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ifw_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i)) (hI0 : I (V0 V X.cpu.gpr)) :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run E.c E.hin (fun j' g' _ V' => (j' = 107 ∨ j' = 61) ∧ V' = V0 V X.cpu.gpr ∧
      Fm X.cpu.gpr.rsp X.cpu.gpr g') hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hs1 hs2 hs3 hs4 (fun _ a b c d _ => ⟨.inl rfl, rfl, a, b, c, d⟩)
      fun _ a b c d _ => ⟨.inr rfl, rfl, a, b, c, d⟩) ?_
  rintro j' g fl V₁ ⟨hj, hV₁, hmY⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁ hgY
  rcases hj with rfl | rfl
  · exact fromE E hKY hAY hrY hmY hI0 out_rfl
  · exact loop E _ Y _ t₁ rfl hKY hAY hrY hmY hI0

end Runs

end FV7z.Ifw
