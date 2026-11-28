import FV7z.Asi.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnMem
import FV7z.Lemmas.FnFar
/-!
# `AString::InsertSpace` (PLAN.md §M, M1)

7-Zip 26.06's `AString::InsertSpace (index, size)` at `0x44c140` in `7zzs` (`CPP/Common/MyString.cpp`), `this` =
`rdi`, `&index` = `rsi`, `size` = `edx`, `S` the entry's `rsp`: `push r12; mov r12, rsi; mov esi, edx; push rbp;
mov ebp, edx; push rbx; mov rbx, rdi` (`V1`, `gC`), `Grow (size)` (`call` at 18 to `0x44c0e0`); back at 23
`esi` = `index` (`[r12]`), `rdi` = `_chars` (`[rbx]`), `edx` = `1 - index + _len` (`[rbx + 8]`), `rsi` =
`_chars + index`, `eax` = `index + size`, `pop rbx; pop rbp`, `rdi` = `_chars + (index + size)`, `pop r12`; then
`memmove (rdi, rsi, rdx)` as a tail jump (`jmp` at 55) to the PLT's entry `0x401020`.

`Grow` is a hypothesis, as the callees in `FV7z/Ain/Holds.lean`: a continuation at its entry (`kf`), given the run
from its return, which keeps `rbx`, `rbp`, `r12`, the frame's `rsp` and the three saved registers in the bytes it
leaves; `Pc` is what it leaves. `memmove` is the continuation `kt`, at its PLT entry.

- `V1`, `gC`, `g23`, `gT`: the bytes with the three pushes; the registers at the `call`, at the `jmp` from those at
  23, and at the `jmp` in terms of the entry's.
- `vc_0`, `vc_23`: the piece from the entry to the `call` and the piece from 23 to the `jmp`.
- `asi_ok`: through `Grow` and the pieces to `memmove`'s PLT entry with `rbx`, `rbp`, `r12`, `rsp` restored (`kt`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Asi

/-- `AString::Grow`. -/
abbrev grow_at : Addr := 0x44c0e0

/-- The PLT's entry for `memmove`. -/
abbrev plt_memmove : Addr := 0x401020

/-- The `call` to `Grow`. -/
def pcg : List Byte := [0xe8, 0x89, 0xff, 0xff, 0xff]
theorem pcg_0 : ∀ feat, Dec feat pcg 0 (FV7z.mk .call 64 [.rel 18446744073709551497] 5) := by dec_rfl
theorem wc_18 : pcg <+: asi.drop 18 := by decide +kernel
theorem call_18 (feat : Features) : Dec feat asi 18 (FV7z.mk .call 64 [.rel 18446744073709551497] 5) :=
  Dec.shift (j := 18) (k := 0) (pcg_0 feat) wc_18 (Nat.zero_le _)
theorem tgt_18 : asi_at.add (18 + 5) + BitVec.ofNat 64 18446744073709551497 = grow_at := by decide

/-- The tail jump to `memmove`. -/
def pjm : List Byte := [0xe9, 0xa4, 0x4e, 0xfb, 0xff]
theorem pjm_0 : ∀ feat, Dec feat pjm 0 (FV7z.mk .jmp 64 [.rel 18446744073709244068] 5) := by dec_rfl
theorem wj_55 : pjm <+: asi.drop 55 := by decide +kernel
theorem jmp_55 (feat : Features) : Dec feat asi 55 (FV7z.mk .jmp 64 [.rel 18446744073709244068] 5) :=
  Dec.shift (j := 55) (k := 0) (pjm_0 feat) wj_55 (Nat.zero_le _)
theorem tgt_55 : asi_at.add (55 + 5) + BitVec.ofNat 64 18446744073709244068 = plt_memmove.add 0 := by decide

/-! ## The frame -/

/-- The bytes with `r12`, `rbp`, `rbx` pushed. -/
abbrev V1 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The registers at the `call` of `Grow`: `rbx` = `this`, `r12` = `&index`, `esi` = `ebp` = `size`. -/
abbrev gC (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdi,
      rsp := g.rsp - 8 - 8 - 8,
      rbp := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx),
      rsi := BitVec.setWidth 64 (BitVec.setWidth 32 g.rdx),
      r12 := g.rsi }

/-- The registers at the `jmp`, from those at 23 (`rbx` = `this`, `r12` = `&index`, `ebp` = `size`). -/
abbrev g23 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
      rax := BitVec.setWidth 64 (rdd(V, g.r12) + BitVec.setWidth 32 g.rbp),
      rbx := rdq(V, g.rsp),
      rsp := g.rsp + 8 + 8 + 8,
      rbp := rdq(V, g.rsp + 8),
      rdx := BitVec.setWidth 64 (1#32 - rdd(V, g.r12) + rdd(V, g.rbx + 8#64)),
      rsi := BitVec.setWidth 64 rdd(V, g.r12) + rdq(V, g.rbx),
      rdi := rdq(V, g.rbx) + BitVec.setWidth 64 (rdd(V, g.r12) + BitVec.setWidth 32 g.rbp),
      r12 := rdq(V, g.rsp + 8 + 8) }

/-- The registers at `memmove`'s PLT entry, in terms of the entry's (`x`) and `Grow`'s bytes `V`: `rdi` =
`_chars + index + size`, `rsi` = `_chars + index`, `edx` = `_len - index + 1`; `rbx`, `rbp`, `r12`, `rsp` restored. -/
abbrev gT (g x : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
      rax := BitVec.setWidth 64 (rdd(V, x.rsi) + BitVec.setWidth 32 x.rdx),
      rbx := x.rbx,
      rsp := x.rsp,
      rbp := x.rbp,
      rdx := BitVec.setWidth 64 (1#32 - rdd(V, x.rsi) + rdd(V, x.rdi + 8#64)),
      rsi := BitVec.setWidth 64 rdd(V, x.rsi) + rdq(V, x.rdi),
      rdi := rdq(V, x.rdi) + BitVec.setWidth 64 (rdd(V, x.rsi) + BitVec.setWidth 32 x.rdx),
      r12 := x.r12 }

theorem aE2 (s : Addr) : s - 8 - 8 - 8 + 8 = s - 8 - 8 := BitVec.sub_add_cancel _ _
theorem aE3 (s : Addr) : s - 8 - 8 + 8 = s - 8 := BitVec.sub_add_cancel _ _
theorem aE4 (s : Addr) : s - 8 + 8 = s := BitVec.sub_add_cancel _ _

/-! ## The pieces -/

variable {F : Footprint} {Wl : List Rgn}

/-- The entry's code: the three pushes and the moves, up to the `call` at 18. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (h : ∀ fl, Q 18 (gC g) fl (V1 V g)) : W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, V1] at hs1 hs2 hs3 h ⊢
  wpx [W_0, o0]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `Grow`, at 23: the loads, the sums, `pop rbx; pop rbp; pop r12`, up to the `jmp` at 55. -/
theorem vc_23 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (fi : ∀ i < 4, Foot F.data (Addr.add g.r12 i)) (fc : ∀ i < 8, Foot F.data (Addr.add g.rbx i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (l1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (l2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (l3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 55 (g23 g V) fl V) : W_23 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g23] at fi fc fl l1 l2 l3 h ⊢
  wpx [W_23, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::InsertSpace (index, size)` (`this` = `rdi`, `&index` = `rsi`, `size` = `edx`) from its entry, `S` =
`rsp`: at `Grow`'s entry with the registers `gC`, the bytes `V1` and the return address `asi_at + 23` at
`S - 32` (`kf`); from its return (`rsp` = `S - 24`, `rbx` = `this`, `ebp` = `size`, `r12` = `&index`, the saved
registers in its bytes, the post `Pc`) at `memmove`'s PLT entry with the registers `gT` and `Grow`'s bytes (`kt`). -/
theorem asi_ok {Pc : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L asi_at asi)
    {codeG : List Byte} (hinG : CodeIn L grow_at codeG) (hG : 0 < codeG.length)
    {codeM : List Byte} (hinM : CodeIn L plt_memmove codeM) (hM : 0 < codeM.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = asi_at)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) i))
    (fi : ∀ i < 4, Foot F.data (Addr.add X.cpu.gpr.rsi i))
    (fc : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fl : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (kf : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V1 V X.cpu.gpr) (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) (toBytesLE (asi_at.add 23) 8)) →
      Y.cpu.rip = grow_at → Y.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = asi_at.add 23 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 →
        Z.cpu.gpr.rbx = X.cpu.gpr.rdi → Z.cpu.gpr.rbp = BitVec.setWidth 64 (BitVec.setWidth 32 X.cpu.gpr.rdx) →
        Z.cpu.gpr.r12 = X.cpu.gpr.rsi →
        rdq(V', X.cpu.gpr.rsp - 8 - 8 - 8) = X.cpu.gpr.rbx → rdq(V', X.cpu.gpr.rsp - 8 - 8) = X.cpu.gpr.rbp →
        rdq(V', X.cpu.gpr.rsp - 8) = X.cpu.gpr.r12 → Pc Z V' →
        GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kt : ∀ (Z : State) (V' : Addr → Byte) (Y : State) (t' : Nat), Pc Z V' → KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem V' → Y.cpu.rip = plt_memmove → Y.cpu.gpr = gT Z.cpu.gpr X.cpu.gpr V' →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8 - 8) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8 - 8) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hrip' : X.cpu.rip = asi_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- the entry's code, to the `call` of `Grow`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 18 ∧ g' = gC X.cpu.gpr ∧ V' = V1 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 hs2 hs3 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl₁ V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 8 - 8 - 8 := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_18 _) hinG hG tgt_18 (by rw [hsY]; exact hs4) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 8 - 8 - 8 - 8) := by rw [hg₂, hsY, hgY]
  refine kf Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `Grow`, at 23: to the `jmp`
  intro Z V' t'' hKZ hAZ hrZ hzs hzb hzp hz12 q1 q2 q3 hP
  refine (c_23 prof).run c hin (fun j' g' _ V'' => j' = 55 ∧ g' = gT Z.cpu.gpr X.cpu.gpr V' ∧ V'' = V') hKZ hAZ hrZ
    (vc_23 (by rw [hz12]; exact fi) (by rw [hzb]; exact fc) (by rw [hzb]; exact fl) (by rw [hzs]; exact h24)
      (by rw [hzs, aE2]; exact h16) (by rw [hzs, aE2, aE3]; exact h8)
      fun _ => ⟨rfl, by dsimp only [g23, gT]; rw [hzs, hzb, hzp, hz12, aE2, aE3, aE4, q1, q2, q3, sw_64_32], rfl⟩) ?_
  rintro j' g fl₂ V₂ ⟨rfl, rfl, hV₂⟩ U t₃ hKU hAU hrU hgU -
  subst V₂
  -- the tail jump to `memmove`'s PLT entry
  refine c.s_jmp_x hKU hAU hin (lt_len (by decide)) hrU (jmp_55 _) hinM (tgt := 0) hM tgt_55 ?_
  rintro U₂ t₄ hK₄ hA₄ ⟨hr₄, hg₄⟩
  refine kt Z V' U₂ t₄ hP hK₄ hA₄ (by rw [hr₄, addr_add_zero]) ?_
  rw [hg₄, hgU]

end FV7z.Asi
