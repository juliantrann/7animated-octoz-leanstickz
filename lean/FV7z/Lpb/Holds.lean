import FV7z.Lpb.Cuts
import FV7z.Lpd.Blocks1
import FV7z.Lap.Blocks1
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `LzmaDec_AllocateProbs` (PLAN.md §M, M1)

7-Zip 26.06's `LzmaDec_AllocateProbs (p, props, propsSize, alloc)` at `0x42bf10` in `7zzs` (`C/LzmaDec.c`;
`objdump -d`), `p` = `rdi`, `alloc` = `rcx`, `S` the stack pointer at the entry: two pushes (`r12`, `rbx`, `P2`),
`r12` = `alloc`, `rbx` = `p`, a frame of 24 bytes (`aQ S` = `S - 40`) with the stack guard (`fs:0x28`) at `aQ S + 8`
(`Vo`), `propNew` (`CLzmaProps`, 8 bytes) at `aQ S`; `LzmaProps_Decode (&propNew, props, propsSize)` (`Lpd.lpd_at`,
call at 36, registers `aG`); back at 41 (`R` the stack pointer there): when its answer (`eax`) is not 0, to 45;
else (72) `edx`, `esi` the bytes `propNew.lp`, `propNew.lc` (`R + 1`, `R`), `rcx` = `alloc`, `rdi` = `p` (`g72`) and
`LzmaDec_AllocateProbs2 (p, &propNew, alloc)` (`Lap.lap_at`, call at 87, back at 92): when its answer is not 0, to
45; else `p->prop = propNew` (the 8 bytes at `R` stored at `p`, `Vp`) and to 45. At 45 the stack guard checked, the
frame dropped, the two pops, the `ret` (68): the registers `tl`.

Both callees are hypotheses, as in `FV7z/Fdn/Holds.lean` (the same split) and `FV7z/Efn/Holds.lean`:
- `lpb_call`: from the entry to `LzmaProps_Decode`'s entry, the return address `lpb_at + 41` below the frame;
- `lpb_tail`: from 45 to the return address (at `R + 40`);
- `lpb_ret`: from 41 to the return address: `LzmaProps_Decode`'s answer not 0 (`k0`); else at
  `LzmaDec_AllocateProbs2`'s entry (`k2`), and from its return (`rsp` = `R`, `rbx` = `p`, the guard and the return
  address as they were, its own post `P`) to the return address: its answer not 0 (`kn`) or 0, `propNew` stored
  (`kz`).

Not covered: the stack guard failing (`__stack_chk_fail`, 105).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Lpb

theorem lpb_36 : ∀ feat, Dec feat lpb 36 (FV7z.mk .call 64 [.rel 18446744073709551463] 5) := by intro feat f; rfl
theorem lpb_87 : ∀ feat, Dec feat lpb 87 (FV7z.mk .call 64 [.rel 18446744073709551252] 5) := by intro feat f; rfl
theorem lpb_68 : ∀ feat, Dec feat lpb 68 (FV7z.mk .ret 64 [] 1) := by intro feat f; rfl

/-! ## The frame -/

/-- The stack pointer after the two pushes and `sub rsp, 24`. -/
abbrev aQ (S : Addr) : Addr := S - 8 - 8 - 24#64

/-- The bytes after the two `push`es. -/
abbrev P2 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbx 8)

/-- The bytes at `LzmaProps_Decode`'s call: the stack guard `cn` stored at `aQ S + 8`. -/
abbrev Vo (V : Addr → Byte) (g : Gprs) (cn : BitVec 64) : Addr → Byte :=
  Vst (P2 V g) (aQ g.rsp + 8#64) (toBytesLE cn 8)

/-- At `LzmaProps_Decode`'s call: `rax` 0, `rbx` = `p`, `r12` = `alloc`, `rdi` = `&propNew` (`rsp`). -/
abbrev aG (g : Gprs) : Gprs :=
  { g with
    rax := 0#64
    rbx := g.rdi
    rsp := aQ g.rsp
    rdi := aQ g.rsp
    r12 := g.rcx }

/-- At `LzmaDec_AllocateProbs2`'s call: `edx` = `propNew.lp`, `esi` = `propNew.lc` (the bytes at `rsp + 1`,
`rsp`), `rcx` = `alloc` (`r12`), `rdi` = `p` (`rbx`). -/
abbrev g72 (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rcx := g.r12
    rdx := ((ofBytesLE 8 ((byteAddrs (g.rsp + 1#64) 1).map V)).setWidth 32).setWidth 64
    rsi := ((ofBytesLE 8 ((byteAddrs g.rsp 1).map V)).setWidth 32).setWidth 64
    rdi := g.rbx }

/-- The bytes after `p->prop = propNew`: the 8 bytes at `rsp` stored at `rbx`. -/
abbrev Vp (V : Addr → Byte) (g : Gprs) : Addr → Byte := Vst V g.rbx (toBytesLE rdq(V, g.rsp) 8)

/-- The registers at the return address, from those at 45 (`rsp` = `R`): `rbx`, `r12` popped from `R + 24`,
`R + 32`, `rsp` 48 above. -/
abbrev tl (g : Gprs) (V : Addr → Byte) : Gprs :=
  { g with
    rbx := rdq(V, g.rsp + 24#64)
    rsp := g.rsp + 24#64 + 8 + 8 + 8
    r12 := rdq(V, g.rsp + 24#64 + 8) }

theorem xz (x : BitVec 32) : BitVec.setWidth 64 (x ^^^ x) = 0#64 := by simp
theorem pa1 (S : Addr) : S + 24#64 + 8 = S + 32#64 := by bv_omega
theorem pa2 (S : Addr) : S + 24#64 + 8 + 8 = S + 40#64 := by bv_omega
theorem tA (x : Addr) (k : Nat) (hk : x.toNat + k < 2 ^ 64) : (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

variable {F : Footprint} {Wl : List Rgn}

/-! ## The pieces -/

/-- From the entry to the first call: the pushes, the frame, the stack guard stored. -/
theorem vc_0 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} {cn : BitVec 64}
    (hcn : rdq(P2 V g, fb + 40#64) = cn)
    (w1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (w2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (wc : ∀ i < 8, Foot Wl (Addr.add (aQ g.rsp + 8#64) i)) :
    W_0 fb F Wl (fun j' g' _ V' => j' = 36 ∧ g' = aG g ∧ V' = Vo V g cn) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Vo, P2, aQ, aG] at hcn w1 w2 wc ⊢
  wpx [W_0, o0, Op.ldf, hcn, xz, Bool.false_eq_true, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 41, `LzmaProps_Decode`'s answer not 0: to 45. -/
theorem vc_41n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 ≠ 0#32) :
    W_41 fb F Wl (fun j' g' _ V' => j' = 45 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_41, W_72, o1, o4, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 41, `LzmaProps_Decode`'s answer 0: the registers `g72`, to the call at 87. -/
theorem vc_41z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 = 0#32)
    (f0 : ∀ i < 1, Foot F.data (Addr.add g.rsp i)) (f1 : ∀ i < 1, Foot F.data (Addr.add (g.rsp + 1#64) i)) :
    W_41 fb F Wl (fun j' g' _ V' => j' = 87 ∧ g' = g72 g V ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g72] at hz f0 f1 ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_41, W_72, o1, o4, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 92, `LzmaDec_AllocateProbs2`'s answer not 0: to 45. -/
theorem vc_92n {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 ≠ 0#32) :
    W_92 fb F Wl (fun j' g' _ V' => j' = 45 ∧ g' = g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz ⊢
  have e : (BitVec.setWidth 32 rax == 0) = false := beq_eq_false_iff_ne.2 hz
  wpx [W_92, W_96, o1, o5, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 92, `LzmaDec_AllocateProbs2`'s answer 0: `rdx` the 8 bytes at `rsp`, stored at `rbx`, to 45. -/
theorem vc_92z {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte} (hz : g.rax.setWidth 32 = 0#32)
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (wb : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) :
    W_92 fb F Wl (fun j' g' _ V' => j' = 45 ∧ g' = { g with rdx := rdq(V, g.rsp) } ∧
      V' = Vst V g.rbx (toBytesLE rdq(V, g.rsp) 8)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hz f0 wb ⊢
  have e : (BitVec.setWidth 32 rax == 0) = true := beq_iff_eq.2 hz
  wpx [W_92, W_96, o1, o5, e, BitVec.and_self, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, eq_self_iff_true, true_implies, implies_true]
  all_goals vfin

/-- From 45: the stack guard checked, the frame dropped, the two pops, to the `ret` (68). -/
theorem vc_45 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hc : rdq(V, g.rsp + 8#64) = rdq(V, fb + 40#64)) (f8 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (fc : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (p1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64) i))
    (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 24#64 + 8) i)) :
    W_45 fb F Wl (fun j' g' _ V' => j' = 68 ∧
      g' = { g with
        rbx := rdq(V, g.rsp + 24#64)
        rsp := g.rsp + 24#64 + 8 + 8
        r12 := rdq(V, g.rsp + 24#64 + 8) } ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hc f8 p1 p2 ⊢
  have z0 : ((0#64 : BitVec 64) == 0) = true := by decide
  wpx [W_45, W_61, o2, o3, Op.xormf, hc, BitVec.xor_self, z0, decide_true, Bool.not_true, Bool.false_eq_true,
    false_implies, eq_self_iff_true, true_implies]
  all_goals vfin

/-! ## The function -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `LzmaDec_AllocateProbs (p, props, propsSize, alloc)` from its entry, the stack guard's 8 bytes at `fs:0x28`
readable, the pushes' slots, the guard's slot and the call's return address's slot in what the run may store into:
at `LzmaProps_Decode`'s entry with the registers `aG`, the pushes and the stack guard (as read after the pushes)
stored (`Vo`) and the return address `lpb_at + 41` below the frame. -/
theorem lpb_call {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L lpb_at lpb)
    (hinD : CodeIn L Lpd.lpd_at Lpd.lpd) (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V)
    (hrip : X.cpu.rip = lpb_at) (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (w1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (w2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8 - 8) i))
    (wc : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp + 8#64) i))
    (wr : ∀ i < 8, Foot Wl (Addr.add (aQ X.cpu.gpr.rsp - 8) i))
    (k : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (Vo V X.cpu.gpr rdq(P2 V X.cpu.gpr, fb + 40#64)) (aQ X.cpu.gpr.rsp - 8)
        (toBytesLE (lpb_at.add 41) 8)) →
      Y.cpu.rip = Lpd.lpd_at → Y.cpu.gpr = (aG X.cpu.gpr).set 4 (aQ X.cpu.gpr.rsp - 8) →
      GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof fb).run c hfs hin (fun j' g' _ V' => j' = 36 ∧ g' = aG X.cpu.gpr ∧
      V' = Vo V X.cpu.gpr rdq(P2 V X.cpu.gpr, fb + 40#64)) hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 rfl w1 w2 hcl wc) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = aQ X.cpu.gpr.rsp := by rw [hgY]
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (lpb_36 _) hinD (Lpd.lt_len (j := 0) (by decide))
    (by decide) (by rw [hsY]; exact wr) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY] at hA₂
  exact k Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgY])

/-- From 45 (`R` = `rsp`) to the return address at `R + 40`, the stack guard at `R + 8` the one at `fs:0x28`: the
registers `tl`, the bytes as at 45. -/
theorem lpb_tail {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L lpb_at lpb)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lpb_at.add 45)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 32#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 40#64) i))
    (hc : rdq(V, X.cpu.gpr.rsp + 8#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 40#64) = e₂.add j₂)
    (k : ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = tl X.cpu.gpr V → GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  refine (c_45 prof fb).run c hfs hin _ hK hA hrip
    (vc_45 (g := X.cpu.gpr) hc f8 hcl f24 (by rw [pa1]; exact f32)) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ Y t₃ hKY hAY hrY hgY -
  subst V₃
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp + 24#64 + 8 + 8 := by rw [hgY]
  refine c.s_ret hKY hAY hin (lt_len (by decide)) hrY (lpb_68 _) (by rw [hsY, pa2]; exact f40) hin₂ h₂
    (by rw [hsY, pa2]; exact hra) ?_
  rintro Z t₄ hKZ hAZ ⟨hrZ, hgZ⟩
  exact k Z t₄ hKZ hAZ hrZ (by rw [hgZ, hgY]; try rfl)

/-- `LzmaDec_AllocateProbs` from the return of `LzmaProps_Decode` (41), `R` = `rsp`: `propNew` at `R`, the stack
guard at `R + 8` the one at `fs:0x28`, the return address at `R + 40`, `p` (`rbx`, its 8 bytes apart from `R + 8` …
`R + 48` and from the stack guard). `LzmaProps_Decode`'s answer not 0: at the return address with the registers `tl`
(`k0`); else at `LzmaDec_AllocateProbs2`'s entry with the registers `g72` and the return address `lpb_at + 92` at
`R - 8` (`k2`), and from its return (`rsp` = `R`, `rbx` = `p`, the guard and the return address kept, its post `P`) at
the return address: its answer not 0, the registers `tl` and its bytes (`kn`); 0, `propNew` stored at `p` (`Vp`,
`kz`). -/
theorem lpb_ret {fb : Addr} {P : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o)
    (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L lpb_at lpb) (hinA : CodeIn L Lap.lap_at Lap.lap)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = lpb_at.add 41)
    (hcl : ∀ i < 8, Foot F.data (Addr.add (fb + 40#64) i)) (hcb : (fb + 40#64).toNat + 8 ≤ 2 ^ 64)
    (hRb : X.cpu.gpr.rsp.toNat + 48 ≤ 2 ^ 64)
    (w8 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f1 : ∀ i < 1, Foot F.data (Addr.add (X.cpu.gpr.rsp + 1#64) i))
    (f8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 8#64) i))
    (f24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 24#64) i))
    (f32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 32#64) i))
    (f40 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp + 40#64) i))
    (wb : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rbx i)) (hbb : X.cpu.gpr.rbx.toNat + 8 ≤ 2 ^ 64)
    (hbd : X.cpu.gpr.rbx.toNat + 8 ≤ X.cpu.gpr.rsp.toNat + 8 ∨ X.cpu.gpr.rsp.toNat + 48 ≤ X.cpu.gpr.rbx.toNat)
    (hbc : X.cpu.gpr.rbx.toNat + 8 ≤ (fb + 40#64).toNat ∨ (fb + 40#64).toNat + 8 ≤ X.cpu.gpr.rbx.toNat)
    (hc : rdq(V, X.cpu.gpr.rsp + 8#64) = rdq(V, fb + 40#64))
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp + 40#64) = e₂.add j₂)
    (k0 : X.cpu.gpr.rax.setWidth 32 ≠ 0#32 → ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z →
      Agree F Z.proc.mm.mem V → Z.cpu.rip = e₂.add j₂ → Z.cpu.gpr = tl X.cpu.gpr V →
      GoG prof L o gev gP gE Z t')
    (k2 : X.cpu.gpr.rax.setWidth 32 = 0#32 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V (X.cpu.gpr.rsp - 8) (toBytesLE (lpb_at.add 92) 8)) →
      Y.cpu.rip = Lap.lap_at → Y.cpu.gpr = (g72 X.cpu.gpr V).set 4 (X.cpu.gpr.rsp - 8) →
      (∀ (Z₂ : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V₂ →
        Z₂.cpu.rip = lpb_at.add 92 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp → Z₂.cpu.gpr.rbx = X.cpu.gpr.rbx →
        rdq(V₂, X.cpu.gpr.rsp + 8#64) = rdq(V₂, fb + 40#64) → rdq(V₂, X.cpu.gpr.rsp + 40#64) = e₂.add j₂ →
        P Z₂ V₂ → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kn : ∀ (Z₂ : State) (V₂ : Addr → Byte), P Z₂ V₂ → Z₂.cpu.gpr.rax.setWidth 32 ≠ 0#32 →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V₂ → Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = tl Z₂.cpu.gpr V₂ → GoG prof L o gev gP gE Z t')
    (kz : ∀ (Z₂ : State) (V₂ : Addr → Byte), P Z₂ V₂ → Z₂.cpu.gpr.rax.setWidth 32 = 0#32 →
      ∀ (Z : State) (t' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem (Vp V₂ X.cpu.gpr) →
      Z.cpu.rip = e₂.add j₂ →
      Z.cpu.gpr = tl { Z₂.cpu.gpr with rdx := rdq(V₂, Z₂.cpu.gpr.rsp) } (Vp V₂ X.cpu.gpr) →
      GoG prof L o gev gP gE Z t') :
    GoG prof L o gev gP gE X t := by
  have hf0 : ∀ i < 1, Foot F.data (Addr.add X.cpu.gpr.rsp i) := fun i hi => f0 i (by omega)
  have q8 : (X.cpu.gpr.rsp + 8#64).toNat = X.cpu.gpr.rsp.toNat + 8 := tA _ 8 (by omega)
  have q40 : (X.cpu.gpr.rsp + 40#64).toNat = X.cpu.gpr.rsp.toNat + 40 := tA _ 40 (by omega)
  by_cases hz : X.cpu.gpr.rax.setWidth 32 = 0#32
  · -- `LzmaDec_AllocateProbs2`
    refine (c_41 prof fb).run c hfs hin _ hK hA hrip (vc_41z hz hf0 f1) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (lpb_87 _) hinA (Lap.lt_len (j := 0) (by decide))
      (by decide) (by rw [hsU]; exact w8) ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    rw [hsU] at hA₂
    refine k2 hz Y₂ t₂ hK₂ hA₂ hr₂ (by rw [hg₂, hgU]) ?_
    intro Z₂ V₂ t'' hKZ hAZ hrZ hzs hzb hgd hrd hP
    by_cases hz2 : Z₂.cpu.gpr.rax.setWidth 32 = 0#32
    · -- `p->prop = propNew`
      refine (c_92 prof fb).run c hfs hin _ hKZ hAZ hrZ
        (vc_92z hz2 (by rw [hzs]; exact f0) (by rw [hzb]; exact wb)) ?_
      rintro j' g fl V₄ ⟨rfl, rfl, rfl⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
      have eV : Vst V₂ Z₂.cpu.gpr.rbx (toBytesLE rdq(V₂, Z₂.cpu.gpr.rsp) 8) = Vp V₂ X.cpu.gpr := by
        rw [hzs, hzb]
      rw [eV] at hAU₂
      have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]; exact hzs
      -- reads apart from `p`'s 8 bytes
      have m : ∀ (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
          X.cpu.gpr.rbx.toNat + 8 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rbx.toNat →
          rdq(Vp V₂ X.cpu.gpr, x) = rdq(V₂, x) := fun x hx hd =>
        congrArg (ofBytesLE 64) (Tun.rd_Vst V₂ X.cpu.gpr.rbx (toBytesLE rdq(V₂, X.cpu.gpr.rsp) 8) x 8
          (by rw [toBytesLE_length]; exact hbb) hx (by rw [toBytesLE_length]; exact hd))
      refine lpb_tail c hfs hin hKU₂ hAU₂ hrU₂ hcl (by rw [hsU₂]; exact f8) (by rw [hsU₂]; exact f24)
        (by rw [hsU₂]; exact f32) (by rw [hsU₂]; exact f40) ?_ hin₂ h₂ ?_ ?_
      · rw [hsU₂, m (X.cpu.gpr.rsp + 8#64) (by rw [q8]; omega) (by rw [q8]; omega), m (fb + 40#64) hcb hbc]
        exact hgd
      · rw [hsU₂, m (X.cpu.gpr.rsp + 40#64) (by rw [q40]; omega) (by rw [q40]; omega)]
        exact hrd
      intro Z t' hKZ' hAZ' hrZ' hgZ'
      exact kz Z₂ V₂ hP hz2 Z t' hKZ' hAZ' hrZ' (by rw [hgZ', hgU₂])
    · -- its answer not 0
      refine (c_92 prof fb).run c hfs hin _ hKZ hAZ hrZ (vc_92n hz2) ?_
      rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U₂ t₃ hKU₂ hAU₂ hrU₂ hgU₂ -
      subst V₄
      have hsU₂ : U₂.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU₂]; exact hzs
      refine lpb_tail c hfs hin hKU₂ hAU₂ hrU₂ hcl (by rw [hsU₂]; exact f8) (by rw [hsU₂]; exact f24)
        (by rw [hsU₂]; exact f32) (by rw [hsU₂]; exact f40) (by rw [hsU₂]; exact hgd) hin₂ h₂
        (by rw [hsU₂]; exact hrd) ?_
      intro Z t' hKZ' hAZ' hrZ' hgZ'
      exact kn Z₂ V₂ hP hz2 Z t' hKZ' hAZ' hrZ' (by rw [hgZ', hgU₂])
  · -- `LzmaProps_Decode`'s answer not 0
    refine (c_41 prof fb).run c hfs hin _ hK hA hrip (vc_41n hz) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ U t₁ hKU hAU hrU hgU -
    subst V₁
    have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
    refine lpb_tail c hfs hin hKU hAU hrU hcl (by rw [hsU]; exact f8) (by rw [hsU]; exact f24)
      (by rw [hsU]; exact f32) (by rw [hsU]; exact f40) (by rw [hsU]; exact hc) hin₂ h₂
      (by rw [hsU]; exact hra) ?_
    intro Z t' hKZ hAZ hrZ hgZ
    exact k0 hz Z t' hKZ hAZ hrZ (by rw [hgZ, hgU])

end FV7z.Lpb
