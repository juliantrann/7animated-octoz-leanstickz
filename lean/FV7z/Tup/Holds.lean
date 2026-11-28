import FV7z.Tup.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
import FV7z.Sen.Holds
/-!
# `towupper` (PLAN.md §M, M1)

glibc 2.31's `towupper (wc)` at `0x669660` in `7zzs` (`wctype/wcfuncs.c`, the three-level table lookup of
`locale/C-translit.h` inlined): no calls, no stores, only loads through the `fs` base `fb`. With `c` the low 32 bits
of `rdi`:

- the thread's locale `fs:-0x70` (`tlsA`), its `LC_CTYPE` data (`lq`), the index of the `toupper` table at the
  word `lq + 0xd0` (`ix`), the table `tt` = the quadword at `lq + 0x40 + 8 · ix`;
- `s1` = `c >> tt[0]`; past the bound `tt[1]` (`cmp esi, [rdx+4]; jae`) `c` is returned (`ret` at 76);
- the first level's entry `o1v` = `tt[s1 + 5]` (4-byte words); 0: `c` (76);
- the second level's entry `o2v` at `tt + 4 · ((c >> tt[2]) & tt[3]) + o1v`; 0: `c` (76);
- else `c` plus the third level's entry `dl` at `tt + 4 · (c & tt[4]) + o2v` (`ret` at 92).

`tupF` is that value; `RdOk` the loads in the footprint's data (the later ones only on the paths that make them).
The registers `rax`, `rcx`, `rdx`, `rsi`, `rdi` change, the bytes do not (`Sen.Rt`).

- `vc_big`, `vc_e1`, `vc_e2`, `vc_hit`: from the entry to a `ret` on each of the four paths.
- `tup_fnK`: `towupper` in a run with its code, as `StringsAreEqualNoCase` (`Sen`) and `CompareFileNames` (`Cfn`)
  take it (`FnK … Sen.tup_at T (Sen.Rt U)`): entered with the return address in the footprint's data, the loads
  in it (`RdOk`) and `U c` = `tupF`, it reaches the return address with `eax` = `U c`.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Tup

/-- The `ret`s. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_76 : pret <+: tup.drop 76 := by decide +kernel
theorem ret_76 (feat : Features) : Dec feat tup 76 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 76) (k := 0) (pret_0 feat) w_76 (Nat.zero_le _)
theorem w_92 : pret <+: tup.drop 92 := by decide +kernel
theorem ret_92 (feat : Features) : Dec feat tup 92 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 92) (k := 0) (pret_0 feat) w_92 (Nat.zero_le _)

/-! ## The loads -/

/-- The thread's locale pointer: `fs:-0x70`. -/
abbrev tlsA (fb : Addr) : Addr := fb + 18446744073709551504#64
/-- The locale's `LC_CTYPE` data. -/
abbrev lq (V : Addr → Byte) (fb : Addr) : Addr := rdq(V, rdq(V, tlsA fb))
/-- The index of the `toupper` table (the word at `lq + 0xd0`), zero-extended. -/
abbrev ix (V : Addr → Byte) (fb : Addr) : Addr :=
  BitVec.setWidth 64 (BitVec.setWidth 32 (ofBytesLE 16 (List.map V (byteAddrs (lq V fb + 208#64) 2))))
/-- The `toupper` table. -/
abbrev tt (V : Addr → Byte) (fb : Addr) : Addr := rdq(V, lq V fb + ix V fb * 8#64 + 64#64)
/-- `c` shifted by the first level's shift. -/
abbrev s1 (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : BitVec 32 :=
  c >>> ((BitVec.setWidth 8 rdd(V, tt V fb)).toNat % 32)
/-- The first level's bound. -/
abbrev bd (V : Addr → Byte) (fb : Addr) : BitVec 32 := rdd(V, tt V fb + 4#64)
/-- Where the first level's entry is. -/
abbrev a6 (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : Addr :=
  tt V fb + BitVec.setWidth 64 (s1 V fb c + 5#32) * 4#64
/-- The first level's entry. -/
abbrev o1v (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : BitVec 32 := rdd(V, a6 V fb c)
/-- `c` shifted by the second level's shift. -/
abbrev s2 (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : BitVec 32 :=
  c >>> ((BitVec.setWidth 8 rdd(V, tt V fb + 8#64)).toNat % 32)
/-- The second level's index. -/
abbrev m2 (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : BitVec 32 := s2 V fb c &&& rdd(V, tt V fb + 12#64)
/-- Where the second level's entry is. -/
abbrev a9 (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : Addr :=
  tt V fb + BitVec.setWidth 64 (m2 V fb c) * 4#64 + BitVec.setWidth 64 (o1v V fb c)
/-- The second level's entry. -/
abbrev o2v (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : BitVec 32 := rdd(V, a9 V fb c)
/-- Where the third level's entry is. -/
abbrev a11 (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : Addr :=
  tt V fb + BitVec.setWidth 64 (c &&& rdd(V, tt V fb + 16#64)) * 4#64 + BitVec.setWidth 64 (o2v V fb c)
/-- The third level's entry: what is added to `c`. -/
abbrev dl (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : BitVec 32 := rdd(V, a11 V fb c)

/-- `towupper (c)`, as the code computes it from the bytes `V` and the `fs` base `fb`. -/
def tupF (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : BitVec 32 :=
  if (s1 V fb c).toNat < (bd V fb).toNat then
    if o1v V fb c = 0 then c else if o2v V fb c = 0 then c else c + dl V fb c
  else c

/-- The loads of `towupper (c)` in the footprint's data, each on the paths that make it. -/
structure RdOk (F : Footprint) (V : Addr → Byte) (fb : Addr) (c : BitVec 32) : Prop where
  f0 : ∀ i < 8, Foot F.data (Addr.add (tlsA fb) i)
  f1 : ∀ i < 8, Foot F.data (Addr.add rdq(V, tlsA fb) i)
  f2 : ∀ i < 2, Foot F.data (Addr.add (lq V fb + 208#64) i)
  f3 : ∀ i < 8, Foot F.data (Addr.add (lq V fb + ix V fb * 8#64 + 64#64) i)
  f4 : ∀ i < 4, Foot F.data (Addr.add (tt V fb) i)
  f5 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 4#64) i)
  f6 : (s1 V fb c).toNat < (bd V fb).toNat → ∀ i < 4, Foot F.data (Addr.add (a6 V fb c) i)
  f7 : (s1 V fb c).toNat < (bd V fb).toNat → o1v V fb c ≠ 0 →
    (∀ i < 4, Foot F.data (Addr.add (tt V fb + 8#64) i)) ∧ (∀ i < 4, Foot F.data (Addr.add (tt V fb + 12#64) i)) ∧
    ∀ i < 4, Foot F.data (Addr.add (a9 V fb c) i)
  f8 : (s1 V fb c).toNat < (bd V fb).toNat → o1v V fb c ≠ 0 → o2v V fb c ≠ 0 →
    (∀ i < 4, Foot F.data (Addr.add (tt V fb + 16#64) i)) ∧ ∀ i < 4, Foot F.data (Addr.add (a11 V fb c) i)

/-- At a `ret` (`j`): the bytes as they were, `rax`, `rcx`, `rdx`, `rsi`, `rdi` changed, `eax` = `R`. -/
def Qr (g : Gprs) (V : Addr → Byte) (j : Nat) (R : BitVec 32) : Nat → Gprs → Rflags → (Addr → Byte) → Prop :=
  fun j' g' _ V' => j' = j ∧ V' = V ∧ ∃ a c d si di : BitVec 64,
    g' = { g with rax := a, rcx := c, rdx := d, rsi := si, rdi := di } ∧ BitVec.setWidth 32 a = R

/-! ## The paths -/

/-- What is left of a piece's condition: its footprint facts, equations, cases that cannot be. -/
local macro "vfin" : tactic =>
  `(tactic| repeat' (first | (with_reducible rfl) | (with_reducible assumption) | exact True.intro |
    (intro h; exact absurd h (by omega)) | apply And.intro | intro _))

/-- `wpx` with the `fs` load and the clean-up of the conditions. -/
local macro "cfx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| wpx [not_true_eq_false, not_false_eq_true, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    Bool.true_eq_false, false_implies, implies_true, ne_eq, Bool.not_eq_true', Bool.not_eq_false',
    decide_eq_true_eq, decide_eq_false_iff_not, decide_true, decide_false, BitVec.and_self, eq_self_iff_true,
    Bool.true_or, Bool.false_or, ↓reduceIte, BitVec.reduceSetWidth, Op.ldf, W_0, W_45, W_55, W_80, o0, o1, o2, o3,
    Qr, $ls,*])

/-- The registers at a `ret`: `rax`, `rcx`, `rdx`, `rsi`, `rdi` as they came, `eax` as the low half. -/
local macro "rfin" : tactic =>
  `(tactic| all_goals first
    | exact ⟨_, _, _, _, _, rfl, sw_64_32 _⟩
    | exact ⟨_, _, _, _, _, rfl, rfl⟩)

variable {F : Footprint} {Wl : List Rgn}

/-- `c >> tt[0]` past the bound: `c` (76). -/
theorem vc_big {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : ¬ (s1 V fb (BitVec.setWidth 32 g.rdi)).toNat < (bd V fb).toNat)
    (f0 : ∀ i < 8, Foot F.data (Addr.add (tlsA fb) i)) (f1 : ∀ i < 8, Foot F.data (Addr.add rdq(V, tlsA fb) i))
    (f2 : ∀ i < 2, Foot F.data (Addr.add (lq V fb + 208#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (lq V fb + ix V fb * 8#64 + 64#64) i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (tt V fb) i)) (f5 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 4#64) i)) :
    W_0 fb F Wl (Qr g V 76 (BitVec.setWidth 32 g.rdi)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [tlsA, lq, ix, tt, s1, bd] at h f0 f1 f2 f3 f4 f5 ⊢
  have hd := decide_eq_false h
  cfx [h, hd]
  all_goals vfin
  rfin

/-- The first level's entry 0: `c` (76). -/
theorem vc_e1 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (s1 V fb (BitVec.setWidth 32 g.rdi)).toNat < (bd V fb).toNat)
    (e1 : (o1v V fb (BitVec.setWidth 32 g.rdi) == 0) = true)
    (f0 : ∀ i < 8, Foot F.data (Addr.add (tlsA fb) i)) (f1 : ∀ i < 8, Foot F.data (Addr.add rdq(V, tlsA fb) i))
    (f2 : ∀ i < 2, Foot F.data (Addr.add (lq V fb + 208#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (lq V fb + ix V fb * 8#64 + 64#64) i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (tt V fb) i)) (f5 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 4#64) i))
    (f6 : ∀ i < 4, Foot F.data (Addr.add (a6 V fb (BitVec.setWidth 32 g.rdi)) i)) :
    W_0 fb F Wl (Qr g V 76 (BitVec.setWidth 32 g.rdi)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [tlsA, lq, ix, tt, s1, bd, a6, o1v] at h e1 f0 f1 f2 f3 f4 f5 f6 ⊢
  have hd := decide_eq_true h
  cfx [h, hd, e1]
  all_goals vfin
  rfin

/-- The second level's entry 0: `c` (76). -/
theorem vc_e2 {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (s1 V fb (BitVec.setWidth 32 g.rdi)).toNat < (bd V fb).toNat)
    (e1 : (o1v V fb (BitVec.setWidth 32 g.rdi) == 0) = false)
    (e2 : (o2v V fb (BitVec.setWidth 32 g.rdi) == 0) = true)
    (f0 : ∀ i < 8, Foot F.data (Addr.add (tlsA fb) i)) (f1 : ∀ i < 8, Foot F.data (Addr.add rdq(V, tlsA fb) i))
    (f2 : ∀ i < 2, Foot F.data (Addr.add (lq V fb + 208#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (lq V fb + ix V fb * 8#64 + 64#64) i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (tt V fb) i)) (f5 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 4#64) i))
    (f6 : ∀ i < 4, Foot F.data (Addr.add (a6 V fb (BitVec.setWidth 32 g.rdi)) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 12#64) i))
    (f9 : ∀ i < 4, Foot F.data (Addr.add (a9 V fb (BitVec.setWidth 32 g.rdi)) i)) :
    W_0 fb F Wl (Qr g V 76 (BitVec.setWidth 32 g.rdi)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [tlsA, lq, ix, tt, s1, bd, a6, o1v, s2, m2, a9, o2v] at h e1 e2 f0 f1 f2 f3 f4 f5 f6 f8 f12 f9 ⊢
  have hd := decide_eq_true h
  cfx [h, hd, e1, e2]
  all_goals vfin
  rfin

/-- Both entries nonzero: `c` plus the third level's entry (92). -/
theorem vc_hit {fb : Addr} {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (h : (s1 V fb (BitVec.setWidth 32 g.rdi)).toNat < (bd V fb).toNat)
    (e1 : (o1v V fb (BitVec.setWidth 32 g.rdi) == 0) = false)
    (e2 : (o2v V fb (BitVec.setWidth 32 g.rdi) == 0) = false)
    (f0 : ∀ i < 8, Foot F.data (Addr.add (tlsA fb) i)) (f1 : ∀ i < 8, Foot F.data (Addr.add rdq(V, tlsA fb) i))
    (f2 : ∀ i < 2, Foot F.data (Addr.add (lq V fb + 208#64) i))
    (f3 : ∀ i < 8, Foot F.data (Addr.add (lq V fb + ix V fb * 8#64 + 64#64) i))
    (f4 : ∀ i < 4, Foot F.data (Addr.add (tt V fb) i)) (f5 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 4#64) i))
    (f6 : ∀ i < 4, Foot F.data (Addr.add (a6 V fb (BitVec.setWidth 32 g.rdi)) i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 8#64) i))
    (f12 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 12#64) i))
    (f9 : ∀ i < 4, Foot F.data (Addr.add (a9 V fb (BitVec.setWidth 32 g.rdi)) i))
    (f16 : ∀ i < 4, Foot F.data (Addr.add (tt V fb + 16#64) i))
    (f11 : ∀ i < 4, Foot F.data (Addr.add (a11 V fb (BitVec.setWidth 32 g.rdi)) i)) :
    W_0 fb F Wl (Qr g V 92 (BitVec.setWidth 32 g.rdi + dl V fb (BitVec.setWidth 32 g.rdi))) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [tlsA, lq, ix, tt, s1, bd, a6, o1v, s2, m2, a9, o2v, a11, dl] at h e1 e2 f0 f1 f2 f3 f4 f5 f6 ⊢
  dsimp only [tlsA, lq, ix, tt, s1, bd, a6, o1v, s2, m2, a9, o2v, a11, dl] at f8 f12 f9 f16 f11
  have hd := decide_eq_true h
  cfx [h, hd, e1, e2]
  all_goals vfin
  rfin

/-! ## `towupper` -/

/-- What `towupper` needs at its entry: the return address in the footprint's data and on code, the loads in the
footprint's data, `U c` = `tupF V fb c`. -/
structure TupT (F : Footprint) (L : List (Addr × List Byte)) (fb : Addr) (U : BitVec 32 → BitVec 32) (g : Gprs)
    (V : Addr → Byte) : Prop where
  hl : ∀ i < 8, Foot F.data (Addr.add g.rsp i)
  ret : ∃ (e₂ : Addr) (code₂ : List Byte) (j₂ : Nat), CodeIn L e₂ code₂ ∧ j₂ < code₂.length ∧
    ofBytesLE 64 (List.map V (byteAddrs g.rsp 8)) = e₂.add j₂
  rd : RdOk F V fb (BitVec.setWidth 32 g.rdi)
  up : tupF V fb (BitVec.setWidth 32 g.rdi) = U (BitVec.setWidth 32 g.rdi)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}

/-- `towupper` in a run with its code, whose start has the `fs` base `fb`: `eax` = `U c` at the return address. -/
theorem tup_fnK {fb : Addr} (c : Seg prof F Wl L s₀ o) (hfs : s₀.cpu.seg.fsBase = fb) (hin : CodeIn L tup_at tup)
    (U : BitVec 32 → BitVec 32) :
    FnK prof F Wl L s₀ o Sen.tup_at (TupT F L fb U) (Sen.Rt U) := by
  refine ⟨?_⟩
  intro gev gP gE X t V hK hA hrip hT k
  obtain ⟨hl, ⟨e₂, code₂, j₂, hin₂, h₂, hra⟩, hR, hU⟩ := hT
  have go : ∀ (j : Nat) (R : BitVec 32), j < tup.length → Dec prof.feat tup j (FV7z.mk .ret 64 [] 1) →
      R = U (BitVec.setWidth 32 X.cpu.gpr.rdi) →
      W_0 fb F Wl (Qr X.cpu.gpr V j R) X.cpu.gpr X.cpu.rflags V → GoG prof L o gev gP gE X t := by
    intro j R hj hd hRU hW
    refine (c_0 prof fb).run c hfs hin (Qr X.cpu.gpr V j R) hK hA (by rw [addr_add_zero]; exact hrip) hW ?_
    rintro j' g fl V₁ ⟨hj', hV₁, a, rc, rd, rs, ri, hg', ha⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    subst hj'
    have hspY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp := by
      rw [hgY, hg'] <;> rfl
    refine c.s_ret hKY hAY hin hj hrY hd (by rw [hspY]; exact hl) hin₂ h₂ (by rw [hspY]; exact hra) ?_
    rintro Z t₂ hKZ hAZ ⟨hrZ, hgZ⟩
    refine k Z t₂ V hKZ hAZ (hrZ.trans hra.symm) ⟨rfl, a, rc, rd, rs, ri, ?_, ha.trans hRU⟩
    rw [hgZ, hgY, hg'] <;> rfl
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := hR
  by_cases h1 : (s1 V fb (BitVec.setWidth 32 X.cpu.gpr.rdi)).toNat < (bd V fb).toNat
  · by_cases e1 : o1v V fb (BitVec.setWidth 32 X.cpu.gpr.rdi) = 0
    · exact go 76 (BitVec.setWidth 32 X.cpu.gpr.rdi) (lt_len (by decide)) (ret_76 _)
        (by rw [← hU, tupF, if_pos h1, if_pos e1])
        (vc_e1 h1 (beq_iff_eq.mpr e1) f0 f1 f2 f3 f4 f5 (f6 h1))
    · obtain ⟨g8, g12, g9⟩ := f7 h1 e1
      by_cases e2 : o2v V fb (BitVec.setWidth 32 X.cpu.gpr.rdi) = 0
      · exact go 76 (BitVec.setWidth 32 X.cpu.gpr.rdi) (lt_len (by decide)) (ret_76 _)
          (by rw [← hU, tupF, if_pos h1, if_neg e1, if_pos e2])
          (vc_e2 h1 (beq_eq_false_iff_ne.mpr e1) (beq_iff_eq.mpr e2) f0 f1 f2 f3 f4 f5 (f6 h1) g8 g12 g9)
      · obtain ⟨g16, g11⟩ := f8 h1 e1 e2
        exact go 92 _ (lt_len (by decide)) (ret_92 _)
          (by rw [← hU, tupF, if_pos h1, if_neg e1, if_neg e2])
          (vc_hit h1 (beq_eq_false_iff_ne.mpr e1) (beq_eq_false_iff_ne.mpr e2) f0 f1 f2 f3 f4 f5 (f6 h1) g8 g12 g9
            g16 g11)
  · exact go 76 (BitVec.setWidth 32 X.cpu.gpr.rdi) (lt_len (by decide)) (ret_76 _)
      (by rw [← hU, tupF, if_neg h1])
      (vc_big h1 f0 f1 f2 f3 f4 f5)

end FV7z.Tup
