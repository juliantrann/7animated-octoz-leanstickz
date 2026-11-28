import FV7z.Ffa.Cuts
import FV7z.Ffp.Holds
/-!
# `CCodecs::FindFormatForArchiveType` (PLAN.md §M, M1)

7-Zip 26.06's `CCodecs::FindFormatForArchiveType (arcType)` at `0x5ced10` in `7zzs` (`CPP/UI/Common/LoadCodecs.cpp`;
`objdump -d`): `FOR_VECTOR (i, Formats) if (StringsAreEqualNoCase (Formats[i].Name, arcType)) return i; return -1;`
(`this` = `rdi`, `&arcType` = `rsi`; `Formats` at `this + 16`, its count at `this + 24`, `Name` at the item's
`+ 24`; `StringsAreEqualNoCase` at `0x44ba80` (`FV7z.Sen`), called at 58).

The same code as `FV7z.Ffp`'s `FindPairForPrefix` but for the offsets (one byte more from the `call`: the cut after
it is 63, the found `ret` 73), and the test after the `call`: `test al, al; je` back to the loop, so `al` not 0 is
the answer. The frame, the arithmetic, the result (`Ffp.Res`) and the pieces after the `call` are `FV7z.Ffp`'s.

No items: `eax` = -1 and the `ret` at 95 (`vc_0z`). Else the pushes, `rbx` = `i` = 0 (`vc_0n`), the loop's head (40):
the item's `Name`'s characters in `rdi`, those of `arcType` in `rsi` (`vc_40`), the `call` (58).
`StringsAreEqualNoCase` is a hypothesis (`Cmp`) for each item. After it (63): `al` not 0 gives `eax` = `i`, the pops
and the `ret` at 73 (`vc_63z`); else `i + 1` and back to 40 while below the count (`vc_63n`), or `eax` = -1, the pops
and the `ret` at 89 (`vc_63e`). `lpHead` is one item, `lpAll` the items from any one, `ffa_ok` the function.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ffa

/-! ## The instructions outside the blocks -/

def pc58 : List Byte := [0xe8, 0x31, 0xcd, 0xe7, 0xff]
def pret : List Byte := [0xc3]
theorem pc58_0 : ∀ feat, Dec feat pc58 0 (FV7z.mk .call 64 [.rel 18446744073707965745] 5) := by dec_rfl
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem wc58 : pc58 <+: ffa.drop 58 := by decide +kernel
theorem w_73 : pret <+: ffa.drop 73 := by decide +kernel
theorem w_89 : pret <+: ffa.drop 89 := by decide +kernel
theorem w_95 : pret <+: ffa.drop 95 := by decide +kernel
theorem call_58 (feat : Features) : Dec feat ffa 58 (FV7z.mk .call 64 [.rel 18446744073707965745] 5) :=
  Dec.shift (j := 58) (k := 0) (pc58_0 feat) wc58 (Nat.zero_le _)
theorem ret_73 (feat : Features) : Dec feat ffa 73 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 73) (k := 0) (pret_0 feat) w_73 (Nat.zero_le _)
theorem ret_89 (feat : Features) : Dec feat ffa 89 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 89) (k := 0) (pret_0 feat) w_89 (Nat.zero_le _)
theorem ret_95 (feat : Features) : Dec feat ffa 95 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 95) (k := 0) (pret_0 feat) w_95 (Nat.zero_le _)

/-- `StringsAreEqualNoCase`. -/
abbrev sen_at : Addr := 0x44ba80
theorem tgt58 : ffa_at.add (58 + 5) + BitVec.ofNat 64 18446744073707965745 = sen_at := by decide

/-! ## The pieces -/

/-- The registers at the loop's head the first time. -/
abbrev g40 (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
    rax := BitVec.setWidth 64 rdd(V, g.rdi + 24#64), rbx := 0#64, rsp := g.rsp - 8 - 8 - 8, rbp := g.rdi,
    r12 := g.rsi }
/-- The item's address read at 50. -/
abbrev ia (V : Addr → Byte) (g : Gprs) : Addr :=
  rdq(V, rdq(V, g.rbp + 16#64) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64)
/-- The registers at the `call`. -/
abbrev gC (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with rax := ia V g, rdx := rdq(V, g.rbp + 16#64), rsi := rdq(V, g.r12), rdi := rdq(V, ia V g + 24#64) }

variable {F : Footprint} {Wl : List Rgn}

/-- No items: `eax` = -1, the `ret` at 95. -/
theorem vc_0z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rdi + 24#64) = 0#32)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 24#64) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 95 ∧ g' = { g with rax := BitVec.setWidth 64 4294967295#32 } ∧ V' = V)
      g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h f8 ⊢
  wpx [W_0, W_90, W_11, o0, o7, o1, h, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, beq_self_eq_true,
    not_true_eq_false, not_false_eq_true, false_implies, Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- Pairs: the pushes, `i` = 0, to the loop's head. -/
theorem vc_0n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : rdd(V, g.rdi + 24#64) ≠ 0#32)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rdi + 24#64) i))
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = g40 V g ∧ V' = Ffp.V1 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [g40, Ffp.V1] at h f8 hs1 hs2 hs3 ⊢
  wpx [W_0, W_90, W_11, o0, o7, o1, lf_xz, BitVec.xor_self, BitVec.setWidth_zero, BitVec.and_self, beq_iff_eq,
    beq_eq_false_iff_ne, ne_eq, beq_self_eq_true, not_true_eq_false, not_false_eq_true, false_implies,
    Bool.true_eq_false, Bool.false_eq_true, implies_true]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | (intro hh; exact absurd hh (by decide))
    | apply And.intro
    | intro _)

/-- The loop's head to the `call`. -/
theorem vc_40 {g : Gprs} {f : Rflags} {V : Addr → Byte} (f0 : ∀ i < 8, Foot F.data (Addr.add (g.rbp + 16#64) i))
    (f12 : ∀ i < 8, Foot F.data (Addr.add g.r12 i))
    (fi : ∀ i < 8,
      Foot F.data (Addr.add (rdq(V, g.rbp + 16#64) + BitVec.setWidth 64 (BitVec.setWidth 32 g.rbx) * 8#64) i))
    (fp : ∀ i < 8, Foot F.data (Addr.add (ia V g + 24#64) i)) :
    W_40 F Wl (fun j' g' _ V' => j' = 58 ∧ g' = gC V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [gC, ia] at f0 f12 fi fp ⊢
  wpx [W_40, o3]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _)

/-- `StringsAreEqualNoCase` gave `al` not 0: the pops, the `ret` at 73. -/
theorem vc_63z {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : ¬BitVec.setWidth 8 g.rax = 0)
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_63 F Wl (fun j' g' _ V' => j' = 73 ∧ g' = Ffp.gZ V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ffp.gZ] at h p1 p2 p3 ⊢
  wpx [W_63, W_32, W_67, W_80, o4, o2, o5, o6, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh h)
    | apply And.intro
    | intro _)

/-- `al` 0 and `i + 1` below the count: back to the loop's head. -/
theorem vc_63n {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 8 g.rax = 0)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 24#64) i))
    (hc : ¬(rdd(V, g.rbp + 24#64).toNat < (BitVec.setWidth 32 g.rbx + 1#32).toNat ∨
      rdd(V, g.rbp + 24#64) = BitVec.setWidth 32 g.rbx + 1#32)) :
    W_63 F Wl (fun j' g' _ V' => j' = 40 ∧ g' = Ffp.gN g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ffp.gN] at h f8 hc ⊢
  wpx [W_63, W_32, W_67, W_80, o4, o2, o5, o6, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hh hc)
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-- `al` 0 and `i + 1` not below the count: the pops, the `ret` at 89. -/
theorem vc_63e {g : Gprs} {f : Rflags} {V : Addr → Byte} (h : BitVec.setWidth 8 g.rax = 0)
    (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbp + 24#64) i))
    (hc : rdd(V, g.rbp + 24#64).toNat < (BitVec.setWidth 32 g.rbx + 1#32).toNat ∨
      rdd(V, g.rbp + 24#64) = BitVec.setWidth 32 g.rbx + 1#32)
    (p1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (p2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (p3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i)) :
    W_63 F Wl (fun j' g' _ V' => j' = 89 ∧ g' = Ffp.gX V g ∧ V' = V) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only [Ffp.gX] at h f8 hc p1 p2 p3 ⊢
  wpx [W_63, W_32, W_67, W_80, o4, o2, o5, o6, Op.cmpmr, BitVec.and_self, beq_iff_eq, beq_eq_false_iff_ne, ne_eq,
    Bool.not_eq_true', Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  all_goals repeat' (first
    | exact rfl
    | assumption
    | exact trivial
    | (intro hh; exact absurd hc (not_or.2 hh))
    | (intro hh; exact absurd h hh)
    | apply And.intro
    | intro _)

/-! ## The frame -/

/-- The number of items, at `this + 24` (the entry's registers `g₀`, bytes `V₀`). -/
abbrev nP (V₀ : Addr → Byte) (g₀ : Gprs) : Nat := rdd(V₀, g₀.rdi + 24#64).toNat
/-- The items' pointers, at `this + 16`. -/
abbrev its (V₀ : Addr → Byte) (g₀ : Gprs) : Addr := rdq(V₀, g₀.rdi + 16#64)
/-- The `k`-th item's pointer's address. -/
abbrev slot (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := its V₀ g₀ + BitVec.ofNat 64 k * 8#64
/-- The `k`-th item. -/
abbrev itm (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := rdq(V₀, slot V₀ g₀ k)
/-- The `k`-th item's `Name`'s characters (at the item's `+ 24`). -/
abbrev nm (V₀ : Addr → Byte) (g₀ : Gprs) (k : Nat) : Addr := rdq(V₀, itm V₀ g₀ k + 24#64)
/-- The characters of `arcType`. -/
abbrev pfx (V₀ : Addr → Byte) (g₀ : Gprs) : Addr := rdq(V₀, g₀.rsi)

/-- The bytes `V` read as at the entry. -/
structure Dat (V₀ : Addr → Byte) (g₀ : Gprs) (V : Addr → Byte) : Prop where
  n : rdd(V, g₀.rdi + 24#64) = rdd(V₀, g₀.rdi + 24#64)
  it : 0 < nP V₀ g₀ → rdq(V, g₀.rdi + 16#64) = its V₀ g₀
  pf : 0 < nP V₀ g₀ → rdq(V, g₀.rsi) = pfx V₀ g₀
  sl : ∀ k < nP V₀ g₀, rdq(V, slot V₀ g₀ k) = itm V₀ g₀ k
  nm : ∀ k < nP V₀ g₀, rdq(V, itm V₀ g₀ k + 24#64) = nm V₀ g₀ k

/-- In the loop: `Dat`, the three registers pushed and the return address `ra`. -/
structure Inv (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (V : Addr → Byte) : Prop where
  d : Dat V₀ g₀ V
  r12 : rdq(V, g₀.rsp - 8#64) = g₀.r12
  rbp : rdq(V, g₀.rsp - 16#64) = g₀.rbp
  rbx : rdq(V, g₀.rsp - 24#64) = g₀.rbx
  ra : rdq(V, g₀.rsp) = ra

/-- The pushes: `Inv` with the entry's return address. -/
theorem inv1 (V₀ : Addr → Byte) (g₀ : Gprs) (hs : 32 ≤ g₀.rsp.toNat) (hs8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64)
    (n8 : Ffp.RdOk F g₀.rsp (g₀.rdi + 24#64) 4) (it : 0 < nP V₀ g₀ → Ffp.RdOk F g₀.rsp (g₀.rdi + 16#64) 8)
    (pf : 0 < nP V₀ g₀ → Ffp.RdOk F g₀.rsp g₀.rsi 8) (sl : ∀ k < nP V₀ g₀, Ffp.RdOk F g₀.rsp (slot V₀ g₀ k) 8)
    (nm' : ∀ k < nP V₀ g₀, Ffp.RdOk F g₀.rsp (itm V₀ g₀ k + 24#64) 8) {ra : Addr} (hra : rdq(V₀, g₀.rsp) = ra) :
    Inv V₀ g₀ ra (Ffp.V1 V₀ g₀) := by
  obtain ⟨s8, s16, s24, t8, t16, t24, e16, e24, -, e8, -⟩ := Ffp.sp_c g₀.rsp hs
  have hl := g₀.rsp.isLt
  have ap : ∀ {x : Addr} {m : Nat}, Ffp.RdOk F g₀.rsp x m →
      List.map (Ffp.V1 V₀ g₀) (byteAddrs x m) = List.map V₀ (byteAddrs x m) := fun h =>
    Ffp.v1_rd V₀ g₀ hs h.fits (by have := h.apart; omega)
  refine ⟨⟨congrArg (ofBytesLE 32) (ap n8), fun h => congrArg (ofBytesLE 64) (ap (it h)),
    fun h => congrArg (ofBytesLE 64) (ap (pf h)), fun k hk => congrArg (ofBytesLE 64) (ap (sl k hk)),
    fun k hk => congrArg (ofBytesLE 64) (ap (nm' k hk))⟩, ?_, ?_, ?_,
    (congrArg (ofBytesLE 64) (Ffp.v1_rd V₀ g₀ hs hs8 (Or.inr (Nat.le_refl _)))).trans hra⟩
  · rw [← e8]
    dsimp only [Ffp.V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst _ (g₀.rsp - 8 - 8) (toBytesLE g₀.rbp 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e16]
    dsimp only [Ffp.V1]
    rw [Tun.rd_Vst _ (g₀.rsp - 8 - 8 - 8) (toBytesLE g₀.rbx 8) _ 8 (by rw [toBytesLE_length]; omega)
        (by omega) (by rw [toBytesLE_length]; omega),
      Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · rw [← e24]
    dsimp only [Ffp.V1]
    rw [Tun.rd_Vst_self _ _ _ (toBytesLE_length _ _) (by omega)]
    exact ofBytesLE_toBytesLE (n := 8) rfl _

/-! ## The run -/

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ X : State} {o : Oracle} {t : Nat}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {V₀ : Addr → Byte} {g₀ : Gprs} {Same : Nat → Prop} {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}

/-- What the run needs around the function: its code and `StringsAreEqualNoCase`'s, the 32 bytes under the entry's `S`
it may store into, the 32 bytes from `S - 24` it reads (the registers pushed, the return address), and the bytes of
the items and of `arcType` it reads (`Ffp.RdOk`). -/
structure Env (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (V₀ : Addr → Byte) (g₀ : Gprs) :
    Prop where
  code : CodeIn L ffa_at ffa
  cfn : ∃ code, CodeIn L sen_at code ∧ 0 < code.length
  s0 : 32 ≤ g₀.rsp.toNat
  s8 : g₀.rsp.toNat + 8 ≤ 2 ^ 64
  w : ∀ i < 32, Foot Wl (Addr.add (g₀.rsp - 32#64) i)
  d : ∀ i < 32, Foot F.data (Addr.add (g₀.rsp - 24#64) i)
  n8 : Ffp.RdOk F g₀.rsp (g₀.rdi + 24#64) 4
  it : 0 < nP V₀ g₀ → Ffp.RdOk F g₀.rsp (g₀.rdi + 16#64) 8
  pf : 0 < nP V₀ g₀ → Ffp.RdOk F g₀.rsp g₀.rsi 8
  sl : ∀ k < nP V₀ g₀, Ffp.RdOk F g₀.rsp (slot V₀ g₀ k) 8
  nm : ∀ k < nP V₀ g₀, Ffp.RdOk F g₀.rsp (itm V₀ g₀ k + 24#64) 8

/-- The pops' and the `ret`'s bytes. -/
theorem Env.ft (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 24#64) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 24#64 + 8) m)) ∧
    (∀ m < 8, Foot F.data (Addr.add (g₀.rsp - 24#64 + 8 + 8) m)) ∧ (∀ m < 8, Foot F.data (Addr.add g₀.rsp m)) := by
  obtain ⟨-, -, -, a0, a8, a16, a24⟩ := Ffp.sp_w g₀.rsp
  exact ⟨Ffp.off_ft hE.d 0 a0 (by decide), Ffp.off_ft hE.d 8 a8 (by decide), Ffp.off_ft hE.d 16 a16 (by decide),
    Ffp.off_ft hE.d 24 a24 (by decide)⟩

/-- The pushes' bytes. -/
theorem Env.wf (hE : Env F Wl L V₀ g₀) :
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8) m)) ∧ (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8) m)) ∧
    (∀ m < 8, Foot Wl (Addr.add (g₀.rsp - 8 - 8 - 8) m)) := by
  obtain ⟨a24, a16, a8, -⟩ := Ffp.sp_w g₀.rsp
  exact ⟨Ffp.off_ft hE.w 24 a24 (by decide), Ffp.off_ft hE.w 16 a16 (by decide), Ffp.off_ft hE.w 8 a8 (by decide)⟩

/-- What the function asks of `StringsAreEqualNoCase` (at `sen_at`) for the `i`-th item: from its entry with `rsp` =
`S - 32`, the return address into the function there, `Inv` for the bytes `V` under it, `rdi` the characters of the
`i`-th item's `Name` and `rsi` those of `arcType`, the run goes on to the goal if it does from every state at the return
address with `Inv`, `rsp` = `S - 24`, the registers a call keeps, and `al` not 0 just when `Same i`. -/
def Cmp (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Same : Nat → Prop) : Prop :=
  ∀ (i : Nat) (Y : State) (t : Nat) (V : Addr → Byte), i < nP V₀ g₀ → KeptW Wl s₀ Y → Inv V₀ g₀ ra V →
    Agree F Y.proc.mm.mem (Vst V (g₀.rsp - 32#64) (toBytesLE (ffa_at.add 63) 8)) → Y.cpu.rip = sen_at →
    Y.cpu.gpr.rsp = g₀.rsp - 32#64 → Y.cpu.gpr.rdi = nm V₀ g₀ i → Y.cpu.gpr.rsi = pfx V₀ g₀ →
    (∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Inv V₀ g₀ ra V' →
      Z.cpu.rip = ffa_at.add 63 → Z.cpu.gpr.rsp = g₀.rsp - 24#64 → Z.cpu.gpr.rbx = Y.cpu.gpr.rbx →
      Z.cpu.gpr.rbp = Y.cpu.gpr.rbp → Z.cpu.gpr.r12 = Y.cpu.gpr.r12 → Z.cpu.gpr.r13 = Y.cpu.gpr.r13 →
      Z.cpu.gpr.r14 = Y.cpu.gpr.r14 → Z.cpu.gpr.r15 = Y.cpu.gpr.r15 →
      (¬BitVec.setWidth 8 Z.cpu.gpr.rax = 0 ↔ Same i) → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE Y t

/-- What the caller asks at the return address `ra`: the bytes `Dat`, the registers a call keeps, the result. -/
def Ret (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Same : Nat → Prop) : Prop :=
  ∀ (Z : State) (t' : Nat) (V' : Addr → Byte), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → Dat V₀ g₀ V' →
    Z.cpu.rip = ra → Ffp.Bk g₀ Z.cpu.gpr → Ffp.Res Same (nP V₀ g₀) Z.cpu.gpr.rax → GoG prof L o gev gP gE Z t'

/-- From the loop's head for the `i`-th item, none of the ones before it `Same`, the run goes on to the goal. -/
def At (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (gev : List Event) (gP : State → Nat → List Event → Prop) (gE : Outcome → List Event → Prop)
    (V₀ : Addr → Byte) (g₀ : Gprs) (ra : Addr) (Same : Nat → Prop) (i : Nat) : Prop :=
  ∀ (Y : State) (t : Nat) (V : Addr → Byte), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Inv V₀ g₀ ra V →
    Y.cpu.rip = ffa_at.add 40 → Ffp.Rg g₀ Y.cpu.gpr i → (∀ k < i, ¬Same k) → GoG prof L o gev gP gE Y t

/-- A `ret` (at `j`) with `rsp` = `S`, the registers a call keeps and the result. -/
theorem fin (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same) {j : Nat} (hj : j < 96)
    (hd : Dec prof.feat ffa j (FV7z.mk .ret 64 [] 1)) {Y : State} {V : Addr → Byte} (hK : KeptW Wl s₀ Y)
    (hA : Agree F Y.proc.mm.mem V) (hD : Dat V₀ g₀ V) (hra : rdq(V, g₀.rsp) = e₂.add j₂)
    (hr : Y.cpu.rip = ffa_at.add j) (hs : Y.cpu.gpr.rsp = g₀.rsp) (hb : Y.cpu.gpr.rbx = g₀.rbx)
    (hp : Y.cpu.gpr.rbp = g₀.rbp) (h12 : Y.cpu.gpr.r12 = g₀.r12) (h13 : Y.cpu.gpr.r13 = g₀.r13)
    (h14 : Y.cpu.gpr.r14 = g₀.r14) (h15 : Y.cpu.gpr.r15 = g₀.r15) (hres : Ffp.Res Same (nP V₀ g₀) Y.cpu.gpr.rax) :
    GoG prof L o gev gP gE Y t := by
  refine c.s_ret hK hA hE.code (lt_len hj) hr hd (fun m hm => by rw [hs]; exact hE.ft.2.2.2 m hm) hin₂ h₂
    (by rw [hs]; exact hra) ?_
  rintro Z t' hKZ hAZ ⟨hrZ, hgZ⟩
  refine kE Z t' V hKZ hAZ hD hrZ ?_ ?_
  · rw [hgZ]
    exact ⟨congrArg (· + 8) hs, hb, hp, h12, h13, h14, h15⟩
  · rw [hgZ]
    exact hres

/-- The `i`-th item: the `call`, then the `ret` at 73 (`Same i`), the `i + 1`-th item, or the `ret` at 89. -/
theorem lpHead {i : Nat} (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hcmp : Cmp prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same) (hi : i < nP V₀ g₀)
    (kn : i + 1 < nP V₀ g₀ → At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same (i + 1)) :
    At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same i := by
  intro Y t V hK hA hI hr hR hno
  have hn32 : nP V₀ g₀ < 2 ^ 32 := (rdd(V₀, g₀.rdi + 24#64)).isLt
  have hn : 0 < nP V₀ g₀ := by omega
  obtain ⟨-, -, -, -, -, -, -, -, x32, -, p16, p8, p0⟩ := Ffp.sp_c g₀.rsp hE.s0
  obtain ⟨q0, q8, q16, -⟩ := hE.ft
  have hsw : BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) = BitVec.ofNat 64 i := by
    rw [hR.rbx]
    exact Ffp.sw32 (by omega)
  have ea : rdq(V, Y.cpu.gpr.rbp + 16#64) + BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) * 8#64 =
      slot V₀ g₀ i := by
    rw [hsw, hR.rbp, hI.d.it hn]
  have eia : ia V Y.cpu.gpr = itm V₀ g₀ i := by
    show rdq(V, rdq(V, Y.cpu.gpr.rbp + 16#64) + BitVec.setWidth 64 (BitVec.setWidth 32 Y.cpu.gpr.rbx) * 8#64) = _
    rw [ea, hI.d.sl i hi]
  -- to the `call`
  refine (c_40 prof).run c hE.code (fun j' g' _ V' => j' = 58 ∧ g' = gC V Y.cpu.gpr ∧ V' = V) hK hA hr
    (vc_40 (fun m hm => by rw [hR.rbp]; exact (hE.it hn).ft m hm) (fun m hm => by rw [hR.r12]; exact (hE.pf hn).ft m hm)
      (fun m hm => by rw [ea]; exact (hE.sl i hi).ft m hm) (fun m hm => by rw [eia]; exact (hE.nm i hi).ft m hm)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y₁ t₁ hK₁ hA₁ hr₁ hg₁ -
  subst V₁
  obtain ⟨codeC, hinC, hC0⟩ := hE.cfn
  have hsY : Y₁.cpu.gpr.rsp = g₀.rsp - 24#64 := by rw [hg₁]; exact hR.rsp
  refine c.s_call hK₁ hA₁ hE.code (lt_len (by decide)) hr₁ (call_58 _) hinC hC0 tgt58
    (fun m hm => by rw [hsY, x32]; exact hE.w m (by omega)) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, x32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gC V Y.cpu.gpr).set 4 (g₀.rsp - 32#64) := by
    rw [hg₂, hg₁]
    exact congrArg (fun v => (gC V Y.cpu.gpr).set 4 v) ((congrArg (· - 8) hR.rsp).trans x32)
  -- `StringsAreEqualNoCase`
  refine hcmp i Y₂ t₂ V hi hK₂ hI hA₂ hr₂ (by rw [hg₂']; rfl)
    (by rw [hg₂']; show rdq(V, ia V Y.cpu.gpr + 24#64) = _; rw [eia, hI.d.nm i hi])
    (by rw [hg₂']; show rdq(V, Y.cpu.gpr.r12) = _; rw [hR.r12, hI.d.pf hn]) ?_
  intro Z t' V' hKZ hAZ hI' hrZ zs hzb hzp hz12 hz13 hz14 hz15 hsame
  rw [hg₂'] at hzb hzp hz12 hz13 hz14 hz15
  have zb : Z.cpu.gpr.rbx = BitVec.ofNat 64 i := hzb.trans hR.rbx
  have zp : Z.cpu.gpr.rbp = g₀.rdi := hzp.trans hR.rbp
  have z12 : Z.cpu.gpr.r12 = g₀.rsi := hz12.trans hR.r12
  have z13 : Z.cpu.gpr.r13 = g₀.r13 := hz13.trans hR.r13
  have z14 : Z.cpu.gpr.r14 = g₀.r14 := hz14.trans hR.r14
  have z15 : Z.cpu.gpr.r15 = g₀.r15 := hz15.trans hR.r15
  by_cases hS : Same i
  · -- found: the `ret` at 73
    refine (c_63 prof).run c hE.code (fun j' g' _ V'' => j' = 73 ∧ g' = Ffp.gZ V' Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_63z (hsame.2 hS) (by rw [zs]; exact q0) (by rw [zs]; exact q8) (by rw [zs]; exact q16)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    have hrx : (Ffp.gZ V' Z.cpu.gpr).rax = BitVec.ofNat 64 i := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rbx) = _
      rw [zb]
      exact Ffp.sw32 (by omega)
    exact fin c hE hin₂ h₂ kE (by decide) (ret_73 _) hK₃ hA₃ hI'.d hI'.ra hr₃
      (by rw [hg₃]; show Z.cpu.gpr.rsp + 8 + 8 + 8 = _; rw [zs]; exact p0)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp) = _; rw [zs]; exact hI'.rbx)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8) = _; rw [zs, p16]; exact hI'.rbp)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8 + 8) = _; rw [zs, p8]; exact hI'.r12)
      (by rw [hg₃]; exact z13) (by rw [hg₃]; exact z14) (by rw [hg₃]; exact z15)
      (Or.inl ⟨i, hi, by rw [hg₃]; exact hrx, hS, hno⟩)
  have hz : BitVec.setWidth 8 Z.cpu.gpr.rax = 0 := Classical.byContradiction fun h => hS (hsame.1 h)
  by_cases hlt : i + 1 < nP V₀ g₀
  · -- the next item
    refine (c_63 prof).run c hE.code (fun j' g' _ V'' => j' = 40 ∧ g' = Ffp.gN Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_63n hz (by rw [zp]; exact hE.n8.ft) (by rw [zp, zb, hI'.d.n]; exact Ffp.cmp_lt hlt)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    have hbx : (Ffp.gN Z.cpu.gpr).rbx = BitVec.ofNat 64 (i + 1) := by
      show BitVec.setWidth 64 (BitVec.setWidth 32 Z.cpu.gpr.rbx + 1#32) = _
      rw [zb]
      exact Ffp.inc32 (by omega)
    refine kn hlt Y₃ t₃ V' hK₃ hA₃ hI' hr₃ ?_ ?_
    · rw [hg₃]
      exact ⟨zs, hbx, zp, z12, z13, z14, z15⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact hno k hk
      · exact hS
  · -- none: the `ret` at 89
    refine (c_63 prof).run c hE.code (fun j' g' _ V'' => j' = 89 ∧ g' = Ffp.gX V' Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
      (vc_63e hz (by rw [zp]; exact hE.n8.ft) (by rw [zp, zb, hI'.d.n]; exact Ffp.cmp_ge hi hlt) (by rw [zs]; exact q0)
        (by rw [zs]; exact q8) (by rw [zs]; exact q16)) ?_
    rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₃ hK₃ hA₃ hr₃ hg₃ -
    subst V₂
    exact fin c hE hin₂ h₂ kE (by decide) (ret_89 _) hK₃ hA₃ hI'.d hI'.ra hr₃
      (by rw [hg₃]; show Z.cpu.gpr.rsp + 8 + 8 + 8 = _; rw [zs]; exact p0)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp) = _; rw [zs]; exact hI'.rbx)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8) = _; rw [zs, p16]; exact hI'.rbp)
      (by rw [hg₃]; show rdq(V', Z.cpu.gpr.rsp + 8 + 8) = _; rw [zs, p8]; exact hI'.r12)
      (by rw [hg₃]; exact z13) (by rw [hg₃]; exact z14) (by rw [hg₃]; exact z15)
      (Or.inr ⟨by rw [hg₃], fun k hk => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 (show k < i + 1 by omega) with hk | rfl
        · exact hno k hk
        · exact hS⟩)

/-- The items from any one: by the number left. -/
theorem lpAll (c : Seg prof F Wl L s₀ o) (hE : Env F Wl L V₀ g₀) (hin₂ : CodeIn L e₂ code₂)
    (h₂ : j₂ < code₂.length) (hcmp : Cmp prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same)
    (kE : Ret prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same) :
    ∀ (m i : Nat), i + m + 1 = nP V₀ g₀ → At prof F Wl L s₀ o gev gP gE V₀ g₀ (e₂.add j₂) Same i
  | 0, _, h => lpHead c hE hin₂ h₂ hcmp kE (by omega) fun h' => absurd h' (by omega)
  | m + 1, i, h => lpHead c hE hin₂ h₂ hcmp kE (by omega) fun _ => lpAll c hE hin₂ h₂ hcmp kE m (i + 1) (by omega)

/-- `CCodecs::FindFormatForArchiveType (arcType)` (`this` = `rdi`, `&arcType` = `rsi`, the entry's bytes `V`): if
`StringsAreEqualNoCase` runs for each item as `Cmp` says (`al` not 0 just when `Same i`), the run reaches the return
address with the bytes it read as they were, the registers a call keeps, and in `rax` the first `i` with `Same i`,
or -1 (`eax`) if there is none (`Ffp.Res`). -/
theorem ffa_ok (c : Seg prof F Wl L s₀ o) {V : Addr → Byte} (hE : Env F Wl L V X.cpu.gpr) (hK : KeptW Wl s₀ X)
    (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ffa_at) (hin₂ : CodeIn L e₂ code₂) (h₂ : j₂ < code₂.length)
    (hra : rdq(V, X.cpu.gpr.rsp) = e₂.add j₂)
    (hcmp : Cmp prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂) Same)
    (kE : Ret prof F Wl L s₀ o gev gP gE V X.cpu.gpr (e₂.add j₂) Same) :
    GoG prof L o gev gP gE X t := by
  obtain ⟨-, -, -, -, -, -, -, x24, -⟩ := Ffp.sp_c X.cpu.gpr.rsp hE.s0
  by_cases h0 : rdd(V, X.cpu.gpr.rdi + 24#64) = 0#32
  · -- no items: the `ret` at 95
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 95 ∧
        g' = { X.cpu.gpr with rax := BitVec.setWidth 64 4294967295#32 } ∧ V' = V) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0z h0 hE.n8.ft) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hn0 : nP V X.cpu.gpr = 0 := by
      show rdd(V, X.cpu.gpr.rdi + 24#64).toNat = 0
      rw [h0]
      rfl
    exact fin c hE hin₂ h₂ kE (by decide) (ret_95 _) hKY hAY
      ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ hra hrY (by rw [hgY]) (by rw [hgY])
      (by rw [hgY]) (by rw [hgY]) (by rw [hgY]) (by rw [hgY]) (by rw [hgY])
      (Or.inr ⟨by rw [hgY], fun k hk => absurd hk (by omega)⟩)
  · -- the pushes, then the loop from the first item
    obtain ⟨w1, w2, w3⟩ := hE.wf
    refine (c_0 prof).run c hE.code (fun j' g' _ V' => j' = 40 ∧ g' = g40 V X.cpu.gpr ∧ V' = Ffp.V1 V X.cpu.gpr) hK hA
      (by rw [addr_add_zero]; exact hrip) (vc_0n h0 hE.n8.ft w1 w2 w3) ?_
    rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
    subst V₁
    have hn : 0 < nP V X.cpu.gpr := by
      have : rdd(V, X.cpu.gpr.rdi + 24#64).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
      show 0 < rdd(V, X.cpu.gpr.rdi + 24#64).toNat
      omega
    exact lpAll c hE hin₂ h₂ hcmp kE (nP V X.cpu.gpr - 1) 0 (by omega) Y t₁ _ hKY hAY
      (inv1 V X.cpu.gpr hE.s0 hE.s8 hE.n8 hE.it hE.pf hE.sl hE.nm hra) hrY
      ⟨by rw [hgY]; exact x24, by rw [hgY], by rw [hgY], by rw [hgY], by rw [hgY], by rw [hgY], by rw [hgY]⟩
      (fun k hk => absurd hk (Nat.not_lt_zero k))

end FV7z.Ffa
