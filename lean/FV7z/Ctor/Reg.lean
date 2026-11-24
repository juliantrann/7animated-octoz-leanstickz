import FV7z.Sga.Holds
import FV7z.Raf.Holds
/-!
# 7-Zip's registrars, what they do (PLAN.md §M, constructors)

64 of the 101 constructors of `.init_array` are `endbr64; lea rdi, [rip + d]; jmp R`, with `R` one of 7-Zip's three
registrars (`RegisterArc`, `RegisterCodec`, `RegisterHasher`): each puts its argument at the end of a table of
`max` pointers if there is room, the count of the table in the 4 bytes just after it. Their contracts (`Rga.rga_ok`,
`Rgc.rgc_ok`, `Rgh.rgh_ok`) say the same of the bytes, `RegOut`, and of the run, `RegSpec`.

- `RegOut`: the bytes after a registrar's call, from those before.
- `RegOut.full`, `RegOut.st`, `RegOut.st'`: `RegOut` of the two outcomes, the second in the two orders of the
  stores (the count first: `RegisterCodec`, `RegisterHasher`; the entry first: `RegisterArc`).
- `RegOut.rd`: bytes apart from the table and its count are unchanged.
- `RegSpec`: the contract's shape, from the registrar's entry to its caller.
- `ja_t`, `ja_f`: what `cmp r32, k; ja` decides.
-/
namespace FV7z.Ctor
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
open FV7z.Sga (vo vr vs rd_out)

/-- The bytes `V'` after a registrar's call with `p`, from those before, `V`: its table at `tab` of `max` entries, the
count at `cnt`. If the count `n` is below `max`, the count is `n + 1`, the entry `n` is `p`, and the other bytes are
unchanged; else no byte changed. -/
def RegOut (cnt tab : Addr) (max : Nat) (p : BitVec 64) (V V' : Addr → Byte) : Prop :=
  if rdd(V, cnt).toNat < max then
    rdd(V', cnt) = rdd(V, cnt) + 1#32 ∧ rdq(V', tab + rdd(V, cnt).setWidth 64 * 8#64) = p ∧
      ∀ a : Addr, (a.toNat < cnt.toNat ∨ cnt.toNat + 4 ≤ a.toNat) →
        (a.toNat < tab.toNat + 8 * rdd(V, cnt).toNat ∨ tab.toNat + 8 * rdd(V, cnt).toNat + 8 ≤ a.toNat) →
        V' a = V a
  else V' = V

/-- The entry `n` of a table at `tab`, as a number, the table well below the top of the addresses. -/
theorem slot_toNat (tab : Addr) (n : BitVec 32) (h : tab.toNat + 8 * 2 ^ 32 ≤ 2 ^ 64) :
    (tab + n.setWidth 64 * 8#64).toNat = tab.toNat + 8 * n.toNat := by
  have := n.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The count one more, as `lea ecx, [rax + 1]` computes it. -/
theorem inc32 (n : BitVec 32) : (n.setWidth 64 + 1#64).setWidth 32 = n + 1#32 := by
  apply BitVec.eq_of_toNat_eq
  have := n.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `cmp r32, k; ja` taken: the register is above `k`. -/
theorem ja_t {n : BitVec 32} {k : Nat} (h : (!(decide (n.toNat < k) || decide (n = BitVec.ofNat 32 k))) = true)
    (hk : k < 2 ^ 32) : ¬ n.toNat < k + 1 := by
  intro hn
  rcases Nat.lt_or_ge n.toNat k with h1 | h1
  · simp [h1] at h
  · have e : n = BitVec.ofNat 32 k := BitVec.eq_of_toNat_eq (by simp; omega)
    simp [e] at h

/-- `cmp r32, k; ja` not taken: the register is at most `k`. -/
theorem ja_f {n : BitVec 32} {k : Nat} (h : (!(decide (n.toNat < k) || decide (n = BitVec.ofNat 32 k))) = false) :
    n.toNat < k + 1 := by
  apply Nat.lt_of_not_ge
  intro hn
  have h1 : ¬ n.toNat < k := by omega
  have h2 : n ≠ BitVec.ofNat 32 k := fun e => by
    subst e
    simp only [BitVec.toNat_ofNat] at hn
    have := Nat.mod_le k (2 ^ 32)
    omega
  simp [h1, h2] at h

theorem RegOut.full {cnt tab : Addr} {max : Nat} {p : BitVec 64} {V : Addr → Byte}
    (h : ¬ rdd(V, cnt).toNat < max) : RegOut cnt tab max p V V := by
  rw [RegOut, if_neg h]

/-- The table and its count where they fit, apart. -/
structure Lay (cnt tab : Addr) (max : Nat) : Prop where
  c4 : cnt.toNat + 4 ≤ 2 ^ 64
  t8 : tab.toNat + 8 * 2 ^ 32 ≤ 2 ^ 64
  ap : cnt.toNat = tab.toNat + 8 * max

/-- With room: the count stored, then the entry. -/
theorem RegOut.st {cnt tab e : Addr} {max : Nat} {p : BitVec 64} {c : BitVec 32} {V : Addr → Byte}
    (hm : rdd(V, cnt).toNat < max) (hc : c = rdd(V, cnt) + 1#32) (he : e.toNat = tab.toNat + 8 * rdd(V, cnt).toNat)
    (hl : Lay cnt tab max) :
    RegOut cnt tab max p V (Vst (Vst V cnt (toBytesLE c 4)) e (toBytesLE p 8)) := by
  obtain ⟨c4, t8, ap⟩ := hl
  have hn := (rdd(V, cnt)).isLt
  have he' : tab + rdd(V, cnt).setWidth 64 * 8#64 = e :=
    BitVec.eq_of_toNat_eq ((slot_toNat tab _ t8).trans he.symm)
  have e8 : e.toNat + 8 ≤ 2 ^ 64 := by omega
  have ec : e.toNat + 8 ≤ cnt.toNat := by omega
  rw [RegOut, if_pos hm, he']
  refine ⟨?_, ?_, fun a h1 h2 => ?_⟩
  · rw [vr (toBytesLE_length _ _) e8 c4 (.inl ec), vs (toBytesLE_length _ _) c4]
    exact (ofBytesLE_toBytesLE (n := 4) rfl _).trans hc
  · rw [vs (toBytesLE_length _ _) e8]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · have h3 : a.toNat < e.toNat ∨ e.toNat + 8 ≤ a.toNat := by omega
    rw [vo (toBytesLE_length _ _) e8 h3, vo (toBytesLE_length _ _) c4 h1]

/-- With room: the entry stored, then the count. -/
theorem RegOut.st' {cnt tab e : Addr} {max : Nat} {p : BitVec 64} {c : BitVec 32} {V : Addr → Byte}
    (hm : rdd(V, cnt).toNat < max) (hc : c = rdd(V, cnt) + 1#32) (he : e.toNat = tab.toNat + 8 * rdd(V, cnt).toNat)
    (hl : Lay cnt tab max) :
    RegOut cnt tab max p V (Vst (Vst V e (toBytesLE p 8)) cnt (toBytesLE c 4)) := by
  obtain ⟨c4, t8, ap⟩ := hl
  have hn := (rdd(V, cnt)).isLt
  have he' : tab + rdd(V, cnt).setWidth 64 * 8#64 = e :=
    BitVec.eq_of_toNat_eq ((slot_toNat tab _ t8).trans he.symm)
  have e8 : e.toNat + 8 ≤ 2 ^ 64 := by omega
  have ec : e.toNat + 8 ≤ cnt.toNat := by omega
  -- the count is read before the stores: name it, so the rewrites below leave it alone
  have hr : rdd(Vst (Vst V e (toBytesLE p 8)) cnt (toBytesLE c 4), cnt) = c := by
    rw [vs (toBytesLE_length _ _) c4]
    exact ofBytesLE_toBytesLE (n := 4) rfl _
  rw [RegOut, if_pos hm, he']
  refine ⟨hr.trans hc, ?_, fun a h1 h2 => ?_⟩
  · rw [vr (toBytesLE_length _ _) c4 e8 (.inr ec), vs (toBytesLE_length _ _) e8]
    exact ofBytesLE_toBytesLE (n := 8) rfl _
  · have h3 : a.toNat < e.toNat ∨ e.toNat + 8 ≤ a.toNat := by omega
    rw [vo (toBytesLE_length _ _) c4 h1, vo (toBytesLE_length _ _) e8 h3]

/-- Bytes apart from the table and its count are as before the call. -/
theorem RegOut.rd {cnt tab : Addr} {max : Nat} {p : BitVec 64} {V V' : Addr → Byte} (h : RegOut cnt tab max p V V')
    (hl : Lay cnt tab max) {x : Addr} {n : Nat} (hx : x.toNat + n ≤ 2 ^ 64)
    (hd : x.toNat + n ≤ tab.toNat ∨ cnt.toNat + 4 ≤ x.toNat) :
    List.map V' (byteAddrs x n) = List.map V (byteAddrs x n) := by
  unfold RegOut at h
  split at h
  · rename_i hm
    have ap := hl.ap
    exact rd_out (lo := tab.toNat) (hi := cnt.toNat + 4) (fun a ha => h.2.2 a (by omega) (by omega)) hx hd
  · rw [h]

variable {prof : Profile} {F : Footprint} {Wl : List Rgn} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}

/-- A registrar's contract, from its entry at `ra` to its caller: with the return address readable, below the top
and apart from the table and its count, the run gets to the return address with the bytes `RegOut` of those at the
entry for the argument in `rdi`, and the registers a call keeps as they were. -/
def RegSpec (prof : Profile) (F : Footprint) (Wl : List Rgn) (L : List (Addr × List Byte)) (s₀ : State) (o : Oracle)
    (ra cnt tab : Addr) (max : Nat) : Prop :=
  ∀ {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop} {X : State}
    {t : Nat} {V : Addr → Byte}, KeptW Wl s₀ X → Agree F X.proc.mm.mem V → X.cpu.rip = ra →
    (∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i)) → X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64 →
    (X.cpu.gpr.rsp.toNat + 8 ≤ tab.toNat ∨ cnt.toNat + 4 ≤ X.cpu.gpr.rsp.toNat) →
    ∀ {e₂ : Addr} {code₂ : List Byte} {j₂ : Nat}, CodeIn L e₂ code₂ → j₂ < code₂.length →
    rdq(V, X.cpu.gpr.rsp) = e₂.add j₂ →
    (∀ V' Z t', KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' → RegOut cnt tab max X.cpu.gpr.rdi V V' →
      Z.cpu.rip = e₂.add j₂ → Osv.Back X.cpu.gpr Z.cpu.gpr → GoG prof L o gev gP gE Z t') →
    GoG prof L o gev gP gE X t

/-- The registers a call keeps, at a callee's `ret` (before it pops). -/
def Kp (g g' : Gprs) : Prop :=
  g'.rsp = g.rsp ∧ g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧
    g'.r15 = g.r15

end FV7z.Ctor
