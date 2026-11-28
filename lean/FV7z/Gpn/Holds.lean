import FV7z.Gpn.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `GetPropName` (PLAN.md §M, M1)

7-Zip 26.06's `static void GetPropName (PROPID propID, const wchar_t *name, AString &nameA, UString &nameU)` at
`0x5ebc80` in `7zzs` (`CPP/7zip/UI/Console/List.cpp`; `objdump -d`), `propID` in `edi`, `name` in `rsi`, `nameA` in
`rdx`, `nameU` in `rcx`: `mov r8d, edi; mov rdi, rdx; cmp r8d, 0x68; jbe 56`.

- A known `propID` (at most 0x68, the size of `kPropIdToName` less one): at 56 `lea rax, [rip + …]` (the table at
  `0x77f520`), `mov rsi, [rax + r8 * 8]`, then a tail jump (67) to `AString::operator= (const char *)` (`0x44c4c0`)
  with `rdi` = `nameA`, `rsi` the table's entry.
- Else with `name` (`test rsi, rsi; je 32` not taken): `mov rdi, rcx`, a tail jump (20) to
  `UString::operator= (const wchar_t *)` (`0x44d670`) with `rdi` = `nameU`, `rsi` = `name`.
- Else (32): `nameA.Empty ()` as `mov rax, [rdx]; mov dword [rdx + 8], 0; mov esi, r8d; mov byte [rax], 0` (`Emp`),
  then a tail jump (48) to `AString::Add_UInt32` (`0x44c980`) with `rdi` = `nameA`, `esi` = `propID`.

No stack is used. The three callees are hypotheses (`kS`, `kU`, `kA`): continuations at their entries.

- `KS`: the callee-saved registers as they were; `pid`: `propID`; `ent`: the table entry's address.
- `Emp`: the bytes after `nameA.Empty ()`.
- `kn_t`, `kn_f`: the `jbe` at 10 as a bound on `propID`.
- `vc_0`: the code from the entry to the three jumps; `gpn_ok`: from the entry to the three callees' entries.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Gpn

/-- The tail jump to `UString::operator= (const wchar_t *)`. -/
def pjU : List Byte := [0xe9, 0xd7, 0x19, 0xe6, 0xff]
theorem pjU_0 : ∀ feat, Dec feat pjU 0 (FV7z.mk .jmp 64 [.rel 18446744073707854295] 5) := by dec_rfl
theorem wjU_20 : pjU <+: gpn.drop 20 := by decide +kernel
theorem jmp_20 (feat : Features) : Dec feat gpn 20 (FV7z.mk .jmp 64 [.rel 18446744073707854295] 5) :=
  Dec.shift (j := 20) (k := 0) (pjU_0 feat) wjU_20 (Nat.zero_le _)

/-- The tail jump to `AString::Add_UInt32`. -/
def pjA : List Byte := [0xe9, 0xcb, 0x0c, 0xe6, 0xff]
theorem pjA_0 : ∀ feat, Dec feat pjA 0 (FV7z.mk .jmp 64 [.rel 18446744073707850955] 5) := by dec_rfl
theorem wjA_48 : pjA <+: gpn.drop 48 := by decide +kernel
theorem jmp_48 (feat : Features) : Dec feat gpn 48 (FV7z.mk .jmp 64 [.rel 18446744073707850955] 5) :=
  Dec.shift (j := 48) (k := 0) (pjA_0 feat) wjA_48 (Nat.zero_le _)

/-- The tail jump to `AString::operator= (const char *)`. -/
def pjS : List Byte := [0xe9, 0xf8, 0x07, 0xe6, 0xff]
theorem pjS_0 : ∀ feat, Dec feat pjS 0 (FV7z.mk .jmp 64 [.rel 18446744073707849720] 5) := by dec_rfl
theorem wjS_67 : pjS <+: gpn.drop 67 := by decide +kernel
theorem jmp_67 (feat : Features) : Dec feat gpn 67 (FV7z.mk .jmp 64 [.rel 18446744073707849720] 5) :=
  Dec.shift (j := 67) (k := 0) (pjS_0 feat) wjS_67 (Nat.zero_le _)

/-- `UString::operator= (const wchar_t *)`. -/
abbrev u_at : Addr := 0x44d670
/-- `AString::Add_UInt32`. -/
abbrev a_at : Addr := 0x44c980
/-- `AString::operator= (const char *)`. -/
abbrev s_at : Addr := 0x44c4c0

theorem tgt_20 : gpn_at.add (20 + 5) + BitVec.ofNat 64 18446744073707854295 = u_at.add 0 := by decide
theorem tgt_48 : gpn_at.add (48 + 5) + BitVec.ofNat 64 18446744073707850955 = a_at.add 0 := by decide
theorem tgt_67 : gpn_at.add (67 + 5) + BitVec.ofNat 64 18446744073707849720 = s_at.add 0 := by decide

/-! ## Names -/

/-- The callee-saved registers as they were. -/
abbrev KS (g g' : Gprs) : Prop :=
  g'.rbx = g.rbx ∧ g'.rbp = g.rbp ∧ g'.r12 = g.r12 ∧ g'.r13 = g.r13 ∧ g'.r14 = g.r14 ∧ g'.r15 = g.r15

/-- `propID`. -/
abbrev pid (g : Gprs) : BitVec 32 := BitVec.setWidth 32 g.rdi

/-- The address of `kPropIdToName[propID]`. -/
abbrev ent (g : Gprs) : Addr := 7861536#64 + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi) * 8#64

/-- The bytes after `nameA.Empty ()` (`nameA` at `p`): the length 0, then a 0 at the characters. -/
abbrev Emp (V : Addr → Byte) (p : Addr) : Addr → Byte :=
  Vst (Vst V (p + 8#64) (toBytesLE (BitVec.ofNat 32 0) 4)) rdq(V, p) (toBytesLE (BitVec.ofNat 8 0) 1)

/-- `cmp r8d, 0x68; jbe` taken. -/
theorem kn_t {s : BitVec 32} (h : s.toNat ≤ 104) : (decide (s.toNat < 104) || decide (s = 104#32)) = true := by
  by_cases h' : s.toNat < 104
  · simp [h']
  · have e : s = 104#32 := BitVec.eq_of_toNat_eq (by show s.toNat = 104; omega)
    simp [e]

/-- `cmp r8d, 0x68; jbe` not taken. -/
theorem kn_f {s : BitVec 32} (h : ¬s.toNat ≤ 104) : (decide (s.toNat < 104) || decide (s = 104#32)) = false := by
  have h1 : ¬s.toNat < 104 := by omega
  have h2 : s ≠ 104#32 := fun e => h (by subst e; decide)
  simp [h1, h2]

variable {F : Footprint} {Wl : List Rgn}

/-- From the entry to the three jumps: 67 (a known `propID`), 20 (`name`), 48 (neither, after `Emp`). -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hT : (BitVec.setWidth 32 g.rdi).toNat ≤ 104 →
      ∀ i < 8, Foot F.data (Addr.add (7861536#64 + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi) * 8#64) i))
    (fd : ¬(BitVec.setWidth 32 g.rdi).toNat ≤ 104 → g.rsi = 0 → ∀ i < 8, Foot F.data (Addr.add g.rdx i))
    (wd : ¬(BitVec.setWidth 32 g.rdi).toNat ≤ 104 → g.rsi = 0 → ∀ i < 4, Foot Wl (Addr.add (g.rdx + 8#64) i))
    (wc : ¬(BitVec.setWidth 32 g.rdi).toNat ≤ 104 → g.rsi = 0 → ∀ i < 1, Foot Wl (Addr.add rdq(V, g.rdx) i))
    (h67 : (BitVec.setWidth 32 g.rdi).toNat ≤ 104 → ∀ g', g'.rdi = g.rdx →
      g'.rsi = rdq(V, 7861536#64 + BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi) * 8#64) → g'.rsp = g.rsp →
      KS g g' → ∀ fl, Q 67 g' fl V)
    (h20 : ¬(BitVec.setWidth 32 g.rdi).toNat ≤ 104 → g.rsi ≠ 0 → ∀ g', g'.rdi = g.rcx → g'.rsi = g.rsi →
      g'.rsp = g.rsp → KS g g' → ∀ fl, Q 20 g' fl V)
    (h48 : ¬(BitVec.setWidth 32 g.rdi).toNat ≤ 104 → g.rsi = 0 → ∀ g', g'.rdi = g.rdx →
      g'.rsi = BitVec.setWidth 64 (BitVec.setWidth 32 g.rdi) → g'.rsp = g.rsp → KS g g' →
      ∀ fl, Q 48 g' fl (Emp V g.rdx)) :
    W_0 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hT fd wd wc h67 h20 h48 ⊢
  by_cases hk : (BitVec.setWidth 32 rdi).toNat ≤ 104
  · have hb := kn_t hk
    wpx [W_0, W_56, o0, o4, hb, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat' (first
      | refine h67 hk _ ?_ ?_ ?_ ?_ _
      | with_reducible rfl
      | exact trivial
      | with_reducible exact hT hk
      | apply And.intro
      | intro _)
  · have hb := kn_f hk
    by_cases h0 : rsi = 0
    · have hz : (rsi == 0) = true := beq_iff_eq.2 h0
      wpx [W_0, W_12, W_32, o0, o1, o3, hb, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
        false_implies, implies_true]
      all_goals repeat' (first
        | refine h48 hk h0 _ ?_ ?_ ?_ ?_ _
        | with_reducible rfl
        | exact trivial
        | with_reducible exact fd hk h0
        | with_reducible exact wd hk h0
        | with_reducible exact wc hk h0
        | apply And.intro
        | intro _)
    · have hz : (rsi == 0) = false := beq_eq_false_iff_ne.2 h0
      wpx [W_0, W_12, W_17, o0, o1, o2, hb, hz, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false,
        false_implies, implies_true]
      all_goals repeat' (first
        | refine h20 hk h0 _ ?_ ?_ ?_ ?_ _
        | with_reducible rfl
        | exact trivial
        | apply And.intro
        | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `GetPropName` from its entry (`g` = `X`'s registers): with `propID` at most 0x68 at `AString::operator= (const
char *)` with `rdi` = `nameA`, `rsi` = `kPropIdToName[propID]` (`kS`); else with `name` not NULL at
`UString::operator= (const wchar_t *)` with `rdi` = `nameU`, `rsi` = `name` (`kU`); else at `AString::Add_UInt32`
with `rdi` = `nameA`, `esi` = `propID` and `nameA` emptied (`Emp`, `kA`); `rsp` and the callee-saved registers as at
the entry. -/
theorem gpn_ok (c : Seg prof F Wl L s₀ o) (hin : CodeIn L gpn_at gpn)
    {codeU codeA codeS : List Byte} (hinU : CodeIn L u_at codeU) (hU : 0 < codeU.length)
    (hinA : CodeIn L a_at codeA) (hA' : 0 < codeA.length) (hinS : CodeIn L s_at codeS) (hS : 0 < codeS.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = gpn_at)
    (hT : (pid X.cpu.gpr).toNat ≤ 104 → ∀ i < 8, Foot F.data (Addr.add (ent X.cpu.gpr) i))
    (fd : ¬(pid X.cpu.gpr).toNat ≤ 104 → X.cpu.gpr.rsi = 0 → ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdx i))
    (wd : ¬(pid X.cpu.gpr).toNat ≤ 104 → X.cpu.gpr.rsi = 0 →
      ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdx + 8#64) i))
    (wc : ¬(pid X.cpu.gpr).toNat ≤ 104 → X.cpu.gpr.rsi = 0 → ∀ i < 1, Foot Wl (Addr.add rdq(V, X.cpu.gpr.rdx) i))
    (kS : (pid X.cpu.gpr).toNat ≤ 104 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = s_at →
      Y.cpu.gpr.rdi = X.cpu.gpr.rdx → Y.cpu.gpr.rsi = rdq(V, ent X.cpu.gpr) → Y.cpu.gpr.rsp = X.cpu.gpr.rsp →
      KS X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kU : ¬(pid X.cpu.gpr).toNat ≤ 104 → X.cpu.gpr.rsi ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem V → Y.cpu.rip = u_at →
      Y.cpu.gpr.rdi = X.cpu.gpr.rcx → Y.cpu.gpr.rsi = X.cpu.gpr.rsi → Y.cpu.gpr.rsp = X.cpu.gpr.rsp →
      KS X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t')
    (kA : ¬(pid X.cpu.gpr).toNat ≤ 104 → X.cpu.gpr.rsi = 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y → Agree F Y.proc.mm.mem (Emp V X.cpu.gpr.rdx) → Y.cpu.rip = a_at →
      Y.cpu.gpr.rdi = X.cpu.gpr.rdx → Y.cpu.gpr.rsi = BitVec.setWidth 64 (pid X.cpu.gpr) →
      Y.cpu.gpr.rsp = X.cpu.gpr.rsp → KS X.cpu.gpr Y.cpu.gpr → GoG prof L o gev gP gE Y t') :
    GoG prof L o gev gP gE X t := by
  refine (c_0 prof).run c hin (fun j' g' _ V' =>
      ((pid X.cpu.gpr).toNat ≤ 104 ∧ j' = 67 ∧ V' = V ∧ g'.rdi = X.cpu.gpr.rdx ∧
        g'.rsi = rdq(V, ent X.cpu.gpr) ∧ g'.rsp = X.cpu.gpr.rsp ∧ KS X.cpu.gpr g') ∨
      (¬(pid X.cpu.gpr).toNat ≤ 104 ∧ X.cpu.gpr.rsi ≠ 0 ∧ j' = 20 ∧ V' = V ∧ g'.rdi = X.cpu.gpr.rcx ∧
        g'.rsi = X.cpu.gpr.rsi ∧ g'.rsp = X.cpu.gpr.rsp ∧ KS X.cpu.gpr g') ∨
      (¬(pid X.cpu.gpr).toNat ≤ 104 ∧ X.cpu.gpr.rsi = 0 ∧ j' = 48 ∧ V' = Emp V X.cpu.gpr.rdx ∧
        g'.rdi = X.cpu.gpr.rdx ∧ g'.rsi = BitVec.setWidth 64 (pid X.cpu.gpr) ∧ g'.rsp = X.cpu.gpr.rsp ∧
        KS X.cpu.gpr g'))
    hK hA (by rw [addr_add_zero]; exact hrip)
    (vc_0 hT fd wd wc
      (fun hk _ h1 h2 h3 h4 _ => Or.inl ⟨hk, rfl, rfl, h1, h2, h3, h4⟩)
      (fun hk h0 _ h1 h2 h3 h4 _ => Or.inr (Or.inl ⟨hk, h0, rfl, rfl, h1, h2, h3, h4⟩))
      (fun hk h0 _ h1 h2 h3 h4 _ => Or.inr (Or.inr ⟨hk, h0, rfl, rfl, h1, h2, h3, h4⟩))) ?_
  rintro j' g fl V₁ hpost Y t₁ hKY hAY hrY hgY -
  subst hgY
  rcases hpost with ⟨hk, rfl, hV, h1, h2, h3, h4⟩ | ⟨hk, h0, rfl, hV, h1, h2, h3, h4⟩ |
    ⟨hk, h0, rfl, hV, h1, h2, h3, h4⟩
  · -- a known `propID`: the tail jump to `AString::operator= (const char *)`
    rw [hV] at hAY
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_67 _) hinS (tgt := 0) hS tgt_67 ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kS hk Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact h1) (by rw [hg₂]; exact h2)
      (by rw [hg₂]; exact h3) (by rw [hg₂]; exact h4)
  · -- `name`: the tail jump to `UString::operator= (const wchar_t *)`
    rw [hV] at hAY
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_20 _) hinU (tgt := 0) hU tgt_20 ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kU hk h0 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact h1) (by rw [hg₂]; exact h2)
      (by rw [hg₂]; exact h3) (by rw [hg₂]; exact h4)
  · -- neither: `nameA` emptied, the tail jump to `AString::Add_UInt32`
    rw [hV] at hAY
    refine c.s_jmp_x hKY hAY hin (lt_len (by decide)) hrY (jmp_48 _) hinA (tgt := 0) hA' tgt_48 ?_
    rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
    exact kA hk h0 Y₂ t₂ hK₂ hA₂ (by rw [hr₂, addr_add_zero]) (by rw [hg₂]; exact h1) (by rw [hg₂]; exact h2)
      (by rw [hg₂]; exact h3) (by rw [hg₂]; exact h4)

end FV7z.Gpn
