import FV7z.Arl.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Tun.Inv
/-!
# `AString::ReAlloc` (PLAN.md §M, M1)

7-Zip's `AString::ReAlloc (newLimit)` at `0x44bfc0` in `7zzs` (`CPP/Common/MyString.cpp`): with `this` in `rdi`
and `newLimit` in `esi`, `newBuf = new char[newLimit + 1]` (`call` at 26 to `0x6029b0`), `memcpy (newBuf, _chars,
_len + 1)` (`_chars`: the 8 bytes at `this`, `_len`: the 4 at `this + 8`; `call` at 50 to the PLT entry at
`0x401070`), `delete [] _chars` (`call` at 58 to `0x6014f0`), then `_chars = newBuf`, `_limit = newLimit` (the 4
bytes at `this + 12`). `push r13; push r12; push rbp; push rbx; sub rsp, 8`; `rbx` = `this`, `rbp` = `newLimit`,
`r12` = `newBuf`, `r13` = the old `_chars` across the calls; `add rsp, 8`, the four `pop`s and `ret` (79).

The callees are hypotheses (`kn`, `km`, `kd`), as in `FV7z/Cib/Holds.lean`: each a continuation at its entry, given
the run from its return (`rsp` 40 below the entry's, the registers the code keeps as they were, after the last call
also the saved registers and the return address of `ReAlloc` as they were (`Sv`), and the callee's own post) on.

- `zl`, `gN`, `V0`: `newLimit` zero-extended; the registers and the bytes at the first `call`.
- `gM`: the registers at the `call` of `memcpy`; `Sv`: the saved registers and the return address; `W2`: the bytes
  after the stores of `_chars` and `_limit`.
- `vc_0`, `vc_31`, `vc_55`, `vc_63`: the verification conditions of the four pieces.
- `arl_ok`: from the entry, through the three callees, to the return address.
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Arl

/-- The `call`s to `operator new []`, `memcpy`'s PLT entry and `operator delete []`. -/
def pcn : List Byte := [0xe8, 0xd1, 0x69, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1796561] 5) := by dec_rfl
theorem wc_26 : pcn <+: arl.drop 26 := by decide +kernel
theorem call_26 (feat : Features) : Dec feat arl 26 (FV7z.mk .call 64 [.rel 1796561] 5) :=
  Dec.shift (j := 26) (k := 0) (pcn_0 feat) wc_26 (Nat.zero_le _)
def pcm : List Byte := [0xe8, 0x79, 0x50, 0xfb, 0xff]
theorem pcm_0 : ∀ feat, Dec feat pcm 0 (FV7z.mk .call 64 [.rel 18446744073709244537] 5) := by dec_rfl
theorem wc_50 : pcm <+: arl.drop 50 := by decide +kernel
theorem call_50 (feat : Features) : Dec feat arl 50 (FV7z.mk .call 64 [.rel 18446744073709244537] 5) :=
  Dec.shift (j := 50) (k := 0) (pcm_0 feat) wc_50 (Nat.zero_le _)
def pcd : List Byte := [0xe8, 0xf1, 0x54, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1791217] 5) := by dec_rfl
theorem wc_58 : pcd <+: arl.drop 58 := by decide +kernel
theorem call_58 (feat : Features) : Dec feat arl 58 (FV7z.mk .call 64 [.rel 1791217] 5) :=
  Dec.shift (j := 58) (k := 0) (pcd_0 feat) wc_58 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_79 : pret <+: arl.drop 79 := by decide +kernel
theorem ret_79 (feat : Features) : Dec feat arl 79 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 79) (k := 0) (pret_0 feat) w_79 (Nat.zero_le _)

/-- `newLimit` (`esi`) zero-extended. -/
abbrev zl (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)

/-- The registers at the first `call`: `rbx` = `this`, `rbp` = `newLimit`, `rdi` = `newLimit + 1`, four pushed, 8
more. -/
abbrev gN (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdi,
      rbp := zl g,
      rsp := g.rsp - 8 - 8 - 8 - 8 - 8,
      rdi := zl g + 1#64 }

/-- The bytes at the first `call`: `r13`, `r12`, `rbp`, `rbx` pushed. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r13 8)) (g.rsp - 8 - 8) (toBytesLE g.r12 8))
    (g.rsp - 8 - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8 - 8) (toBytesLE g.rbx 8)

/-- The registers at the `call` of `memcpy`: `r13` = `rsi` = the old `_chars`, `rdx` = `_len + 1`, `r12` = `rdi` =
`newBuf` (`rax`). -/
abbrev gM (V : Addr → Byte) (g : Gprs) : Gprs :=
  { g with
      r13 := rdq(V, g.rbx),
      rdx := (rdd(V, g.rbx + 8#64)).setWidth 64 + 1#64,
      rdi := g.rax,
      r12 := g.rax,
      rsi := rdq(V, g.rbx) }

/-- The saved `r13`, `r12`, `rbp`, `rbx` and the return address, for the registers `g` at the entry. -/
def Sv (V : Addr → Byte) (g : Gprs) (ra : Addr) : Prop :=
  rdq(V, g.rsp - 8) = g.r13 ∧ rdq(V, g.rsp - 16) = g.r12 ∧ rdq(V, g.rsp - 24) = g.rbp ∧
    rdq(V, g.rsp - 32) = g.rbx ∧ rdq(V, g.rsp) = ra

/-- The bytes after `_chars` = `p` and `_limit` = `v` for the object at `b`. -/
abbrev W2 (V : Addr → Byte) (b : Addr) (p : BitVec 64) (v : BitVec 32) : Addr → Byte :=
  Vst (Vst V b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4)

variable {F : Footprint} {Wl : List Rgn}

/-- `push r13; push r12; push rbp; push rbx; mov rbx, rdi; mov edi, esi; mov rbp, rdi; add rdi, 1; sub rsp, 8`. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 26 ∧ g' = gN g ∧ V' = V0 V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 hs4 ⊢
  wpx [W_0, o0, gN, V0, zl]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `operator new []`: `mov r13, [rbx]; mov edx, [rbx + 8]; mov rdi, rax; mov r12, rax; mov rsi, r13;
add rdx, 1`, to the `call` at 50. -/
theorem vc_31 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (g.rbx + 8#64) i))
    (h : ∀ fl, Q 50 (gM V g) fl V) :
    W_31 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 f8 h ⊢
  wpx [W_31, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `memcpy`: `mov rdi, r13`, to the `call` at 58. -/
theorem vc_55 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 58 { g with rdi := g.r13 } fl V) :
    W_55 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_55, o2]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator delete []`: `mov [rbx], r12; mov [rbx + 12], ebp; add rsp, 8; pop rbx; pop rbp; pop r12;
pop r13`, to the `ret` at 79. -/
theorem vc_63 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (hw12 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 12#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8) i))
    (hl4 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8#64 + 8 + 8 + 8) i))
    (h : ∀ fl, Q 79
      { g with
          rbx := rdq(W2 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8#64),
          rbp := rdq(W2 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8#64 + 8),
          r12 := rdq(W2 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8#64 + 8 + 8),
          r13 := rdq(W2 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8#64 + 8 + 8 + 8),
          rsp := g.rsp + 8#64 + 8 + 8 + 8 + 8 } fl
      (W2 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp))) :
    W_63 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw0 hw12 hl1 hl2 hl3 hl4 h ⊢
  wpx [W_63, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::ReAlloc (newLimit)` (`this` = `rdi`, `newLimit` = `esi`) from its entry. At `operator new []`'s entry
the registers are `gN` with `rsp` 48 below the entry's and the bytes `V0` with the return address pushed (`kn`); back
at 31 (`rsp` 40 below, `rbx` = `this`, `rbp` = `newLimit`, `P1`), at `memcpy`'s entry the registers are `gM`
(`km`); back at 55 (`r12` = `newBuf`, `r13` = the old `_chars`, `P2`), at `operator delete []`'s entry `rdi` =
the old `_chars` (`kd`); back at 63 (`r12` kept, `Sv`, `P3`), the run reaches the return address with `_chars` =
`newBuf` and `_limit` = `newLimit` (`W2`), and `rbx`, `rbp`, `r12`, `r13`, `rsp` restored (`kr`). -/
theorem arl_ok {P1 P2 P3 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L arl_at arl)
    {codeN codeM codeD : List Byte} (hinN : CodeIn L 0x6029b0#64 codeN) (hN : 0 < codeN.length)
    (hinM : CodeIn L 0x401070#64 codeM) (hM : 0 < codeM.length)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = arl_at)
    (hp : 48 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hs6 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 48) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (f8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 32 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kn : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 31) 8)) →
      Y.cpu.rip = 0x6029b0#64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = arl_at.add 31 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = zl X.cpu.gpr → P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (km : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V' (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 55) 8)) →
      Y.cpu.rip = 0x401070#64 → Y.cpu.gpr = (gM V' Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = arl_at.add 55 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₂.cpu.gpr.rbp = zl X.cpu.gpr → Z₂.cpu.gpr.r12 = Z.cpu.gpr.rax → Z₂.cpu.gpr.r13 = rdq(V', X.cpu.gpr.rdi) →
        P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V'' (X.cpu.gpr.rsp - 48) (toBytesLE (arl_at.add 63) 8)) →
      Y.cpu.rip = 0x6014f0#64 → Y.cpu.gpr = { Z₂.cpu.gpr with rdi := Z₂.cpu.gpr.r13 }.set 4 (X.cpu.gpr.rsp - 48) →
      (∀ (Z₃ : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₃ → Agree F Z₃.proc.mm.mem V₃ →
        Z₃.cpu.rip = arl_at.add 63 → Z₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 → Z₃.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₃.cpu.gpr.rbp = zl X.cpu.gpr → Z₃.cpu.gpr.r12 = Z₂.cpu.gpr.r12 → Sv V₃ X.cpu.gpr (e₂.add j₂) →
        P3 Z₃ V₃ → GoG prof L o gev gP gE Z₃ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₃ : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), P3 Z₃ V₃ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Z₃.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
        r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn40 : (X.cpu.gpr.rsp - 40).toNat = X.cpu.gpr.rsp.toNat - 40 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn48 : (X.cpu.gpr.rsp - 48).toNat = X.cpu.gpr.rsp.toNat - 48 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 32 := by
    rw [e24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have e40 : X.cpu.gpr.rsp - 8 - 8 - 8 - 8 - 8 = X.cpu.gpr.rsp - 40 := by
    rw [e32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn32, tn40]
    simp <;> omega
  have e48 : X.cpu.gpr.rsp - 40 - 8 = X.cpu.gpr.rsp - 48 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn40, tn48]
    simp <;> omega
  have r32 : X.cpu.gpr.rsp - 40 + 8#64 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn40, tn32]
    simp <;> omega
  have r24 : X.cpu.gpr.rsp - 32 + 8 = X.cpu.gpr.rsp - 24 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn32, tn24]
    simp <;> omega
  have r16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have r8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have r0 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the bytes outside the object as they were after the stores of `_chars` and `_limit`
  have m1 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (W2 W X.cpu.gpr.rdi p v) = (byteAddrs x 8).map W := by
    intro W p v x hx h
    have a1 := Tun.rd_Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) x 8
      (by rw [toBytesLE_length, t12]; omega) hx (by rw [toBytesLE_length, t12]; omega)
    have a2 := Tun.rd_Vst W X.cpu.gpr.rdi (toBytesLE p 8) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
    exact a1.trans a2
  have hrip' : X.cpu.rip = arl_at.add 0 := by rw [addr_add_zero]; exact hrip
  have hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 40 - 8) i) := by rw [e48]; exact hs6
  -- to the `call` of `operator new []`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 26 ∧ g' = gN X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3) (by rw [e32]; exact hs4)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hgY]; exact e40
  refine c.s_call hKY hAY hin (lt_len (by decide)) hrY (call_26 _) hinN hN (by decide) (by rw [hsY]; exact hst) ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, e48] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) := by
    rw [hg₂, hsY, e48, hgY]
  refine kn Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `operator new []`, to the `call` of `memcpy`
  intro Z V' t₃ hKZ hAZ hrZ hzs hzb _ hP1
  refine (c_31 prof).run c hin (fun j' g' _ V'' => j' = 50 ∧ g' = gM V' Z.cpu.gpr ∧ V'' = V') hKZ hAZ hrZ
    (vc_31 (by rw [hzb]; exact f0) (by rw [hzb]; exact f8) fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3' : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₃]; exact hzs
  refine c.s_call hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_50 _) hinM hM (by decide) (by rw [hs3']; exact hst) ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3', e48] at hA₄
  have hg₄' : Y₄.cpu.gpr = (gM V' Z.cpu.gpr).set 4 (X.cpu.gpr.rsp - 48) := by
    rw [hg₄, hs3', e48, hg₃]
  refine km Z V' hP1 Y₄ t₅ hK₄ hA₄ hr₄ hg₄' ?_
  -- back from `memcpy`, to the `call` of `operator delete []`
  intro Z₂ V'' t₆ hK₅ hA₅ hr₅ hz2s _ _ _ _ hP2
  refine (c_55 prof).run c hin (fun j' g' _ V₃ => j' = 58 ∧ g' = { Z₂.cpu.gpr with rdi := Z₂.cpu.gpr.r13 } ∧
      V₃ = V'') hK₅ hA₅ hr₅ (vc_55 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₃ ⟨rfl, rfl, hV₃⟩ Y₅ t₇ hK₆ hA₆ hr₆ hg₆ -
  subst V₃
  have hs5 : Y₅.cpu.gpr.rsp = X.cpu.gpr.rsp - 40 := by rw [hg₆]; exact hz2s
  refine c.s_call hK₆ hA₆ hin (lt_len (by decide)) hr₆ (call_58 _) hinD hD (by decide) (by rw [hs5]; exact hst) ?_
  rintro Y₆ t₈ hK₇ hA₇ ⟨hr₇, hg₇⟩
  rw [hs5, e48] at hA₇
  have hg₇' : Y₆.cpu.gpr = { Z₂.cpu.gpr with rdi := Z₂.cpu.gpr.r13 }.set 4 (X.cpu.gpr.rsp - 48) := by
    rw [hg₇, hs5, e48, hg₆]
  refine kd Z₂ V'' hP2 Y₆ t₈ hK₇ hA₇ hr₇ hg₇' ?_
  -- back from `operator delete []`: the stores, the `pop`s and the `ret`
  intro Z₃ V₃ t₉ hK₈ hA₈ hr₈ hz3s hz3b hz3p _ hSv hP3
  obtain ⟨hv13, hv12, hvbp, hvbx, hvra⟩ := hSv
  have hv : BitVec.setWidth 32 Z₃.cpu.gpr.rbp = BitVec.setWidth 32 X.cpu.gpr.rsi := by
    rw [hz3p]
    exact sw_64_32 _
  have hW : W2 V₃ Z₃.cpu.gpr.rbx Z₃.cpu.gpr.r12 (BitVec.setWidth 32 Z₃.cpu.gpr.rbp) =
      W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi) := by rw [hz3b, hv]
  have b1 : rdq(W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 32) =
      X.cpu.gpr.rbx := by
    rw [m1 V₃ _ _ (X.cpu.gpr.rsp - 32) (by rw [tn32]; omega) (by rw [tn32]; omega)]
    exact hvbx
  have b2 : rdq(W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 24) =
      X.cpu.gpr.rbp := by
    rw [m1 V₃ _ _ (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)]
    exact hvbp
  have b3 : rdq(W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 16) =
      X.cpu.gpr.r12 := by
    rw [m1 V₃ _ _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
    exact hv12
  have b4 : rdq(W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 8) =
      X.cpu.gpr.r13 := by
    rw [m1 V₃ _ _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
    exact hv13
  have b5 : rdq(W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp) =
      e₂.add j₂ := by
    rw [m1 V₃ _ _ X.cpu.gpr.rsp hp8 (by omega)]
    exact hvra
  have h32 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 32) i) := fun i hi => c.hws _ (hs4 i hi)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  refine (c_63 prof).run c hin (fun j' g' _ V₄ => j' = 79 ∧
      g' = { Z₃.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
        r13 := X.cpu.gpr.r13, rsp := X.cpu.gpr.rsp } ∧
      V₄ = W2 V₃ X.cpu.gpr.rdi Z₃.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) hK₈ hA₈ hr₈
    (vc_63 (by rw [hz3b]; exact w0) (by rw [hz3b]; exact w12) (by rw [hz3s, r32]; exact h32)
      (by rw [hz3s, r32, r24]; exact h24) (by rw [hz3s, r32, r24, r16]; exact h16)
      (by rw [hz3s, r32, r24, r16, r8]; exact h8)
      fun _ => ⟨rfl, by rw [hW, hz3s, r32, r24, r16, r8, r0, b1, b2, b3, b4], hW⟩) ?_
  rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U t₁₀ hKU hAU hrU hgU -
  subst V₄
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU]
  refine c.s_ret hKU hAU hin (lt_len (by decide)) hrU (ret_79 _) (by rw [hsU]; exact hl) hin₂ h₂
    (by rw [hsU]; exact b5) ?_
  rintro Z' t₁₁ hKZ' hAZ' ⟨hrZ', hgZ'⟩
  refine kr Z₃ V₃ Z' t₁₁ hP3 hKZ' hAZ' hrZ' ?_
  rw [hgZ', hgU]
  try rfl

end FV7z.Arl
