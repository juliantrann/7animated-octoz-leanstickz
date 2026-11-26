import FV7z.Arb.Cuts
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.FnFar
import FV7z.Tun.Inv
/-!
# `AString::ReAlloc2` (PLAN.md §M, M1)

7-Zip's `AString::ReAlloc2 (newLimit)` at `0x44c010` in `7zzs` (`CPP/Common/MyString.cpp`): with `this` in `rdi`
and `newLimit` in `esi`, `push r12; push rbp; push rbx`; above `k_Alloc_Len_Limit` (`0x3ffffffe`) the `ja` at 14 to
the throw at `0x401350`; else `newBuf = new char[newLimit + 1]` (`call` at 31 to `0x6029b0`), `newBuf[0] = 0`,
`delete [] _chars` (`_chars`: the 8 bytes at `this`; `call` at 50 to `0x6014f0`) unless null, then `_chars =
newBuf`, `_limit = newLimit` (the 4 bytes at `this + 12`), `_len = 0` (at `this + 8`); the three `pop`s and `ret`
(72). `rbx` = `this`, `rbp` = `newLimit`, `r12` = `newBuf` across the calls.

The callees and the throw are hypotheses (`kn`, `kd`, `kt`), as in `FV7z/Cib/Holds.lean`.

- `c7`: the `ja` after `cmp esi, 0x3ffffffe`.
- `zl`, `gA`, `V0`, `gN`: `newLimit` zero-extended; the registers and the bytes after the `push`es; the registers at
  the first `call`.
- `Sv`: the saved registers and the return address; `W3`: the bytes after the stores of `_chars`, `_limit`, `_len`.
- `vc_0`, `vc_20`, `vc_36`, `vc_55`: the verification conditions of the four pieces.
- `arb_ok`: from the entry to the throw (`kt`), or through `operator new []` (`kn`) to the return address, with
  `_chars` null (`kz`) or through `operator delete []` (`kd`, `kr`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Arb

/-- The `ja` to the throw. -/
def pja : List Byte := [0x0f, 0x87, 0x2c, 0x53, 0xfb, 0xff]
theorem pja_0 : ∀ feat, Dec feat pja 0 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709245228] 6) := by dec_rfl
theorem wa_14 : pja <+: arb.drop 14 := by decide +kernel
theorem ja_14 (feat : Features) : Dec feat arb 14 (FV7z.mk (.jcc 7) 64 [.rel 18446744073709245228] 6) :=
  Dec.shift (j := 14) (k := 0) (pja_0 feat) wa_14 (Nat.zero_le _)

/-- The `call`s to `operator new []` and `operator delete []`. -/
def pcn : List Byte := [0xe8, 0x7c, 0x69, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1796476] 5) := by dec_rfl
theorem wc_31 : pcn <+: arb.drop 31 := by decide +kernel
theorem call_31 (feat : Features) : Dec feat arb 31 (FV7z.mk .call 64 [.rel 1796476] 5) :=
  Dec.shift (j := 31) (k := 0) (pcn_0 feat) wc_31 (Nat.zero_le _)
def pcd : List Byte := [0xe8, 0xa9, 0x54, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1791145] 5) := by dec_rfl
theorem wc_50 : pcd <+: arb.drop 50 := by decide +kernel
theorem call_50 (feat : Features) : Dec feat arb 50 (FV7z.mk .call 64 [.rel 1791145] 5) :=
  Dec.shift (j := 50) (k := 0) (pcd_0 feat) wc_50 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_72 : pret <+: arb.drop 72 := by decide +kernel
theorem ret_72 (feat : Features) : Dec feat arb 72 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 72) (k := 0) (pret_0 feat) w_72 (Nat.zero_le _)

/-- `ja` after `cmp m, 0x3ffffffe`: taken just above the limit. -/
theorem c7 (f : Rflags) (m : BitVec 32) :
    (subF f m (BitVec.ofNat 32 1073741822)).cond 7 = decide (1073741822 < m.toNat) := by
  have hy : (BitVec.ofNat 32 1073741822).toNat = 1073741822 := rfl
  have e : (m = BitVec.ofNat 32 1073741822) ↔ m.toNat = 1073741822 := by rw [BitVec.toNat_eq, hy]
  rw [cond_7, subF_cf, subF_zf, hy]
  by_cases h : 1073741822 < m.toNat
  · have h1 : ¬ m.toNat < 1073741822 := by omega
    have h2 : ¬ m = BitVec.ofNat 32 1073741822 := fun h' => by rw [e] at h'; omega
    simp [h, h1, h2]
  · by_cases h3 : m.toNat < 1073741822
    · simp [h, h3]
    · have h2 : m = BitVec.ofNat 32 1073741822 := e.2 (by omega)
      simp [h, h3, h2]

/-- `newLimit` (`esi`) zero-extended. -/
abbrev zl (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)

/-- The registers after the three `push`es. -/
abbrev gA (g : Gprs) : Gprs := { g with rsp := g.rsp - 8 - 8 - 8 }

/-- The bytes after the three `push`es. -/
abbrev V0 (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The registers at the first `call`: `rbx` = `this`, `rbp` = `newLimit`, `rdi` = `newLimit + 1`. -/
abbrev gN (g : Gprs) : Gprs :=
  { g with
      rbx := g.rdi,
      rbp := zl g,
      rsp := g.rsp - 8 - 8 - 8,
      rdi := zl g + 1#64 }

/-- The saved `r12`, `rbp`, `rbx` and the return address, for the registers `g` at the entry. -/
def Sv (V : Addr → Byte) (g : Gprs) (ra : Addr) : Prop :=
  rdq(V, g.rsp - 8) = g.r12 ∧ rdq(V, g.rsp - 16) = g.rbp ∧ rdq(V, g.rsp - 24) = g.rbx ∧ rdq(V, g.rsp) = ra

/-- The bytes after `_chars` = `p`, `_limit` = `v` and `_len` = 0 for the object at `b`. -/
abbrev W3 (V : Addr → Byte) (b : Addr) (p : BitVec 64) (v : BitVec 32) : Addr → Byte :=
  Vst (Vst (Vst V b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4)) (b + 8#64) (toBytesLE 0#32 4)

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; push rbp; push rbx; cmp esi, 0x3ffffffe`, to the `ja` at 14. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' f' V' => j' = 14 ∧ g' = gA g ∧ V' = V0 V g ∧
      f' = subF (rfz f) (BitVec.setWidth 32 g.rsi) (BitVec.ofNat 32 1073741822)) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 ⊢
  wpx [W_0, o0, gA, V0]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- `mov rbx, rdi; mov edi, esi; mov ebp, esi; add rdi, 1`, to the `call` at 31. -/
theorem vc_20 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (h : ∀ fl, Q 31 { g with rbx := g.rdi, rbp := zl g, rdi := zl g + 1#64 } fl V) :
    W_20 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at h ⊢
  wpx [W_20, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `operator new []`: `mov rdi, [rbx]; mov byte [rax], 0; mov r12, rax; test rdi, rdi; je 55`, else to
the `call` at 50. -/
theorem vc_36 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (f0 : ∀ i < 8, Foot F.data (Addr.add g.rbx i)) (wn : ∀ i < 1, Foot Wl (Addr.add g.rax i))
    (h55 : rdq(V, g.rbx) = 0 → ∀ fl, Q 55 { g with rdi := rdq(V, g.rbx), r12 := g.rax } fl
      (Vst V g.rax (toBytesLE 0#8 1)))
    (h50 : rdq(V, g.rbx) ≠ 0 → ∀ fl, Q 50 { g with rdi := rdq(V, g.rbx), r12 := g.rax } fl
      (Vst V g.rax (toBytesLE 0#8 1))) :
    W_36 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at f0 wn h55 h50 ⊢
  by_cases h0 : rdq(V, rbx) = 0
  · have hb : (rdq(V, rbx) == 0) = true := beq_iff_eq.2 h0
    wpx [W_36, o2, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h55 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hb : (rdq(V, rbx) == 0) = false := beq_eq_false_iff_ne.2 h0
    wpx [W_36, o2, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h50 h0 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- `mov [rbx], r12; mov [rbx + 12], ebp; mov dword [rbx + 8], 0; pop rbx; pop rbp; pop r12`, to the `ret` at 72. -/
theorem vc_55 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (hw0 : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (hw12 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 12#64) i))
    (hw8 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 8#64) i))
    (hl1 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl3 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 72
      { g with
          rbx := rdq(W3 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp),
          rbp := rdq(W3 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8),
          r12 := rdq(W3 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 } fl
      (W3 V g.rbx g.r12 (BitVec.setWidth 32 g.rbp))) :
    W_55 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hw0 hw12 hw8 hl1 hl2 hl3 h ⊢
  wpx [W_55, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `AString::ReAlloc2 (newLimit)` (`this` = `rdi`, `newLimit` = `esi`) from its entry. Above the limit, at the
throw with the registers `gA` and the bytes `V0` (`kt`). Else at `operator new []`'s entry the registers are `gN`
with `rsp` 32 below the entry's and the bytes `V0` with the return address pushed (`kn`); back at 36 (`rsp` 24 below,
`rbx` = `this`, `rbp` = `newLimit`, the first byte of `newBuf` (`rax`) writable and off the stack, `Sv`, `P1`): with
`_chars` null the run reaches the return address with `_chars` = `newBuf`, `_limit` = `newLimit`, `_len` = 0 (`W3`)
and `rbx`, `rbp`, `r12`, `rsp` restored (`kz`); else at `operator delete []`'s entry `rdi` = `_chars` (`kd`), and
back at 55 (`r12` = `newBuf`, `Sv`, `P2`) likewise (`kr`). -/
theorem arb_ok {P1 P2 : State → (Addr → Byte) → Prop} (c : Seg prof F Wl L s₀ o) (hin : CodeIn L arb_at arb)
    {codeT codeN codeD : List Byte} (hinT : CodeIn L 0x401350#64 codeT) (hT : 0 < codeT.length)
    (hinN : CodeIn L 0x6029b0#64 codeN) (hN : 0 < codeN.length)
    (hinD : CodeIn L 0x6014f0#64 codeD) (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = arb_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (f0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (w0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (w8 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (w12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kt : 1073741822 < (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (V0 V X.cpu.gpr) → Y.cpu.rip = 0x401350#64 → Y.cpu.gpr = gA X.cpu.gpr →
      GoG prof L o gev gP gE Y t')
    (kn : (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ 1073741822 → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (V0 V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (arb_at.add 36) 8)) →
      Y.cpu.rip = 0x6029b0#64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z : State) (V' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z → Agree F Z.proc.mm.mem V' →
        Z.cpu.rip = arb_at.add 36 → Z.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z.cpu.gpr.rbp = zl X.cpu.gpr → (∀ i < 1, Foot Wl (Addr.add Z.cpu.gpr.rax i)) →
        (Z.cpu.gpr.rax.toNat + 1 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ Z.cpu.gpr.rax.toNat) →
        Sv V' X.cpu.gpr (e₂.add j₂) → P1 Z V' → GoG prof L o gev gP gE Z t'') →
      GoG prof L o gev gP gE Y t')
    (kz : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) = 0 → ∀ (Z' : State) (t' : Nat),
      KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem
        (W3 (Vst V' Z.cpu.gpr.rax (toBytesLE 0#8 1)) X.cpu.gpr.rdi Z.cpu.gpr.rax (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr =
        { Z.cpu.gpr with
            rdi := rdq(V', X.cpu.gpr.rdi)
            rbx := X.cpu.gpr.rbx
            rbp := X.cpu.gpr.rbp
            r12 := X.cpu.gpr.r12
            rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kd : ∀ (Z : State) (V' : Addr → Byte), P1 Z V' → rdq(V', X.cpu.gpr.rdi) ≠ 0 → ∀ (Y : State) (t' : Nat),
      KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem
        (Vst (Vst V' Z.cpu.gpr.rax (toBytesLE 0#8 1)) (X.cpu.gpr.rsp - 32) (toBytesLE (arb_at.add 55) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r12 := Z.cpu.gpr.rax }.set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Z₂ : State) (V'' : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Z₂ → Agree F Z₂.proc.mm.mem V'' →
        Z₂.cpu.rip = arb_at.add 55 → Z₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Z₂.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Z₂.cpu.gpr.rbp = zl X.cpu.gpr → Z₂.cpu.gpr.r12 = Z.cpu.gpr.rax → Sv V'' X.cpu.gpr (e₂.add j₂) →
        P2 Z₂ V'' → GoG prof L o gev gP gE Z₂ t'') →
      GoG prof L o gev gP gE Y t')
    (kr : ∀ (Z₂ : State) (V'' : Addr → Byte), P2 Z₂ V'' → ∀ (Z' : State) (t' : Nat), KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (W3 V'' X.cpu.gpr.rdi Z₂.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr =
        { Z₂.cpu.gpr with
            rbx := X.cpu.gpr.rbx
            rbp := X.cpu.gpr.rbp
            r12 := X.cpu.gpr.r12
            rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t') :
    GoG prof L o gev gP gE X t := by
  have hlt := X.cpu.gpr.rsp.isLt
  have tn8 : (X.cpu.gpr.rsp - 8).toNat = X.cpu.gpr.rsp.toNat - 8 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn16 : (X.cpu.gpr.rsp - 16).toNat = X.cpu.gpr.rsp.toNat - 16 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn24 : (X.cpu.gpr.rsp - 24).toNat = X.cpu.gpr.rsp.toNat - 24 := by rw [BitVec.toNat_sub]; simp <;> omega
  have tn32 : (X.cpu.gpr.rsp - 32).toNat = X.cpu.gpr.rsp.toNat - 32 := by rw [BitVec.toNat_sub]; simp <;> omega
  have e16 : X.cpu.gpr.rsp - 8 - 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn8, tn16]
    simp <;> omega
  have e24 : X.cpu.gpr.rsp - 8 - 8 - 8 = X.cpu.gpr.rsp - 24 := by
    rw [e16]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn16, tn24]
    simp <;> omega
  have e32 : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
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
  have t8 : (X.cpu.gpr.rdi + 8#64).toNat = X.cpu.gpr.rdi.toNat + 8 := by
    rw [BitVec.toNat_add]; simp <;> omega
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the bytes outside the object as they were after the stores of `_chars`, `_limit` and `_len`
  have m1 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (x : Addr), x.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ x.toNat ∨ x.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs x 8).map (W3 W X.cpu.gpr.rdi p v) = (byteAddrs x 8).map W := by
    intro W p v x hx h
    have a1 := Tun.rd_Vst (Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4))
      (X.cpu.gpr.rdi + 8#64) (toBytesLE 0#32 4) x 8 (by rw [toBytesLE_length, t8]; omega) hx
      (by rw [toBytesLE_length, t8]; omega)
    have a2 := Tun.rd_Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) x 8
      (by rw [toBytesLE_length, t12]; omega) hx (by rw [toBytesLE_length, t12]; omega)
    have a3 := Tun.rd_Vst W X.cpu.gpr.rdi (toBytesLE p 8) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
    exact a1.trans (a2.trans a3)
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  have hst : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24 - 8) i) := by rw [e32]; exact hs4
  -- from 55: the stores, the `pop`s and the `ret`
  have fin : ∀ (U : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
      U.cpu.rip = arb_at.add 55 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → U.cpu.gpr.rbx = X.cpu.gpr.rdi →
      U.cpu.gpr.rbp = zl X.cpu.gpr → Sv W X.cpu.gpr (e₂.add j₂) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (W3 W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
        Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr =
          { U.cpu.gpr with
              rbx := X.cpu.gpr.rbx
              rbp := X.cpu.gpr.rbp
              r12 := X.cpu.gpr.r12
              rsp := X.cpu.gpr.rsp + 8 } →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U W t' hKU hAU hrU hus hub hup hSv k
    obtain ⟨hv12, hvbp, hvbx, hvra⟩ := hSv
    have hv : BitVec.setWidth 32 U.cpu.gpr.rbp = BitVec.setWidth 32 X.cpu.gpr.rsi := by
      rw [hup]
      exact sw_64_32 _
    have hW : W3 W U.cpu.gpr.rbx U.cpu.gpr.r12 (BitVec.setWidth 32 U.cpu.gpr.rbp) =
        W3 W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi) := by rw [hub, hv]
    have b1 : rdq(W3 W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 24) =
        X.cpu.gpr.rbx := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)]
      exact hvbx
    have b2 : rdq(W3 W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 16) =
        X.cpu.gpr.rbp := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
      exact hvbp
    have b3 : rdq(W3 W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 8) =
        X.cpu.gpr.r12 := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
      exact hv12
    have b4 : rdq(W3 W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp) =
        e₂.add j₂ := by
      rw [m1 W _ _ X.cpu.gpr.rsp hp8 (by omega)]
      exact hvra
    refine (c_55 prof).run c hin (fun j' g' _ V₄ => j' = 72 ∧
        g' =
          { U.cpu.gpr with
              rbx := X.cpu.gpr.rbx
              rbp := X.cpu.gpr.rbp
              r12 := X.cpu.gpr.r12
              rsp := X.cpu.gpr.rsp } ∧
        V₄ = W3 W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) hKU hAU hrU
      (vc_55 (by rw [hub]; exact w0) (by rw [hub]; exact w12) (by rw [hub]; exact w8) (by rw [hus]; exact h24)
        (by rw [hus, r16]; exact h16) (by rw [hus, r16, r8]; exact h8)
        fun _ => ⟨rfl, by rw [hW, hus, r16, r8, r0, b1, b2, b3], hW⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₁ hKU' hAU' hrU' hgU' -
    subst V₄
    have hsU : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_72 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact b4) ?_
    rintro Z' t₂ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₂ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl
  have hrip' : X.cpu.rip = arb_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `ja`
  refine (c_0 prof).run c hin (fun j' g' f' V' => j' = 14 ∧ g' = gA X.cpu.gpr ∧ V' = V0 V X.cpu.gpr ∧
      f' = subF (rfz X.cpu.rflags) (BitVec.setWidth 32 X.cpu.gpr.rsi) (BitVec.ofNat 32 1073741822)) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁, hfl⟩ Y t₁ hKY hAY hrY hgY hfY
  subst V₁
  have hcc : Y.cpu.rflags.cond 7 = decide (1073741822 < (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat) := by
    rw [hfY, hfl, c7]
  refine c.s_jcc_x hKY hAY hin (lt_len (by decide)) hrY (ja_14 _) hinT hT (tgt := 0) (by decide) ?_ ?_
  · -- the throw
    intro hc Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
    rw [hcc] at hc
    exact kt (of_decide_eq_true hc) Y₁ t₂ hK₁ hA₁ (by rw [hr₁, addr_add_zero]) (by rw [hg₁, hgY])
  intro hc Y₁ t₂ hK₁ hA₁ ⟨hr₁, hg₁⟩
  rw [hcc] at hc
  have hlim : (BitVec.setWidth 32 X.cpu.gpr.rsi).toNat ≤ 1073741822 := by
    have := of_decide_eq_false hc
    omega
  -- to the `call` of `operator new []`
  refine (c_20 prof).run c hin (fun j' g' _ V' => j' = 31 ∧ g' = gN X.cpu.gpr ∧ V' = V0 V X.cpu.gpr) hK₁ hA₁ hr₁
    (vc_20 fun _ => ⟨rfl, by rw [hg₁, hgY], rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₂ t₃ hK₂ hA₂ hr₂ hg₂ -
  subst V₂
  have hs2' : Y₂.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₂]; exact e24
  refine c.s_call hK₂ hA₂ hin (lt_len (by decide)) hr₂ (call_31 _) hinN hN (by decide) (by rw [hs2']; exact hst) ?_
  rintro Y₃ t₄ hK₃ hA₃ ⟨hr₃, hg₃⟩
  rw [hs2', e32] at hA₃
  have hg₃' : Y₃.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₃, hs2', e32, hg₂]
  refine kn hlim Y₃ t₄ hK₃ hA₃ hr₃ hg₃' ?_
  -- back from `operator new []`
  intro Z V' t₅ hKZ hAZ hrZ hzs hzb hzp hwn hdn hSv hP1
  have hrax := Z.cpu.gpr.rax.isLt
  -- the byte stored into `newBuf` is off the stack
  have mn : ∀ x : Addr, x.toNat + 8 ≤ 2 ^ 64 → X.cpu.gpr.rsp.toNat - 24 ≤ x.toNat → x.toNat ≤ X.cpu.gpr.rsp.toNat →
      (byteAddrs x 8).map (Vst V' Z.cpu.gpr.rax (toBytesLE 0#8 1)) = (byteAddrs x 8).map V' := fun x hx h1 h2 =>
    Tun.rd_Vst V' Z.cpu.gpr.rax (toBytesLE 0#8 1) x 8 (by rw [toBytesLE_length]; omega) hx
      (by rw [toBytesLE_length]; omega)
  refine (c_36 prof).run c hin (fun j' g' _ V'' =>
      g' = { Z.cpu.gpr with rdi := rdq(V', Z.cpu.gpr.rbx), r12 := Z.cpu.gpr.rax } ∧
      V'' = Vst V' Z.cpu.gpr.rax (toBytesLE 0#8 1) ∧
      ((j' = 55 ∧ rdq(V', X.cpu.gpr.rdi) = 0) ∨ (j' = 50 ∧ rdq(V', X.cpu.gpr.rdi) ≠ 0))) hKZ hAZ hrZ
    (vc_36 (by rw [hzb]; exact f0) hwn (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, by rw [← hzb]; exact h0⟩⟩)
      (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, by rw [← hzb]; exact h0⟩⟩)) ?_
  rintro j' g fl V₃ ⟨rfl, hV₃, h⟩ Y₄ t₆ hK₄ hA₄ hr₄ hg₄ -
  subst V₃
  rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · -- `_chars` null
    obtain ⟨hv12, hvbp, hvbx, hvra⟩ := hSv
    refine fin Y₄ _ t₆ hK₄ hA₄ hr₄ (by rw [hg₄]; exact hzs) (by rw [hg₄]; exact hzb) (by rw [hg₄]; exact hzp)
      ⟨by rw [mn _ (by rw [tn8]; omega) (by rw [tn8]; omega) (by rw [tn8]; omega)]; exact hv12,
        by rw [mn _ (by rw [tn16]; omega) (by rw [tn16]; omega) (by rw [tn16]; omega)]; exact hvbp,
        by rw [mn _ (by rw [tn24]; omega) (by rw [tn24]; omega) (by rw [tn24]; omega)]; exact hvbx,
        by rw [mn _ hp8 (by omega) (by omega)]; exact hvra⟩ ?_
    intro Z' t₇ hKZ' hAZ' hrZ' hgZ'
    refine kz Z V' hP1 h0 Z' t₇ hKZ' ?_ hrZ' ?_
    · rw [hg₄] at hAZ'
      exact hAZ'
    · rw [hgZ', hg₄, hzb]
  · -- `operator delete [] (_chars)`
    have hs4' : Y₄.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₄]; exact hzs
    refine c.s_call hK₄ hA₄ hin (lt_len (by decide)) hr₄ (call_50 _) hinD hD (by decide) (by rw [hs4']; exact hst) ?_
    rintro Y₅ t₇ hK₅ hA₅ ⟨hr₅, hg₅⟩
    rw [hs4', e32] at hA₅
    have hg₅' : Y₅.cpu.gpr =
        { Z.cpu.gpr with rdi := rdq(V', X.cpu.gpr.rdi), r12 := Z.cpu.gpr.rax }.set 4 (X.cpu.gpr.rsp - 32) := by
      rw [hg₅, hs4', e32, hg₄, hzb]
    refine kd Z V' hP1 h0 Y₅ t₇ hK₅ hA₅ hr₅ hg₅' ?_
    intro Z₂ V'' t₈ hK₆ hA₆ hr₆ hz2s hz2b hz2p _ hSv₂ hP2
    refine fin Z₂ V'' t₈ hK₆ hA₆ hr₆ hz2s hz2b hz2p hSv₂ ?_
    intro Z' t₉ hKZ' hAZ' hrZ' hgZ'
    exact kr Z₂ V'' hP2 Z' t₉ hKZ' hAZ' hrZ' hgZ'

end FV7z.Arb
