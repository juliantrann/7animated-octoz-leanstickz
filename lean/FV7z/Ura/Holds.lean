import FV7z.Ura.Cuts
import FV7z.Onw
import FV7z.Wmc.Code
import FV7z.Wmc.Blocks
import FV7z.Lemmas.LeafRet
import FV7z.Lemmas.Lock2
import FV7z.Tun.Inv
/-!
# `UString::ReAlloc` (PLAN.md §M, M1)

7-Zip 26.06's `UString::ReAlloc (newLimit)` at `0x44cfc0` in `7zzs` (`CPP/Common/MyString.cpp`), `this` in `rdi`,
`newLimit` in `esi`: `newBuf = new wchar_t[newLimit + 1]` (`call` at 24 to `operator new`, `Onw.onw_at + 64`, with
`4 newLimit + 4` bytes), `wmemcpy (newBuf, _chars, _len + 1)` (`call` at 44 to `Wmc.wmc_at`; `_chars` the 8 bytes at
`this`, `_len` the 4 at `this + 8`), `delete [] _chars` unless null (`call` at 57 to the thunk at `0x6014f0`), then
`_chars = newBuf` and `_limit` (the 4 bytes at `this + 12`) = `newLimit`. `push r12; push rbp; push rbx`, `rbx` =
`this`, `rbp` = `newLimit` across the calls and `r12` = `newBuf` after the first, `pop rbx; pop rbp; pop r12; ret`
(72).

The callees are hypotheses (`kn`, `kw`, `kd`), as in `FV7z/Cib/Holds.lean`: a continuation at each entry, given the
run from its return (`rsp` 24 below the entry's, `rbx`, `rbp` and `r12` as the caller left them, the saved registers
and the return address as they were: `Sv`) and the callee's own post (`Pn`, `Pw`, `Pd`).

- `zl`, `gN`, `VN`: `newLimit` zero-extended; the registers and the bytes at the first `call`.
- `gW`: the registers at the `call` of `wmemcpy`; `VE`: the bytes after the stores of `_chars` and `_limit`.
- `Sv`: the saved `rbx`, `rbp`, `r12` and the return address in the bytes.
- `vc_0`, `vc_29`, `vc_49`, `vc_62`: the verification conditions of the pieces.
- `ura_ok`: from the entry, through the callees, to the return address (`kr0` for a null `_chars`, else `kr1`).
-/
open ZellicX86 Decode FV7z FV7z.Leaf FV7z.Fn
namespace FV7z.Ura

/-- The `call`s to `operator new`, `wmemcpy` and the thunk of `operator delete []`. -/
def pcn : List Byte := [0xe8, 0xd3, 0x59, 0x1b, 0x00]
theorem pcn_0 : ∀ feat, Dec feat pcn 0 (FV7z.mk .call 64 [.rel 1792467] 5) := by dec_rfl
theorem wc_24 : pcn <+: ura.drop 24 := by decide +kernel
theorem call_24 (feat : Features) : Dec feat ura 24 (FV7z.mk .call 64 [.rel 1792467] 5) :=
  Dec.shift (j := 24) (k := 0) (pcn_0 feat) wc_24 (Nat.zero_le _)
theorem tgt_24 : ura_at.add (24 + 5) + BitVec.ofNat 64 1792467 = Onw.onw_at.add 64 := by decide
def pcw : List Byte := [0xe8, 0x0f, 0x03, 0x21, 0x00]
theorem pcw_0 : ∀ feat, Dec feat pcw 0 (FV7z.mk .call 64 [.rel 2163471] 5) := by dec_rfl
theorem wc_44 : pcw <+: ura.drop 44 := by decide +kernel
theorem call_44 (feat : Features) : Dec feat ura 44 (FV7z.mk .call 64 [.rel 2163471] 5) :=
  Dec.shift (j := 44) (k := 0) (pcw_0 feat) wc_44 (Nat.zero_le _)
theorem tgt_44 : ura_at.add (44 + 5) + BitVec.ofNat 64 2163471 = Wmc.wmc_at.add 0 := by decide
def pcd : List Byte := [0xe8, 0xf2, 0x44, 0x1b, 0x00]
theorem pcd_0 : ∀ feat, Dec feat pcd 0 (FV7z.mk .call 64 [.rel 1787122] 5) := by dec_rfl
theorem wc_57 : pcd <+: ura.drop 57 := by decide +kernel
theorem call_57 (feat : Features) : Dec feat ura 57 (FV7z.mk .call 64 [.rel 1787122] 5) :=
  Dec.shift (j := 57) (k := 0) (pcd_0 feat) wc_57 (Nat.zero_le _)

/-- The `ret`. -/
def pret : List Byte := [0xc3]
theorem pret_0 : ∀ feat, Dec feat pret 0 (FV7z.mk .ret 64 [] 1) := by dec_rfl
theorem w_72 : pret <+: ura.drop 72 := by decide +kernel
theorem ret_72 (feat : Features) : Dec feat ura 72 (FV7z.mk .ret 64 [] 1) :=
  Dec.shift (j := 72) (k := 0) (pret_0 feat) w_72 (Nat.zero_le _)

/-- `newLimit` (`esi`) zero-extended. -/
abbrev zl (g : Gprs) : BitVec 64 := BitVec.setWidth 64 (BitVec.setWidth 32 g.rsi)

/-- The registers at the first `call`: `rax` = `rbp` = `newLimit`, `rbx` = `this`, `rdi` = `4 newLimit + 4`, 24
below the entry. -/
abbrev gN (g : Gprs) : Gprs :=
  { g with rax := zl g, rbp := zl g, rbx := g.rdi, rsp := g.rsp - 8 - 8 - 8, rdi := zl g * 4#64 + 4#64 }

/-- The bytes at the first `call`: `r12`, `rbp`, `rbx` pushed. -/
abbrev VN (V : Addr → Byte) (g : Gprs) : Addr → Byte :=
  Vst (Vst (Vst V (g.rsp - 8) (toBytesLE g.r12 8)) (g.rsp - 8 - 8) (toBytesLE g.rbp 8)) (g.rsp - 8 - 8 - 8)
    (toBytesLE g.rbx 8)

/-- The registers at the `call` of `wmemcpy` for the bytes `V` (`z` the registers back from `operator new`, `x` the
entry's): `rdi` = `r12` = `newBuf`, `rsi` = `_chars`, `edx` = `_len + 1`, `rax` = `_len`. -/
abbrev gW (V : Addr → Byte) (z x : Gprs) : Gprs :=
  { z with
      rsi := rdq(V, x.rdi),
      r12 := z.rax,
      rax := (rdd(V, x.rdi + 8#64)).setWidth 64,
      rdi := z.rax,
      rdx := BitVec.setWidth 64 (BitVec.setWidth 32 ((rdd(V, x.rdi + 8#64)).setWidth 64 + 1#64)) }

/-- The bytes after `_chars` = `p` and `_limit` = `v` for the object at `b`. -/
abbrev VE (V : Addr → Byte) (b : Addr) (p : BitVec 64) (v : BitVec 32) : Addr → Byte :=
  Vst (Vst V b (toBytesLE p 8)) (b + 12#64) (toBytesLE v 4)

/-- The saved `rbx`, `rbp`, `r12` (the entry's `x`) and the return address `r` in the bytes `V`. -/
abbrev Sv (V : Addr → Byte) (x : Gprs) (r : Addr) : Prop :=
  rdq(V, x.rsp - 24) = x.rbx ∧ rdq(V, x.rsp - 16) = x.rbp ∧ rdq(V, x.rsp - 8) = x.r12 ∧ rdq(V, x.rsp) = r

variable {F : Footprint} {Wl : List Rgn}

/-- `push r12; mov eax, esi; push rbp; mov rbp, rax; push rbx; mov rbx, rdi; lea rdi, [rax * 4 + 4]` to the
`call` at 24. -/
theorem vc_0 {g : Gprs} {f : Rflags} {V : Addr → Byte}
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8) i)) (hs2 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (g.rsp - 8 - 8 - 8) i)) :
    W_0 F Wl (fun j' g' _ V' => j' = 24 ∧ g' = gN g ∧ V' = VN V g) g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hs1 hs2 hs3 ⊢
  wpx [W_0, o0, gN, VN, zl]
  all_goals repeat'
    first
    | exact rfl
    | assumption
    | exact trivial
    | apply And.intro
    | intro _

/-- Back from `operator new`: `mov rsi, [rbx]; mov r12, rax; mov eax, [rbx + 8]; mov rdi, r12; lea edx, [rax + 1]`
to the `call` at 44. -/
theorem vc_29 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbx : g.rbx = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i)) (f8 : ∀ i < 4, Foot F.data (Addr.add (p + 8#64) i))
    (h : ∀ fl, Q 44
      { g with
          rsi := rdq(V, p),
          r12 := g.rax,
          rax := (rdd(V, p + 8#64)).setWidth 64,
          rdi := g.rax,
          rdx := BitVec.setWidth 64 (BitVec.setWidth 32 ((rdd(V, p + 8#64)).setWidth 64 + 1#64)) } fl V) :
    W_29 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx f0 f8 h ⊢
  subst hbx
  wpx [W_29, o1]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

/-- Back from `wmemcpy`: `mov rdi, [rbx]; test rdi, rdi; je 62`, else to the `call` at 57. -/
theorem vc_49 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post} {p : Addr} (hbx : g.rbx = p)
    (f0 : ∀ i < 8, Foot F.data (Addr.add p i))
    (h62 : rdq(V, p) = 0 → ∀ fl, Q 62 { g with rdi := rdq(V, p) } fl V)
    (h57 : rdq(V, p) ≠ 0 → ∀ fl, Q 57 { g with rdi := rdq(V, p) } fl V) :
    W_49 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at hbx f0 h62 h57 ⊢
  subst hbx
  by_cases h1 : rdq(V, rbx) = 0
  · have hb : (rdq(V, rbx) == 0) = true := beq_iff_eq.2 h1
    wpx [W_49, o2, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h62 h1 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _
  · have hb : (rdq(V, rbx) == 0) = false := beq_eq_false_iff_ne.2 h1
    wpx [W_49, o2, hb, BitVec.and_self, Bool.false_eq_true, Bool.true_eq_false, false_implies, implies_true]
    all_goals repeat'
      first
      | exact h57 h1 _
      | assumption
      | exact trivial
      | apply And.intro
      | intro _

/-- `mov [rbx], r12; mov [rbx + 12], ebp; pop rbx; pop rbp; pop r12` to the `ret` at 72. -/
theorem vc_62 {g : Gprs} {f : Rflags} {V : Addr → Byte} {Q : Post}
    (w0 : ∀ i < 8, Foot Wl (Addr.add g.rbx i)) (w12 : ∀ i < 4, Foot Wl (Addr.add (g.rbx + 12#64) i))
    (hl0 : ∀ i < 8, Foot F.data (Addr.add g.rsp i)) (hl1 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8) i))
    (hl2 : ∀ i < 8, Foot F.data (Addr.add (g.rsp + 8 + 8) i))
    (h : ∀ fl, Q 72
      { g with
          rbx := rdq(VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp),
          rbp := rdq(VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8),
          r12 := rdq(VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp), g.rsp + 8 + 8),
          rsp := g.rsp + 8 + 8 + 8 } fl
      (VE V g.rbx g.r12 (BitVec.setWidth 32 g.rbp))) :
    W_62 F Wl Q g f V := by
  obtain ⟨rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15⟩ := g
  dsimp only at w0 w12 hl0 hl1 hl2 h ⊢
  wpx [W_62, o3]
  all_goals repeat' (first | exact h _ | assumption | exact trivial | apply And.intro | intro _)

variable {prof : Profile} {L : List (Addr × List Byte)} {s₀ : State} {o : Oracle}
  {gev : List Event} {gP : State → Nat → List Event → Prop} {gE : Outcome → List Event → Prop}
  {X : State} {t : Nat} {V : Addr → Byte}

/-- `UString::ReAlloc (newLimit)` (`this` = `rdi`, `newLimit` = `esi`) from its entry. At `operator new`'s entry the
registers are `gN`, `rsp` 32 below the entry's, the bytes `VN` with the return address pushed (`kn`); back at
`ura_at + 29` (`Sv`, `Pn`), at `wmemcpy`'s entry with the registers `gW` (`kw`); back at `ura_at + 49` with `r12` =
`newBuf` (`Pw`), at the return address with `_chars` = `newBuf`, `_limit` = `newLimit` (`VE`) if `_chars` was null
(`kr0`), else at the thunk of `operator delete []` with `rdi` = `_chars` (`kd`), and back at `ura_at + 62` (`Pd`) at
the return address likewise (`kr1`). -/
theorem ura_ok {Pn : State → (Addr → Byte) → Prop} {Pw Pd : State → State → (Addr → Byte) → Prop}
    (c : Seg prof F Wl L s₀ o) (hin : CodeIn L ura_at ura) (hinN : CodeIn L Onw.onw_at Onw.onw)
    (hinW : CodeIn L Wmc.wmc_at Wmc.wmc) {codeD : List Byte} (hinD : CodeIn L 0x6014f0#64 codeD)
    (hD : 0 < codeD.length)
    (hK : KeptW Wl s₀ X) (hA : Agree F X.proc.mm.mem V) (hrip : X.cpu.rip = ura_at)
    (hp : 32 ≤ X.cpu.gpr.rsp.toNat) (hp8 : X.cpu.gpr.rsp.toNat + 8 ≤ 2 ^ 64)
    (hs1 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 8) i))
    (hs2 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 16) i))
    (hs3 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 24) i))
    (hs4 : ∀ i < 8, Foot Wl (Addr.add (X.cpu.gpr.rsp - 32) i))
    (hl : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rsp i))
    (fr0 : ∀ i < 8, Foot F.data (Addr.add X.cpu.gpr.rdi i))
    (fr8 : ∀ i < 4, Foot F.data (Addr.add (X.cpu.gpr.rdi + 8#64) i))
    (fw0 : ∀ i < 8, Foot Wl (Addr.add X.cpu.gpr.rdi i))
    (fw12 : ∀ i < 4, Foot Wl (Addr.add (X.cpu.gpr.rdi + 12#64) i))
    (hq : X.cpu.gpr.rdi.toNat + 16 ≤ 2 ^ 64)
    (hd : X.cpu.gpr.rdi.toNat + 16 ≤ X.cpu.gpr.rsp.toNat - 24 ∨ X.cpu.gpr.rsp.toNat + 8 ≤ X.cpu.gpr.rdi.toNat)
    {e₂ : Addr} {code₂ : List Byte} (hin₂ : CodeIn L e₂ code₂) {j₂ : Nat} (h₂ : j₂ < code₂.length)
    (kn : ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst (VN V X.cpu.gpr) (X.cpu.gpr.rsp - 32) (toBytesLE (ura_at.add 29) 8)) →
      Y.cpu.rip = Onw.onw_at.add 64 → Y.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Zn : State) (V₁ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zn → Agree F Zn.proc.mm.mem V₁ →
        Zn.cpu.rip = ura_at.add 29 → Zn.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Zn.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zn.cpu.gpr.rbp = zl X.cpu.gpr → Sv V₁ X.cpu.gpr (e₂.add j₂) → Pn Zn V₁ → GoG prof L o gev gP gE Zn t'') →
      GoG prof L o gev gP gE Y t')
    (kw : ∀ (Zn : State) (V₁ : Addr → Byte), Pn Zn V₁ → ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₁ (X.cpu.gpr.rsp - 32) (toBytesLE (ura_at.add 49) 8)) →
      Y.cpu.rip = Wmc.wmc_at → Y.cpu.gpr = (gW V₁ Zn.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Zw : State) (V₂ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zw → Agree F Zw.proc.mm.mem V₂ →
        Zw.cpu.rip = ura_at.add 49 → Zw.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Zw.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zw.cpu.gpr.rbp = zl X.cpu.gpr → Zw.cpu.gpr.r12 = Zn.cpu.gpr.rax → Sv V₂ X.cpu.gpr (e₂.add j₂) →
        Pw Zn Zw V₂ → GoG prof L o gev gP gE Zw t'') →
      GoG prof L o gev gP gE Y t')
    (kd : ∀ (Zn Zw : State) (V₂ : Addr → Byte), Pw Zn Zw V₂ → rdq(V₂, X.cpu.gpr.rdi) ≠ 0 →
      ∀ (Y : State) (t' : Nat), KeptW Wl s₀ Y →
      Agree F Y.proc.mm.mem (Vst V₂ (X.cpu.gpr.rsp - 32) (toBytesLE (ura_at.add 62) 8)) →
      Y.cpu.rip = 0x6014f0#64 →
      Y.cpu.gpr = { Zw.cpu.gpr with rdi := rdq(V₂, X.cpu.gpr.rdi) }.set 4 (X.cpu.gpr.rsp - 32) →
      (∀ (Zd : State) (V₃ : Addr → Byte) (t'' : Nat), KeptW Wl s₀ Zd → Agree F Zd.proc.mm.mem V₃ →
        Zd.cpu.rip = ura_at.add 62 → Zd.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → Zd.cpu.gpr.rbx = X.cpu.gpr.rdi →
        Zd.cpu.gpr.rbp = zl X.cpu.gpr → Zd.cpu.gpr.r12 = Zn.cpu.gpr.rax → Sv V₃ X.cpu.gpr (e₂.add j₂) →
        Pd Zn Zd V₃ → GoG prof L o gev gP gE Zd t'') →
      GoG prof L o gev gP gE Y t')
    (kr0 : ∀ (Zn Zw : State) (V₂ : Addr → Byte) (Z' : State) (t' : Nat), Pw Zn Zw V₂ →
      rdq(V₂, X.cpu.gpr.rdi) = 0 → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VE V₂ X.cpu.gpr.rdi Zn.cpu.gpr.rax (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zw.cpu.gpr with rdi := rdq(V₂, X.cpu.gpr.rdi), rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp,
        r12 := X.cpu.gpr.r12, rsp := X.cpu.gpr.rsp + 8 } →
      GoG prof L o gev gP gE Z' t')
    (kr1 : ∀ (Zn Zd : State) (V₃ : Addr → Byte) (Z' : State) (t' : Nat), Pd Zn Zd V₃ → KeptW Wl s₀ Z' →
      Agree F Z'.proc.mm.mem (VE V₃ X.cpu.gpr.rdi Zn.cpu.gpr.rax (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
      Z'.cpu.rip = e₂.add j₂ →
      Z'.cpu.gpr = { Zd.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
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
  have c32 : X.cpu.gpr.rsp - 24 - 8 = X.cpu.gpr.rsp - 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, tn24, tn32]
    simp <;> omega
  have a16 : X.cpu.gpr.rsp - 24 + 8 = X.cpu.gpr.rsp - 16 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn24, tn16]
    simp <;> omega
  have a8 : X.cpu.gpr.rsp - 16 + 8 = X.cpu.gpr.rsp - 8 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, tn16, tn8]
    simp <;> omega
  have e8 : X.cpu.gpr.rsp - 8 + 8 = X.cpu.gpr.rsp := BitVec.sub_add_cancel _ _
  have t12 : (X.cpu.gpr.rdi + 12#64).toNat = X.cpu.gpr.rdi.toNat + 12 := by
    rw [BitVec.toNat_add]; simp <;> omega
  -- the bytes outside the object as they were after the stores of `_chars` and `_limit`
  have m1 : ∀ (W : Addr → Byte) (p : BitVec 64) (v : BitVec 32) (y : Addr), y.toNat + 8 ≤ 2 ^ 64 →
      (X.cpu.gpr.rdi.toNat + 16 ≤ y.toNat ∨ y.toNat + 8 ≤ X.cpu.gpr.rdi.toNat) →
      (byteAddrs y 8).map (VE W X.cpu.gpr.rdi p v) = (byteAddrs y 8).map W := by
    intro W p v y hy h
    have a1 := Tun.rd_Vst (Vst W X.cpu.gpr.rdi (toBytesLE p 8)) (X.cpu.gpr.rdi + 12#64) (toBytesLE v 4) y 8
      (by rw [toBytesLE_length, t12]; omega) hy (by rw [toBytesLE_length, t12]; omega)
    have a2 := Tun.rd_Vst W X.cpu.gpr.rdi (toBytesLE p 8) y 8 (by rw [toBytesLE_length]; omega) hy
      (by rw [toBytesLE_length]; omega)
    exact a1.trans a2
  have h24 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 24) i) := fun i hi => c.hws _ (hs3 i hi)
  have h16 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 16) i) := fun i hi => c.hws _ (hs2 i hi)
  have h8 : ∀ i < 8, Foot F.data (Addr.add (X.cpu.gpr.rsp - 8) i) := fun i hi => c.hws _ (hs1 i hi)
  -- from 62 to the return address, either way
  have fin : ∀ (U : State) (W : Addr → Byte) (t' : Nat), KeptW Wl s₀ U → Agree F U.proc.mm.mem W →
      U.cpu.rip = ura_at.add 62 → U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 → U.cpu.gpr.rbx = X.cpu.gpr.rdi →
      U.cpu.gpr.rbp = zl X.cpu.gpr → Sv W X.cpu.gpr (e₂.add j₂) →
      (∀ (Z' : State) (t'' : Nat), KeptW Wl s₀ Z' →
        Agree F Z'.proc.mm.mem (VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) →
        Z'.cpu.rip = e₂.add j₂ →
        Z'.cpu.gpr = { U.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          rsp := X.cpu.gpr.rsp + 8 } →
        GoG prof L o gev gP gE Z' t'') →
      GoG prof L o gev gP gE U t' := by
    intro U W t' hKU hAU hrU hus hub hup hsv k
    have hv : BitVec.setWidth 32 U.cpu.gpr.rbp = BitVec.setWidth 32 X.cpu.gpr.rsi := by
      rw [hup]
      exact sw_64_32 _
    have hb1 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 24) =
        X.cpu.gpr.rbx := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 24) (by rw [tn24]; omega) (by rw [tn24]; omega)]
      exact hsv.1
    have hb2 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 16) =
        X.cpu.gpr.rbp := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 16) (by rw [tn16]; omega) (by rw [tn16]; omega)]
      exact hsv.2.1
    have hb3 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp - 8) =
        X.cpu.gpr.r12 := by
      rw [m1 W _ _ (X.cpu.gpr.rsp - 8) (by rw [tn8]; omega) (by rw [tn8]; omega)]
      exact hsv.2.2.1
    have hb4 : rdq(VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi), X.cpu.gpr.rsp) =
        e₂.add j₂ := by
      rw [m1 W _ _ X.cpu.gpr.rsp hp8 (by omega)]
      exact hsv.2.2.2
    refine (c_62 prof).run c hin (fun j' g' _ V' => j' = 72 ∧
        g' = { U.cpu.gpr with rbx := X.cpu.gpr.rbx, rbp := X.cpu.gpr.rbp, r12 := X.cpu.gpr.r12,
          rsp := X.cpu.gpr.rsp } ∧
        V' = VE W X.cpu.gpr.rdi U.cpu.gpr.r12 (BitVec.setWidth 32 X.cpu.gpr.rsi)) hKU hAU hrU
      (vc_62 (by rw [hub]; exact fw0) (by rw [hub]; exact fw12) (by rw [hus]; exact h24)
        (by rw [hus, a16]; exact h16) (by rw [hus, a16, a8]; exact h8)
        fun _ => ⟨rfl, by rw [hub, hv, hus, a16, a8, e8, hb1, hb2, hb3], by rw [hub, hv]⟩) ?_
    rintro j' g fl V₄ ⟨rfl, rfl, hV₄⟩ U' t₄ hKU' hAU' hrU' hgU' -
    subst V₄
    have hsU : U'.cpu.gpr.rsp = X.cpu.gpr.rsp := by rw [hgU']
    refine c.s_ret hKU' hAU' hin (lt_len (by decide)) hrU' (ret_72 _) (by rw [hsU]; exact hl) hin₂ h₂
      (by rw [hsU]; exact hb4) ?_
    rintro Z' t₅ hKZ' hAZ' ⟨hrZ', hgZ'⟩
    refine k Z' t₅ hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU']
    try rfl
  have hrip' : X.cpu.rip = ura_at.add 0 := by rw [addr_add_zero]; exact hrip
  -- to the `call` of `operator new`
  refine (c_0 prof).run c hin (fun j' g' _ V' => j' = 24 ∧ g' = gN X.cpu.gpr ∧ V' = VN V X.cpu.gpr) hK hA hrip'
    (vc_0 hs1 (by rw [e16]; exact hs2) (by rw [e24]; exact hs3)) ?_
  rintro j' g fl V₁ ⟨rfl, rfl, hV₁⟩ Y t₁ hKY hAY hrY hgY -
  subst V₁
  have hsY : Y.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgY]; exact e24
  have hst : ∀ i < 8, Foot Wl (Addr.add (Y.cpu.gpr.rsp - 8) i) := by rw [hsY, c32]; exact hs4
  refine c.s_call_x hKY hAY hin (lt_len (by decide)) hrY (call_24 _) hinN (tgt := 64) (Onw.lt_len (by decide))
    tgt_24 hst ?_
  rintro Y₂ t₂ hK₂ hA₂ ⟨hr₂, hg₂⟩
  rw [hsY, c32] at hA₂
  have hg₂' : Y₂.cpu.gpr = (gN X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by rw [hg₂, hsY, c32, hgY]
  refine kn Y₂ t₂ hK₂ hA₂ hr₂ hg₂' ?_
  -- back from `operator new`
  intro Zn V₁ t₃ hKn hAn hrn hns hnb hnp hsv1 hPn
  refine (c_29 prof).run c hin (fun j' g' _ V' => j' = 44 ∧ g' = gW V₁ Zn.cpu.gpr X.cpu.gpr ∧ V' = V₁) hKn hAn hrn
    (vc_29 hnb fr0 fr8 fun _ => ⟨rfl, rfl, rfl⟩) ?_
  rintro j' g fl V₂ ⟨rfl, rfl, hV₂⟩ Y₃ t₄ hK₃ hA₃ hr₃ hg₃ -
  subst V₂
  have hs3' : Y₃.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hg₃]; exact hns
  have hst3 : ∀ i < 8, Foot Wl (Addr.add (Y₃.cpu.gpr.rsp - 8) i) := by rw [hs3', c32]; exact hs4
  refine c.s_call_x hK₃ hA₃ hin (lt_len (by decide)) hr₃ (call_44 _) hinW (tgt := 0) (Wmc.lt_len (by decide))
    tgt_44 hst3 ?_
  rintro Y₄ t₅ hK₄ hA₄ ⟨hr₄, hg₄⟩
  rw [hs3', c32] at hA₄
  have hg₄' : Y₄.cpu.gpr = (gW V₁ Zn.cpu.gpr X.cpu.gpr).set 4 (X.cpu.gpr.rsp - 32) := by
    rw [hg₄, hs3', c32, hg₃]
  refine kw Zn V₁ hPn Y₄ t₅ hK₄ hA₄ (by rw [hr₄, addr_add_zero]) hg₄' ?_
  -- back from `wmemcpy`
  intro Zw V₂ t₆ hKw hAw hrw hws hwb hwp hw12 hsv2 hPw
  refine (c_49 prof).run c hin (fun j' g' _ V' => V' = V₂ ∧ g' = { Zw.cpu.gpr with rdi := rdq(V₂, X.cpu.gpr.rdi) } ∧
      ((j' = 62 ∧ rdq(V₂, X.cpu.gpr.rdi) = 0) ∨ (j' = 57 ∧ rdq(V₂, X.cpu.gpr.rdi) ≠ 0))) hKw hAw hrw
    (vc_49 hwb fr0 (fun h0 _ => ⟨rfl, rfl, .inl ⟨rfl, h0⟩⟩) (fun h0 _ => ⟨rfl, rfl, .inr ⟨rfl, h0⟩⟩)) ?_
  rintro j' g fl V₃ ⟨hV₃, rfl, h⟩ U t₇ hKU hAU hrU hgU -
  subst V₃
  have hsU : U.cpu.gpr.rsp = X.cpu.gpr.rsp - 24 := by rw [hgU]; exact hws
  have hbU : U.cpu.gpr.rbx = X.cpu.gpr.rdi := by rw [hgU]; exact hwb
  have hpU : U.cpu.gpr.rbp = zl X.cpu.gpr := by rw [hgU]; exact hwp
  rcases h with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · -- a null `_chars`: no `delete []`
    refine fin U V₂ t₇ hKU hAU hrU hsU hbU hpU hsv2 ?_
    intro Z' t₈ hKZ' hAZ' hrZ' hgZ'
    have hr12 : U.cpu.gpr.r12 = Zn.cpu.gpr.rax := by rw [hgU]; exact hw12
    rw [hr12] at hAZ'
    refine kr0 Zn Zw V₂ Z' t₈ hPw h0 hKZ' hAZ' hrZ' ?_
    rw [hgZ', hgU]
  · -- `delete [] _chars`
    have hst5 : ∀ i < 8, Foot Wl (Addr.add (U.cpu.gpr.rsp - 8) i) := by rw [hsU, c32]; exact hs4
    refine c.s_call hKU hAU hin (lt_len (by decide)) hrU (call_57 _) hinD hD (by decide) hst5 ?_
    rintro Y₅ t₈ hK₅ hA₅ ⟨hr₅, hg₅⟩
    rw [hsU, c32] at hA₅
    have hg₅' : Y₅.cpu.gpr = { Zw.cpu.gpr with rdi := rdq(V₂, X.cpu.gpr.rdi) }.set 4 (X.cpu.gpr.rsp - 32) := by
      rw [hg₅, hsU, c32, hgU]
    refine kd Zn Zw V₂ hPw h0 Y₅ t₈ hK₅ hA₅ hr₅ hg₅' ?_
    intro Zd V₃ t₉ hKd hAd hrd hds hdb hdp hd12 hsv3 hPd
    refine fin Zd V₃ t₉ hKd hAd hrd hds hdb hdp hsv3 ?_
    intro Z' t₁₀ hKZ' hAZ' hrZ' hgZ'
    rw [hd12] at hAZ'
    exact kr1 Zn Zd V₃ Z' t₁₀ hPd hKZ' hAZ' hrZ' hgZ'

end FV7z.Ura
